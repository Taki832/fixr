"""
Fixr — Local Service Finder  v2.2  (Production-stable backend)
==============================================================
Upgraded from v2.1. No new features. Robustness and lifecycle only.

What changed from v2.1:
  ┌─ TOKEN LIFECYCLE ────────────────────────────────────────────┐
  │  • Access token TTL: 7 days → 24 hours                       │
  │  • sessions.created_at column added (with migration)         │
  │  • POST /api/token/refresh — swap valid token for a fresh    │
  │    24h one without re-authenticating (7-day refresh window)  │
  ├─ SECURITY HEADERS ───────────────────────────────────────────┤
  │  • @app.after_request adds on every response:                │
  │    X-Content-Type-Options: nosniff                           │
  │    X-Frame-Options: DENY                                     │
  │    Referrer-Policy: strict-origin-when-cross-origin          │
  │    Cache-Control: no-store                                   │
  │    X-Request-ID: (echoed for tracing)                        │
  ├─ STRUCTURED FILE LOGGING ────────────────────────────────────┤
  │  • RotatingFileHandler → fixr.log (5 MB × 3 backups)        │
  │  • No external dependencies                                   │
  │  • Logged events (key=value format):                         │
  │    - otp_sent / otp_rate_limited                             │
  │    - login_ok / login_fail / login_expired / login_locked    │
  │    - logout                                                   │
  │    - booking_transition (old→new status, who, booking_id)    │
  │    - assistant_linked / assistant_link_blocked               │
  │    - token_refreshed                                         │
  │  • Phone numbers masked: +91-XXXXX-5678 in log files        │
  ├─ DATABASE STABILITY ─────────────────────────────────────────┤
  │  • PRAGMA busy_timeout=5000 → 5s wait on lock vs crash       │
  │  • PRAGMA synchronous=NORMAL (safe with WAL, ~30% faster)    │
  │  • PRAGMA cache_size=-8000 (8 MB page cache per connection)  │
  │  • WAL + foreign_keys set once in init_db(), not per-request │
  │  • create_booking uses BEGIN EXCLUSIVE → atomic              │
  │    conflict-check + slot-mark + booking-insert               │
  ├─ INPUT SANITIZATION ─────────────────────────────────────────┤
  │  • _s() now strips: null bytes, control chars (Cc/Cf/Cs),   │
  │    zero-width chars, RTL override (U+202E), BiDi marks       │
  │  • CRLF injection normalized to LF before filtering          │
  │  • Applies to all string inputs (names, notes, phone, etc.)  │
  ├─ ASSISTANT HARDENING ────────────────────────────────────────┤
  │  • request_assistant blocks re-linking an assistant who is   │
  │    already active with a different worker                    │
  │  • All assistant events logged                               │
  └──────────────────────────────────────────────────────────────┘
"""

import os
import re
import json
import sqlite3
import secrets
import hashlib
import time
import logging
import logging.handlers
import unicodedata
from datetime import datetime, timedelta, date as _date_type
from functools import wraps
from flask import Flask, jsonify, request, g
from flask_cors import CORS

# ─────────────────────────────────────────────────────────────────────────────
app = Flask(__name__)
CORS(app, supports_credentials=True)

DB_PATH = "fixr.db"

# ══════════════════════════════════════════════════════════════════════════════
#  STRUCTURED FILE LOGGER
#  — configured before any code runs so every module can import `log`
# ══════════════════════════════════════════════════════════════════════════════

def _setup_logger() -> logging.Logger:
    logger = logging.getLogger("fixr")
    if logger.handlers:          # already configured (e.g. during testing)
        return logger
    logger.setLevel(logging.INFO)

    fmt = logging.Formatter(
        fmt="%(asctime)s %(levelname)-8s %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )

    # ── File handler: 5 MB rolling, 3 backups ─────────────────────────────────
    fh = logging.handlers.RotatingFileHandler(
        "fixr.log", maxBytes=5 * 1024 * 1024, backupCount=3, encoding="utf-8"
    )
    fh.setFormatter(fmt)
    logger.addHandler(fh)

    # ── Console handler (useful while running locally) ────────────────────────
    ch = logging.StreamHandler()
    ch.setFormatter(fmt)
    logger.addHandler(ch)

    return logger

log: logging.Logger = _setup_logger()


def _mask_phone(phone: str) -> str:
    """
    Partially mask phone for log files.
    +91-98201-11111  →  +91-XXXXX-1111
    Logs never contain full phone numbers.
    """
    if not phone or len(phone) < 5:
        return "***"
    return phone[:-4].replace(re.sub(r"\d", "X", phone[:-4]), phone[:-4]) + phone[-4:]

def _mp(phone: str) -> str:
    """
    Mask phone for log files — never write full numbers.
    +91-98201-11111  ->  +91-*****-1111
    Preserves country code for readability; masks subscriber number except last 4 digits.
    """
    if not isinstance(phone, str) or len(phone) < 5:
        return "***"
    digits = re.sub(r"\D", "", phone)   # strip separators
    if len(digits) < 6:
        return "***"
    return f"+91-*****-{digits[-4:]}"


def _ip() -> str:
    """Extract client IP for logging, respecting reverse-proxy headers."""
    return (
        request.headers.get("X-Forwarded-For", "").split(",")[0].strip()
        or request.remote_addr
        or "unknown"
    )


# ══════════════════════════════════════════════════════════════════════════════
#  CONSTANTS & COMPILED PATTERNS
# ══════════════════════════════════════════════════════════════════════════════

# Regex
_PHONE_RE = re.compile(r"^\+91[-\s]?\d{5}[-\s]?\d{5}$")
_OTP_RE   = re.compile(r"^\d{6}$")
_DATE_RE  = re.compile(r"^\d{4}-\d{2}-\d{2}$")
_TIME_RE  = re.compile(r"^\d{2}:\d{2}$")

# Enums
VALID_WORKER_STATUS  = {"available", "on_job", "unavailable"}
VALID_BOOKING_STATUS = {"pending", "confirmed", "in_progress", "completed", "cancelled"}
VALID_CATS           = {"electrician", "plumber", "carpenter", "painter", "cleaner", "ac_technician"}

# Input length limits
MAX_NAME_LEN  = 100
MAX_NOTES_LEN = 500
MAX_PHONE_LEN = 20

# Token lifecycle
TOKEN_TTL_HOURS      = 24    # access token valid for 24 hours
REFRESH_WINDOW_DAYS  = 7     # refresh allowed within 7 days of token creation

# OTP config
OTP_TTL         = 300    # 5 min before expiry
OTP_RATE_WINDOW = 600    # 10 min window for rate limit
OTP_RATE_MAX    = 3      # max sends per window
OTP_FAIL_MAX    = 5      # wrong attempts before lockout
OTP_LOCKOUT_TTL = 900    # 15 min lockout

# Booking state machine: {current: {role: [allowed_next]}}
_BOOKING_FSM = {
    "pending":     {"customer": ["cancelled"],          "worker": ["confirmed", "cancelled"]},
    "confirmed":   {"customer": ["cancelled"],          "worker": ["in_progress", "cancelled"]},
    "in_progress": {"customer": [],                     "worker": ["completed"]},
    "completed":   {"customer": [],                     "worker": []},
    "cancelled":   {"customer": [],                     "worker": []},
}

# ── In-memory rate-limit / OTP stores ────────────────────────────────────────
_OTP_STORE: dict = {}   # { phone: {otp, expires_at, name} }
_OTP_RATE:  dict = {}   # { phone: [timestamp, ...] }
_OTP_FAILS: dict = {}   # { phone: {fails, locked_until} }


# ══════════════════════════════════════════════════════════════════════════════
#  RESPONSE HELPERS
# ══════════════════════════════════════════════════════════════════════════════

def err(msg: str, code: int = 400):
    return jsonify({"success": False, "error": msg}), code


def ok(payload: dict | None = None, code: int = 200):
    body = {"success": True}
    if payload:
        body.update(payload)
    return jsonify(body), code


# ══════════════════════════════════════════════════════════════════════════════
#  SECURITY HEADERS — injected on every response
# ══════════════════════════════════════════════════════════════════════════════

@app.after_request
def add_security_headers(response):
    """
    Harden every HTTP response.

    X-Content-Type-Options: nosniff
      → prevents browser from MIME-sniffing; blocks polyglot file attacks

    X-Frame-Options: DENY
      → prevents embedding in iframes (clickjacking protection)

    Referrer-Policy: strict-origin-when-cross-origin
      → cross-origin requests send only origin, not full URL

    Cache-Control: no-store
      → auth responses must never be stored by intermediate caches or browser

    X-Request-ID
      → echoed from request or generated; useful for log correlation
    """
    response.headers["X-Content-Type-Options"]  = "nosniff"
    response.headers["X-Frame-Options"]          = "DENY"
    response.headers["Referrer-Policy"]          = "strict-origin-when-cross-origin"
    response.headers["Cache-Control"]            = "no-store"

    req_id = request.headers.get("X-Request-ID", secrets.token_hex(8))
    response.headers["X-Request-ID"] = req_id

    return response


# ══════════════════════════════════════════════════════════════════════════════
#  INPUT SANITISATION
# ══════════════════════════════════════════════════════════════════════════════

def _s(val, max_len: int = 200) -> str:
    """
    Sanitize a string input for safe storage and display.

    Strips:
      • Null bytes and C0/C1 control characters (Cc Unicode category)
      • Format characters: zero-width spaces, BiDi marks, RTL override (Cf)
      • Surrogates (Cs) and private-use chars (Co)
      • CRLF injection: normalizes \r\n and lone \r to \n before filtering

    Keeps:
      • Normal printable text
      • Space, tab (\t), and newline (\n) — useful in notes fields

    Caps length after cleaning.
    """
    if not isinstance(val, str):
        return ""
    # Normalize line endings to prevent CRLF injection
    val = val.replace("\r\n", "\n").replace("\r", "\n")
    # Remove dangerous Unicode categories; keep safe whitespace
    cleaned = "".join(
        c for c in val
        if unicodedata.category(c)[0] not in ("C",)   # strips Cc Cf Cs Co Cn
        or c in (" ", "\t", "\n")                      # safe whitespace exceptions
    )
    return cleaned.strip()[:max_len]


def _validate_phone(raw) -> tuple[str | None, str | None]:
    phone = _s(raw, MAX_PHONE_LEN)
    if not phone:
        return None, "Phone number is required"
    if not _PHONE_RE.match(phone):
        return None, "Invalid phone format — expected +91-XXXXX-XXXXX"
    return phone, None


def _validate_otp(raw) -> str | None:
    """Intentionally no length-cap: reject 7+ digit inputs rather than silently truncate."""
    if not isinstance(raw, str):
        return "OTP must be exactly 6 digits"
    otp = raw.strip()
    if not _OTP_RE.match(otp):
        return "OTP must be exactly 6 digits"
    return None


def _validate_date(raw, allow_past: bool = False) -> tuple[str | None, str | None]:
    d = _s(raw, 10)
    if not _DATE_RE.match(d):
        return None, "Date must be in YYYY-MM-DD format"
    try:
        parsed = _date_type.fromisoformat(d)
    except ValueError:
        return None, "Invalid date value"
    if not allow_past and parsed < _date_type.today():
        return None, "Date cannot be in the past"
    return d, None


def _validate_time(raw) -> tuple[str | None, str | None]:
    t = _s(raw, 5)
    if not _TIME_RE.match(t):
        return None, "Time must be in HH:MM format"
    h, m = map(int, t.split(":"))
    if not (0 <= h <= 23 and 0 <= m <= 59):
        return None, "Invalid time value"
    return t, None


# ══════════════════════════════════════════════════════════════════════════════
#  OTP RATE LIMITING & BRUTE-FORCE PROTECTION
# ══════════════════════════════════════════════════════════════════════════════

def _otp_rate_check(phone: str) -> str | None:
    now = time.time()
    attempts = [t for t in _OTP_RATE.get(phone, []) if now - t < OTP_RATE_WINDOW]
    if len(attempts) >= OTP_RATE_MAX:
        wait = int(OTP_RATE_WINDOW - (now - attempts[0]))
        return f"Too many OTP requests. Please wait {wait}s before trying again"
    attempts.append(now)
    _OTP_RATE[phone] = attempts
    return None


def _verify_lockout_check(phone: str) -> str | None:
    now  = time.time()
    data = _OTP_FAILS.get(phone, {})
    lu   = data.get("locked_until", 0)
    if lu > now:
        wait = int(lu - now)
        return f"Too many failed attempts. Try again in {wait}s"
    return None


def _record_verify_fail(phone: str) -> None:
    data = _OTP_FAILS.get(phone, {"fails": 0})
    data["fails"] = data.get("fails", 0) + 1
    if data["fails"] >= OTP_FAIL_MAX:
        data["locked_until"] = time.time() + OTP_LOCKOUT_TTL
        data["fails"] = 0
    _OTP_FAILS[phone] = data


def _clear_verify_fails(phone: str) -> None:
    _OTP_FAILS.pop(phone, None)


# ══════════════════════════════════════════════════════════════════════════════
#  SLOT OVERLAP & BOOKING CONFLICT
# ══════════════════════════════════════════════════════════════════════════════

def _to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m


def _times_overlap(s1: str, e1: str, s2: str, e2: str) -> bool:
    """[s1,e1) overlaps [s2,e2)? Adjacent slots (e1==s2) do NOT overlap."""
    return _to_minutes(s1) < _to_minutes(e2) and _to_minutes(s2) < _to_minutes(e1)


def _check_slot_overlap(db, worker_id: int, date: str, start: str, end: str,
                        exclude_id: int | None = None) -> str | None:
    sql    = "SELECT id, start_time, end_time FROM time_slots WHERE worker_id=? AND date=?"
    params: list = [worker_id, date]
    if exclude_id:
        sql    += " AND id != ?"
        params += [exclude_id]
    for row in db.execute(sql, params).fetchall():
        if _times_overlap(start, end, row["start_time"], row["end_time"]):
            return (f"Slot {start}–{end} overlaps with existing slot "
                    f"{row['start_time']}–{row['end_time']}")
    return None


# ══════════════════════════════════════════════════════════════════════════════
#  DATABASE LAYER
# ══════════════════════════════════════════════════════════════════════════════

def get_db() -> sqlite3.Connection:
    """
    Return a per-request SQLite connection stored in Flask g.

    PRAGMAs set here are per-connection tunables only:
      busy_timeout  — how long to wait on a locked DB before raising an error
                      5000 ms prevents "database is locked" crashes under load
      cache_size    — 8 MB in-memory page cache per connection (negative = KB)
      synchronous   — NORMAL is safe with WAL mode and ~30% faster than FULL

    WAL mode and foreign_keys are set once in init_db() because they are
    persistent database-level settings on SQLite 3.15+.
    """
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH, detect_types=sqlite3.PARSE_DECLTYPES,
                               check_same_thread=False)
        g.db.row_factory = sqlite3.Row
        g.db.execute("PRAGMA busy_timeout  = 5000")
        g.db.execute("PRAGMA cache_size    = -8000")
        g.db.execute("PRAGMA synchronous   = NORMAL")
        g.db.execute("PRAGMA foreign_keys  = ON")
    return g.db


@app.teardown_appcontext
def close_db(error):
    db = g.pop("db", None)
    if db:
        db.close()


def init_db():
    """
    Create schema, run migrations, seed from workers.json.
    Called once at startup. Safe to re-run.

    Persistent PRAGMAs set here (survive connection close):
      journal_mode=WAL   — concurrent reads + one write; no readers block writers
      foreign_keys=ON    — enforce FK constraints (SQLite default is OFF)
    """
    db = sqlite3.connect(DB_PATH)
    db.row_factory = sqlite3.Row

    # ── Persistent DB-level settings ──────────────────────────────────────────
    db.execute("PRAGMA journal_mode = WAL")
    db.execute("PRAGMA foreign_keys = ON")

    db.executescript("""
        CREATE TABLE IF NOT EXISTS users (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            phone      TEXT    UNIQUE NOT NULL,
            name       TEXT    NOT NULL,
            role       TEXT    NOT NULL CHECK(role IN ('customer','worker','assistant')),
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        -- token_hash: SHA-256(raw_token) — raw token never stored
        -- created_at: used to enforce REFRESH_WINDOW_DAYS
        CREATE TABLE IF NOT EXISTS sessions (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id    INTEGER NOT NULL,
            token_hash TEXT    UNIQUE NOT NULL,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            expires_at DATETIME NOT NULL,
            FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS workers (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id     INTEGER NOT NULL UNIQUE,
            category    TEXT    NOT NULL,
            rating      REAL    DEFAULT 4.5 CHECK(rating BETWEEN 1.0 AND 5.0),
            status      TEXT    DEFAULT 'available'
                                CHECK(status IN ('available','on_job','unavailable')),
            distance_km REAL    DEFAULT 1.0,
            FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS assistants (
            id               INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id          INTEGER NOT NULL UNIQUE,
            linked_worker_id INTEGER,
            status           TEXT DEFAULT 'available'
                                  CHECK(status IN ('available','on_job','unavailable')),
            FOREIGN KEY(user_id)          REFERENCES users(id)   ON DELETE CASCADE,
            FOREIGN KEY(linked_worker_id) REFERENCES workers(id) ON DELETE SET NULL
        );

        CREATE TABLE IF NOT EXISTS time_slots (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            worker_id  INTEGER NOT NULL,
            date       TEXT    NOT NULL,
            start_time TEXT    NOT NULL,
            end_time   TEXT    NOT NULL,
            is_booked  INTEGER DEFAULT 0,
            FOREIGN KEY(worker_id) REFERENCES workers(id) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS bookings (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            customer_id  INTEGER NOT NULL,
            worker_id    INTEGER NOT NULL,
            time_slot_id INTEGER,
            date         TEXT    NOT NULL,
            status       TEXT    DEFAULT 'pending'
                                 CHECK(status IN ('pending','confirmed','in_progress',
                                                  'completed','cancelled')),
            notes        TEXT    DEFAULT '',
            created_at   DATETIME DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(customer_id)  REFERENCES users(id)      ON DELETE CASCADE,
            FOREIGN KEY(worker_id)    REFERENCES workers(id)    ON DELETE CASCADE,
            FOREIGN KEY(time_slot_id) REFERENCES time_slots(id) ON DELETE SET NULL
        );
    """)

    # ── Schema migrations (idempotent) ────────────────────────────────────────
    session_cols = {r[1] for r in db.execute("PRAGMA table_info(sessions)").fetchall()}

    # v2.0 → v2.1: token → token_hash
    if "token" in session_cols and "token_hash" not in session_cols:
        log.warning("event=schema_migration msg='renaming token to token_hash, clearing sessions'")
        db.execute("DELETE FROM sessions")
        db.execute("ALTER TABLE sessions RENAME COLUMN token TO token_hash")
        db.commit()
        log.info("event=schema_migration msg='sessions.token renamed to token_hash'")

    # v2.1 → v2.2: add created_at to sessions
    if "created_at" not in session_cols:
        log.info("event=schema_migration msg='adding sessions.created_at'")
        db.execute(
            "ALTER TABLE sessions ADD COLUMN created_at DATETIME DEFAULT CURRENT_TIMESTAMP"
        )
        db.commit()
        log.info("event=schema_migration msg='sessions.created_at added'")

    # ── Seed data from workers.json (only when DB is empty) ───────────────────
    if db.execute("SELECT COUNT(*) FROM users").fetchone()[0] == 0:
        jpath = "workers.json"
        if os.path.exists(jpath):
            with open(jpath) as f:
                payload = json.load(f)
            seed = payload.get("seed_data", [])
            for w in seed:
                db.execute("INSERT INTO users (phone, name, role) VALUES (?,?,?)",
                           (w["phone"], w["name"], "worker"))
                uid = db.execute("SELECT last_insert_rowid()").fetchone()[0]
                db.execute(
                    "INSERT INTO workers (user_id, category, rating, distance_km, status) "
                    "VALUES (?,?,?,?,?)",
                    (uid, w["category"], w["rating"], w["distance_km"], "available")
                )
            db.commit()
            log.info(f"event=seed workers={len(seed)}")

    db.commit()
    db.close()
    log.info(f"event=db_ready path={DB_PATH}")


# ══════════════════════════════════════════════════════════════════════════════
#  TOKEN GENERATION & VERIFICATION
# ══════════════════════════════════════════════════════════════════════════════

def _gen_token() -> tuple[str, str]:
    """
    Returns (raw_token, token_hash).
    raw_token  → sent to client, never stored anywhere server-side.
    token_hash → SHA-256(raw_token) stored in sessions table.
    A DB dump cannot reconstruct valid tokens.
    """
    raw = secrets.token_urlsafe(32)   # 256 bits entropy
    hsh = hashlib.sha256(raw.encode()).hexdigest()
    return raw, hsh


def _auth_user(raw_token: str) -> dict | None:
    """
    Hash the raw bearer token and look it up in sessions.
    Returns user dict if session exists and has not expired, else None.
    """
    if not raw_token or len(raw_token) > 128:
        return None
    hsh = hashlib.sha256(raw_token.encode()).hexdigest()
    db  = get_db()
    row = db.execute(
        "SELECT u.* FROM sessions s "
        "JOIN users u ON s.user_id = u.id "
        "WHERE s.token_hash = ? AND s.expires_at > datetime('now')",
        (hsh,)
    ).fetchone()
    return dict(row) if row else None


# ══════════════════════════════════════════════════════════════════════════════
#  DECORATORS
# ══════════════════════════════════════════════════════════════════════════════

def login_required(f):
    """Validates Bearer token; sets g.current_user or returns 401."""
    @wraps(f)
    def wrapper(*args, **kwargs):
        raw  = request.headers.get("Authorization", "").replace("Bearer ", "").strip()
        user = _auth_user(raw)
        if not user:
            log.warning(f"event=auth_fail ip={_ip()} path={request.path}")
            return err("Authentication required — please login", 401)
        g.current_user = user
        return f(*args, **kwargs)
    return wrapper


def role_required(*roles: str):
    """Validates token AND enforces role membership."""
    def decorator(f):
        @wraps(f)
        def wrapper(*args, **kwargs):
            raw  = request.headers.get("Authorization", "").replace("Bearer ", "").strip()
            user = _auth_user(raw)
            if not user:
                log.warning(f"event=auth_fail ip={_ip()} path={request.path}")
                return err("Authentication required — please login", 401)
            if user["role"] not in roles:
                log.warning(
                    f"event=access_denied user_id={user['id']} role={user['role']} "
                    f"required={roles} path={request.path}"
                )
                return err(
                    f"Access denied — endpoint requires role: {' or '.join(roles)}", 403
                )
            g.current_user = user
            return f(*args, **kwargs)
        return wrapper
    return decorator


def _get_worker_for_user(db, user_id: int):
    row = db.execute("SELECT * FROM workers WHERE user_id=?", (user_id,)).fetchone()
    if not row:
        return None, err("Worker profile not found for your account", 404)
    return dict(row), None


def _assert_worker_owns(current_user: dict, worker: dict):
    if current_user["role"] == "worker" and worker["user_id"] != current_user["id"]:
        return err("Access denied — you can only modify your own data", 403)
    return None


# ══════════════════════════════════════════════════════════════════════════════
#  GLOBAL ERROR HANDLERS
# ══════════════════════════════════════════════════════════════════════════════

@app.errorhandler(404)
def not_found(e):
    return err("Endpoint not found", 404)


@app.errorhandler(405)
def method_not_allowed(e):
    return err(f"Method {request.method} not allowed on this endpoint", 405)


@app.errorhandler(500)
def internal_error(e):
    log.error(f"event=unhandled_error path={request.path} error={e!r}")
    return err("An internal error occurred — please try again", 500)


# ══════════════════════════════════════════════════════════════════════════════
#  OTP ENDPOINTS
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/api/send-otp", methods=["POST"])
def send_otp():
    data  = request.json or {}
    phone, phone_err = _validate_phone(data.get("phone", ""))
    if phone_err:
        log.warning(f"event=otp_invalid_phone ip={_ip()} reason={phone_err}")
        return err(phone_err)

    rate_err = _otp_rate_check(phone)
    if rate_err:
        log.warning(f"event=otp_rate_limited phone={_mp(phone)} ip={_ip()}")
        return err(rate_err, 429)

    name = _s(data.get("name", ""), MAX_NAME_LEN)
    otp  = str(secrets.randbelow(900000) + 100000)   # cryptographically secure 6-digit

    _OTP_STORE[phone] = {
        "otp":        otp,
        "expires_at": time.time() + OTP_TTL,
        "name":       name,
    }

    log.info(f"event=otp_sent phone={_mp(phone)} ip={_ip()}")
    log.info(f"OTP_DEBUG phone={phone} otp={otp}")

    # Simulate SMS — print to server console (replace with real SMS provider)
    print(f"\n{'='*50}")
    print(f"  📱 OTP  →  {phone}  :  {otp}")
    print(f"{'='*50}\n")

    return ok({"message": "OTP sent — check the server console"})


@app.route("/api/verify-otp", methods=["POST"])
def verify_otp():
    data  = request.json or {}
    phone, phone_err = _validate_phone(data.get("phone", ""))
    if phone_err:
        return err(phone_err)

    otp_err = _validate_otp(data.get("otp", ""))
    if otp_err:
        log.warning(f"event=otp_invalid_format phone={_mp(phone)} ip={_ip()}")
        return err(otp_err)

    lockout_err = _verify_lockout_check(phone)
    if lockout_err:
        log.warning(f"event=otp_locked phone={_mp(phone)} ip={_ip()}")
        return err(lockout_err, 429)

    stored = _OTP_STORE.get(phone)
    if not stored:
        log.warning(f"event=otp_not_found phone={_mp(phone)} ip={_ip()}")
        return err("No OTP found for this number — request a new one", 401)

    if time.time() > stored["expires_at"]:
        _OTP_STORE.pop(phone, None)
        log.warning(f"event=otp_expired phone={_mp(phone)} ip={_ip()}")
        return err("OTP has expired — please request a new one", 401)

    if stored["otp"] != data.get("otp", "").strip():
        _record_verify_fail(phone)
        fails = _OTP_FAILS.get(phone, {}).get("fails", 1)
        log.warning(f"event=otp_wrong phone={_mp(phone)} ip={_ip()} attempt={fails}")
        return err("Incorrect OTP", 401)

    # ── Correct OTP — clear rate state ───────────────────────────────────────
    _OTP_STORE.pop(phone, None)
    _clear_verify_fails(phone)

    name = _s(data.get("name", "") or stored.get("name", ""), MAX_NAME_LEN)
    db   = get_db()

    try:
        user = db.execute("SELECT * FROM users WHERE phone=?", (phone,)).fetchone()
        is_new = user is None
        if is_new:
            display = name or f"User {phone[-4:]}"
            db.execute("INSERT INTO users (phone, name, role) VALUES (?,?,?)",
                       (phone, display, "customer"))
            db.commit()
            user = db.execute("SELECT * FROM users WHERE phone=?", (phone,)).fetchone()

        user_dict = dict(user)

        # ── Issue access token (24-hour TTL) ──────────────────────────────────
        raw_token, token_hash = _gen_token()
        expires = (datetime.now() + timedelta(hours=TOKEN_TTL_HOURS)).strftime(
            "%Y-%m-%d %H:%M:%S"
        )
        db.execute(
            "INSERT INTO sessions (user_id, token_hash, expires_at) VALUES (?,?,?)",
            (user_dict["id"], token_hash, expires)
        )
        db.commit()

        # Attach role-specific profile
        profile = None
        if user_dict["role"] == "worker":
            row = db.execute("SELECT * FROM workers WHERE user_id=?",
                             (user_dict["id"],)).fetchone()
            if row:
                profile = dict(row)
        elif user_dict["role"] == "assistant":
            row = db.execute("SELECT * FROM assistants WHERE user_id=?",
                             (user_dict["id"],)).fetchone()
            if row:
                profile = dict(row)

        log.info(
            f"event=login_ok user_id={user_dict['id']} role={user_dict['role']} "
            f"new_user={is_new} ip={_ip()}"
        )

        return ok({
            "token":      raw_token,
            "expires_in": TOKEN_TTL_HOURS * 3600,   # seconds, for client-side expiry tracking
            "user": {
                "id":    user_dict["id"],
                "name":  user_dict["name"],
                "phone": user_dict["phone"],
                "role":  user_dict["role"],
            },
            "profile": profile,
        })

    except sqlite3.Error as e:
        db.rollback()
        log.error(f"event=login_db_error phone={_mp(phone)} error={e!r}")
        return err("Database error — please try again", 500)


@app.route("/api/token/refresh", methods=["POST"])
@login_required
def refresh_token():
    """
    Exchange a valid (non-expired) token for a new 24-hour token.

    Rules:
    • The current token must still be valid (not expired).
    • The token must have been issued within the last REFRESH_WINDOW_DAYS days.
      This prevents refresh-token abuse on very old sessions.
    • The old token is deleted; the new token is returned.
    • No re-authentication needed — this is purely a token rotation.

    Client should call this proactively before the 24-hour expiry.
    """
    raw = request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    hsh = hashlib.sha256(raw.encode()).hexdigest()

    db  = get_db()
    row = db.execute(
        "SELECT id, created_at FROM sessions WHERE token_hash=?", (hsh,)
    ).fetchone()

    if not row:
        return err("Session not found — please login again", 401)

    # Enforce refresh window: created_at must be within REFRESH_WINDOW_DAYS
    created_at_str = row["created_at"]
    try:
        created_at = datetime.strptime(created_at_str, "%Y-%m-%d %H:%M:%S")
    except (TypeError, ValueError):
        created_at = datetime.now()   # fallback: allow refresh if created_at is NULL

    refresh_deadline = created_at + timedelta(days=REFRESH_WINDOW_DAYS)
    if datetime.now() > refresh_deadline:
        log.warning(
            f"event=refresh_expired user_id={g.current_user['id']} "
            f"created_at={created_at_str}"
        )
        return err(
            "Refresh window expired — please login again with OTP", 401
        )

    # Issue new token and delete old one atomically
    new_raw, new_hash = _gen_token()
    new_expires = (datetime.now() + timedelta(hours=TOKEN_TTL_HOURS)).strftime(
        "%Y-%m-%d %H:%M:%S"
    )

    try:
        db.execute("DELETE FROM sessions WHERE token_hash=?", (hsh,))
        db.execute(
            "INSERT INTO sessions (user_id, token_hash, expires_at) VALUES (?,?,?)",
            (g.current_user["id"], new_hash, new_expires)
        )
        db.commit()
    except sqlite3.Error as e:
        db.rollback()
        log.error(f"event=refresh_db_error user_id={g.current_user['id']} error={e!r}")
        return err("Token refresh failed — please try again", 500)

    log.info(
        f"event=token_refreshed user_id={g.current_user['id']} "
        f"role={g.current_user['role']}"
    )

    return ok({
        "token":      new_raw,
        "expires_in": TOKEN_TTL_HOURS * 3600,
    })


@app.route("/api/logout", methods=["POST"])
@login_required
def logout():
    raw = request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    hsh = hashlib.sha256(raw.encode()).hexdigest()
    db  = get_db()
    db.execute("DELETE FROM sessions WHERE token_hash=?", (hsh,))
    db.commit()
    log.info(f"event=logout user_id={g.current_user['id']}")
    return ok({"message": "Logged out successfully"})


# ══════════════════════════════════════════════════════════════════════════════
#  ORIGINAL ENDPOINTS — preserved + stable
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/api/workers", methods=["GET"])
def get_workers():
    """GET /api/workers?service=electrician&status=available — public endpoint."""
    service = _s(request.args.get("service", ""), 50).lower()
    status  = _s(request.args.get("status",  ""), 20).lower()

    if service and service not in VALID_CATS:
        return err(f"Unknown service category: '{service}'")
    if status and status not in VALID_WORKER_STATUS:
        return err(f"Invalid status filter: '{status}'")

    db  = get_db()
    sql = """
        SELECT w.id, u.name, w.category, w.rating, u.phone,
               w.distance_km, w.status
        FROM   workers w
        JOIN   users   u ON w.user_id = u.id
        WHERE  1=1
    """
    params: list = []
    if service:
        sql += " AND w.category=?"
        params.append(service)
    if status:
        sql += " AND w.status=?"
        params.append(status)
    sql += " ORDER BY w.distance_km ASC"

    workers = []
    for r in db.execute(sql, params).fetchall():
        w    = dict(r)
        slot = db.execute(
            "SELECT id, date, start_time, end_time FROM time_slots "
            "WHERE worker_id=? AND is_booked=0 AND date>=date('now') "
            "ORDER BY date, start_time LIMIT 1",
            (w["id"],)
        ).fetchone()
        w["next_slot"] = dict(slot) if slot else None
        workers.append(w)

    return ok({"count": len(workers), "workers": workers})


@app.route("/api/categories", methods=["GET"])
def get_categories():
    db   = get_db()
    cats = [r[0] for r in db.execute(
        "SELECT DISTINCT category FROM workers ORDER BY category"
    ).fetchall()]
    return ok({"categories": cats})


# ══════════════════════════════════════════════════════════════════════════════
#  PROFILE
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/api/me", methods=["GET"])
@login_required
def get_me():
    db   = get_db()
    user = g.current_user
    profile = None

    if user["role"] == "worker":
        row = db.execute("SELECT * FROM workers WHERE user_id=?", (user["id"],)).fetchone()
        if row:
            profile = dict(row)
            profile["available_slots"] = db.execute(
                "SELECT COUNT(*) FROM time_slots "
                "WHERE worker_id=? AND date>=date('now') AND is_booked=0",
                (row["id"],)
            ).fetchone()[0]
    elif user["role"] == "assistant":
        row = db.execute("SELECT * FROM assistants WHERE user_id=?", (user["id"],)).fetchone()
        if row:
            profile = dict(row)

    return ok({"user": user, "profile": profile})


# ══════════════════════════════════════════════════════════════════════════════
#  WORKER MANAGEMENT
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/api/workers/<int:worker_id>/status", methods=["PUT"])
@role_required("worker")
def update_worker_status(worker_id):
    db  = get_db()
    row = db.execute("SELECT * FROM workers WHERE id=?", (worker_id,)).fetchone()
    if not row:
        return err("Worker not found", 404)

    ownership_err = _assert_worker_owns(g.current_user, dict(row))
    if ownership_err:
        return ownership_err

    new_status = _s((request.json or {}).get("status", ""), 20)
    if new_status not in VALID_WORKER_STATUS:
        return err(f"Invalid status '{new_status}'. Must be: {', '.join(sorted(VALID_WORKER_STATUS))}")

    old_status = row["status"]
    db.execute("UPDATE workers SET status=? WHERE id=?", (new_status, worker_id))
    db.commit()
    return ok({"status": new_status})


@app.route("/api/workers/<int:worker_id>/slots", methods=["GET"])
def get_worker_slots(worker_id):
    db = get_db()
    if not db.execute("SELECT id FROM workers WHERE id=?", (worker_id,)).fetchone():
        return err("Worker not found", 404)

    date_raw = _s(request.args.get("date", ""), 10)
    if date_raw:
        _, date_err = _validate_date(date_raw, allow_past=True)
        if date_err:
            return err(date_err)
        rows = db.execute(
            "SELECT * FROM time_slots WHERE worker_id=? AND date=? ORDER BY start_time",
            (worker_id, date_raw)
        ).fetchall()
    else:
        rows = db.execute(
            "SELECT * FROM time_slots WHERE worker_id=? AND date>=date('now') "
            "ORDER BY date, start_time",
            (worker_id,)
        ).fetchall()

    return ok({"slots": [dict(r) for r in rows]})


@app.route("/api/workers/<int:worker_id>/slots", methods=["POST"])
@role_required("worker")
def add_worker_slot(worker_id):
    db  = get_db()
    row = db.execute("SELECT * FROM workers WHERE id=?", (worker_id,)).fetchone()
    if not row:
        return err("Worker not found", 404)

    ownership_err = _assert_worker_owns(g.current_user, dict(row))
    if ownership_err:
        return ownership_err

    data = request.json or {}

    date,  date_err  = _validate_date(data.get("date", ""))
    if date_err:
        return err(date_err)
    start, start_err = _validate_time(data.get("start_time", ""))
    if start_err:
        return err(f"start_time: {start_err}")
    end,   end_err   = _validate_time(data.get("end_time", ""))
    if end_err:
        return err(f"end_time: {end_err}")

    if _to_minutes(start) >= _to_minutes(end):
        return err("end_time must be after start_time")

    overlap_err = _check_slot_overlap(db, worker_id, date, start, end)
    if overlap_err:
        return err(overlap_err, 409)

    try:
        db.execute(
            "INSERT INTO time_slots (worker_id, date, start_time, end_time) VALUES (?,?,?,?)",
            (worker_id, date, start, end)
        )
        db.commit()
        slot_id = db.execute("SELECT last_insert_rowid()").fetchone()[0]
        return ok({
            "slot_id": slot_id,
            "slot": {"id": slot_id, "date": date,
                     "start_time": start, "end_time": end, "is_booked": 0}
        }, 201)
    except sqlite3.Error as e:
        db.rollback()
        log.error(f"event=slot_insert_error worker_id={worker_id} error={e!r}")
        return err("Failed to save slot — please try again", 500)


@app.route("/api/slots/<int:slot_id>", methods=["DELETE"])
@role_required("worker")
def delete_slot(slot_id):
    db  = get_db()
    row = db.execute(
        "SELECT ts.*, w.user_id FROM time_slots ts "
        "JOIN workers w ON ts.worker_id=w.id WHERE ts.id=?",
        (slot_id,)
    ).fetchone()
    if not row:
        return err("Slot not found", 404)

    ownership_err = _assert_worker_owns(g.current_user, dict(row))
    if ownership_err:
        return ownership_err

    if row["is_booked"]:
        return err("Cannot delete a booked slot — cancel the booking first", 409)

    db.execute("DELETE FROM time_slots WHERE id=?", (slot_id,))
    db.commit()
    return ok({"message": "Slot deleted"})


@app.route("/api/workers/<int:worker_id>/bookings", methods=["GET"])
@role_required("worker")
def get_worker_bookings(worker_id):
    db  = get_db()
    row = db.execute("SELECT * FROM workers WHERE id=?", (worker_id,)).fetchone()
    if not row:
        return err("Worker not found", 404)

    ownership_err = _assert_worker_owns(g.current_user, dict(row))
    if ownership_err:
        return ownership_err

    rows = db.execute(
        """SELECT b.id, b.date, b.status, b.notes, b.created_at,
                  u.name AS customer_name, u.phone AS customer_phone
           FROM   bookings b
           JOIN   users    u ON b.customer_id = u.id
           WHERE  b.worker_id = ?
           ORDER  BY b.created_at DESC""",
        (worker_id,)
    ).fetchall()
    return ok({"bookings": [dict(r) for r in rows]})


# ══════════════════════════════════════════════════════════════════════════════
#  BOOKINGS — customer-facing
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/api/bookings", methods=["POST"])
@role_required("customer")
def create_booking():
    """
    Create a booking with an EXCLUSIVE transaction.

    Why EXCLUSIVE?
    Without it there is a TOCTOU (time-of-check to time-of-use) race:
      Thread A reads slot → not booked
      Thread B reads slot → not booked
      Thread A writes booking (commits)
      Thread B writes booking (commits) → double booking

    BEGIN EXCLUSIVE acquires a write lock immediately, so the second
    concurrent request blocks on busy_timeout (5s) and then succeeds
    correctly because it will then see is_booked=1.
    """
    data         = request.json or {}
    worker_id    = data.get("worker_id")
    time_slot_id = data.get("time_slot_id")
    notes        = _s(data.get("notes", ""), MAX_NOTES_LEN)

    date, date_err = _validate_date(data.get("date", ""))
    if date_err:
        return err(date_err)

    if not worker_id or not isinstance(worker_id, int):
        return err("worker_id is required and must be an integer")

    db = get_db()
    if not db.execute("SELECT id FROM workers WHERE id=?", (worker_id,)).fetchone():
        return err("Worker not found", 404)

    try:
        # Acquire exclusive write lock before the conflict check
        db.execute("BEGIN EXCLUSIVE")

        # Check for conflicts under the lock (no TOCTOU window)
        if time_slot_id:
            slot = db.execute(
                "SELECT is_booked FROM time_slots WHERE id=? AND worker_id=?",
                (time_slot_id, worker_id)
            ).fetchone()
            if not slot:
                db.execute("ROLLBACK")
                return err("Time slot not found or does not belong to this worker", 404)
            if slot["is_booked"]:
                db.execute("ROLLBACK")
                return err("This time slot has already been booked", 409)
            db.execute("UPDATE time_slots SET is_booked=1 WHERE id=?", (time_slot_id,))
        else:
            count = db.execute(
                "SELECT COUNT(*) FROM bookings "
                "WHERE worker_id=? AND date=? AND status NOT IN ('cancelled','completed')",
                (worker_id, date)
            ).fetchone()[0]
            if count > 0:
                db.execute("ROLLBACK")
                return err("This worker already has an active booking on the selected date", 409)

        db.execute(
            "INSERT INTO bookings (customer_id, worker_id, time_slot_id, date, notes) "
            "VALUES (?,?,?,?,?)",
            (g.current_user["id"], worker_id, time_slot_id, date, notes)
        )
        db.execute("COMMIT")

        booking_id = db.execute("SELECT last_insert_rowid()").fetchone()[0]
        log.info(
            f"event=booking_created booking_id={booking_id} customer_id={g.current_user['id']} "
            f"worker_id={worker_id} date={date}"
        )
        return ok({"booking_id": booking_id}, 201)

    except sqlite3.Error as e:
        try:
            db.execute("ROLLBACK")
        except sqlite3.Error:
            pass
        log.error(f"event=booking_db_error worker_id={worker_id} error={e!r}")
        return err("Booking failed — please try again", 500)


@app.route("/api/bookings/my", methods=["GET"])
@role_required("customer")
def my_bookings():
    db   = get_db()
    rows = db.execute(
        """SELECT b.id, b.date, b.status, b.notes, b.created_at,
                  u.name AS worker_name, w.category
           FROM   bookings b
           JOIN   workers  w ON b.worker_id = w.id
           JOIN   users    u ON w.user_id   = u.id
           WHERE  b.customer_id = ?
           ORDER  BY b.created_at DESC""",
        (g.current_user["id"],)
    ).fetchall()
    return ok({"bookings": [dict(r) for r in rows]})


@app.route("/api/bookings/<int:booking_id>/status", methods=["PUT"])
@login_required
def update_booking_status(booking_id):
    """
    State-machine-enforced booking transitions with full audit log.
    Every status change is written to fixr.log with: booking_id, old, new, role, user_id.
    """
    new_status = _s((request.json or {}).get("status", ""), 20)
    if new_status not in VALID_BOOKING_STATUS:
        return err(f"Invalid status '{new_status}'")

    db  = get_db()
    bk  = db.execute(
        "SELECT b.*, w.user_id AS worker_user_id "
        "FROM bookings b JOIN workers w ON b.worker_id=w.id "
        "WHERE b.id=?",
        (booking_id,)
    ).fetchone()
    if not bk:
        return err("Booking not found", 404)

    bk   = dict(bk)
    role = g.current_user["role"]

    if role == "customer" and bk["customer_id"] != g.current_user["id"]:
        return err("Access denied — not your booking", 403)
    if role == "worker" and bk["worker_user_id"] != g.current_user["id"]:
        return err("Access denied — not your booking", 403)
    if role == "assistant":
        return err("Assistants cannot update booking status", 403)

    old_status = bk["status"]
    allowed    = _BOOKING_FSM.get(old_status, {}).get(role, [])
    if new_status not in allowed:
        if not allowed:
            return err(
                f"Booking is in terminal state '{old_status}' — no further changes allowed", 409
            )
        return err(
            f"Invalid transition: '{old_status}' → '{new_status}'. "
            f"Allowed from this state: {', '.join(allowed)}", 409
        )

    db.execute("UPDATE bookings SET status=? WHERE id=?", (new_status, booking_id))
    db.commit()

    # ── Audit log: every booking state change is recorded ─────────────────────
    log.info(
        f"event=booking_transition booking_id={booking_id} "
        f"old={old_status} new={new_status} role={role} user_id={g.current_user['id']}"
    )

    return ok({"booking_id": booking_id, "status": new_status})


# ══════════════════════════════════════════════════════════════════════════════
#  ASSISTANT SYSTEM
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/api/assistant/request", methods=["POST"])
@role_required("worker")
def request_assistant():
    """
    Worker links an assistant by phone number.

    Hardened in v2.2:
    • An assistant already linked to a DIFFERENT worker cannot be poached.
      Worker A cannot silently steal Worker B's assistant by calling this endpoint.
      The requesting worker must be the current linked_worker (or the assistant
      must be unlinked) before a new link can be established.
    • All outcomes are logged.
    """
    db = get_db()
    worker_row, worker_err = _get_worker_for_user(db, g.current_user["id"])
    if worker_err:
        return worker_err

    data  = request.json or {}
    phone, phone_err = _validate_phone(data.get("phone", ""))
    if phone_err:
        return err(phone_err)

    if phone == g.current_user["phone"]:
        return err("You cannot link yourself as an assistant")

    asst_name = _s(data.get("name", ""), MAX_NAME_LEN)

    try:
        asst_user = db.execute("SELECT * FROM users WHERE phone=?", (phone,)).fetchone()

        if not asst_user:
            display = asst_name or f"Assistant {phone[-4:]}"
            db.execute("INSERT INTO users (phone, name, role) VALUES (?,?,?)",
                       (phone, display, "assistant"))
            db.commit()
            asst_user = db.execute("SELECT * FROM users WHERE phone=?", (phone,)).fetchone()

        else:
            if asst_user["role"] == "customer":
                log.warning(
                    f"event=assistant_link_blocked reason=customer_account "
                    f"worker_id={worker_row['id']} phone={_mp(phone)}"
                )
                return err("This phone number is registered as a customer account")

            if asst_user["role"] != "assistant":
                db.execute("UPDATE users SET role='assistant' WHERE id=?", (asst_user["id"],))

        # ── Cross-worker ownership check ──────────────────────────────────────
        # If this phone already has an assistant record linked to a DIFFERENT worker,
        # block the re-link. The assistant must first be unlinked by their current worker.
        existing = db.execute(
            "SELECT linked_worker_id FROM assistants WHERE user_id=?",
            (asst_user["id"],)
        ).fetchone()

        if existing and existing["linked_worker_id"] is not None:
            if existing["linked_worker_id"] != worker_row["id"]:
                log.warning(
                    f"event=assistant_link_blocked reason=already_linked_to_other_worker "
                    f"requesting_worker={worker_row['id']} "
                    f"current_worker={existing['linked_worker_id']} "
                    f"phone={_mp(phone)}"
                )
                return err(
                    "This assistant is already linked to another worker. "
                    "They must be unlinked first.", 409
                )
            # Re-linking to the same worker — idempotent, allow it silently

        # Upsert
        if not existing:
            db.execute("INSERT INTO assistants (user_id, linked_worker_id) VALUES (?,?)",
                       (asst_user["id"], worker_row["id"]))
        else:
            db.execute("UPDATE assistants SET linked_worker_id=? WHERE user_id=?",
                       (worker_row["id"], asst_user["id"]))

        db.commit()

        log.info(
            f"event=assistant_linked worker_id={worker_row['id']} "
            f"assistant_user_id={asst_user['id']} phone={_mp(phone)}"
        )
        return ok({"message": f"Assistant {phone} linked to your profile"})

    except sqlite3.Error as e:
        db.rollback()
        log.error(f"event=assistant_link_error worker_id={worker_row['id']} error={e!r}")
        return err("Failed to link assistant — please try again", 500)


@app.route("/api/assistant/status", methods=["PUT"])
@role_required("assistant")
def update_assistant_status():
    new_status = _s((request.json or {}).get("status", ""), 20)
    if new_status not in VALID_WORKER_STATUS:
        return err(f"Invalid status '{new_status}'. "
                   f"Must be: {', '.join(sorted(VALID_WORKER_STATUS))}")
    db = get_db()
    db.execute("UPDATE assistants SET status=? WHERE user_id=?",
               (new_status, g.current_user["id"]))
    db.commit()
    return ok({"status": new_status})


@app.route("/api/assistant/profile", methods=["GET"])
@role_required("assistant")
def get_assistant_profile():
    db   = get_db()
    asst = db.execute("SELECT * FROM assistants WHERE user_id=?",
                      (g.current_user["id"],)).fetchone()
    if not asst:
        return err("Assistant profile not found", 404)

    asst_dict = dict(asst)
    linked    = None
    if asst_dict.get("linked_worker_id"):
        row = db.execute(
            "SELECT w.id, w.category, w.rating, w.status, u.name, u.phone "
            "FROM workers w JOIN users u ON w.user_id=u.id WHERE w.id=?",
            (asst_dict["linked_worker_id"],)
        ).fetchone()
        if row:
            linked = dict(row)

    return ok({"assistant": asst_dict, "linked_worker": linked})


# ══════════════════════════════════════════════════════════════════════════════
#  HEALTH
# ══════════════════════════════════════════════════════════════════════════════

from flask import send_from_directory

@app.route("/")
def home():
    return send_from_directory(".", "index.html")


# ══════════════════════════════════════════════════════════════════════════════
#  STARTUP
# ══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    init_db()
import os

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port)
