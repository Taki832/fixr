"""
init_db.py — Run this ONCE to create the SQLite schema and seed workers.
Usage:  python init_db.py
Safe to re-run (won't overwrite existing data).
"""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))

from app import init_db

if __name__ == "__main__":
    init_db()
    print("Done. You can now run:  python app.py")
