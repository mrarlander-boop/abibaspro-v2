import io
import os
import glob
import json
import math
import time
import hashlib
import random
import sqlite3
import asyncio
import threading
from datetime import datetime, timedelta, timezone

import numpy as np
import discord
from discord.ext import commands, tasks
from discord import app_commands
from PIL import Image, ImageDraw, ImageFont

try:
    from dotenv import load_dotenv
except ImportError:
    load_dotenv = None

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
if load_dotenv is not None:
    load_dotenv(os.path.join(BASE_DIR, ".env"))

# ---------- НАСТРОЙКИ ----------
TOKEN = os.getenv("DISCORD_BOT_TOKEN") or os.getenv("DISCORD_TOKEN") or os.getenv("BOT_TOKEN")
if not TOKEN:
    raise RuntimeError("Токен не найден! Укажи DISCORD_BOT_TOKEN в настройках бота на Bothost или в .env")
TOKEN = TOKEN.strip().strip('"').strip("'").strip()
print(f"[ТОКЕН] найден, длина: {len(TOKEN)}", flush=True)

# --- AFK ---
AFK_CHANNEL_ID = 0            # ID AFK-комнаты, куда перекидывать (0 = взять "Неактивный канал" из настроек сервера)
AFK_CHANNEL_IDS = []          # дополнительные каналы, где время не считается, например [123456789]
AFK_TIMEOUT = 15 * 60         # через сколько секунд неактивности перекидывать в AFK (15 минут)

TICK_SECONDS = 15             # как часто бот проверяет голосовые каналы
MAX_CREDIT = 60               # максимум секунд, которые можно начислить за один раз (защита от лагов)

# --- ЭКОНОМИКА И ОПЫТ ---
VOICE_COIN_INTERVAL = 5 * 60  # каждые 5 минут в войсе выдаётся награда
VOICE_COINS_MIN = 5           # минимум монет за 5 минут в войсе
VOICE_COINS_MAX = 20          # максимум монет за 5 минут в войсе

MSG_COINS_MIN = 5             # минимум монет за сообщение
MSG_COINS_MAX = 20            # максимум монет за сообщение
MSG_REWARD_COOLDOWN = 60      # кулдаун на получение монет/XP за сообщения (в секундах)

XP_PER_VOICE_MINUTE = 10      # XP за каждую минуту в голосовом канале
XP_PER_MESSAGE = 15           # XP за сообщение (с учётом кулдауна)
COIN_UNIT = "монет"

# --- ПРЕДУПРЕЖДЕНИЯ ---
MAX_WARNS = 3
AUTO_BAN_ON_MAX_WARNS = True  # авто-бан при 3 активных предупреждениях (если у бота есть права)

# --- КАРТОЧКИ ---
CARD_PRICE = 100              # цена одной карточки
CARD_SERIES = "MINESHIELD"    # надпись над ником на карточке
CARD_SEASON = "SEASON IV"     # надпись под ником на карточке

BG_PATH = os.path.join(BASE_DIR, "background.png")          # фон для /profile (1536x1024)
TOP_BG_PATH = os.path.join(BASE_DIR, "top_background.png")  # фон для /top (1967x799)
DB_PATH = os.getenv("DB_PATH") or os.path.join(BASE_DIR, "voice_time.db")
JSON_BACKUP_PATH = DB_PATH + ".backup.json"
CARDS_DIR = os.path.join(BASE_DIR, "cards")

# --- БЭКАП В DISCORD (ДЛЯ ПЕРЕЗАГРУЗОК / ПЕРЕЗАЛИВОК НА BOTHOST) ---
BACKUP_CHANNEL_ID = int(os.getenv("BACKUP_CHANNEL_ID") or 0)
AUTO_CREATE_BACKUP_CHANNEL = True   # если BACKUP_CHANNEL_ID=0, бот сам найдёт/создаст скрытый канал для бэкапов
BACKUP_CHANNEL_NAME = "bot-db-backup"
BACKUP_CHANNEL_MARKER = "[ABIBAS_DB_BACKUP]"
BACKUP_FILENAME = "voice_time.db"
BACKUP_KEEP = 3
BACKUP_LOOP_SECONDS = 60
BACKUP_DEBOUNCE_SECONDS = 5

# --- Таблица лидеров (/top) ---
TOP_OUT_W = 1600
TOP_RANK_X = 300
TOP_NAME_X = 400
TOP_SUB_RIGHT = 1320
TOP_VAL_RIGHT = 1670
TOP_PITCH = 66
TOP_PITCH_5 = 56
TOP_CENTER_Y = 450
TOP_LINE_CENTER_X = 985
TOP_LINE_X = (290, 1680)
TOP_LINE_COLOR = (170, 30, 30)
TOP_RANK_COLOR = (215, 45, 45)
TOP_NAME_COLOR = (255, 255, 255)
TOP_SUB_COLOR = (165, 165, 175)
TOP_VAL_COLOR = (235, 235, 235)
TOP_DX = 0
TOP_DY = 0

RARITY_COLORS = {
    "Обычная": (150, 155, 160),
    "Редкая": (70, 140, 255),
    "Эпическая": (170, 80, 255),
    "Легендарная": (255, 180, 40),
}

CARDS = [
    {"id": "bez_ls", "name": "Bez_LS", "rarity": "Обычная", "weight": 60, "image": "bez_ls.png"},
    {"id": "abibaspro", "name": "abibaspro", "rarity": "Редкая", "weight": 30, "image": "abibaspro.png"},
    {"id": "nick3", "name": "Ник 3", "rarity": "Эпическая", "weight": 9, "image": "nick3.png"},
    {"id": "nick4", "name": "Ник 4", "rarity": "Легендарная", "weight": 1, "image": "nick4.png"},
]
CARDS_BY_ID = {c["id"]: c for c in CARDS}
# --------------------------------

intents = discord.Intents.default()
intents.members = True
intents.voice_states = True

voice_sessions = {}   # {user_id: время последнего начисления}
session_start = {}    # {user_id: начало текущей сессии}
last_active = {}      # {user_id: время последней активности}

_db_lock = threading.Lock()
_last_backup_hash = None
_backup_debounce_task = None
_active_backup_channel_id = BACKUP_CHANNEL_ID


# ---------- УРОВНИ И ФОРМАТИРОВАНИЕ ----------
def xp_needed_for_level(level: int) -> int:
    """На 6 уровне требуется 580 XP (как в макете 470 / 580 XP)."""
    if level <= 0:
        return 100
    return 100 + level * 80


def fmt_num(value) -> str:
    return f"{int(value):,}".replace(",", " ")


def format_hm(sec: int) -> str:
    h, rem = divmod(max(0, int(sec)), 3600)
    return f"{h} ч {rem // 60} м"


def format_seconds(sec: int) -> str:
    return str(timedelta(seconds=max(0, int(sec))))


# ---------- БАЗА ДАННЫХ ----------
def _connect():
    conn = sqlite3.connect(DB_PATH, timeout=15)
    conn.execute("PRAGMA busy_timeout=15000")
    return conn


def _bump_revision(conn_or_cur, now: float = None):
    ts = str(int(now or time.time()))
    conn_or_cur.execute("""
        INSERT INTO bot_meta (key, value) VALUES ('revision', '1')
        ON CONFLICT(key) DO UPDATE SET value = CAST(COALESCE(CAST(value AS INTEGER), 0) + 1 AS TEXT)
    """)
    conn_or_cur.execute("""
        INSERT INTO bot_meta (key, value) VALUES ('updated_at', ?)
        ON CONFLICT(key) DO UPDATE SET value = ?
    """, (ts, ts))


def _ensure_column(c, table: str, column: str, ddl: str):
    cols = {row[1] for row in c.execute(f"PRAGMA table_info({table})").fetchall()}
    if column not in cols:
        c.execute(f"ALTER TABLE {table} ADD COLUMN {ddl}")


def _apply_xp_delta(c, user_id: int, guild_id: int, xp_gain: int):
    if xp_gain <= 0:
        return
    row = c.execute(
        "SELECT xp, level FROM levels WHERE user_id = ? AND guild_id = ?",
        (user_id, guild_id),
    ).fetchone()
    xp, level = (row[0], row[1]) if row else (0, 0)
    xp += xp_gain
    while xp >= xp_needed_for_level(level):
        xp -= xp_needed_for_level(level)
        level += 1
    c.execute("""
        INSERT INTO levels (user_id, guild_id, xp, level) VALUES (?, ?, ?, ?)
        ON CONFLICT(user_id, guild_id) DO UPDATE SET xp = ?, level = ?
    """, (user_id, guild_id, xp, level, xp, level))


def init_db():
    db_dir = os.path.dirname(os.path.abspath(DB_PATH))
    if db_dir:
        os.makedirs(db_dir, exist_ok=True)
    with _db_lock:
        conn = _connect()
        try:
            c = conn.cursor()
            c.execute("PRAGMA journal_mode=WAL")
            c.execute("PRAGMA synchronous=NORMAL")
            c.execute("""
                CREATE TABLE IF NOT EXISTS voice_time (
                    user_id INTEGER,
                    guild_id INTEGER,
                    total_seconds INTEGER DEFAULT 0,
                    coin_progress INTEGER DEFAULT 0,
                    xp_progress INTEGER DEFAULT 0,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)
            _ensure_column(c, "voice_time", "coin_progress", "coin_progress INTEGER DEFAULT 0")
            _ensure_column(c, "voice_time", "xp_progress", "xp_progress INTEGER DEFAULT 0")

            c.execute("""
                CREATE TABLE IF NOT EXISTS wallet (
                    user_id INTEGER,
                    guild_id INTEGER,
                    coins REAL DEFAULT 0,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)
            c.execute("""
                CREATE TABLE IF NOT EXISTS messages (
                    user_id INTEGER,
                    guild_id INTEGER,
                    count INTEGER DEFAULT 0,
                    last_reward_at REAL DEFAULT 0,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)
            c.execute("""
                CREATE TABLE IF NOT EXISTS levels (
                    user_id INTEGER,
                    guild_id INTEGER,
                    xp INTEGER DEFAULT 0,
                    level INTEGER DEFAULT 0,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)
            c.execute("""
                CREATE TABLE IF NOT EXISTS cards (
                    user_id INTEGER,
                    guild_id INTEGER,
                    card_id TEXT,
                    count INTEGER DEFAULT 0,
                    PRIMARY KEY (user_id, guild_id, card_id)
                )
            """)
            c.execute("""
                CREATE TABLE IF NOT EXISTS marriages (
                    guild_id INTEGER,
                    user_id INTEGER,
                    partner_id INTEGER NOT NULL,
                    married_at REAL NOT NULL,
                    PRIMARY KEY (guild_id, user_id)
                )
            """)
            c.execute("""
                CREATE TABLE IF NOT EXISTS warnings (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    moderator_id INTEGER NOT NULL,
                    reason TEXT NOT NULL,
                    created_at REAL NOT NULL,
                    active INTEGER DEFAULT 1,
                    removed_at REAL,
                    removed_by INTEGER
                )
            """)
            c.execute("""
                CREATE INDEX IF NOT EXISTS idx_warnings_user
                ON warnings (guild_id, user_id, active)
            """)
            c.execute("""
                CREATE TABLE IF NOT EXISTS bot_meta (
                    key TEXT PRIMARY KEY,
                    value TEXT
                )
            """)

            # Миграция опыта для аккаунтов из старой базы (у кого есть войс-время, но ещё нет строки в levels)
            legacy_users = c.execute("""
                SELECT v.user_id, v.guild_id, v.total_seconds
                FROM voice_time v
                LEFT JOIN levels l ON l.user_id = v.user_id AND l.guild_id = v.guild_id
                WHERE l.user_id IS NULL AND v.total_seconds >= 60
            """).fetchall()
            for uid, gid, secs in legacy_users:
                legacy_xp = (secs // 60) * XP_PER_VOICE_MINUTE
                _apply_xp_delta(c, uid, gid, legacy_xp)

            conn.commit()
        finally:
            conn.close()


def _export_json_snapshot_unlocked(conn) -> dict:
    def rows_as_dicts(sql):
        cur = conn.execute(sql)
        cols = [d[0] for d in cur.description]
        return [dict(zip(cols, r)) for r in cur.fetchall()]

    return {
        "exported_at": int(time.time()),
        "bot_meta": rows_as_dicts("SELECT key, value FROM bot_meta"),
        "voice_time": rows_as_dicts("SELECT user_id, guild_id, total_seconds, coin_progress, xp_progress FROM voice_time"),
        "wallet": rows_as_dicts("SELECT user_id, guild_id, coins FROM wallet"),
        "messages": rows_as_dicts("SELECT user_id, guild_id, count, last_reward_at FROM messages"),
        "levels": rows_as_dicts("SELECT user_id, guild_id, xp, level FROM levels"),
        "cards": rows_as_dicts("SELECT user_id, guild_id, card_id, count FROM cards"),
        "marriages": rows_as_dicts("SELECT guild_id, user_id, partner_id, married_at FROM marriages"),
        "warnings": rows_as_dicts("SELECT id, guild_id, user_id, moderator_id, reason, created_at, active, removed_at, removed_by FROM warnings"),
    }


def save_local_json_snapshot():
    if not os.path.isfile(DB_PATH):
        return
    with _db_lock:
        conn = _connect()
        try:
            data = _export_json_snapshot_unlocked(conn)
        finally:
            conn.close()
    tmp = JSON_BACKUP_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False)
    os.replace(tmp, JSON_BACKUP_PATH)


def restore_from_json_if_needed():
    """Резервное восстановление из локального JSON, если .db потеряна, а JSON остался."""
    if not os.path.isfile(JSON_BACKUP_PATH):
        return
    if os.path.isfile(DB_PATH) and _db_score(DB_PATH) not in (None, (0, 0)):
        return
    try:
        with open(JSON_BACKUP_PATH, "r", encoding="utf-8") as f:
            snap = json.load(f)
    except Exception:
        return
    init_db()
    with _db_lock:
        conn = _connect()
        try:
            with conn:
                for r in snap.get("voice_time", []):
                    conn.execute(
                        "INSERT OR REPLACE INTO voice_time (user_id, guild_id, total_seconds, coin_progress, xp_progress) VALUES (?, ?, ?, ?, ?)",
                        (r["user_id"], r["guild_id"], r["total_seconds"], r.get("coin_progress", 0), r.get("xp_progress", 0)),
                    )
                for r in snap.get("wallet", []):
                    conn.execute(
                        "INSERT OR REPLACE INTO wallet (user_id, guild_id, coins) VALUES (?, ?, ?)",
                        (r["user_id"], r["guild_id"], r["coins"]),
                    )
                for r in snap.get("messages", []):
                    conn.execute(
                        "INSERT OR REPLACE INTO messages (user_id, guild_id, count, last_reward_at) VALUES (?, ?, ?, ?)",
                        (r["user_id"], r["guild_id"], r["count"], r.get("last_reward_at", 0)),
                    )
                for r in snap.get("levels", []):
                    conn.execute(
                        "INSERT OR REPLACE INTO levels (user_id, guild_id, xp, level) VALUES (?, ?, ?, ?)",
                        (r["user_id"], r["guild_id"], r["xp"], r["level"]),
                    )
                for r in snap.get("cards", []):
                    conn.execute(
                        "INSERT OR REPLACE INTO cards (user_id, guild_id, card_id, count) VALUES (?, ?, ?, ?)",
                        (r["user_id"], r["guild_id"], r["card_id"], r["count"]),
                    )
                for r in snap.get("marriages", []):
                    conn.execute(
                        "INSERT OR REPLACE INTO marriages (guild_id, user_id, partner_id, married_at) VALUES (?, ?, ?, ?)",
                        (r["guild_id"], r["user_id"], r["partner_id"], r["married_at"]),
                    )
                for r in snap.get("warnings", []):
                    conn.execute(
                        "INSERT OR REPLACE INTO warnings (id, guild_id, user_id, moderator_id, reason, created_at, active, removed_at, removed_by) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                        (r["id"], r["guild_id"], r["user_id"], r["moderator_id"], r["reason"], r["created_at"], r["active"], r.get("removed_at"), r.get("removed_by")),
                    )
                for r in snap.get("bot_meta", []):
                    conn.execute(
                        "INSERT OR REPLACE INTO bot_meta (key, value) VALUES (?, ?)",
                        (r["key"], r["value"]),
                    )
        finally:
            conn.close()
    print("[БЭКАП] база восстановлена из локального JSON-снимка", flush=True)


def add_time_batch(items):
    """items: [(user_id, guild_id, seconds)]. Начисляет время, монеты (5-20 каждые 5 мин) и XP."""
    if not items:
        return
    with _db_lock:
        conn = _connect()
        try:
            with conn:
                c = conn.cursor()
                for user_id, guild_id, sec in items:
                    if sec <= 0:
                        continue
                    row = c.execute(
                        "SELECT total_seconds, coin_progress, xp_progress FROM voice_time WHERE user_id = ? AND guild_id = ?",
                        (user_id, guild_id),
                    ).fetchone()
                    total_sec, coin_prog, xp_prog = row if row else (0, 0, 0)
                    total_sec += sec
                    coin_prog += sec
                    xp_prog += sec

                    coins_gain = 0
                    while coin_prog >= VOICE_COIN_INTERVAL:
                        coin_prog -= VOICE_COIN_INTERVAL
                        coins_gain += random.randint(VOICE_COINS_MIN, VOICE_COINS_MAX)

                    xp_mins = xp_prog // 60
                    xp_prog = xp_prog % 60
                    xp_gain = xp_mins * XP_PER_VOICE_MINUTE

                    c.execute("""
                        INSERT INTO voice_time (user_id, guild_id, total_seconds, coin_progress, xp_progress)
                        VALUES (?, ?, ?, ?, ?)
                        ON CONFLICT(user_id, guild_id) DO UPDATE SET
                            total_seconds = ?, coin_progress = ?, xp_progress = ?
                    """, (user_id, guild_id, total_sec, coin_prog, xp_prog, total_sec, coin_prog, xp_prog))

                    if coins_gain > 0:
                        c.execute("""
                            INSERT INTO wallet (user_id, guild_id, coins) VALUES (?, ?, ?)
                            ON CONFLICT(user_id, guild_id) DO UPDATE SET coins = coins + ?
                        """, (user_id, guild_id, coins_gain, coins_gain))

                    if xp_gain > 0:
                        _apply_xp_delta(c, user_id, guild_id, xp_gain)

                _bump_revision(c)
        finally:
            conn.close()


def record_message(user_id: int, guild_id: int, now: float) -> tuple[int, int]:
    """Увеличивает счётчик сообщений и с кулдауном начисляет 5-20 монет + XP."""
    with _db_lock:
        conn = _connect()
        try:
            with conn:
                c = conn.cursor()
                row = c.execute(
                    "SELECT count, last_reward_at FROM messages WHERE user_id = ? AND guild_id = ?",
                    (user_id, guild_id),
                ).fetchone()
                count, last_reward = row if row else (0, 0.0)
                count += 1
                coins_gain = 0
                if now - (last_reward or 0.0) >= MSG_REWARD_COOLDOWN:
                    coins_gain = random.randint(MSG_COINS_MIN, MSG_COINS_MAX)
                    last_reward = now
                    c.execute("""
                        INSERT INTO wallet (user_id, guild_id, coins) VALUES (?, ?, ?)
                        ON CONFLICT(user_id, guild_id) DO UPDATE SET coins = coins + ?
                    """, (user_id, guild_id, coins_gain, coins_gain))
                    _apply_xp_delta(c, user_id, guild_id, XP_PER_MESSAGE)

                c.execute("""
                    INSERT INTO messages (user_id, guild_id, count, last_reward_at) VALUES (?, ?, ?, ?)
                    ON CONFLICT(user_id, guild_id) DO UPDATE SET count = ?, last_reward_at = ?
                """, (user_id, guild_id, count, last_reward, count, last_reward))
                _bump_revision(c, now)
                return count, coins_gain
        finally:
            conn.close()


def get_time(user_id: int, guild_id: int) -> int:
    with _db_lock:
        conn = _connect()
        try:
            row = conn.execute(
                "SELECT total_seconds FROM voice_time WHERE user_id = ? AND guild_id = ?",
                (user_id, guild_id),
            ).fetchone()
            return row[0] if row else 0
        finally:
            conn.close()


def get_coins(user_id: int, guild_id: int) -> float:
    with _db_lock:
        conn = _connect()
        try:
            row = conn.execute(
                "SELECT coins FROM wallet WHERE user_id = ? AND guild_id = ?",
                (user_id, guild_id),
            ).fetchone()
            return float(row[0]) if row else 0.0
        finally:
            conn.close()


def get_messages_count(user_id: int, guild_id: int) -> int:
    with _db_lock:
        conn = _connect()
        try:
            row = conn.execute(
                "SELECT count FROM messages WHERE user_id = ? AND guild_id = ?",
                (user_id, guild_id),
            ).fetchone()
            return int(row[0]) if row else 0
        finally:
            conn.close()


def give_coins(user_id: int, guild_id: int, amount: float):
    with _db_lock:
        conn = _connect()
        try:
            with conn:
                conn.execute("""
                    INSERT INTO wallet (user_id, guild_id, coins) VALUES (?, ?, ?)
                    ON CONFLICT(user_id, guild_id) DO UPDATE SET coins = coins + ?
                """, (user_id, guild_id, amount, amount))
                _bump_revision(conn)
        finally:
            conn.close()


def set_time(user_id: int, guild_id: int, seconds: int, coins: float = None):
    with _db_lock:
        conn = _connect()
        try:
            with conn:
                conn.execute("""
                    INSERT INTO voice_time (user_id, guild_id, total_seconds, coin_progress, xp_progress)
                    VALUES (?, ?, ?, 0, 0)
                    ON CONFLICT(user_id, guild_id) DO UPDATE SET total_seconds = ?
                """, (user_id, guild_id, seconds, seconds))
                if coins is not None:
                    conn.execute("""
                        INSERT INTO wallet (user_id, guild_id, coins) VALUES (?, ?, ?)
                        ON CONFLICT(user_id, guild_id) DO UPDATE SET coins = ?
                    """, (user_id, guild_id, coins, coins))
                _bump_revision(conn)
        finally:
            conn.close()


def set_messages(user_id: int, guild_id: int, count: int, xp_total: int = None):
    with _db_lock:
        conn = _connect()
        try:
            with conn:
                conn.execute("""
                    INSERT INTO messages (user_id, guild_id, count, last_reward_at) VALUES (?, ?, ?, 0)
                    ON CONFLICT(user_id, guild_id) DO UPDATE SET count = ?
                """, (user_id, guild_id, count, count))
                if xp_total is not None:
                    xp = max(0, xp_total)
                    level = 0
                    while xp >= xp_needed_for_level(level):
                        xp -= xp_needed_for_level(level)
                        level += 1
                    conn.execute("""
                        INSERT INTO levels (user_id, guild_id, xp, level) VALUES (?, ?, ?, ?)
                        ON CONFLICT(user_id, guild_id) DO UPDATE SET xp = ?, level = ?
                    """, (user_id, guild_id, xp, level, xp, level))
                _bump_revision(conn)
        finally:
            conn.close()


def buy_card(user_id: int, guild_id: int, card_id: str, price: int) -> bool:
    with _db_lock:
        conn = sqlite3.connect(DB_PATH, timeout=15, isolation_level=None)
        c = conn.cursor()
        try:
            c.execute("PRAGMA busy_timeout=15000")
            c.execute("BEGIN IMMEDIATE")
            c.execute("SELECT coins FROM wallet WHERE user_id = ? AND guild_id = ?", (user_id, guild_id))
            row = c.fetchone()
            if not row or row[0] < price:
                c.execute("ROLLBACK")
                return False
            c.execute("UPDATE wallet SET coins = coins - ? WHERE user_id = ? AND guild_id = ?",
                      (price, user_id, guild_id))
            c.execute("""
                INSERT INTO cards (user_id, guild_id, card_id, count) VALUES (?, ?, ?, 1)
                ON CONFLICT(user_id, guild_id, card_id) DO UPDATE SET count = count + 1
            """, (user_id, guild_id, card_id))
            _bump_revision(c)
            c.execute("COMMIT")
            return True
        except Exception:
            try:
                c.execute("ROLLBACK")
            except Exception:
                pass
            raise
        finally:
            conn.close()


def get_inventory(user_id: int, guild_id: int) -> dict:
    with _db_lock:
        conn = _connect()
        try:
            rows = conn.execute(
                "SELECT card_id, count FROM cards WHERE user_id = ? AND guild_id = ? AND count > 0",
                (user_id, guild_id),
            ).fetchall()
            return {cid: cnt for cid, cnt in rows}
        finally:
            conn.close()


def get_partner(guild_id: int, user_id: int):
    with _db_lock:
        conn = _connect()
        try:
            row = conn.execute(
                "SELECT partner_id, married_at FROM marriages WHERE guild_id = ? AND user_id = ?",
                (guild_id, user_id),
            ).fetchone()
            return row if row else None
        finally:
            conn.close()


def create_marriage(guild_id: int, user1: int, user2: int) -> tuple[bool, str]:
    now = time.time()
    with _db_lock:
        conn = sqlite3.connect(DB_PATH, timeout=15, isolation_level=None)
        c = conn.cursor()
        try:
            c.execute("PRAGMA busy_timeout=15000")
            c.execute("BEGIN IMMEDIATE")
            r1 = c.execute("SELECT partner_id FROM marriages WHERE guild_id = ? AND user_id = ?", (guild_id, user1)).fetchone()
            if r1:
                c.execute("ROLLBACK")
                return False, "first_married"
            r2 = c.execute("SELECT partner_id FROM marriages WHERE guild_id = ? AND user_id = ?", (guild_id, user2)).fetchone()
            if r2:
                c.execute("ROLLBACK")
                return False, "second_married"
            c.execute("INSERT INTO marriages (guild_id, user_id, partner_id, married_at) VALUES (?, ?, ?, ?)",
                      (guild_id, user1, user2, now))
            c.execute("INSERT INTO marriages (guild_id, user_id, partner_id, married_at) VALUES (?, ?, ?, ?)",
                      (guild_id, user2, user1, now))
            _bump_revision(c, now)
            c.execute("COMMIT")
            return True, "ok"
        except Exception:
            try:
                c.execute("ROLLBACK")
            except Exception:
                pass
            raise
        finally:
            conn.close()


def delete_marriage(guild_id: int, user_id: int):
    with _db_lock:
        conn = sqlite3.connect(DB_PATH, timeout=15, isolation_level=None)
        c = conn.cursor()
        try:
            c.execute("PRAGMA busy_timeout=15000")
            c.execute("BEGIN IMMEDIATE")
            row = c.execute("SELECT partner_id FROM marriages WHERE guild_id = ? AND user_id = ?", (guild_id, user_id)).fetchone()
            if not row:
                c.execute("ROLLBACK")
                return None
            partner_id = row[0]
            c.execute("DELETE FROM marriages WHERE guild_id = ? AND user_id IN (?, ?)", (guild_id, user_id, partner_id))
            _bump_revision(c)
            c.execute("COMMIT")
            return partner_id
        except Exception:
            try:
                c.execute("ROLLBACK")
            except Exception:
                pass
            raise
        finally:
            conn.close()


def add_warning(guild_id: int, user_id: int, moderator_id: int, reason: str) -> tuple[int, int]:
    now = time.time()
    with _db_lock:
        conn = _connect()
        try:
            with conn:
                c = conn.cursor()
                c.execute("""
                    INSERT INTO warnings (guild_id, user_id, moderator_id, reason, created_at, active)
                    VALUES (?, ?, ?, ?, ?, 1)
                """, (guild_id, user_id, moderator_id, reason.strip()[:200], now))
                warn_id = c.lastrowid
                active_cnt = c.execute(
                    "SELECT COUNT(*) FROM warnings WHERE guild_id = ? AND user_id = ? AND active = 1",
                    (guild_id, user_id),
                ).fetchone()[0]
                _bump_revision(c, now)
                return warn_id, active_cnt
        finally:
            conn.close()


def remove_warning(guild_id: int, user_id: int, moderator_id: int, warn_id: int = None) -> tuple[bool, int]:
    now = time.time()
    with _db_lock:
        conn = _connect()
        try:
            with conn:
                c = conn.cursor()
                if warn_id is not None:
                    row = c.execute(
                        "SELECT id FROM warnings WHERE id = ? AND guild_id = ? AND user_id = ? AND active = 1",
                        (warn_id, guild_id, user_id),
                    ).fetchone()
                else:
                    row = c.execute(
                        "SELECT id FROM warnings WHERE guild_id = ? AND user_id = ? AND active = 1 ORDER BY id DESC LIMIT 1",
                        (guild_id, user_id),
                    ).fetchone()
                if not row:
                    return False, c.execute(
                        "SELECT COUNT(*) FROM warnings WHERE guild_id = ? AND user_id = ? AND active = 1",
                        (guild_id, user_id),
                    ).fetchone()[0]
                target_id = row[0]
                c.execute(
                    "UPDATE warnings SET active = 0, removed_at = ?, removed_by = ? WHERE id = ?",
                    (now, moderator_id, target_id),
                )
                active_cnt = c.execute(
                    "SELECT COUNT(*) FROM warnings WHERE guild_id = ? AND user_id = ? AND active = 1",
                    (guild_id, user_id),
                ).fetchone()[0]
                _bump_revision(c, now)
                return True, active_cnt
        finally:
            conn.close()


def clear_warnings(guild_id: int, user_id: int, moderator_id: int) -> int:
    now = time.time()
    with _db_lock:
        conn = _connect()
        try:
            with conn:
                c = conn.cursor()
                res = c.execute(
                    "UPDATE warnings SET active = 0, removed_at = ?, removed_by = ? WHERE guild_id = ? AND user_id = ? AND active = 1",
                    (now, moderator_id, guild_id, user_id),
                )
                if res.rowcount > 0:
                    _bump_revision(c, now)
                return res.rowcount
        finally:
            conn.close()


def get_warnings(guild_id: int, user_id: int, limit: int = 10) -> tuple[int, list]:
    with _db_lock:
        conn = _connect()
        try:
            active_cnt = conn.execute(
                "SELECT COUNT(*) FROM warnings WHERE guild_id = ? AND user_id = ? AND active = 1",
                (guild_id, user_id),
            ).fetchone()[0]
            rows = conn.execute("""
                SELECT id, moderator_id, reason, created_at, active
                FROM warnings
                WHERE guild_id = ? AND user_id = ?
                ORDER BY id DESC LIMIT ?
            """, (guild_id, user_id, limit)).fetchall()
            return active_cnt, rows
        finally:
            conn.close()


def get_profile_data(user_id: int, guild_id: int) -> dict:
    with _db_lock:
        conn = _connect()
        try:
            vt = conn.execute("SELECT total_seconds FROM voice_time WHERE user_id = ? AND guild_id = ?",
                              (user_id, guild_id)).fetchone()
            wl = conn.execute("SELECT coins FROM wallet WHERE user_id = ? AND guild_id = ?",
                              (user_id, guild_id)).fetchone()
            ms = conn.execute("SELECT count FROM messages WHERE user_id = ? AND guild_id = ?",
                              (user_id, guild_id)).fetchone()
            lv = conn.execute("SELECT xp, level FROM levels WHERE user_id = ? AND guild_id = ?",
                              (user_id, guild_id)).fetchone()
            mr = conn.execute("SELECT partner_id, married_at FROM marriages WHERE guild_id = ? AND user_id = ?",
                              (guild_id, user_id)).fetchone()
            cc = conn.execute("SELECT COALESCE(SUM(count), 0) FROM cards WHERE user_id = ? AND guild_id = ?",
                              (user_id, guild_id)).fetchone()
            active_warns = conn.execute(
                "SELECT COUNT(*) FROM warnings WHERE guild_id = ? AND user_id = ? AND active = 1",
                (guild_id, user_id),
            ).fetchone()[0]
            warn_rows = conn.execute("""
                SELECT id, moderator_id, reason, created_at, active
                FROM warnings
                WHERE guild_id = ? AND user_id = ?
                ORDER BY id DESC LIMIT 3
            """, (guild_id, user_id)).fetchall()
        finally:
            conn.close()

    xp, level = (lv[0], lv[1]) if lv else (0, 0)
    return {
        "total_seconds": int(vt[0]) if vt else 0,
        "coins": int(wl[0]) if wl else 0,
        "messages": int(ms[0]) if ms else 0,
        "xp": int(xp),
        "level": int(level),
        "xp_need": xp_needed_for_level(int(level)),
        "partner_id": int(mr[0]) if mr else None,
        "married_at": float(mr[1]) if mr else None,
        "cards_count": int(cc[0]) if cc else 0,
        "active_warns": int(active_warns),
        "warnings": warn_rows,
    }


def get_top_users(guild_id: int) -> list[dict]:
    """Возвращает агрегированную статистику всех участников сервера из базы."""
    with _db_lock:
        conn = _connect()
        try:
            users = {}

            def entry(uid):
                if uid not in users:
                    users[uid] = {
                        "user_id": uid,
                        "coins": 0,
                        "messages": 0,
                        "total_seconds": 0,
                        "level": 0,
                        "xp": 0,
                    }
                return users[uid]

            for uid, coins in conn.execute("SELECT user_id, coins FROM wallet WHERE guild_id = ?", (guild_id,)):
                entry(uid)["coins"] = int(coins or 0)
            for uid, cnt in conn.execute("SELECT user_id, count FROM messages WHERE guild_id = ?", (guild_id,)):
                entry(uid)["messages"] = int(cnt or 0)
            for uid, sec in conn.execute("SELECT user_id, total_seconds FROM voice_time WHERE guild_id = ?", (guild_id,)):
                entry(uid)["total_seconds"] = int(sec or 0)
            for uid, xp, lvl in conn.execute("SELECT user_id, xp, level FROM levels WHERE guild_id = ?", (guild_id,)):
                e = entry(uid)
                e["xp"] = int(xp or 0)
                e["level"] = int(lvl or 0)
            return list(users.values())
        finally:
            conn.close()


# ---------- КАРТОЧКИ: ШАНСЫ ----------
def roll_card() -> dict:
    return random.choices(CARDS, weights=[c["weight"] for c in CARDS], k=1)[0]


def card_chance(card: dict) -> float:
    total = sum(c["weight"] for c in CARDS)
    return card["weight"] / total * 100


# ---------- ШРИФТЫ ----------
_font_cache = {}
_logged = set()

SYSTEM_BOLD = [
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
    "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf",
    "DejaVuSans-Bold.ttf",
]
SYSTEM_REGULAR = [
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
    "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf",
    "DejaVuSans.ttf",
]


def _local_fonts(bold: bool):
    files = []
    for pattern in ("*.ttf", "*.otf", os.path.join("fonts", "*.ttf"), os.path.join("fonts", "*.otf")):
        files += glob.glob(os.path.join(BASE_DIR, pattern))
    files = sorted(set(files))

    def name(p):
        return os.path.basename(p).lower()

    bad = ("italic", "light", "thin", "medium", "black", "condensed", "semi", "extra")
    result = []

    def add(p, genuine):
        if p not in [r[0] for r in result]:
            result.append((p, genuine))

    if bold:
        for p in files:
            if name(p) == "font_bold.ttf":
                add(p, True)
        for p in files:
            if "bold" in name(p) and not any(b in name(p) for b in bad):
                add(p, True)
        for p in files:
            if "italic" not in name(p):
                add(p, False)
    else:
        for p in files:
            if name(p) == "font.ttf":
                add(p, True)
        for p in files:
            if "regular" in name(p) and "italic" not in name(p):
                add(p, True)
        for p in files:
            if "italic" not in name(p) and "bold" not in name(p):
                add(p, True)
        for p in files:
            add(p, True)
    return result


def _has_cyrillic(font) -> bool:
    try:
        a, b = font.getmask("Ж"), font.getmask("Щ")
        return a.size != b.size or a.tobytes() != b.tobytes()
    except Exception:
        return False


def load_font(size: int, bold: bool = False):
    size = max(8, int(size))
    key = (size, bold)
    if key in _font_cache:
        return _font_cache[key]

    candidates = _local_fonts(bold)
    sys_list = SYSTEM_BOLD if bold else SYSTEM_REGULAR
    candidates += [(p, True) for p in sys_list]
    if bold:
        candidates += [(p, False) for p in SYSTEM_REGULAR]

    font = None
    for path, genuine in candidates:
        try:
            f = ImageFont.truetype(path, size)
        except Exception:
            continue
        faux = bold and not genuine
        try:
            f.set_variation_by_name("Bold" if bold else "Regular")
            if bold:
                faux = False
        except Exception:
            pass
        if not _has_cyrillic(f):
            continue
        f._faux = faux
        font = f
        if (path, bold) not in _logged:
            _logged.add((path, bold))
            print(f"[ШРИФТ] {'bold' if bold else 'regular'}: {path}{' (+жирность)' if faux else ''}", flush=True)
        break

    if font is None:
        try:
            font = ImageFont.load_default(size)
        except TypeError:
            font = ImageFont.load_default()
        try:
            font._faux = False
        except Exception:
            pass

    _font_cache[key] = font
    return font


def txt(d: ImageDraw.ImageDraw, xy, text: str, font, fill, anchor=None):
    """Рисует текст; аккуратно имитирует жирный шрифт без размытия мелких букв."""
    kw = {}
    if anchor:
        kw["anchor"] = anchor
    faux = getattr(font, "_faux", False)
    size = getattr(font, "size", 20)
    if faux and size >= 34:
        kw["stroke_width"] = max(1, round(size / 42))
        kw["stroke_fill"] = fill
        d.text(xy, text, font=font, fill=fill, **kw)
    elif faux:
        x, y = xy
        d.text((x, y), text, font=font, fill=fill, **kw)
        d.text((x + 1, y), text, font=font, fill=fill, **kw)
    else:
        d.text(xy, text, font=font, fill=fill, **kw)


def fit_text(d: ImageDraw.ImageDraw, text: str, max_width: int, start_size: int,
             min_size: int = 14, bold: bool = False):
    """Подбирает размер шрифта под ширину и обрезает слишком длинную строку с '…'."""
    for sz in range(start_size, min_size - 1, -1):
        f = load_font(sz, bold=bold)
        bbox = d.textbbox((0, 0), text, font=f)
        if bbox[2] - bbox[0] <= max_width:
            return text, f
    f = load_font(min_size, bold=bold)
    trimmed = text
    while len(trimmed) > 1:
        candidate = trimmed + "…"
        bbox = d.textbbox((0, 0), candidate, font=f)
        if bbox[2] - bbox[0] <= max_width:
            return candidate, f
        trimmed = trimmed[:-1]
    return text[:1], f


# ---------- КАРТИНКИ ----------
_bg_cache = {}


def get_bg(path: str, width: int = None):
    key = (path, width)
    if key not in _bg_cache:
        bg = Image.open(path).convert("RGBA")
        if width is not None and width != bg.width:
            s = width / bg.width
            img = bg.resize((width, int(bg.height * s)), Image.LANCZOS)
        else:
            s = bg.width / 1536.0 if path == BG_PATH else 1.0
            img = bg
        _bg_cache[key] = (img, s)
    img, s = _bg_cache[key]
    return img.copy(), s


def circle_avatar(data: bytes, size: int) -> Image.Image:
    img = Image.open(io.BytesIO(data)).convert("RGBA").resize((size, size), Image.LANCZOS)
    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).ellipse((0, 0, size - 1, size - 1), fill=255)
    img.putalpha(mask)
    return img


def rounded_avatar(data: bytes, size: int, radius: int) -> Image.Image:
    img = Image.open(io.BytesIO(data)).convert("RGBA").resize((size, size), Image.LANCZOS)
    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, size - 1, size - 1), radius=radius, fill=255)
    img.putalpha(mask)
    return img


def _draw_segmented_ring(base_img: Image.Image, cx: int, cy: int,
                         r_inner: int, r_outer: int, progress: float, s: float):
    """Рисует динамическое 8-сегментное кольцо уровня поверх шаблона с 4x сглаживанием."""
    progress = max(0.0, min(1.0, progress))
    pad = int(round((r_outer + 10) * s))
    box_size = pad * 2
    scale = 4
    hi_size = box_size * scale

    c_hi = hi_size // 2
    ro = int(round(r_outer * s * scale))
    ri = int(round(r_inner * s * scale))
    track_bbox = (c_hi - ro, c_hi - ro, c_hi + ro, c_hi + ro)

    # 1. Тёмная подложка под кольцом, чтобы полностью перекрыть статичные сектора фона
    ro_bg = ro + 3 * scale
    ri_bg = ri - 3 * scale
    cover = Image.new("RGBA", (hi_size, hi_size), (10, 8, 10, 240))
    cover_mask = Image.new("L", (hi_size, hi_size), 0)
    cmd = ImageDraw.Draw(cover_mask)
    cmd.ellipse((c_hi - ro_bg, c_hi - ro_bg, c_hi + ro_bg, c_hi + ro_bg), fill=255)
    cmd.ellipse((c_hi - ri_bg, c_hi - ri_bg, c_hi + ri_bg, c_hi + ri_bg), fill=0)
    cover.putalpha(cover_mask)

    # 2. Цветной слой кольца (серый трек + красная дуга прогресса)
    ring_rgb = Image.new("RGBA", (hi_size, hi_size), (0, 0, 0, 0))
    rd = ImageDraw.Draw(ring_rgb)
    rd.pieslice(track_bbox, start=0, end=360, fill=(64, 64, 70, 255))
    if progress > 0.001:
        end_deg = -90.0 + 360.0 * progress
        rd.pieslice(track_bbox, start=-90.0, end=end_deg, fill=(215, 42, 58, 255))

    # 3. Альфа-маска в режиме "L" (гарантирует прозрачный центр и 8 радиальных зазоров)
    ring_mask = Image.new("L", (hi_size, hi_size), 0)
    md = ImageDraw.Draw(ring_mask)
    md.ellipse(track_bbox, fill=255)
    md.ellipse((c_hi - ri, c_hi - ri, c_hi + ri, c_hi + ri), fill=0)

    gap_half = math.radians(2.2)
    r_cut = ro + 4 * scale
    for k in range(8):
        ang = math.radians(k * 45.0)
        poly = [
            (c_hi, c_hi),
            (c_hi + r_cut * math.cos(ang - gap_half), c_hi + r_cut * math.sin(ang - gap_half)),
            (c_hi + r_cut * math.cos(ang + gap_half), c_hi + r_cut * math.sin(ang + gap_half)),
        ]
        md.polygon(poly, fill=0)

    ring_rgb.putalpha(ring_mask)
    combined = Image.alpha_composite(cover, ring_rgb)
    ring_layer = combined.resize((box_size, box_size), Image.LANCZOS)
    base_img.alpha_composite(ring_layer, (int(round(cx * s)) - pad, int(round(cy * s)) - pad))


def _draw_filled_star(d: ImageDraw.ImageDraw, cx: float, cy: float,
                      r_out: float, r_in: float, fill, outline=None, width: int = 2):
    pts = []
    for i in range(10):
        ang = math.radians(-90 + i * 36)
        r = r_out if i % 2 == 0 else r_in
        pts.append((cx + r * math.cos(ang), cy + r * math.sin(ang)))
    d.polygon(pts, fill=fill)
    if outline:
        d.line(pts + [pts[0]], fill=outline, width=width)


def make_profile_card(
    name: str,
    user_id: int,
    avatar_bytes: bytes,
    stats: dict,
    current_voice_session: int = 0,
    partner_name: str = None,
    partner_avatar_bytes: bytes = None,
    mod_names: dict = None,
) -> io.BytesIO:
    """Рендерит карточку профиля в стиле 2-го фото на новом фоне Agency 'ARG' (1536x1024)."""
    img, s = get_bg(BG_PATH)
    s = img.width / 1536.0

    def S(v):
        return int(round(v * s))

    d = ImageDraw.Draw(img)
    mod_names = mod_names or {}

    # 1. Квадратный аватар со скруглением внутри красных уголков (78, 254, 250x250)
    av_size = S(250)
    av = rounded_avatar(avatar_bytes, av_size, S(10))
    ax, ay = S(78), S(254)
    img.paste(av, (ax, ay), av)
    d.rounded_rectangle((ax, ay, ax + av_size, ay + av_size), radius=S(10),
                        outline=(195, 38, 48), width=max(1, S(2)))

    # 2. Ник и Discord ID справа от аватара (выше кольца и шкалы XP)
    clean_name, f_name = fit_text(d, name, S(1020), S(46), S(26), bold=True)
    txt(d, (S(404), S(238)), clean_name, f_name, (255, 255, 255), anchor="lt")
    txt(d, (S(404), S(292)), f"ID: {user_id}", load_font(S(20)), (165, 165, 175), anchor="lt")
    d.line((S(404), S(325), S(1446), S(325)), fill=(85, 34, 38), width=max(1, S(1)))

    # 3. Кольцо уровня (центр 483, 411) + шкала XP (612..1446, 403..425)
    xp = stats["xp"]
    xp_need = max(1, stats["xp_need"])
    level = stats["level"]
    progress = min(1.0, xp / xp_need)
    xp_left = max(0, xp_need - xp)

    _draw_segmented_ring(img, 483, 411, 68, 80, progress, s)
    d = ImageDraw.Draw(img)  # обновляем Draw после alpha_composite

    txt(d, (S(483), S(400)), str(level), load_font(S(46), True), (255, 255, 255), anchor="mm")
    txt(d, (S(483), S(434)), "УРОВЕНЬ", load_font(S(15)), (170, 170, 180), anchor="mm")

    txt(d, (S(612), S(352)), f"{fmt_num(xp)} / {fmt_num(xp_need)} XP",
        load_font(S(30), True), (255, 255, 255), anchor="lt")

    bar_x1, bar_y1, bar_x2, bar_y2 = S(612), S(403), S(1446), S(425)
    bar_r = S(11)
    d.rounded_rectangle((bar_x1, bar_y1, bar_x2, bar_y2), radius=bar_r, fill=(36, 36, 42))
    if xp > 0:
        fill_w = max(bar_r * 2, int((bar_x2 - bar_x1) * progress))
        d.rounded_rectangle((bar_x1, bar_y1, min(bar_x2, bar_x1 + fill_w), bar_y2),
                            radius=bar_r, fill=(210, 42, 58))

    # Скрываем фоновую серую плашку под шкалой XP, чтобы текст был идеально читаемым
    d.rounded_rectangle((S(602), S(448), S(875), S(478)), radius=S(6), fill=(10, 8, 10))
    txt(d, (S(612), S(449)), f"До следующего уровня: {fmt_num(xp_left)} XP",
        load_font(S(22)), (185, 185, 195), anchor="lt")

    # 4. Четыре карточки статистики (y = 547..685)
    # 4.1 БАЛАНС
    txt(d, (S(180), S(580)), "БАЛАНС", load_font(S(18)), (165, 165, 175), anchor="lt")
    bal_str, f_bal = fit_text(d, f"{fmt_num(stats['coins'])} {COIN_UNIT}", S(196), S(30), S(18), bold=True)
    txt(d, (S(180), S(614)), bal_str, f_bal, (255, 255, 255), anchor="lt")

    # 4.2 СООБЩЕНИЯ
    txt(d, (S(532), S(580)), "СООБЩЕНИЯ", load_font(S(18)), (165, 165, 175), anchor="lt")
    msg_str, f_msg = fit_text(d, fmt_num(stats["messages"]), S(208), S(32), S(20), bold=True)
    txt(d, (S(532), S(614)), msg_str, f_msg, (255, 255, 255), anchor="lt")

    # 4.3 В ВОЙСЕ
    txt(d, (S(882), S(580)), "В ВОЙСЕ", load_font(S(18)), (165, 165, 175), anchor="lt")
    voice_str, f_voice = fit_text(d, format_hm(stats["total_seconds"]), S(230), S(30), S(18), bold=True)
    txt(d, (S(882), S(614)), voice_str, f_voice, (255, 255, 255), anchor="lt")
    if current_voice_session > 0:
        txt(d, (S(882), S(654)), f"сессия: {format_hm(current_voice_session)}",
            load_font(S(15)), (210, 75, 85), anchor="lt")

    # 4.4 ПАРТНЁР (/marry)
    txt(d, (S(1266), S(580)), "ПАРТНЁР", load_font(S(18)), (165, 165, 175), anchor="lt")
    if partner_name:
        if partner_avatar_bytes:
            pav_sz = S(42)
            pav = circle_avatar(partner_avatar_bytes, pav_sz)
            px, py = S(1266), S(610)
            img.paste(pav, (px, py), pav)
            d.ellipse((px, py, px + pav_sz, py + pav_sz), outline=(210, 48, 60), width=max(1, S(2)))
            p_text_x = S(1318)
            p_max_w = S(162)
        else:
            p_text_x = S(1266)
            p_max_w = S(214)
        p_clean, f_partner = fit_text(d, partner_name, p_max_w, S(24), S(16), bold=True)
        txt(d, (p_text_x, S(631)), p_clean, f_partner, (255, 255, 255), anchor="lm")
    else:
        txt(d, (S(1266), S(615)), "Нет пары", load_font(S(24), True), (185, 185, 195), anchor="lt")
        txt(d, (S(1266), S(649)), "/marry", load_font(S(16)), (140, 140, 150), anchor="lt")

    # 5. Панель предупреждений (y = 713..806)
    active_warns = min(MAX_WARNS, max(0, stats["active_warns"]))
    txt(d, (S(162), S(748)), "ПРЕДУПРЕЖДЕНИЯ", load_font(S(26), True), (255, 255, 255), anchor="lm")
    d.line((S(785), S(724), S(785), S(794)), fill=(85, 36, 40), width=max(1, S(1)))

    warn_col = (255, 255, 255) if active_warns == 0 else (235, 75, 85)
    txt(d, (S(812), S(738)), f"АКТИВНЫХ: {active_warns} / {MAX_WARNS}",
        load_font(S(23), True), warn_col, anchor="lm")
    txt(d, (S(812), S(769)), f"При {MAX_WARNS} активных предупреждениях — бан",
        load_font(S(17)), (155, 155, 165), anchor="lm")

    # Заливаем активные звёзды предупреждений справа (центры x = 1272, 1349, 1428; y = 748)
    for idx, star_x in enumerate((1272, 1349, 1428)):
        if idx < active_warns:
            _draw_filled_star(d, S(star_x), S(748), S(27), S(11.5),
                              fill=(210, 42, 58), outline=(255, 110, 120), width=max(1, S(2)))

    # 6. Нижний блок: ИСТОРИЯ ПРЕДУПРЕЖДЕНИЙ (y = 829..980)
    txt(d, (S(78), S(844)), "ИСТОРИЯ ПРЕДУПРЕЖДЕНИЙ", load_font(S(22), True), (255, 255, 255), anchor="lt")
    warnings_list = stats.get("warnings") or []
    if not warnings_list:
        txt(d, (S(772), S(924)), "История предупреждений пуста",
            load_font(S(22)), (145, 145, 155), anchor="mm")
    else:
        for i, (w_id, mod_id, reason, created_at, is_active) in enumerate(warnings_list[:2]):
            dt_str = datetime.fromtimestamp(created_at, tz=timezone.utc).strftime("%d.%m.%Y")
            mod_label = mod_names.get(mod_id) or f"ID {mod_id}"
            status_tag = " [активно]" if is_active else " [снято]"
            line = f"• #{w_id} · {dt_str} · {reason} — {mod_label}{status_tag}"
            line_clean, f_line = fit_text(d, line, S(1380), S(20), S(15), bold=False)
            color = (235, 185, 185) if is_active else (140, 140, 150)
            txt(d, (S(78), S(888 + i * 36)), line_clean, f_line, color, anchor="lt")

    buf = io.BytesIO()
    img.convert("RGB").save(buf, "PNG")
    buf.seek(0)
    return buf


def make_top_card(rows: list[dict], category: str = "balance", names: dict = None) -> io.BytesIO:
    """Рендерит картинку /top на top_background.png."""
    img, _ = get_bg(TOP_BG_PATH, 1967)
    s = 1.0
    names = names or {}

    def S(v):
        return int(round(v * s))

    rows = rows[:5]
    n = len(rows)
    pitch = TOP_PITCH if n <= 4 else TOP_PITCH_5
    first_center = TOP_CENTER_Y - (n - 1) * pitch / 2 + TOP_DY
    baselines = [first_center + 14 + i * pitch for i in range(n)]

    if n > 1:
        arr = np.array(img.convert("RGB"), dtype=np.float32)
        x_a, x_b = S(TOP_LINE_X[0] + TOP_DX), S(TOP_LINE_X[1] + TOP_DX)
        xs = np.arange(x_a, x_b)
        cx = (TOP_LINE_CENTER_X + TOP_DX) * s
        alpha_x = np.exp(-((xs - cx) / (420 * s)) ** 2)
        color = np.array(TOP_LINE_COLOR, dtype=np.float32)
        for i in range(n - 1):
            y = S(baselines[i] + pitch * 0.3)
            for dy, w in ((-1, 0.12), (0, 1.0), (1, 0.35)):
                yy = y + dy
                if 0 <= yy < arr.shape[0]:
                    a = (alpha_x * w)[:, None]
                    arr[yy, x_a:x_b] = arr[yy, x_a:x_b] * (1 - a) + color * a
        img = Image.fromarray(arr.clip(0, 255).astype(np.uint8)).convert("RGBA")

    d = ImageDraw.Draw(img)
    titles = {
        "balance": "ТОП ПО БАЛАНСУ",
        "messages": "ТОП ПО СООБЩЕНИЯМ",
        "voice": "ТОП ПО ГОЛОСОВОМУ ВРЕМЕНИ",
        "level": "ТОП ПО УРОВНЮ",
    }
    txt(d, (S(1725), S(268)), titles.get(category, "ТОП ПО БАЛАНСУ"),
        load_font(S(26), True), (225, 70, 75), anchor="rs")

    f_rank = load_font(S(38), True)
    f_name = load_font(S(36))
    f_sub = load_font(S(24))
    f_val = load_font(S(36), True)

    for i, (row, base) in enumerate(zip(rows, baselines), 1):
        y = S(base)
        uid = row["user_id"]
        display = names.get(uid) or f"ID {uid}"
        txt(d, (S(TOP_RANK_X + TOP_DX), y), f"{i}.", f_rank, TOP_RANK_COLOR, anchor="ls")
        clean_disp, f_n = fit_text(d, display, S(480), S(36), S(22), bold=False)
        txt(d, (S(TOP_NAME_X + TOP_DX), y), clean_disp, f_n, TOP_NAME_COLOR, anchor="ls")

        if category == "balance":
            val_text = f"{fmt_num(row['coins'])} {COIN_UNIT}"
            sub_text = f"{fmt_num(row['messages'])} сообщ. · {format_hm(row['total_seconds'])}"
        elif category == "messages":
            val_text = f"{fmt_num(row['messages'])} сообщ."
            sub_text = f"{fmt_num(row['coins'])} {COIN_UNIT} · {format_hm(row['total_seconds'])}"
        elif category == "voice":
            val_text = format_hm(row["total_seconds"])
            sub_text = f"{fmt_num(row['coins'])} {COIN_UNIT} · {fmt_num(row['messages'])} сообщ."
        else:
            val_text = f"Ур. {row['level']} ({fmt_num(row['xp'])} XP)"
            sub_text = f"{fmt_num(row['coins'])} {COIN_UNIT} · {fmt_num(row['messages'])} сообщ."

        txt(d, (S(TOP_SUB_RIGHT + TOP_DX), y), sub_text, f_sub, TOP_SUB_COLOR, anchor="rs")
        txt(d, (S(TOP_VAL_RIGHT + TOP_DX), y), val_text, f_val, TOP_VAL_COLOR, anchor="rs")

    out_h = int(img.height * TOP_OUT_W / img.width)
    img = img.convert("RGB").resize((TOP_OUT_W, out_h), Image.LANCZOS)
    buf = io.BytesIO()
    img.save(buf, "PNG")
    buf.seek(0)
    return buf


def make_card_image(card: dict) -> io.BytesIO:
    path = os.path.join(CARDS_DIR, card.get("image") or "")
    if card.get("image") and os.path.isfile(path):
        img = Image.open(path).convert("RGBA")
        img.thumbnail((800, 1100))
    else:
        W, H = 600, 840
        color = RARITY_COLORS.get(card["rarity"], (150, 155, 160))
        img = Image.new("RGBA", (W, H), (30, 20, 35, 255))
        d = ImageDraw.Draw(img)
        for y in range(H):
            t = y / H
            d.line((0, y, W, y), fill=(int(255 - 60 * t), int(170 - 60 * t), int(205 - 40 * t), 255))
        d.rounded_rectangle((8, 8, W - 8, H - 8), radius=40, outline=color, width=10)
        txt(d, (W // 2, 330), card["name"][:1].upper(), load_font(280, True), (255, 255, 255, 140), anchor="mm")
        txt(d, (W // 2, 60), card["rarity"].upper(), load_font(30, True), color, anchor="mm")
        d.rounded_rectangle((50, 600, W - 50, 790), radius=22, fill=(255, 205, 225), outline=(230, 190, 90), width=6)
        txt(d, (W // 2, 640), CARD_SERIES, load_font(26, True), (200, 80, 130), anchor="mm")
        txt(d, (W // 2, 700), card["name"][:16], load_font(60, True), (205, 70, 125), anchor="mm")
        txt(d, (W // 2, 760), CARD_SEASON, load_font(24, True), (200, 80, 130), anchor="mm")

    buf = io.BytesIO()
    img.save(buf, "PNG")
    buf.seek(0)
    return buf


# ---------- БЭКАП И СОХРАНЕНИЕ БАЗЫ ПРИ ПЕРЕЗАПУСКЕ ----------
def _db_score(path: str):
    """Оценка актуальности базы по (revision, суммарная активность). None, если файл битый."""
    try:
        conn = sqlite3.connect(path)
        tables = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'").fetchall()}
        if not tables:
            conn.close()
            return None

        rev = 0
        if "bot_meta" in tables:
            row = conn.execute("SELECT value FROM bot_meta WHERE key = 'revision'").fetchone()
            if row and row[0] and str(row[0]).isdigit():
                rev = int(row[0])

        score = 0
        if "voice_time" in tables:
            score += int(conn.execute("SELECT COALESCE(SUM(total_seconds), 0) FROM voice_time").fetchone()[0] or 0)
        if "wallet" in tables:
            score += int((conn.execute("SELECT COALESCE(SUM(coins), 0) FROM wallet").fetchone()[0] or 0) * 10)
        if "messages" in tables:
            score += int((conn.execute("SELECT COALESCE(SUM(count), 0) FROM messages").fetchone()[0] or 0) * 10)
        if "levels" in tables:
            score += int(conn.execute("SELECT COALESCE(SUM(xp + level * 1000), 0) FROM levels").fetchone()[0] or 0)
        if "cards" in tables:
            score += int((conn.execute("SELECT COALESCE(SUM(count), 0) FROM cards").fetchone()[0] or 0) * 100)
        if "marriages" in tables:
            score += int(conn.execute("SELECT COUNT(*) FROM marriages").fetchone()[0] or 0) * 100
        if "warnings" in tables:
            score += int(conn.execute("SELECT COUNT(*) FROM warnings").fetchone()[0] or 0) * 100

        conn.close()
        return (rev, score)
    except Exception:
        return None


def _snapshot_db(dst: str):
    """Потокобезопасная согласованная копия базы (сбрасывая WAL)."""
    with _db_lock:
        src = _connect()
        dest = sqlite3.connect(dst)
        try:
            src.execute("PRAGMA wal_checkpoint(TRUNCATE)")
            src.backup(dest)
        finally:
            dest.close()
            src.close()


def _checkpoint_db_sync():
    if not os.path.isfile(DB_PATH):
        return
    with _db_lock:
        conn = _connect()
        try:
            conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        finally:
            conn.close()


def _remove_quiet(*paths):
    for p in paths:
        try:
            os.remove(p)
        except OSError:
            pass


async def _resolve_backup_channel(bot_ref):
    global _active_backup_channel_id
    cid = _active_backup_channel_id or BACKUP_CHANNEL_ID
    if cid:
        ch = bot_ref.get_channel(cid)
        if ch is None:
            try:
                ch = await bot_ref.fetch_channel(cid)
            except Exception:
                ch = None
        if ch is not None:
            _active_backup_channel_id = ch.id
            return ch

    # Автопоиск существующего канала бэкапа (полезно при полном сбросе контейнера на Bothost)
    for guild in bot_ref.guilds:
        for ch in guild.text_channels:
            if (ch.topic and BACKUP_CHANNEL_MARKER in ch.topic) or ch.name == BACKUP_CHANNEL_NAME:
                _active_backup_channel_id = ch.id
                print(f"[БЭКАП] найден канал бэкапа #{ch.name} ({ch.id})", flush=True)
                return ch

    if AUTO_CREATE_BACKUP_CHANNEL and bot_ref.guilds:
        guild = bot_ref.guilds[0]
        overwrites = {
            guild.default_role: discord.PermissionOverwrite(read_messages=False),
            guild.me: discord.PermissionOverwrite(
                read_messages=True, send_messages=True, attach_files=True, read_message_history=True
            ),
        }
        try:
            ch = await guild.create_text_channel(
                BACKUP_CHANNEL_NAME,
                overwrites=overwrites,
                topic=f"{BACKUP_CHANNEL_MARKER} Автосохранение базы данных бота при перезагрузках",
                reason="Автосоздание скрытого канала для сохранения аккаунтов при перезапусках",
            )
            _active_backup_channel_id = ch.id
            print(f"[БЭКАП] создан скрытый канал #{ch.name} ({ch.id})", flush=True)
            return ch
        except (discord.Forbidden, discord.HTTPException) as e:
            print(f"[БЭКАП] не удалось автосоздать канал бэкапа (задайте BACKUP_CHANNEL_ID вручную): {e}", flush=True)

    return None


async def restore_db_from_discord(bot_ref):
    global _last_backup_hash
    ch = await _resolve_backup_channel(bot_ref)
    if not ch:
        print("[БЭКАП] канал бэкапа не найден, работаем с локальной базой", flush=True)
        return
    tmp = DB_PATH + ".restore"
    try:
        att = None
        async for msg in ch.history(limit=50):
            if msg.author.id != bot_ref.user.id:
                continue
            att = next((a for a in msg.attachments if a.filename == BACKUP_FILENAME), None)
            if att:
                break
        if not att:
            print("[БЭКАП] в канале пока нет сохранённых копий базы", flush=True)
            return

        data = await att.read()
        with open(tmp, "wb") as f:
            f.write(data)

        remote = _db_score(tmp)
        local = _db_score(DB_PATH) if os.path.isfile(DB_PATH) else None
        if remote is None:
            print("[БЭКАП] копия в канале повреждена, пропускаю", flush=True)
        elif local is None or remote > local:
            with _db_lock:
                _remove_quiet(DB_PATH + "-wal", DB_PATH + "-shm")
                os.replace(tmp, DB_PATH)
            if remote[0] > 0:
                _last_backup_hash = hashlib.md5(data).hexdigest()
            print(f"[БЭКАП] база восстановлена из Discord (было {local}, стало {remote})", flush=True)
        else:
            print(f"[БЭКАП] локальная база актуальна ({local}), восстановление не нужно", flush=True)
    except Exception as e:
        print(f"[БЭКАП] ошибка восстановления: {e!r}", flush=True)
    finally:
        _remove_quiet(tmp, tmp + "-wal", tmp + "-shm", tmp + "-journal")


async def backup_db_to_discord(bot_ref, force: bool = False) -> bool:
    global _last_backup_hash
    if not os.path.isfile(DB_PATH):
        return False
    ch = await _resolve_backup_channel(bot_ref)
    if not ch:
        return False

    tmp = DB_PATH + ".backup"
    try:
        await asyncio.to_thread(_snapshot_db, tmp)
        await asyncio.to_thread(save_local_json_snapshot)
        with open(tmp, "rb") as f:
            data = f.read()

        h = hashlib.md5(data).hexdigest()
        if not force and h == _last_backup_hash:
            return True

        score = _db_score(tmp)
        rev = score[0] if score else 0
        await ch.send(
            content=f"Бэкап базы · rev `{rev}` · {time.strftime('%d.%m.%Y %H:%M:%S')} UTC",
            file=discord.File(io.BytesIO(data), BACKUP_FILENAME),
        )
        _last_backup_hash = h

        old = []
        async for msg in ch.history(limit=50):
            if msg.author.id == bot_ref.user.id and msg.attachments:
                old.append(msg)
        for msg in old[BACKUP_KEEP:]:
            try:
                await msg.delete()
            except Exception:
                pass
        return True
    except Exception as e:
        print(f"[БЭКАП] ошибка бэкапа: {e!r}", flush=True)
        return False
    finally:
        _remove_quiet(tmp, tmp + "-wal", tmp + "-shm", tmp + "-journal")


def schedule_backup():
    """Планирует быстрый бэкап через BACKUP_DEBOUNCE_SECONDS без спама."""
    global _backup_debounce_task
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        return
    if _backup_debounce_task and not _backup_debounce_task.done():
        return

    async def _worker():
        await asyncio.sleep(BACKUP_DEBOUNCE_SECONDS)
        await backup_db_to_discord(bot, force=False)

    _backup_debounce_task = loop.create_task(_worker())


def flush_active_voice_sessions_sync():
    """Сбрасывает все незаписанные голосовые секунды в SQLite перед выключением или чтением."""
    now = time.time()
    credits = []
    for uid, last in list(voice_sessions.items()):
        sec = int(min(now - last, MAX_CREDIT))
        guild_id = None
        for g in bot.guilds:
            m = g.get_member(uid)
            if m and m.voice and m.voice.channel:
                guild_id = g.id
                break
        if sec > 0 and guild_id is not None:
            credits.append((uid, guild_id, sec))
            voice_sessions[uid] = now
    if credits:
        add_time_batch(credits)


# ---------- БОТ С ГРАЦИОЗНЫМ СОХРАНЕНИЕМ ПРИ ОСТАНОВКЕ ----------
class AbibasBot(commands.Bot):
    async def close(self):
        print("[ОСТАНОВКА] Сохраняю активные сессии и базу данных...", flush=True)
        try:
            await asyncio.to_thread(flush_active_voice_sessions_sync)
            await asyncio.to_thread(_checkpoint_db_sync)
            await asyncio.to_thread(save_local_json_snapshot)
            await backup_db_to_discord(self, force=True)
        except Exception as e:
            print(f"[ОСТАНОВКА] ошибка финального сохранения: {e!r}", flush=True)
        await super().close()


bot = AbibasBot(command_prefix=commands.when_mentioned, intents=intents)
synced = False
restored = False


@tasks.loop(seconds=BACKUP_LOOP_SECONDS)
async def backup_loop():
    await backup_db_to_discord(bot, force=False)


# ---------- УЧЁТ ГОЛОСА ----------
def excluded_channels(guild: discord.Guild) -> set:
    ids = set(AFK_CHANNEL_IDS)
    if AFK_CHANNEL_ID:
        ids.add(AFK_CHANNEL_ID)
    if guild.afk_channel:
        ids.add(guild.afk_channel.id)
    return ids


def afk_target(guild: discord.Guild):
    if AFK_CHANNEL_ID:
        ch = guild.get_channel(AFK_CHANNEL_ID)
        if isinstance(ch, discord.VoiceChannel):
            return ch
    return guild.afk_channel


def is_deaf(vs) -> bool:
    return bool(vs and (vs.self_deaf or vs.deaf))


def is_muted(vs) -> bool:
    return bool(vs and (vs.self_mute or vs.mute or vs.self_deaf or vs.deaf))


def pending_seconds(user_id: int, now: float = None) -> int:
    last = voice_sessions.get(user_id)
    if last is None:
        return 0
    return int(min((now or time.time()) - last, MAX_CREDIT))


@tasks.loop(seconds=TICK_SECONDS)
async def voice_tick():
    now = time.time()
    credits = []
    to_move = []
    active = set()

    for guild in bot.guilds:
        skip = excluded_channels(guild)
        for vc in guild.voice_channels:
            if vc.id in skip:
                continue
            humans = [m for m in vc.members if not m.bot and m.voice]
            for m in humans:
                vs = m.voice

                if not is_muted(vs) or vs.self_stream or vs.self_video:
                    last_active[m.id] = now
                elif now - last_active.setdefault(m.id, now) >= AFK_TIMEOUT:
                    to_move.append(m)
                    continue

                if is_deaf(vs):
                    continue
                has_company = any(o.id != m.id and not is_deaf(o.voice) for o in humans)
                if not has_company:
                    continue

                active.add(m.id)
                last = voice_sessions.get(m.id)
                if last is None:
                    voice_sessions[m.id] = now
                    session_start[m.id] = now
                else:
                    sec = int(min(now - last, MAX_CREDIT))
                    if sec > 0:
                        credits.append((m.id, guild.id, sec))
                        voice_sessions[m.id] = now

    for uid in [u for u in voice_sessions if u not in active]:
        voice_sessions.pop(uid, None)
        session_start.pop(uid, None)

    if credits:
        await asyncio.to_thread(add_time_batch, credits)

    for m in to_move:
        target = afk_target(m.guild)
        if not target:
            continue
        try:
            await m.move_to(target, reason=f"Неактивность в голосовом канале {AFK_TIMEOUT // 60} мин")
            last_active[m.id] = now
            voice_sessions.pop(m.id, None)
            session_start.pop(m.id, None)
            print(f"[AFK] {m.display_name} перемещён в {target.name}")
        except (discord.Forbidden, discord.HTTPException) as e:
            print(f"[AFK] не удалось переместить {m.display_name}: {e}")


@voice_tick.before_loop
async def _before_tick():
    await bot.wait_until_ready()


@backup_loop.before_loop
async def _before_backup():
    await bot.wait_until_ready()


@bot.event
async def on_ready():
    global synced, restored
    if not restored:
        restore_from_json_if_needed()
        await restore_db_from_discord(bot)
        restored = True
    init_db()
    os.makedirs(CARDS_DIR, exist_ok=True)

    if not voice_tick.is_running():
        voice_tick.start()

    if not backup_loop.is_running():
        backup_loop.start()

    if not synced:
        for guild in bot.guilds:
            bot.tree.copy_global_to(guild=guild)
            await bot.tree.sync(guild=guild)
        synced = True

    print(f"Бот {bot.user} запущен. Профили, войс, сообщения и автосохранение активны.", flush=True)


@bot.event
async def on_guild_join(guild: discord.Guild):
    bot.tree.copy_global_to(guild=guild)
    await bot.tree.sync(guild=guild)


@bot.event
async def on_voice_state_update(member, before, after):
    if member.bot:
        return

    now = time.time()
    last_active[member.id] = now

    if before.channel != after.channel:
        last = voice_sessions.pop(member.id, None)
        session_start.pop(member.id, None)
        if last and before.channel:
            sec = int(min(now - last, MAX_CREDIT))
            if sec > 0:
                await asyncio.to_thread(add_time_batch, [(member.id, before.channel.guild.id, sec)])
                schedule_backup()


@bot.listen("on_message")
async def _activity_from_messages(message: discord.Message):
    if message.author.bot or not message.guild:
        return
    now = time.time()
    last_active[message.author.id] = now
    _, coins_gain = await asyncio.to_thread(record_message, message.author.id, message.guild.id, now)
    if coins_gain > 0:
        schedule_backup()


@bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    print(f"[ОШИБКА КОМАНДЫ] {error!r}", flush=True)
    msg = "Команда доступна только на сервере." if isinstance(error, app_commands.NoPrivateMessage) else "Произошла ошибка при выполнении команды."
    try:
        if interaction.response.is_done():
            await interaction.followup.send(msg, ephemeral=True)
        else:
            await interaction.response.send_message(msg, ephemeral=True)
    except Exception:
        pass


# ---------- КОМАНДЫ: ПРОФИЛЬ И ТОП ----------
@bot.tree.command(name="profile", description="Показать карточку профиля участника")
@app_commands.guild_only()
@app_commands.describe(member="Участник (по умолчанию вы)")
async def profile_cmd(interaction: discord.Interaction, member: discord.Member = None):
    await interaction.response.defer()
    member = member or interaction.user
    last_active[interaction.user.id] = time.time()

    # Сбросим накопленные секунды пользователя перед отрисовкой, чтобы баланс/XP были точными
    now = time.time()
    sec = pending_seconds(member.id, now)
    if sec > 0:
        await asyncio.to_thread(add_time_batch, [(member.id, interaction.guild.id, sec)])
        voice_sessions[member.id] = now

    stats = await asyncio.to_thread(get_profile_data, member.id, interaction.guild.id)
    current = int(now - session_start[member.id]) if member.id in session_start else 0

    avatar_bytes = await member.display_avatar.replace(size=256, format="png").read()

    partner_name = None
    partner_avatar_bytes = None
    if stats["partner_id"]:
        p_member = interaction.guild.get_member(stats["partner_id"])
        if p_member is None:
            try:
                p_member = await bot.fetch_user(stats["partner_id"])
            except Exception:
                p_member = None
        if p_member:
            partner_name = p_member.display_name
            try:
                partner_avatar_bytes = await p_member.display_avatar.replace(size=128, format="png").read()
            except Exception:
                partner_avatar_bytes = None
        else:
            partner_name = f"ID {stats['partner_id']}"

    mod_names = {}
    for _, mod_id, _, _, _ in stats["warnings"]:
        if mod_id not in mod_names:
            mm = interaction.guild.get_member(mod_id)
            if mm:
                mod_names[mod_id] = mm.display_name
            else:
                try:
                    u = await bot.fetch_user(mod_id)
                    mod_names[mod_id] = u.display_name
                except Exception:
                    mod_names[mod_id] = f"ID {mod_id}"

    buf = await asyncio.to_thread(
        make_profile_card,
        member.display_name,
        member.id,
        avatar_bytes,
        stats,
        current,
        partner_name,
        partner_avatar_bytes,
        mod_names,
    )
    await interaction.followup.send(file=discord.File(buf, "profile.png"))


@bot.tree.command(name="top", description="Топ участников (по умолчанию по балансу)")
@app_commands.guild_only()
@app_commands.describe(
    category="По какому показателю сортировать",
    limit="Сколько мест показать (1-5)",
)
@app_commands.choices(category=[
    app_commands.Choice(name="Баланс", value="balance"),
    app_commands.Choice(name="Сообщения", value="messages"),
    app_commands.Choice(name="Время в войсе", value="voice"),
    app_commands.Choice(name="Уровень", value="level"),
])
async def top_cmd(
    interaction: discord.Interaction,
    category: str = "balance",
    limit: app_commands.Range[int, 1, 5] = 5,
):
    await interaction.response.defer()
    last_active[interaction.user.id] = time.time()

    await asyncio.to_thread(flush_active_voice_sessions_sync)
    rows = await asyncio.to_thread(get_top_users, interaction.guild.id)
    if not rows:
        await interaction.followup.send("Пока нет данных.")
        return

    if category == "balance":
        rows.sort(key=lambda r: (r["coins"], r["messages"], r["total_seconds"]), reverse=True)
    elif category == "messages":
        rows.sort(key=lambda r: (r["messages"], r["coins"], r["total_seconds"]), reverse=True)
    elif category == "voice":
        rows.sort(key=lambda r: (r["total_seconds"], r["coins"], r["messages"]), reverse=True)
    else:
        rows.sort(key=lambda r: (r["level"], r["xp"], r["coins"]), reverse=True)

    top_rows = rows[:limit]
    names = {}
    for r in top_rows:
        uid = r["user_id"]
        m = interaction.guild.get_member(uid)
        if m:
            names[uid] = m.display_name
        else:
            try:
                u = await bot.fetch_user(uid)
                names[uid] = u.display_name
            except Exception:
                names[uid] = f"ID {uid}"

    buf = await asyncio.to_thread(make_top_card, top_rows, category, names)
    await interaction.followup.send(file=discord.File(buf, "top.png"))


# ---------- КОМАНДЫ: ПАРЫ (/marry, /divorce) ----------
class MarryProposalView(discord.ui.View):
    def __init__(self, guild_id: int, proposer: discord.Member, target: discord.Member):
        super().__init__(timeout=120)
        self.guild_id = guild_id
        self.proposer = proposer
        self.target = target
        self.done = False
        self.message = None

    async def on_timeout(self):
        if self.done:
            return
        self.done = True
        for child in self.children:
            child.disabled = True
        if self.message:
            try:
                await self.message.edit(view=self)
            except Exception:
                pass

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.target.id:
            await interaction.response.send_message(
                f"Ответить на предложение может только {self.target.mention}.",
                ephemeral=True,
            )
            return False
        return True

    @discord.ui.button(label="💍 Принять", style=discord.ButtonStyle.success)
    async def accept(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.done:
            return
        self.done = True
        for child in self.children:
            child.disabled = True

        ok, reason = await asyncio.to_thread(
            create_marriage, self.guild_id, self.proposer.id, self.target.id
        )
        if not ok:
            msg = (
                f"{self.proposer.mention} уже состоит в паре."
                if reason == "first_married"
                else f"{self.target.mention} уже состоит в паре."
            )
            embed = discord.Embed(title="💔 Не удалось создать пару", description=msg, color=discord.Color.red())
            await interaction.response.edit_message(embed=embed, view=self)
            return

        embed = discord.Embed(
            title="💖 Новая пара!",
            description=f"{self.proposer.mention} и {self.target.mention} теперь пара!\nОтображается в блоке партнёра в `/profile`.",
            color=discord.Color.red(),
        )
        await interaction.response.edit_message(embed=embed, view=self)
        schedule_backup()

    @discord.ui.button(label="❌ Отклонить", style=discord.ButtonStyle.danger)
    async def decline(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.done:
            return
        self.done = True
        for child in self.children:
            child.disabled = True
        embed = discord.Embed(
            title="💔 Предложение отклонено",
            description=f"{self.target.mention} отклонил(а) предложение от {self.proposer.mention}.",
            color=discord.Color.dark_gray(),
        )
        await interaction.response.edit_message(embed=embed, view=self)


class DivorceConfirmView(discord.ui.View):
    def __init__(self, guild_id: int, user: discord.Member, partner_id: int):
        super().__init__(timeout=60)
        self.guild_id = guild_id
        self.user = user
        self.partner_id = partner_id
        self.done = False

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user.id:
            await interaction.response.send_message("Подтвердить может только автор команды.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="💔 Расторгнуть пару", style=discord.ButtonStyle.danger)
    async def confirm(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.done:
            return
        self.done = True
        for child in self.children:
            child.disabled = True
        pid = await asyncio.to_thread(delete_marriage, self.guild_id, self.user.id)
        if pid is None:
            await interaction.response.edit_message(content="Вы уже не состоите в паре.", embed=None, view=self)
            return
        embed = discord.Embed(
            title="💔 Пара распущена",
            description=f"{self.user.mention} и <@{pid}> больше не в паре.",
            color=discord.Color.dark_red(),
        )
        await interaction.response.edit_message(embed=embed, view=self)
        schedule_backup()

    @discord.ui.button(label="Отмена", style=discord.ButtonStyle.secondary)
    async def cancel(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.done:
            return
        self.done = True
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(content="Отменено.", embed=None, view=self)


@bot.tree.command(name="marry", description="Предложить участнику стать парой (отображается в /profile)")
@app_commands.guild_only()
@app_commands.describe(member="Кому сделать предложение")
async def marry_cmd(interaction: discord.Interaction, member: discord.Member):
    last_active[interaction.user.id] = time.time()
    if member.bot:
        await interaction.response.send_message("Нельзя создать пару с ботом.", ephemeral=True)
        return
    if member.id == interaction.user.id:
        await interaction.response.send_message("Нельзя создать пару с самим собой.", ephemeral=True)
        return

    p1 = await asyncio.to_thread(get_partner, interaction.guild.id, interaction.user.id)
    if p1:
        await interaction.response.send_message(
            f"Вы уже в паре с <@{p1[0]}>. Сначала используйте `/divorce`.", ephemeral=True
        )
        return
    p2 = await asyncio.to_thread(get_partner, interaction.guild.id, member.id)
    if p2:
        await interaction.response.send_message(
            f"{member.display_name} уже состоит в паре с <@{p2[0]}>.", ephemeral=True
        )
        return

    embed = discord.Embed(
        title="💍 Предложение пары",
        description=f"{interaction.user.mention} предлагает {member.mention} стать парой!\nНажмите кнопку ниже, чтобы ответить.",
        color=discord.Color.red(),
    )
    view = MarryProposalView(interaction.guild.id, interaction.user, member)
    await interaction.response.send_message(content=member.mention, embed=embed, view=view)
    view.message = await interaction.original_response()


@bot.tree.command(name="divorce", description="Расторгнуть текущую пару")
@app_commands.guild_only()
async def divorce_cmd(interaction: discord.Interaction):
    last_active[interaction.user.id] = time.time()
    partner = await asyncio.to_thread(get_partner, interaction.guild.id, interaction.user.id)
    if not partner:
        await interaction.response.send_message("Вы сейчас не состоите в паре.", ephemeral=True)
        return
    embed = discord.Embed(
        title="💔 Расторжение пары",
        description=f"Вы уверены, что хотите расторгнуть пару с <@{partner[0]}>?",
        color=discord.Color.orange(),
    )
    view = DivorceConfirmView(interaction.guild.id, interaction.user, partner[0])
    await interaction.response.send_message(embed=embed, view=view, ephemeral=True)


# ---------- КОМАНДЫ: МОНЕТЫ И КАРТОЧКИ ----------
@bot.tree.command(name="balance", description="Показать баланс, сообщения, войс и карточки")
@app_commands.guild_only()
@app_commands.describe(member="Участник (по умолчанию вы)")
async def balance(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    last_active[interaction.user.id] = time.time()

    now = time.time()
    sec = pending_seconds(member.id, now)
    if sec > 0:
        await asyncio.to_thread(add_time_batch, [(member.id, interaction.guild.id, sec)])
        voice_sessions[member.id] = now

    stats = await asyncio.to_thread(get_profile_data, member.id, interaction.guild.id)
    partner_txt = f"<@{stats['partner_id']}>" if stats["partner_id"] else "Нет пары"

    embed = discord.Embed(title="💰 Баланс и статистика", description=member.mention, color=discord.Color.gold())
    embed.add_field(name="Монеты", value=f"{fmt_num(stats['coins'])} {COIN_UNIT}", inline=True)
    embed.add_field(name="Сообщения", value=fmt_num(stats["messages"]), inline=True)
    embed.add_field(name="В войсе", value=format_hm(stats["total_seconds"]), inline=True)
    embed.add_field(name="Уровень", value=f"{stats['level']} ({stats['xp']}/{stats['xp_need']} XP)", inline=True)
    embed.add_field(name="Карточек", value=str(stats["cards_count"]), inline=True)
    embed.add_field(name="Партнёр", value=partner_txt, inline=True)
    embed.set_footer(
        text=f"Войс: {VOICE_COINS_MIN}-{VOICE_COINS_MAX} монет / 5 мин · Сообщения: {MSG_COINS_MIN}-{MSG_COINS_MAX} монет (КД {MSG_REWARD_COOLDOWN}с)"
    )
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="shop", description="Цена карточки и шансы выпадения")
@app_commands.guild_only()
async def shop(interaction: discord.Interaction):
    last_active[interaction.user.id] = time.time()
    coins = int(await asyncio.to_thread(get_coins, interaction.user.id, interaction.guild.id))
    lines = [f"**{c['name']}** — {c['rarity']}, шанс {card_chance(c):.1f}%"
             for c in sorted(CARDS, key=lambda x: x["weight"], reverse=True)]

    embed = discord.Embed(title="🃏 Магазин карточек", color=discord.Color.pink())
    embed.add_field(name="Цена", value=f"{CARD_PRICE} монет за одну карточку", inline=False)
    embed.add_field(name="Ваш баланс", value=f"{fmt_num(coins)} монет", inline=False)
    embed.add_field(name="Шансы", value="\n".join(lines), inline=False)
    embed.set_footer(text="Открыть карточку: /opencard")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="opencard", description="Купить случайную карточку игрока")
@app_commands.guild_only()
async def opencard(interaction: discord.Interaction):
    await interaction.response.defer()
    user_id, guild_id = interaction.user.id, interaction.guild.id
    last_active[user_id] = time.time()

    sec = pending_seconds(user_id)
    if sec > 0:
        await asyncio.to_thread(add_time_batch, [(user_id, guild_id, sec)])
        voice_sessions[user_id] = time.time()

    card = roll_card()
    ok = await asyncio.to_thread(buy_card, user_id, guild_id, card["id"], CARD_PRICE)
    if not ok:
        have = int(await asyncio.to_thread(get_coins, user_id, guild_id))
        await interaction.followup.send(
            f"Не хватает монет: нужно **{CARD_PRICE}**, у вас **{fmt_num(have)}**. "
            f"Общайтесь в чатах или сидите в войсе (не в одиночку), чтобы заработать больше.")
        return

    buf = await asyncio.to_thread(make_card_image, card)
    left = int(await asyncio.to_thread(get_coins, user_id, guild_id))
    owned = (await asyncio.to_thread(get_inventory, user_id, guild_id)).get(card["id"], 1)
    dup = " (дубликат)" if owned > 1 else " (новая!)"
    await interaction.followup.send(
        content=(f"{interaction.user.mention} открыл карточку: **{card['name']}** — "
                 f"{card['rarity']}{dup}\nШанс выпадения: {card_chance(card):.1f}% · "
                 f"Осталось монет: {fmt_num(left)}"),
        file=discord.File(buf, "card.png"))
    schedule_backup()


@bot.tree.command(name="collection", description="Показать коллекцию карточек")
@app_commands.guild_only()
@app_commands.describe(member="Участник (по умолчанию вы)")
async def collection(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    inv = await asyncio.to_thread(get_inventory, member.id, interaction.guild.id)

    if not inv:
        await interaction.response.send_message(f"У {member.display_name} пока нет карточек.")
        return

    lines = [f"**{c['name']}** — {c['rarity']} ×{inv[c['id']]}" for c in CARDS if c["id"] in inv]
    embed = discord.Embed(title="🗂️ Коллекция", description=member.mention + "\n\n" + "\n".join(lines),
                          color=discord.Color.pink())
    embed.set_footer(text=f"Собрано {len(lines)} из {len(CARDS)}")
    await interaction.response.send_message(embed=embed)


async def card_autocomplete(interaction: discord.Interaction, current: str):
    return [app_commands.Choice(name=c["name"], value=c["id"])
            for c in CARDS if current.lower() in c["name"].lower()][:25]


@bot.tree.command(name="showcard", description="Показать свою карточку")
@app_commands.guild_only()
@app_commands.describe(card="Какую карточку показать")
@app_commands.autocomplete(card=card_autocomplete)
async def showcard(interaction: discord.Interaction, card: str):
    data = CARDS_BY_ID.get(card)
    if not data:
        await interaction.response.send_message("Такой карточки нет.", ephemeral=True)
        return
    inv = await asyncio.to_thread(get_inventory, interaction.user.id, interaction.guild.id)
    if inv.get(card, 0) <= 0:
        await interaction.response.send_message("У вас нет этой карточки.", ephemeral=True)
        return

    await interaction.response.defer()
    buf = await asyncio.to_thread(make_card_image, data)
    await interaction.followup.send(
        content=f"{interaction.user.mention}: **{data['name']}** — {data['rarity']}",
        file=discord.File(buf, "card.png"))


# ---------- КОМАНДЫ: ПРЕДУПРЕЖДЕНИЯ ----------
@bot.tree.command(name="warns", description="Посмотреть предупреждения участника")
@app_commands.guild_only()
@app_commands.describe(member="Участник (по умолчанию вы)")
async def warns_cmd(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    active_cnt, rows = await asyncio.to_thread(get_warnings, interaction.guild.id, member.id, 10)
    if not rows:
        await interaction.response.send_message(f"У {member.mention} история предупреждений пуста (0/{MAX_WARNS}).")
        return

    lines = []
    for wid, mod_id, reason, created_at, active in rows:
        dt = datetime.fromtimestamp(created_at, tz=timezone.utc).strftime("%d.%m.%Y %H:%M")
        mark = "🔴 Активно" if active else "⚪ Снято"
        lines.append(f"**#{wid}** · {mark} · `{dt}`\nПричина: {reason} (модератор: <@{mod_id}>)")

    embed = discord.Embed(
        title=f"⚠️ Предупреждения ({active_cnt} / {MAX_WARNS})",
        description=f"{member.mention}\n\n" + "\n\n".join(lines),
        color=discord.Color.red() if active_cnt > 0 else discord.Color.dark_gray(),
    )
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="warn", description="Выдать предупреждение участнику (модераторы/админы)")
@app_commands.guild_only()
@app_commands.describe(member="Кому выдать", reason="Причина предупреждения")
@app_commands.default_permissions(moderate_members=True)
async def warn_cmd(interaction: discord.Interaction, member: discord.Member, reason: str = "Нарушение правил"):
    if not (interaction.user.guild_permissions.administrator or interaction.user.guild_permissions.moderate_members):
        await interaction.response.send_message("Недостаточно прав.", ephemeral=True)
        return
    if member.bot:
        await interaction.response.send_message("Нельзя выдать предупреждение боту.", ephemeral=True)
        return

    wid, active_cnt = await asyncio.to_thread(add_warning, interaction.guild.id, member.id, interaction.user.id, reason)
    extra = ""
    if active_cnt >= MAX_WARNS and AUTO_BAN_ON_MAX_WARNS:
        try:
            await member.ban(reason=f"Достигнуто {MAX_WARNS}/{MAX_WARNS} активных предупреждений. Последнее: {reason}")
            extra = f"\n🔨 Участник забанен автоматически ({active_cnt}/{MAX_WARNS})."
        except (discord.Forbidden, discord.HTTPException):
            extra = f"\n⚠️ Достигнут лимит {MAX_WARNS}/{MAX_WARNS}, но у бота нет прав для бана."

    await interaction.response.send_message(
        f"⚠️ {member.mention} получил(а) предупреждение **#{wid}** (`{active_cnt}/{MAX_WARNS}`)\n"
        f"Причина: **{reason}**{extra}"
    )
    schedule_backup()


@bot.tree.command(name="unwarn", description="Снять активное предупреждение (модераторы/админы)")
@app_commands.guild_only()
@app_commands.describe(member="У кого снять", warn_id="ID предупреждения (если не указать — последнее)")
@app_commands.default_permissions(moderate_members=True)
async def unwarn_cmd(interaction: discord.Interaction, member: discord.Member, warn_id: int = None):
    if not (interaction.user.guild_permissions.administrator or interaction.user.guild_permissions.moderate_members):
        await interaction.response.send_message("Недостаточно прав.", ephemeral=True)
        return
    ok, active_cnt = await asyncio.to_thread(remove_warning, interaction.guild.id, member.id, interaction.user.id, warn_id)
    if not ok:
        await interaction.response.send_message("Подходящего активного предупреждения не найдено.", ephemeral=True)
        return
    await interaction.response.send_message(
        f"✅ С {member.mention} снято предупреждение. Активных сейчас: **{active_cnt}/{MAX_WARNS}**."
    )
    schedule_backup()


@bot.tree.command(name="clearwarns", description="Снять все активные предупреждения участника (только админы)")
@app_commands.guild_only()
@app_commands.describe(member="У кого снять")
@app_commands.default_permissions(administrator=True)
async def clearwarns_cmd(interaction: discord.Interaction, member: discord.Member):
    if not interaction.user.guild_permissions.administrator:
        await interaction.response.send_message("Только для администраторов.", ephemeral=True)
        return
    cnt = await asyncio.to_thread(clear_warnings, interaction.guild.id, member.id, interaction.user.id)
    await interaction.response.send_message(f"✅ У {member.mention} снято активных предупреждений: **{cnt}**.")
    if cnt:
        schedule_backup()


# ---------- АДМИН-КОМАНДЫ И БЭКАП ----------
@bot.tree.command(name="addcoins", description="Выдать или списать монеты участнику (только админы)")
@app_commands.guild_only()
@app_commands.describe(member="Кому выдать", amount="Сколько монет (можно отрицательное)")
@app_commands.default_permissions(administrator=True)
async def addcoins(interaction: discord.Interaction, member: discord.Member, amount: int):
    if not interaction.user.guild_permissions.administrator:
        await interaction.response.send_message("Только для администраторов.", ephemeral=True)
        return
    await asyncio.to_thread(give_coins, member.id, interaction.guild.id, amount)
    new_bal = int(await asyncio.to_thread(get_coins, member.id, interaction.guild.id))
    await interaction.response.send_message(
        f"{member.mention}: {amount:+d} монет. Баланс: {fmt_num(new_bal)}"
    )
    await backup_db_to_discord(bot, force=True)


@bot.tree.command(name="setvoice", description="Задать время в войсе участнику (только админы)")
@app_commands.guild_only()
@app_commands.describe(member="Кому", hours="Часы", minutes="Минуты",
                       coins="Монеты (если не указать, баланс не меняется)")
@app_commands.default_permissions(administrator=True)
async def setvoice(interaction: discord.Interaction, member: discord.Member,
                   hours: int, minutes: int = 0, coins: int = None):
    if not interaction.user.guild_permissions.administrator:
        await interaction.response.send_message("Только для администраторов.", ephemeral=True)
        return
    seconds = max(0, hours * 3600 + minutes * 60)
    await asyncio.to_thread(set_time, member.id, interaction.guild.id, seconds, coins)
    if member.id in voice_sessions:
        voice_sessions[member.id] = time.time()
    await interaction.response.send_message(
        f"{member.mention}: время задано {hours} ч {minutes} мин."
        + (f" Монеты: {fmt_num(coins)}." if coins is not None else "")
    )
    await backup_db_to_discord(bot, force=True)


@bot.tree.command(name="setmessages", description="Задать количество сообщений (и опционально XP) участнику (только админы)")
@app_commands.guild_only()
@app_commands.describe(member="Кому", count="Количество сообщений", xp="Общий XP (опционально)")
@app_commands.default_permissions(administrator=True)
async def setmessages(interaction: discord.Interaction, member: discord.Member, count: int, xp: int = None):
    if not interaction.user.guild_permissions.administrator:
        await interaction.response.send_message("Только для администраторов.", ephemeral=True)
        return
    await asyncio.to_thread(set_messages, member.id, interaction.guild.id, max(0, count), xp)
    await interaction.response.send_message(
        f"{member.mention}: сообщений задано **{fmt_num(max(0, count))}**."
        + (f" XP пересчитан из **{fmt_num(max(0, xp))}**." if xp is not None else "")
    )
    await backup_db_to_discord(bot, force=True)


@bot.tree.command(name="backup", description="Сделать бэкап базы прямо сейчас (только админы)")
@app_commands.guild_only()
@app_commands.default_permissions(administrator=True)
async def backup_cmd(interaction: discord.Interaction):
    if not interaction.user.guild_permissions.administrator:
        await interaction.response.send_message("Только для администраторов.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    await asyncio.to_thread(flush_active_voice_sessions_sync)
    ok = await backup_db_to_discord(bot, force=True)
    ch = await _resolve_backup_channel(bot)
    where = f" в <#{ch.id}>" if ch else ""
    await interaction.followup.send(
        f"Бэкап сохранён{where}." if ok else "Не получилось. Проверь права бота в канале бэкапа и логи.",
        ephemeral=True,
    )


@bot.tree.command(name="setbackupchannel", description="Привязать канал для автосохранения базы (только админы)")
@app_commands.guild_only()
@app_commands.describe(channel="Текстовый канал (по умолчанию текущий)")
@app_commands.default_permissions(administrator=True)
async def setbackupchannel_cmd(interaction: discord.Interaction, channel: discord.TextChannel = None):
    global _active_backup_channel_id
    if not interaction.user.guild_permissions.administrator:
        await interaction.response.send_message("Только для администраторов.", ephemeral=True)
        return
    target = channel or interaction.channel
    if not isinstance(target, discord.TextChannel):
        await interaction.response.send_message("Нужен текстовый канал.", ephemeral=True)
        return
    _active_backup_channel_id = target.id
    try:
        topic = target.topic or ""
        if BACKUP_CHANNEL_MARKER not in topic:
            await target.edit(topic=(f"{BACKUP_CHANNEL_MARKER} {topic}").strip()[:1024])
    except (discord.Forbidden, discord.HTTPException):
        pass
    await interaction.response.defer(ephemeral=True)
    ok = await backup_db_to_discord(bot, force=True)
    await interaction.followup.send(
        f"Канал <#{target.id}> привязан для автобэкапа. Тестовый бэкап: {'успешно' if ok else 'ошибка прав'}.",
        ephemeral=True,
    )


# ---------- ЗАПУСК ----------
if __name__ == "__main__":
    bot.run(TOKEN)
