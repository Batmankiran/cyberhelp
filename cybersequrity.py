#!/usr/bin/env python3
"""
CyberSentinel - Firewall + Password Manager (SQLite DB) + User Login/Signup
Save as cybersentinel.py and run with: python3 cybersentinel.py

This version stores password entries in a normal SQLite database at ./users/users.db.
Sensitive fields (password, notes) are encrypted per-user with AES-GCM; list/search fields
(name, entry_username) are stored plaintext for convenience.
"""
import os
import sys
import shutil
import platform
import subprocess
import threading
import time
import shlex
import json
import base64
import getpass
import secrets
import textwrap
import string
import hmac
import hashlib
import sqlite3
from collections import defaultdict, deque, Counter
from typing import Tuple
from datetime import datetime, UTC, timezone
#from phishing_detector import PhishingDetector
import re
import socket
import requests
import tldextract
import idna
import validators
from urllib.parse import urlparse

# ---------- CLI styling helpers (colors + emojis) ----------
# ANSI colors — safe for most modern terminals (Linux Mint, macOS, Windows WSL)
CSI = "\033["
RESET = CSI + "0m"

BOLD = CSI + "1m"
DIM = CSI + "2m"
ITALIC = CSI + "3m"
UNDER = CSI + "4m"

FG_RED = CSI + "31m"
FG_GREEN = CSI + "32m"
FG_YELLOW = CSI + "33m"
FG_BLUE = CSI + "34m"
FG_MAGENTA = CSI + "35m"
FG_CYAN = CSI + "36m"
FG_WHITE = CSI + "97m"
BG_RED = CSI + "41m"
BG_GREEN = CSI + "42m"
BG_BLUE = CSI + "44m"

# Emojis / icons (fall back to ascii if terminal doesn't support emoji)
EMOJI_CHECK = "✅"
EMOJI_WARN = "⚠️"
EMOJI_FIRE = "🔥"
EMOJI_LOCK = "🔒"
EMOJI_SHIELD = "🛡️"
EMOJI_MAG = "🔎"
EMOJI_DB = "🗄️"
EMOJI_STAR = "⭐"
EMOJI_BACK = "↩️"

# Helper prints
def styled_header(title: str):
    """Large header with colors and emoji."""
    clear_screen()
    print(FG_CYAN + BOLD + f"{EMOJI_SHIELD}  {title}  {EMOJI_SHIELD}" + RESET)
    print(FG_BLUE + ("─" * max(40, len(title) + 10)) + RESET)

def styled_section(title: str, emoji: str = EMOJI_MAG):
    print()
    print(FG_MAGENTA + BOLD + f"{emoji}  {title}" + RESET)
    print(FG_MAGENTA + ("─" * max(20, len(title) + 4)) + RESET)

def color_line(key: str, value: str, key_color=FG_YELLOW, value_color=FG_WHITE):
    print(f"{key_color}{key}:{RESET} {value_color}{value}{RESET}")

def verdict_banner(verdict: str):
    """Return colored verdict string for inline display."""
    if verdict == "Malicious":
        return FG_RED + BOLD + EMOJI_FIRE + " MALICIOUS " + RESET
    if verdict == "Suspicious":
        return FG_YELLOW + BOLD + EMOJI_WARN + " SUSPICIOUS " + RESET
    return FG_GREEN + BOLD + EMOJI_CHECK + " LIKELY SAFE " + RESET


# cryptography
try:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    CRYPTO_AVAILABLE = True
except Exception:
    CRYPTO_AVAILABLE = False

# Optional scapy imports (AsyncSniffer preferred)
try:
    from scapy.all import AsyncSniffer, IP, TCP, UDP
    SCAPY_ASYNC = True
except Exception:
    SCAPY_ASYNC = False

# ---------- App paths ----------
APP_DIR = os.path.abspath(os.path.dirname(__file__))
USERS_DIR = os.path.join(APP_DIR, "users")
os.makedirs(USERS_DIR, exist_ok=True)
USERS_DB = os.path.join(USERS_DIR, "users.db")

# Set db file permissions when created (best-effort)
def _ensure_db_permissions(path):
    try:
        os.chmod(path, 0o600)
    except Exception:
        pass

# ---------- Utilities ----------
def require_root():
    """
    Cross-platform admin privilege check.
    - Linux/macOS: checks os.geteuid() == 0
    - Windows: checks if running with Administrator rights
    """
    import os
    import ctypes
    import platform

    system = platform.system().lower()

    # Windows check
    if system.startswith("windows"):
        try:
            is_admin = ctypes.windll.shell32.IsUserAnAdmin() != 0
        except Exception:
            # Fallback: assume not admin
            return False

        if not is_admin:
            print(FG_RED + "❌ Administrator privileges required!" + RESET)
            print(FG_YELLOW + "Run PowerShell *as Administrator* to use firewall features." + RESET)
            return False
        return True

    # Linux / macOS check
    if hasattr(os, "geteuid"):
        if os.geteuid() != 0:
            print(FG_RED + "❌ Root privileges required!" + RESET)
            print(FG_YELLOW + "Run using: sudo python3 cybersentinel.py" + RESET)
            return False
        return True

    # Unknown OS fallback
    return True


def run_cmd(cmd, timeout: int = 10) -> Tuple[int, str]:
    if isinstance(cmd, str):
        proc_cmd = shlex.split(cmd)
    else:
        proc_cmd = cmd
    try:
        completed = subprocess.run(proc_cmd, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True, timeout=timeout)
        return (completed.returncode, (completed.stdout or "").strip())
    except subprocess.TimeoutExpired as e:
        return (124, f"Command timed out after {timeout}s: {e}")
    except FileNotFoundError:
        return (127, f"Command not found: {proc_cmd[0] if proc_cmd else cmd}")
    except Exception as e:
        return (1, f"Error running command {proc_cmd}: {e}")

# ---------- FirewallManager (unchanged, robust) ----------
# 

import os
import platform
import subprocess
import shutil
import socket
import textwrap

class FirewallManager:
    """
    Cross-platform FirewallManager:
      - Windows: uses PowerShell New-NetFirewallRule / Remove-NetFirewallRule
      - macOS (Darwin): uses pf (pfctl) with an anchor/table
      - Linux: tries ufw/nft/iptables (existing code path kept as fallback)

    Methods:
      - block_ip(ip, reason)
      - unblock_ip(ip)
      - list_rules()
      - ufw_enable(), ufw_disable(), ufw_status() (Linux-only stubs)
    """

    # anchor/table names for macOS pf
    PF_ANCHOR_NAME = "cybersentinel"
    PF_TABLE_NAME = "cybersentinel_tbl"

    def __init__(self):
        self.system = platform.system().lower()
        self.backend = None

        if self.system.startswith("windows"):
            self.backend = "windows"
        elif self.system.startswith("darwin"):
            self.backend = "macos"
        else:
            # detect linux utilities (existing code fallback)
            if shutil.which("ufw"):
                self.backend = "ufw"
            elif shutil.which("nft"):
                self.backend = "nft"
            elif shutil.which("iptables"):
                self.backend = "iptables"
            else:
                self.backend = None

    # ---------------------------
    # Helpers
    # ---------------------------
    def _run(self, cmd_list, capture=True, text=True, timeout=30):
        """Run a command list (no shell) and return (ok, stdout+stderr)."""
        try:
            completed = subprocess.run(cmd_list, capture_output=capture, text=text, timeout=timeout)
            out = (completed.stdout or "") + (completed.stderr or "")
            ok = (completed.returncode == 0)
            return ok, out.strip()
        except Exception as e:
            return False, str(e)

    def _pw_run(self, ps_command):
        """Run PowerShell command and return (ok, output)."""
        try:
            completed = subprocess.run(
                ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", ps_command],
                capture_output=True, text=True, timeout=30
            )
            out = (completed.stdout or "") + (completed.stderr or "")
            ok = (completed.returncode == 0)
            return ok, out.strip()
        except Exception as e:
            return False, str(e)

    # --- Windows enable/disable/status using netsh advfirewall ---

    def _win_enable_firewall(self):
        """
        Enable Windows Firewall for all profiles. Requires Administrator.
        Uses netsh advfirewall set allprofiles state on
        """
        cmd = "netsh advfirewall set allprofiles state on"
        # run via powershell so permission/encoding is handled
        ok, out = self._pw_run(cmd)
        if ok:
            return True, "Windows Firewall enabled for all profiles."
        return False, f"Failed to enable Windows Firewall: {out}"


    def _win_disable_firewall(self):
        """
        Disable Windows Firewall for all profiles.
        """
        cmd = "netsh advfirewall set allprofiles state off"
        ok, out = self._pw_run(cmd)
        if ok:
            return True, "Windows Firewall disabled for all profiles."
        return False, f"Failed to disable Windows Firewall: {out}"

    def _win_firewall_status(self):
        """
        Return a short status string using 'netsh advfirewall show allprofiles'.
        """
        cmd = "netsh advfirewall show allprofiles"
        ok, out = self._pw_run(cmd)
        if ok:
            # out contains multiple profiles; return as-is
            return True, out
        return False, f"Failed to get Windows Firewall status: {out}"

    # ---------------------------
    # Windows implementations
    # ---------------------------
    def _win_block_ip(self, ip: str, reason: str):
        rule_base = f"CyberSentinel-block-{ip}".replace(":", "-")
        cmd_in = f"if (-not (Get-NetFirewallRule -DisplayName '{rule_base}-IN' -ErrorAction SilentlyContinue)) {{ New-NetFirewallRule -DisplayName '{rule_base}-IN' -Direction Inbound -Action Block -RemoteAddress '{ip}' -Description '{reason}' }}"
        cmd_out = f"if (-not (Get-NetFirewallRule -DisplayName '{rule_base}-OUT' -ErrorAction SilentlyContinue)) {{ New-NetFirewallRule -DisplayName '{rule_base}-OUT' -Direction Outbound -Action Block -RemoteAddress '{ip}' -Description '{reason}' }}"
        ok1, out1 = self._pw_run(cmd_in)
        ok2, out2 = self._pw_run(cmd_out)
        if ok1 or ok2:
            return True, f"Blocked {ip} on Windows firewall (IN/OUT rules created)."
        return False, f"Failed to block IP on Windows. In:{out1}\nOut:{out2}"

    def _win_unblock_ip(self, ip: str):
        rule_base = f"CyberSentinel-block-{ip}".replace(":", "-")
        cmd_in = f"Get-NetFirewallRule -DisplayName '{rule_base}-IN' -ErrorAction SilentlyContinue | Remove-NetFirewallRule -Confirm:$false"
        cmd_out = f"Get-NetFirewallRule -DisplayName '{rule_base}-OUT' -ErrorAction SilentlyContinue | Remove-NetFirewallRule -Confirm:$false"
        ok1, out1 = self._pw_run(cmd_in)
        ok2, out2 = self._pw_run(cmd_out)
        if ok1 or ok2:
            return True, f"Unblocked {ip} (Windows firewall rules removed)."
        return False, f"No rules found or failed to remove. In:{out1}\nOut:{out2}"

    def _win_list_rules(self):
        cmd = "Get-NetFirewallRule -DisplayName 'CyberSentinel-block-*' -ErrorAction SilentlyContinue | Select-Object DisplayName,Direction,Action,Enabled,Description | Format-Table -AutoSize | Out-String"
        ok, out = self._pw_run(cmd)
        if ok:
            return True, out or "(no CyberSentinel rules)"
        return False, out

    # ---------------------------
    # macOS (pf) implementations
    # ---------------------------
    def _mac_pf_enabled(self):
        ok, out = self._run(["pfctl", "-s", "info"])
        if not ok:
            return False
        return "Status: Enabled" in out or "Status: Enabled" in out

    def _mac_ensure_anchor(self):
        """
        Ensure the anchor file exists and is loaded. Creates /etc/pf.anchors/cybersentinel
        with a table named PF_TABLE_NAME and a block rule referring to it,
        then loads it into pf (requires root).
        """
        anchor_path = f"/etc/pf.anchors/{self.PF_ANCHOR_NAME}"
        # anchor content: table persist + block rule using table
        anchor_content = textwrap.dedent(f"""\
            # CyberSentinel PF anchor
            table <{self.PF_TABLE_NAME}> persist
            block quick drop on egress from any to <{self.PF_TABLE_NAME}>
            block quick drop on ingress from any to <{self.PF_TABLE_NAME}>
        """)
        try:
            # write anchor file (needs root) - use temp file + mv to avoid partial writes
            with open("/tmp/cybersentinel_pf_anchor.tmp", "w") as f:
                f.write(anchor_content)
            # move into place (requires sudo) using pf-friendly command; try direct move
            ok, out = self._run(["sudo", "mv", "/tmp/cybersentinel_pf_anchor.tmp", anchor_path])
            if not ok:
                return False, f"Failed to place anchor: {out}"
            # Load/refresh anchor into pf
            ok2, out2 = self._run(["sudo", "pfctl", "-a", self.PF_ANCHOR_NAME, "-f", anchor_path])
            if not ok2:
                return False, f"Failed to load pf anchor: {out2}"
            # Ensure pf is enabled
            ok3, out3 = self._run(["sudo", "pfctl", "-e"])
            # if pf already enabled, pfctl -e returns non-zero but harmless; ignore
            return True, "Anchor created & loaded"
        except Exception as e:
            return False, str(e)

    def _mac_block_ip(self, ip: str, reason: str):
        # Ensure anchor/table exists in pf
        ok, out = self._mac_ensure_anchor()
        if not ok:
            return False, f"Failed to prepare PF anchor: {out}"

        # add ip to the pf table
        ok2, out2 = self._run(["sudo", "pfctl", "-t", self.PF_TABLE_NAME, "-T", "add", ip])
        if ok2:
            return True, f"Blocked {ip} via pf table {self.PF_TABLE_NAME}."
        return False, f"Failed to add IP to pf table: {out2}"

    def _mac_unblock_ip(self, ip: str):
        ok, out = self._run(["sudo", "pfctl", "-t", self.PF_TABLE_NAME, "-T", "delete", ip])
        if ok:
            return True, f"Removed {ip} from pf table {self.PF_TABLE_NAME}."
        return False, f"Failed to remove IP from pf table: {out}"

    def _mac_list_rules(self):
        ok, out = self._run(["sudo", "pfctl", "-t", self.PF_TABLE_NAME, "-T", "show"])
        if ok:
            return True, out or "(pf table empty)"
        # If table doesn't exist, return empty
        return False, out

    # ---------------------------
    # Public API
    # ---------------------------
    def block_ip(self, ip: str, reason: str = "blocked_by_cybersentinel"):
        # basic ip validation
        try:
            socket.inet_aton(ip)
        except Exception:
            # allow IPv6 too (best-effort)
            try:
                socket.inet_pton(socket.AF_INET6, ip)
            except Exception:
                # not an IP
                pass

        if self.backend == "windows":
            ok, out = self._win_block_ip(ip, reason)
            return out
        elif self.backend == "macos":
            ok, out = self._mac_block_ip(ip, reason)
            return out
        elif self.backend == "ufw" or self.backend == "nft" or self.backend == "iptables":
            # use existing linux methods if available (call them if implemented)
            # attempt ufw first
            try:
                if self.backend == "ufw":
                    # call ufw via subprocess (requires root)
                    ok, out = self._run(["sudo", "ufw", "deny", "from", ip])
                    return out if ok else f"Failed to block via ufw: {out}"
                # nft/iptables support could be added similarly; fallback message:
                return f"Linux backend '{self.backend}' blocking not implemented in this unified manager."
            except Exception as e:
                return f"Failed to block IP on Linux backend: {e}"
        else:
            return "No supported firewall backend detected on this system."

    def unblock_ip(self, ip: str):
        if self.backend == "windows":
            ok, out = self._win_unblock_ip(ip)
            return out
        elif self.backend == "macos":
            ok, out = self._mac_unblock_ip(ip)
            return out
        elif self.backend == "ufw":
            ok, out = self._run(["sudo", "ufw", "delete", "deny", "from", ip])
            return out if ok else f"Failed to unblock via ufw: {out}"
        else:
            return "No supported firewall backend detected for unblock."

    def list_rules(self):
        if self.backend == "windows":
            ok, out = self._win_list_rules()
            return out
        elif self.backend == "macos":
            ok, out = self._mac_list_rules()
            return out
        elif self.backend:
            # fallback to linux listing if available
            if self.backend == "ufw":
                ok, out = self._run(["sudo", "ufw", "status", "numbered"])
                return out
            else:
                return f"List rules not implemented for backend: {self.backend}"
        else:
            return "No firewall backend detected."

    # ufw stubs for compatibility
    def ufw_enable(self):
        # for Linux 'ufw' backend this enables ufw; for windows map to netsh
        if self.backend == "windows":
            ok, out = self._win_enable_firewall()
            return out
        if self.backend == "ufw":
            ok, out = self._run(["sudo", "ufw", "enable"])
            return out if ok else f"Failed to enable ufw: {out}"
        return "Enable firewall not supported on this platform."


        
    def ufw_disable(self):
        if self.backend == "windows":
            ok, out = self._win_disable_firewall()
            return out
        if self.backend == "ufw":
            ok, out = self._run(["sudo", "ufw", "disable"])
            return out if ok else f"Failed to disable ufw: {out}"
        return "Disable firewall not supported on this platform."

    def ufw_status(self):
        if self.backend == "windows":
            ok, out = self._win_firewall_status()
            return out if ok else f"(status failed) {out}"
        if self.backend == "ufw":
            ok, out = self._run(["sudo", "ufw", "status"])
            return out if ok else f"Failed to get ufw status: {out}"
        # fallback to list_rules for other backends
        try:
            return self.list_rules()
        except Exception as e:
            return f"No firewall status available: {e}"


# ---------- Simple Monitor ----------
class SimpleMonitor:
    def __init__(self, iface=None, conn_rate_threshold=100, scan_ports_threshold=30,
                 window_seconds=10, report_interval=5):
        if not SCAPY_ASYNC:
            raise RuntimeError("scapy AsyncSniffer is required for monitoring. Install: sudo pip3 install scapy")
        self.iface = iface
        self.conn_rate_threshold = conn_rate_threshold
        self.scan_ports_threshold = scan_ports_threshold
        self.window_seconds = window_seconds
        self.report_interval = report_interval

        self.conn_times = defaultdict(deque)
        self.port_hits = defaultdict(dict)
        self.total_packets = 0
        self.lock = threading.Lock()
        self.running = False
        self.alerts = deque(maxlen=200)
        self._sniffer = None
        self._report_thread = None

    def _is_connection_packet(self, pkt):
        if IP not in pkt:
            return False
        if TCP in pkt:
            flags = pkt[TCP].flags
            return (flags & 0x02) and not (flags & 0x10)
        if UDP in pkt:
            return True
        return False

    def _handle_pkt(self, pkt):
        with self.lock:
            self.total_packets += 1
            if IP not in pkt:
                return
            src = pkt[IP].src
            now = time.time()
            if self._is_connection_packet(pkt):
                dq = self.conn_times[src]
                dq.append(now)
                while dq and dq[0] < now - self.window_seconds:
                    dq.popleft()
                if len(dq) >= self.conn_rate_threshold:
                    msg = f"HIGH_CONN_RATE: {src} made {len(dq)} conns in {self.window_seconds}s"
                    if msg not in self.alerts:
                        self.alerts.append(msg)
                        print(f"[ALERT] {msg}")

            dport = None
            if TCP in pkt:
                dport = pkt[TCP].dport
            elif UDP in pkt:
                dport = pkt[UDP].dport
            if dport is not None:
                ph = self.port_hits[src]
                ph[dport] = now
                for p in list(ph.keys()):
                    if ph[p] < now - self.window_seconds:
                        del ph[p]
                if len(ph) >= self.scan_ports_threshold:
                    msg = f"PORT_SCAN: {src} touched {len(ph)} distinct dst ports in {self.window_seconds}s"
                    if msg not in self.alerts:
                        self.alerts.append(msg)
                        print(f"[ALERT] {msg}")

    def _report_loop(self):
        last_total = 0
        while self.running:
            time.sleep(self.report_interval)
            with self.lock:
                total = self.total_packets
                delta = total - last_total
                last_total = total
                top = Counter({k: len(v) for k, v in self.conn_times.items()}).most_common(5)
                alerts_snapshot = list(self.alerts)
            print(f"\n[{datetime.now(UTC).isoformat()}] total_packets={total} (+{delta} in last {self.report_interval}s)")
            if top:
                print("Top recent sources:")
                for s, c in top:
                    print(f"  {s}: {c} recent conns")
            if alerts_snapshot:
                print("Alerts:")
                for a in alerts_snapshot[-10:]:
                    print(" ", a)

    def start(self):
        if self.running:
            return "Monitor already running."
        self.running = True
        self._sniffer = AsyncSniffer(iface=self.iface, prn=self._handle_pkt, store=False)
        self._sniffer.start()
        self._report_thread = threading.Thread(target=self._report_loop, daemon=True)
        self._report_thread.start()
        return "Monitor started."

    def stop(self):
        if not self.running:
            return "Monitor not running."
        self.running = False
        try:
            if self._sniffer:
                self._sniffer.stop()
                self._sniffer = None
        except Exception:
            pass
        return "Monitor stopped."

# ---------- Database & Crypto helpers ----------
PBKDF2_ITERS = 200_000
SALT_SIZE = 16
AES_KEY_SIZE = 32
NONCE_SIZE = 12

def _b64(b: bytes) -> str:
    return base64.b64encode(b).decode('ascii')

def _unb64(s: str) -> bytes:
    return base64.b64decode(s.encode('ascii'))

def _init_db():
    create = not os.path.exists(USERS_DB)
    conn = sqlite3.connect(USERS_DB, check_same_thread=False)
    cur = conn.cursor()
    # users: username PK, pw_salt, pw_verifier, vault_salt, created
    cur.execute("""
    CREATE TABLE IF NOT EXISTS users (
        username TEXT PRIMARY KEY,
        pw_salt TEXT NOT NULL,
        pw_verifier TEXT NOT NULL,
        vault_salt TEXT NOT NULL,
        created TEXT NOT NULL
    )
    """)
    # entries: id, owner, name (plaintext), entry_username (plaintext),
    # password_ct (base64), nonce (base64), notes_ct (base64)
    cur.execute("""
    CREATE TABLE IF NOT EXISTS entries (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        owner TEXT NOT NULL,
        name TEXT NOT NULL,
        entry_username TEXT,
        password_ct TEXT NOT NULL,
        nonce TEXT NOT NULL,
        notes_ct TEXT,
        created TEXT NOT NULL,
        FOREIGN KEY(owner) REFERENCES users(username) ON DELETE CASCADE
    )
    """)
    conn.commit()
    conn.close()
    if create:
        _ensure_db_permissions(USERS_DB)

_init_db()


def _init_phishing_table():
    """Create phishing_reports table inside USERS_DB (if missing)."""
    try:
        # ensure users.db exists (touch) so permissions and path are stable
        if not os.path.exists(USERS_DB):
            # create empty DB file
            open(USERS_DB, "a").close()
            _ensure_db_permissions(USERS_DB)
        conn = sqlite3.connect(USERS_DB)
        cur = conn.cursor()
        cur.execute("""
        CREATE TABLE IF NOT EXISTS phishing_reports (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            url TEXT NOT NULL,
            host TEXT,
            ip TEXT,
            verdict TEXT,
            score REAL,
            issues TEXT,     -- json list
            explain TEXT,    -- json dict
            reason_summary TEXT,
            created TEXT
        )
        """)
        conn.commit()
        conn.close()
        # make file private (best-effort)
        try:
            _ensure_db_permissions(USERS_DB)
        except Exception:
            pass
    except Exception as e:
        # non-fatal: print for debugging
        print("Failed to init phishing table:", e)

# initialize table at import/startup
_init_phishing_table()



def hash_password_pbkdf2(password: str, salt: bytes = None) -> Tuple[bytes, bytes]:
    if salt is None:
        salt = os.urandom(SALT_SIZE)
    pwd = password.encode('utf-8')
    verifier = hashlib.pbkdf2_hmac('sha256', pwd, salt, PBKDF2_ITERS, dklen=32)
    return salt, verifier

def verify_password_pbkdf2(password: str, salt: bytes, verifier: bytes) -> bool:
    derived = hashlib.pbkdf2_hmac('sha256', password.encode('utf-8'), salt, PBKDF2_ITERS, dklen=32)
    return hmac.compare_digest(derived, verifier)

def derive_key(password: str, salt: bytes, length=AES_KEY_SIZE) -> bytes:
    return hashlib.pbkdf2_hmac('sha256', password.encode('utf-8'), salt, PBKDF2_ITERS, dklen=length)

# ---------- User & vault (DB-backed) operations ----------
def user_exists(username: str) -> bool:
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("SELECT 1 FROM users WHERE username = ?", (username,))
    exists = cur.fetchone() is not None
    conn.close()
    return exists

def create_user(username: str, password: str) -> Tuple[bool, str]:
    if not CRYPTO_AVAILABLE:
        return False, "Required package 'cryptography' not available. Install: sudo pip3 install cryptography"
    if user_exists(username):
        return False, "User already exists."
    pw_salt, verifier = hash_password_pbkdf2(password)
    vault_salt = os.urandom(SALT_SIZE)
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("INSERT INTO users (username, pw_salt, pw_verifier, vault_salt, created) VALUES (?, ?, ?, ?, ?)",
                (username, _b64(pw_salt), _b64(verifier), _b64(vault_salt), datetime.now(UTC).isoformat()))
    conn.commit()
    conn.close()
    return True, "User created."

def authenticate_user(username: str, password: str) -> Tuple[bool, str]:
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("SELECT pw_salt, pw_verifier FROM users WHERE username = ?", (username,))
    row = cur.fetchone()
    conn.close()
    if not row:
        return False, "User does not exist."
    try:
        salt = _unb64(row[0])
        verifier = _unb64(row[1])
        ok = verify_password_pbkdf2(password, salt, verifier)
        return (ok, "Authenticated" if ok else "Invalid password.")
    except Exception as e:
        return False, f"Error verifying password: {e}"

def _get_vault_salt(username: str) -> bytes:
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("SELECT vault_salt FROM users WHERE username = ?", (username,))
    r = cur.fetchone()
    conn.close()
    if not r:
        raise ValueError("User not found")
    return _unb64(r[0])

def load_entries(username: str, password: str) -> Tuple[bool, list or str]:
    """
    Return list of decrypted entries on success.
    Each entry: dict {id, name, entry_username, password, notes, created}
    """
    if not CRYPTO_AVAILABLE:
        return False, "cryptography missing"
    try:
        vault_salt = _get_vault_salt(username)
        key = derive_key(password, vault_salt)
        aesgcm = AESGCM(key)
    except Exception as e:
        return False, f"Failed deriving key: {e}"

    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("SELECT id, name, entry_username, password_ct, nonce, notes_ct, created FROM entries WHERE owner = ? ORDER BY created DESC", (username,))
    rows = cur.fetchall()
    conn.close()
    out = []
    for r in rows:
        try:
            password_ct = _unb64(r[3])
            nonce = _unb64(r[4])
            pw = aesgcm.decrypt(nonce, password_ct, None).decode('utf-8')
        except Exception:
            pw = "<decryption failed>"
        notes = None
        if r[5]:
            try:
                notes_ct = _unb64(r[5])
                notes = aesgcm.decrypt(nonce, notes_ct, None).decode('utf-8')
            except Exception:
                notes = "<decryption failed>"
        out.append({
            "id": r[0],
            "name": r[1],
            "entry_username": r[2],
            "password": pw,
            "notes": notes,
            "created": r[6],
        })
    return True, out

def add_entry(username: str, password: str, name: str, entry_username: str, entry_password: str, notes: str) -> Tuple[bool, str]:
    if not CRYPTO_AVAILABLE:
        return False, "cryptography missing"
    try:
        vault_salt = _get_vault_salt(username)
        key = derive_key(password, vault_salt)
        aesgcm = AESGCM(key)
    except Exception as e:
        return False, f"Failed deriving key: {e}"
    nonce = os.urandom(NONCE_SIZE)
    ct = aesgcm.encrypt(nonce, entry_password.encode('utf-8'), None)
    notes_ct = aesgcm.encrypt(nonce, (notes or "").encode('utf-8'), None) if notes is not None else None
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("""INSERT INTO entries (owner, name, entry_username, password_ct, nonce, notes_ct, created)
                   VALUES (?, ?, ?, ?, ?, ?, ?)""",
                (username, name, entry_username, _b64(ct), _b64(nonce), _b64(notes_ct) if notes_ct else None, datetime.now(UTC).isoformat()))
    conn.commit()
    conn.close()
    return True, "Entry added."

def update_entry(username: str, password: str, entry_id: int, name: str = None, entry_username: str = None,
                 entry_password: str = None, notes: str = None) -> Tuple[bool, str]:
    if not CRYPTO_AVAILABLE:
        return False, "cryptography missing"
    try:
        vault_salt = _get_vault_salt(username)
        key = derive_key(password, vault_salt)
        aesgcm = AESGCM(key)
    except Exception as e:
        return False, f"Failed deriving key: {e}"
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("SELECT owner FROM entries WHERE id = ?", (entry_id,))
    row = cur.fetchone()
    if not row or row[0] != username:
        conn.close()
        return False, "Entry not found or permission denied."
    updates = []
    params = []
    if name is not None:
        updates.append("name = ?"); params.append(name)
    if entry_username is not None:
        updates.append("entry_username = ?"); params.append(entry_username)
    if entry_password is not None:
        nonce = os.urandom(NONCE_SIZE)
        ct = aesgcm.encrypt(nonce, entry_password.encode('utf-8'), None)
        updates.append("password_ct = ?"); params.append(_b64(ct))
        updates.append("nonce = ?"); params.append(_b64(nonce))
    if notes is not None:
        # must use same nonce as password or generate new one; we use a new nonce to be safe
        nonce2 = os.urandom(NONCE_SIZE)
        notes_ct = aesgcm.encrypt(nonce2, notes.encode('utf-8'), None)
        updates.append("notes_ct = ?"); params.append(_b64(notes_ct))
        updates.append("nonce = ?"); params.append(_b64(nonce2))
    if not updates:
        conn.close()
        return False, "No changes provided."
    params.append(entry_id)
    sql = "UPDATE entries SET " + ", ".join(updates) + " WHERE id = ?"
    cur.execute(sql, tuple(params))
    conn.commit()
    conn.close()
    return True, "Entry updated."

def delete_entry(username: str, entry_id: int) -> Tuple[bool, str]:
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("SELECT owner FROM entries WHERE id = ?", (entry_id,))
    row = cur.fetchone()
    if not row or row[0] != username:
        conn.close()
        return False, "Entry not found or permission denied."
    cur.execute("DELETE FROM entries WHERE id = ?", (entry_id,))
    conn.commit()
    conn.close()
    return True, "Entry deleted."


# ------------Phishing data store-----------------------------------

def phish_save_report(url: str, verdict: str, score: float, issues: list, explain: dict, reason_summary: str, host: str = None, ip: str = None):
    ts = datetime.now(timezone.utc).isoformat()
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO phishing_reports (url, host, ip, verdict, score, issues, explain, reason_summary, created)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (url, host, ip, verdict, score, json.dumps(issues), json.dumps(explain), reason_summary, ts))
    conn.commit()
    rowid = cur.lastrowid
    conn.close()
    return rowid

def phish_count(filter_verdict: str = None):
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    if filter_verdict:
        cur.execute("SELECT COUNT(*) FROM phishing_reports WHERE verdict = ?", (filter_verdict,))
    else:
        cur.execute("SELECT COUNT(*) FROM phishing_reports")
    c = cur.fetchone()[0]
    conn.close()
    return c

def phish_list(filter_verdict: str = None, limit: int = 100):
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    if filter_verdict:
        cur.execute("SELECT id, url, host, ip, verdict, score, created FROM phishing_reports WHERE verdict = ? ORDER BY created DESC LIMIT ?", (filter_verdict, limit))
    else:
        cur.execute("SELECT id, url, host, ip, verdict, score, created FROM phishing_reports ORDER BY created DESC LIMIT ?", (limit,))
    rows = cur.fetchall()
    conn.close()
    return rows

def phish_search(substring: str, filter_verdict: str = None, limit: int = 200):
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    pattern = f"%{substring}%"
    if filter_verdict:
        cur.execute("SELECT id, url, host, ip, verdict, score, created FROM phishing_reports WHERE url LIKE ? AND verdict = ? ORDER BY created DESC LIMIT ?", (pattern, filter_verdict, limit))
    else:
        cur.execute("SELECT id, url, host, ip, verdict, score, created FROM phishing_reports WHERE url LIKE ? ORDER BY created DESC LIMIT ?", (pattern, limit))
    rows = cur.fetchall()
    conn.close()
    return rows

def phish_get_report(report_id: int):
    conn = sqlite3.connect(USERS_DB)
    cur = conn.cursor()
    cur.execute("SELECT id, url, host, ip, verdict, score, issues, explain, reason_summary, created FROM phishing_reports WHERE id = ?", (report_id,))
    r = cur.fetchone()
    conn.close()
    if not r:
        return None
    return {
        "id": r[0],
        "url": r[1],
        "host": r[2],
        "ip": r[3],
        "verdict": r[4],
        "score": r[5],
        "issues": json.loads(r[6]) if r[6] else [],
        "explain": json.loads(r[7]) if r[7] else {},
        "reason_summary": r[8],
        "created": r[9]
    }




# ---------- Password manager CLI (DB-backed) ----------
def generate_password(length: int = 16, use_symbols: bool = True) -> str:
    alphabet = string.ascii_letters + string.digits
    if use_symbols:
        alphabet += "!@#$%^&*()-_=+[]{};:,.<>/?"
    return ''.join(secrets.choice(alphabet) for _ in range(length))

def password_manager_cli(username: str, password: str):
    """
    Styled Password Manager CLI for CyberSentinel.
    Relies on helper functions:
      - load_entries, add_entry, update_entry, delete_entry, generate_password
      - get_choice, pause, clear_screen
      - styled_section, color_line, FG_*, EMOJI_*
      - USERS_DB (for export/import)
    """
    import getpass
    import sqlite3
    import json
    from datetime import datetime, timezone as _tz

    while True:
        styled_section(f"Password Manager — {username}", emoji=EMOJI_LOCK)
        print(FG_WHITE + " 1) " + FG_CYAN + "List entries" + RESET)
        print(FG_WHITE + " 2) " + FG_CYAN + "Add entry" + RESET)
        print(FG_WHITE + " 3) " + FG_CYAN + "View entry" + RESET)
        print(FG_WHITE + " 4) " + FG_CYAN + "Edit entry" + RESET)
        print(FG_WHITE + " 5) " + FG_CYAN + "Delete entry" + RESET)
        print(FG_WHITE + " 6) " + FG_CYAN + "Generate password" + RESET)
        print(FG_WHITE + " 7) " + FG_CYAN + "Export entries (JSON, encrypted fields preserved)" + RESET)
        print(FG_WHITE + " 8) " + FG_CYAN + "Import entries (JSON, encrypted fields preserved)" + RESET)
        print(FG_WHITE + " 9) " + FG_CYAN + "Back to main menu" + RESET)

        choice = get_choice(FG_BLUE + BOLD + "\nChoose [1-9]: " + RESET, [str(i) for i in range(1, 10)])

        # -------------------------
        # 1) List entries
        # -------------------------
        if choice == "1":
            ok, data_or_err = load_entries(username, password)
            if not ok:
                print(FG_RED + "Error: " + str(data_or_err) + RESET)
                pause(); continue

            if not data_or_err:
                print(FG_YELLOW + EMOJI_WARN + " No entries found." + RESET)
            else:
                styled_section("Your Entries", emoji=EMOJI_DB)
                # show brief table: id | name | entry_username | created
                for e in data_or_err:
                    created = e.get("created") or ""
                    entry_un = e.get("entry_username") or ""
                    print(f"{BOLD}{e['id']:4d}{RESET}  {FG_MAGENTA}{e['name']}{RESET}  {DIM}{entry_un}{RESET}  {FG_CYAN}{created}{RESET}")
            pause()

        # -------------------------
        # 2) Add entry
        # -------------------------
        elif choice == "2":
            styled_section("Add Entry", emoji=EMOJI_LOCK)
            name = input("Entry name (unique per user): ").strip()
            if not name:
                print(FG_YELLOW + "Name required." + RESET); pause(); continue

            entry_un = input("Username for this entry (optional): ").strip()

            pw_choice = get_choice("Provide password or generate? (p/g): ", ["p", "g"])
            if pw_choice == "p":
                ent_pw = getpass.getpass("Password (hidden): ")
            else:
                ent_pw = generate_password()
                print(FG_GREEN + "Generated password:" + RESET, ent_pw)

            notes = input("Notes (optional): ").strip()

            ok, msg = add_entry(username, password, name, entry_un, ent_pw, notes)
            if ok:
                print(FG_GREEN + EMOJI_CHECK + " " + msg + RESET)
            else:
                print(FG_RED + "Error: " + str(msg) + RESET)
            pause()

        # -------------------------
        # 3) View entry
        # -------------------------
        elif choice == "3":
            eid = input("Entry id to view: ").strip()
            if not eid.isdigit():
                print(FG_YELLOW + "Enter numeric id." + RESET); pause(); continue
            ok, entries = load_entries(username, password)
            if not ok:
                print(FG_RED + "Error: " + str(entries) + RESET); pause(); continue
            entry = next((x for x in entries if x["id"] == int(eid)), None)
            if not entry:
                print(FG_YELLOW + "Entry not found." + RESET); pause(); continue

            styled_section("Entry Details", emoji=EMOJI_LOCK)
            color_line("ID", str(entry["id"]), key_color=FG_CYAN)
            color_line("Name", entry["name"], key_color=FG_CYAN)
            color_line("Entry username", entry.get("entry_username") or "N/A", key_color=FG_CYAN)
            if get_choice("Show password? (y/n): ", ["y", "n"]) == "y":
                color_line("Password", entry.get("password") or "<decryption failed>", key_color=FG_CYAN, value_color=FG_GREEN)
            else:
                color_line("Password", "********", key_color=FG_CYAN, value_color=FG_YELLOW)
            print()
            print(FG_WHITE + "Notes:" + RESET)
            print(" ", entry.get("notes") or "")
            print()
            color_line("Created", entry.get("created") or "N/A", key_color=FG_CYAN)
            pause()

        # -------------------------
        # 4) Edit entry
        # -------------------------
        elif choice == "4":
            eid = input("Entry id to edit: ").strip()
            if not eid.isdigit():
                print(FG_YELLOW + "Enter numeric id." + RESET); pause(); continue
            eid = int(eid)
            ok, entries = load_entries(username, password)
            if not ok:
                print(FG_RED + "Error: " + str(entries) + RESET); pause(); continue
            entry = next((x for x in entries if x["id"] == eid), None)
            if not entry:
                print(FG_YELLOW + "Entry not found." + RESET); pause(); continue

            print(FG_BLUE + "Leave blank to keep current value." + RESET)
            new_name = input(f"Name [{entry['name']}]: ").strip() or None
            new_un = input(f"Entry username [{entry.get('entry_username') or ''}]: ").strip() or None
            change_pw = get_choice("Change password? (y/N): ", ["y", "n"]) == "y"
            new_pw = None
            if change_pw:
                prov = get_choice("Provide or generate? (p/g): ", ["p", "g"])
                if prov == "p":
                    new_pw = getpass.getpass("New password: ")
                else:
                    new_pw = generate_password()
                    print(FG_GREEN + "Generated:" + RESET, new_pw)
            new_notes = input(f"Notes [{entry.get('notes') or ''}]: ").strip() or None

            ok2, msg = update_entry(username, password, eid, name=new_name, entry_username=new_un,
                                    entry_password=new_pw, notes=new_notes)
            if ok2:
                print(FG_GREEN + EMOJI_CHECK + " " + msg + RESET)
            else:
                print(FG_RED + "Error: " + str(msg) + RESET)
            pause()

        # -------------------------
        # 5) Delete entry
        # -------------------------
        elif choice == "5":
            eid = input("Entry id to delete: ").strip()
            if not eid.isdigit():
                print(FG_YELLOW + "Enter numeric id." + RESET); pause(); continue
            eid = int(eid)
            if get_choice(FG_YELLOW + "Confirm deletion? (y/n): " + RESET, ["y", "n"]) == "y":
                ok, msg = delete_entry(username, eid)
                if ok:
                    print(FG_GREEN + EMOJI_CHECK + " " + msg + RESET)
                else:
                    print(FG_RED + "Error: " + str(msg) + RESET)
            else:
                print(FG_CYAN + "Deletion cancelled." + RESET)
            pause()

        # -------------------------
        # 6) Generate password
        # -------------------------
        elif choice == "6":
            length = input("Password length (default 16): ").strip()
            try:
                length = int(length) if length else 16
            except Exception:
                length = 16
            use_symbols = get_choice("Include symbols? (y/n): ", ["y", "n"]) == "y"
            pw = generate_password(length=length, use_symbols=use_symbols)
            styled_section("Generated Password", emoji=EMOJI_STAR)
            print(FG_GREEN + pw + RESET)
            print(FG_BLUE + "Use copy/paste carefully. Clear clipboard after use." + RESET)
            pause()

        # -------------------------
        # 7) Export entries (JSON)
        # -------------------------
        elif choice == "7":
            dest = input("Export path (full path, will be JSON): ").strip()
            if not dest:
                print(FG_YELLOW + "No path provided." + RESET); pause(); continue
            try:
                conn = sqlite3.connect(USERS_DB)
                cur = conn.cursor()
                cur.execute("SELECT id, name, entry_username, password_ct, nonce, notes_ct, created FROM entries WHERE owner = ?", (username,))
                rows = cur.fetchall()
                conn.close()
                payload = []
                for r in rows:
                    payload.append({
                        "id": r[0],
                        "name": r[1],
                        "entry_username": r[2],
                        "password_ct": r[3],
                        "nonce": r[4],
                        "notes_ct": r[5],
                        "created": r[6],
                    })
                with open(dest, "w") as f:
                    json.dump(payload, f, indent=2)
                print(FG_GREEN + EMOJI_DB + " Exported to " + dest + RESET)
            except Exception as e:
                print(FG_RED + "Export failed: " + str(e) + RESET)
            pause()

        # -------------------------
        # 8) Import entries (JSON)
        # -------------------------
        elif choice == "8":
            src = input("Path to JSON export file to import: ").strip()
            if not src or not os.path.exists(src):
                print(FG_YELLOW + "File not found." + RESET); pause(); continue
            try:
                with open(src, "r") as f:
                    data = json.load(f)
            except Exception as e:
                print(FG_RED + "Failed to load JSON: " + str(e) + RESET); pause(); continue

            try:
                conn = sqlite3.connect(USERS_DB)
                cur = conn.cursor()
                imported = 0
                for item in data:
                    try:
                        cur.execute("""INSERT INTO entries (owner, name, entry_username, password_ct, nonce, notes_ct, created)
                                       VALUES (?, ?, ?, ?, ?, ?, ?)""",
                                    (username, item["name"], item.get("entry_username"), item["password_ct"], item["nonce"], item.get("notes_ct"), item.get("created", datetime.now(_tz.utc).isoformat())))
                        imported += 1
                    except Exception:
                        # skip duplicates or malformed entries
                        pass
                conn.commit()
                conn.close()
                print(FG_GREEN + EMOJI_DB + f" Imported {imported} entries (encrypted fields preserved)." + RESET)
            except Exception as e:
                print(FG_RED + "Import failed: " + str(e) + RESET)
            pause()

        # -------------------------
        # 9) Back
        # -------------------------
        elif choice == "9":
            break

        else:
            # defensive fallback
            print(FG_YELLOW + "Unknown option." + RESET)
            pause()



# ---------- Phishing detector ----------------

SAFE_BROWSING_API = "https://safebrowsing.googleapis.com/v4/threatMatches:find?key={api_key}"

# Basic suspicious TLDs and tokens (extendable)
SUSPICIOUS_TLDS = { "zip","review","country","kim","top","work","loan","download","gq" }
SUSPICIOUS_KEYWORDS = {"login","secure","account","update","verify","bank","confirm","password","signin","wp-login"}

class PhishingDetector:
    """
    PhishingDetector - rule-based checks with optional Google Safe Browsing integration.

    Usage:
        pd = PhishingDetector(google_api_key=os.environ.get("GSB_API_KEY"))
        result = pd.check_url("http://example.com", do_content_check=False, do_gsb_check=True)

    Output (result) contains:
        - url, valid_url (bool)
        - score (0..1)
        - issues (list of raw issue keys)
        - explain (dict issue -> weight)
        - verdict (str): "Likely safe" / "Suspicious" / "Malicious"
        - top_reasons (list[str]): top 3 human-readable reasons with weights
        - reason_summary (str): short natural-language explanation
    """

    def __init__(self, google_api_key: str = None, user_agent: str = "CyberSentinel/1.0"):
        import requests
        import validators
        import tldextract
        # store imported modules as instance attrs so helper methods can reuse without repeated imports
        self.requests = requests
        self.validators = validators
        self.tldextract = tldextract
        self.google_api_key = google_api_key
        self.user_agent = user_agent
        self.session = self.requests.Session()
        self.session.headers.update({"User-Agent": self.user_agent})

        # Tunable sets and weights
        self.SUSPICIOUS_TLDS = {"zip", "review", "country", "kim", "top", "work", "loan", "download", "gq", "xyz", "cc"}
        self.SUSPICIOUS_KEYWORDS = {"login", "secure", "account", "update", "verify", "bank", "confirm",
                                    "password", "signin", "wp-login", "security", "authenticate"}
        # weights used when adding explain scores (tunable)
        self.WEIGHTS = {
            "lexical_default": 1.0,
            "ssl_issue": 1.5,
            "content_issue": 1.0,
            "gsb_match": 5.0
        }
        # Google Safe Browsing API endpoint template
        self.SAFE_BROWSING_API = "https://safebrowsing.googleapis.com/v4/threatMatches:find?key={api_key}"

    def _lexical_checks(self, url: str):
        """
        Quick string/domain based heuristics.
        Returns list of issue keys (strings).
        """
        import socket
        from urllib.parse import urlparse

        issues = []
        try:
            parsed = urlparse(url)
            host = (parsed.hostname or "").strip()
            path = parsed.path or ""
            qs = parsed.query or ""
        except Exception:
            issues.append("invalid_url_parse")
            return issues

        # length
        if len(url) > 200:
            issues.append("long_url")

        # IP address in host (IPv4/IPv6)
        if host:
            h = host.strip("[]")
            try:
                # IPv4
                socket.inet_aton(h)
                issues.append("ip_in_host")
            except Exception:
                try:
                    # IPv6
                    socket.inet_pton(socket.AF_INET6, h)
                    issues.append("ip_in_host")
                except Exception:
                    pass

        # presence of '@' (old trick)
        if "@" in url:
            issues.append("at_symbol_in_url")

        # too many '//' occurrences (odd redirect patterns)
        if url.count("//") > 2:
            issues.append("multiple_double_slashes")

        # many subdomains
        if host.count('.') >= 5:
            issues.append("many_dots_in_host")

        # suspicious keywords in host/path/query
        lower = (host + " " + path + " " + qs).lower()
        for tok in self.SUSPICIOUS_KEYWORDS:
            if tok in lower:
                issues.append(f"suspicious_token:{tok}")

        # unicode or punycode in domain -> homograph risk
        try:
            if any(ord(ch) > 127 for ch in host):
                issues.append("unicode_in_host")
            if host.startswith("xn--") or ".xn--" in host:
                issues.append("punycode_host")
        except Exception:
            pass

        # suspicious TLD
        try:
            ext = self.tldextract.extract(host)
            if ext.suffix:
                # take last part of suffix chain (e.g. co.uk -> uk)
                last_tld = ext.suffix.lower().split('.')[-1]
                if last_tld in self.SUSPICIOUS_TLDS:
                    issues.append(f"suspicious_tld:{last_tld}")
        except Exception:
            pass

        # complex path or very long query
        if len(qs) > 200 or path.count('/') > 10:
            issues.append("complex_path_or_query")

        return issues

    def _ssl_check(self, url: str, timeout=6):
        """
        Check TLS/HTTPS presence and basic certificate validity via a HEAD request.
        Returns a list of issue keys. If site is not https, we add 'not_https' (lower-severity).
        """
        issues = []
        from urllib.parse import urlparse
        parsed = urlparse(url)
        scheme = parsed.scheme.lower()
        if scheme != "https":
            issues.append("not_https")
            return issues
        # For https, attempt a HEAD to allow requests/urllib to validate certs
        try:
            r = self.session.head(url, allow_redirects=True, timeout=timeout)
            # If requests did not raise SSLError, we treat it as OK.
            # But status codes 4xx/5xx are not in themselves SSL issues; we ignore.
        except self.requests.exceptions.SSLError:
            issues.append("ssl_error")
        except self.requests.exceptions.ConnectionError:
            issues.append("conn_error")
        except self.requests.exceptions.Timeout:
            issues.append("timeout")
        except Exception:
            issues.append("ssl_check_failed")
        return issues

    def _content_checks(self, url: str, timeout=6, max_bytes=200_000):
        """
        Shallow fetch of the page (text/html) and simple content heuristics.
        Returns list of issue keys. This is optional and can be slow or dangerous on untrusted pages.
        """
        issues = []
        try:
            r = self.session.get(url, allow_redirects=True, timeout=timeout, stream=True)
            content_type = r.headers.get("content-type", "")
            if "text/html" not in content_type.lower():
                return issues
            body = r.content[:max_bytes].decode(errors="replace").lower()
            # look for password input elements or login-like forms
            if "<input" in body and "type=\"password\"" in body:
                issues.append("password_input_found")
            # login form heuristics
            if ("<form" in body and "login" in body) or ("signin" in body and "<form" in body):
                issues.append("login_form_like")
            # iframe usage
            if "<iframe" in body:
                issues.append("iframe_present")
            # many links could indicate phishing aggregator pages
            links = body.count("<a ")
            if links > 50:
                issues.append("many_links")
            # presence of known brand names in strange contexts (heuristic)
            # e.g., 'paypal' in body but domain not paypal -> suspicious impersonation
            # We'll not add it here automatically, but keep for future tuning.
        except Exception:
            # network errors or blocking -> don't add heavy-weight issues
            pass
        return issues

    def _safe_browsing_check(self, url: str):
        """
        Call Google Safe Browsing API if api key is provided.
        Returns list of issue keys (e.g., ["google_safebrowsing:match"]) or API status indicators.
        """
        issues = []
        if not self.google_api_key:
            return issues
        try:
            payload = {
                "client": {"clientId": "cybersentinel", "clientVersion": "1.0"},
                "threatInfo": {
                    "threatTypes": ["MALWARE", "SOCIAL_ENGINEERING", "UNWANTED_SOFTWARE", "POTENTIALLY_HARMFUL_APPLICATION"],
                    "platformTypes": ["ANY_PLATFORM"],
                    "threatEntryTypes": ["URL"],
                    "threatEntries": [{"url": url}]
                }
            }
            api_url = self.SAFE_BROWSING_API.format(api_key=self.google_api_key)
            r = self.session.post(api_url, json=payload, timeout=10)
            if r.status_code == 200:
                j = r.json()
                if j and "matches" in j:
                    issues.append("google_safebrowsing:match")
            else:
                # non-200 - surface the HTTP status for debugging (low weight)
                issues.append(f"gsb_api_status:{r.status_code}")
        except Exception as e:
            issues.append(f"gsb_api_error:{str(e)}")
        return issues

    def _compute_verdict(self, result: dict):
        """
        Compute final verdict string and top human-readable reasons based on result['explain'] weights
        and presence of high-confidence signals (Google SB).
        Returns: (verdict_str, top_reasons_list, reason_summary)
        """
        explain = result.get("explain", {})
        issues = result.get("issues", [])

        # Immediate high-confidence check
        for it in issues:
            if it.startswith("google_safebrowsing:match"):
                # Highest confidence - malicious
                return "Malicious", ["Google Safe Browsing reported the URL as a threat."], "Google Safe Browsing flagged this URL as malicious."

        # Build sorted list of (issue, weight)
        sorted_items = sorted(explain.items(), key=lambda kv: kv[1], reverse=True)
        top = sorted_items[:3]

        # Convert issue keys into human-readable reason strings
        readable_reasons = []
        for key, weight in top:
            # split keys like "suspicious_token:login" into friendly text
            if key.startswith("suspicious_token:"):
                token = key.split(":", 1)[1]
                readable_reasons.append(f"Suspicious keyword '{token}' found (weight={weight})")
            elif key.startswith("suspicious_tld:"):
                tld = key.split(":", 1)[1]
                readable_reasons.append(f"Suspicious top-level domain '.{tld}' (weight={weight})")
            elif key == "long_url":
                readable_reasons.append(f"URL is unusually long (weight={weight})")
            elif key == "ip_in_host":
                readable_reasons.append(f"IP address used as host (weight={weight})")
            elif key == "at_symbol_in_url":
                readable_reasons.append(f"URL contains '@' (used to obfuscate real host) (weight={weight})")
            elif key == "punycode_host":
                readable_reasons.append(f"Domain uses punycode (possible homograph attack) (weight={weight})")
            elif key == "unicode_in_host":
                readable_reasons.append(f"Unicode characters in domain (possible homograph) (weight={weight})")
            elif key == "not_https":
                readable_reasons.append(f"Site does not use HTTPS (weight={weight})")
            elif key == "ssl_error":
                readable_reasons.append(f"SSL certificate error detected (weight={weight})")
            elif key.startswith("gsb_api_status:"):
                readable_reasons.append(f"Google SB API returned status {key.split(':',1)[1]} (info)")
            elif key.startswith("gsb_api_error:"):
                readable_reasons.append(f"Google SB API error: {key.split(':',1)[1]}")
            elif key == "password_input_found":
                readable_reasons.append(f"Page contains password input fields (weight={weight})")
            elif key == "iframe_present":
                readable_reasons.append(f"Page contains iframes (weight={weight})")
            elif key.startswith("many_links"):
                readable_reasons.append(f"Page contains many links (weight={weight})")
            else:
                # generic fallback
                readable_reasons.append(f"{key} (weight={weight})")

        # Default readable reasons if none found
        if not readable_reasons and issues:
            readable_reasons = [str(x) for x in issues[:3]]

        # Decide verdict based on normalized score
        score = result.get("score", 0.0)
        if score >= 0.70:
            verdict = "Malicious"
        elif score >= 0.40:
            verdict = "Suspicious"
        else:
            verdict = "Likely safe"

        # Natural language reason summary (concise)
        if verdict == "Malicious":
            summary = "High-risk signals detected: " + "; ".join(readable_reasons[:3])
        elif verdict == "Suspicious":
            summary = "Potentially suspicious: " + "; ".join(readable_reasons[:3])
        else:
            summary = "No strong phishing signals detected."

        return verdict, readable_reasons, summary

    def check_url(self, url: str, do_content_check=False, do_gsb_check=True):
        """
        Run checks and return enriched result dict:
        {
          url, valid_url (bool), score (0..1),
          issues (list), explain (dict issue->weight),
          verdict (str), top_reasons (list[str]), reason_summary (str)
        }
        """
        result = {"url": url, "valid_url": True, "issues": [], "explain": {}, "score": 0.0}

        # validate syntactic URL
        try:
            if not self.validators.url(url):
                result["valid_url"] = False
                result["issues"].append("invalid_url")
                result["explain"]["invalid_url"] = 10.0
                # immediate malicious verdict for invalid URLs
                result["score"] = 1.0
                result["verdict"] = "Malicious"
                result["top_reasons"] = ["URL is not syntactically valid."]
                result["reason_summary"] = "Provided value is not a valid URL."
                return result
        except Exception:
            # validators might throw unexpectedly; fallback to marking invalid
            result["valid_url"] = False
            result["issues"].append("invalid_url")
            result["explain"]["invalid_url"] = 10.0
            result["score"] = 1.0
            result["verdict"] = "Malicious"
            result["top_reasons"] = ["URL is not syntactically valid."]
            result["reason_summary"] = "Provided value is not a valid URL."
            return result

        # Lexical checks
        lex_issues = self._lexical_checks(url)
        for it in lex_issues:
            result["issues"].append(it)
            result["explain"][it] = result["explain"].get(it, 0.0) + self.WEIGHTS["lexical_default"]

        # SSL checks
        ssl_issues = self._ssl_check(url)
        for it in ssl_issues:
            result["issues"].append(it)
            result["explain"][it] = result["explain"].get(it, 0.0) + self.WEIGHTS["ssl_issue"]

        # Content checks 
        if do_content_check:
            content_issues = self._content_checks(url)
            for it in content_issues:
                result["issues"].append(it)
                result["explain"][it] = result["explain"].get(it, 0.0) + self.WEIGHTS["content_issue"]

        # Google Safe Browsing
        if do_gsb_check:
            gsb_issues = self._safe_browsing_check(url)
            for it in gsb_issues:
                result["issues"].append(it)
                # if it's a match give it a high weight
                if it == "google_safebrowsing:match":
                    result["explain"][it] = result["explain"].get(it, 0.0) + self.WEIGHTS["gsb_match"]
                else:
                    # API status or error get smaller weight
                    result["explain"][it] = result["explain"].get(it, 0.0) + 0.5

        # compute numeric score (sum of explain weights normalized)
        total_weight = sum(result["explain"].values()) if result["explain"] else 0.0
        # normalization factor: tuned so score ~1 when many high-weight issues exist
        norm = 6.0
        score = min(1.0, total_weight / norm)
        result["score"] = score

        # compute final verdict and readable reasons
        verdict, readable_reasons, summary = self._compute_verdict(result)
        result["verdict"] = verdict
        result["top_reasons"] = readable_reasons
        result["reason_summary"] = summary

        return result


GSB_KEY = os.environ.get("AIzaSyCxu6aeTx1C9tIDRhd6is9M_QziYU5oUSI")
pd = PhishingDetector(google_api_key=GSB_KEY)

# ---------- CLI helpers ----------
def clear_screen():
    os.system("clear" if os.name == "posix" else "cls")

def pause():
    input("\nPress Enter to continue...")

def get_choice(prompt, choices):
    while True:
        val = input(prompt).strip()
        if val in choices:
            return val
        print("Invalid choice, try again.")

# ---------- Login / Signup / Main menus ----------
def signup_flow():
    clear_screen()
    print("=== Sign up ===")
    username = input("Choose a username: ").strip()
    if not username:
        print("Username required."); pause(); return
    if user_exists(username):
        print("Username already exists."); pause(); return
    pw = getpass.getpass("Choose a master password (hidden): ")
    pw2 = getpass.getpass("Confirm master password: ")
    if pw != pw2:
        print("Passwords do not match."); pause(); return
    ok, msg = create_user(username, pw)
    print(msg); pause()

def login_flow():
    clear_screen()
    print("=== Log in ===")
    username = input("Username: ").strip()
    if not user_exists(username):
        print("User does not exist."); pause(); return None, None
    pw = getpass.getpass("Master password: ")
    ok, msg = authenticate_user(username, pw)
    if not ok:
        print(msg); pause(); return None, None
    # quick vault check (loads entries; harmless if empty)
    ok2, entries_or_err = load_entries(username, pw)
    if not ok2 and "missing" not in str(entries_or_err).lower():
        # warn but allow login
        print("Warning: could not load entries:", entries_or_err)
        print("You may continue; import or recreate entries if needed.")
        pause()
    return username, pw

def logged_in_menu(username: str, password: str):
    fw = FirewallManager()
    monitor = None

    while True:
        styled_header(f"CyberSentinel  —  {username}")
        # Main menu (styled)
        print(FG_WHITE + " 1) " + FG_CYAN + "Firewall manager" + RESET)
        print(FG_WHITE + " 2) " + FG_CYAN + "Password manager" + RESET)
        print(FG_WHITE + " 3) " + FG_CYAN + "Phishing Detector" + RESET)
        print(FG_WHITE + " 4) " + FG_CYAN + "Log out" + RESET)
        choice = get_choice(FG_BLUE + BOLD + "\nChoose [1-4]: " + RESET, ["1", "2", "3", "4"])

        # -----------------------
        # 1) Firewall manager
        # -----------------------
        if choice == "1":
            while True:
                styled_section("Firewall Manager", emoji=EMOJI_SHIELD)
                color_line("Backend detected", fw.backend or "none (nft/ufw/iptables not found)")
                print()

                # show OS-appropriate labels but keep numeric mapping for handlers
                if fw.backend == "ufw":
                    print(FG_WHITE + " 1) " + FG_CYAN + "Enable firewall (ufw)" + RESET)
                    print(FG_WHITE + " 2) " + FG_CYAN + "Disable firewall (ufw)" + RESET)
                else:
                    if fw.backend == "windows":
                        print(FG_WHITE + " 1) " + FG_CYAN + "Enable firewall (Windows)" + RESET)
                        print(FG_WHITE + " 2) " + FG_CYAN + "Disable firewall (Windows)" + RESET)
                    elif fw.backend == "macos":
                        print(FG_WHITE + " 1) " + FG_CYAN + "Enable firewall (macOS pf)" + RESET)
                        print(FG_WHITE + " 2) " + FG_CYAN + "Disable firewall (macOS pf)" + RESET)
                    else:
                        print(FG_WHITE + " 1) " + FG_YELLOW + "Enable firewall (not supported on this OS)" + RESET)
                        print(FG_WHITE + " 2) " + FG_YELLOW + "Disable firewall (not supported on this OS)" + RESET)

                print(FG_WHITE + " 3) " + FG_CYAN + "Show firewall status" + RESET)
                print(FG_WHITE + " 4) " + FG_CYAN + "List firewall rules" + RESET)
                print(FG_WHITE + " 5) " + FG_CYAN + "Block an IP" + RESET)
                print(FG_WHITE + " 6) " + FG_CYAN + "Unblock an IP" + RESET)
                print(FG_WHITE + " 7) " + FG_CYAN + "Start traffic monitor (requires scapy)" + RESET)
                print(FG_WHITE + " 8) " + FG_CYAN + "Stop traffic monitor" + RESET)
                print(FG_WHITE + " 9) " + FG_CYAN + "Back" + RESET)
                sub = get_choice(FG_BLUE + BOLD + "\nChoose [1-9]: " + RESET, [str(i) for i in range(1, 10)])

                # 1) Enable
                if sub == "1":
                    if fw.backend in ("windows", "ufw", "macos"):
                        if not require_root():
                            pause(); continue
                        print(FG_GREEN + "Enabling firewall..." + RESET)
                        out = fw.ufw_enable()
                        print(out); pause()
                    else:
                        print(FG_YELLOW + "Enable firewall not supported on this platform." + RESET)
                        pause(); continue

                # 2) Disable
                elif sub == "2":
                    if fw.backend in ("windows", "ufw", "macos"):
                        if not require_root():
                            pause(); continue
                        print(FG_YELLOW + "Disabling firewall..." + RESET)
                        out = fw.ufw_disable()
                        print(out); pause()
                    else:
                        print(FG_YELLOW + "Disable firewall not supported on this platform." + RESET)
                        pause(); continue

                # 3) Show status
                elif sub == "3":
                    print(FG_CYAN + "Firewall status:" + RESET)
                    try:
                        # ufw_status is mapped for windows/ufw/macos in FirewallManager
                        out = fw.ufw_status()
                    except Exception:
                        try:
                            out = fw.list_rules()
                        except Exception as e:
                            out = f"Error getting firewall status: {e}"
                    print(out); pause()

                # 4) List rules
                elif sub == "4":
                    print(FG_CYAN + "Listing rules..." + RESET)
                    try:
                        out = fw.list_rules()
                    except Exception as e:
                        out = f"Failed to list rules: {e}"
                    print(out); pause()

                # 5) Block IP
                elif sub == "5":
                    ip = input("Enter IP to block: ").strip()
                    if not ip:
                        print(FG_YELLOW + "No IP entered." + RESET); pause(); continue
                    if not require_root():
                        pause(); continue
                    reason = input("Optional reason/comment for block (press Enter to skip): ").strip() or "blocked_by_cybersentinel"
                    print(FG_RED + f"Blocking {ip}..." + RESET)
                    try:
                        out = fw.block_ip(ip, reason)
                    except Exception as e:
                        out = f"Block failed: {e}"
                    print(out); pause()

                # 6) Unblock IP
                elif sub == "6":
                    ip = input("Enter IP to unblock: ").strip()
                    if not ip:
                        print(FG_YELLOW + "No IP entered." + RESET); pause(); continue
                    if not require_root():
                        pause(); continue
                    print(FG_GREEN + f"Unblocking {ip}..." + RESET)
                    try:
                        out = fw.unblock_ip(ip)
                    except Exception as e:
                        out = f"Unblock failed: {e}"
                    print(out); pause()

                # 7) Start traffic monitor
                elif sub == "7":
                    if not SCAPY_ASYNC:
                        print(FG_YELLOW + "scapy AsyncSniffer not available. Install with: python -m pip install scapy" + RESET); pause(); continue
                    if monitor and getattr(monitor, "running", False):
                        print(FG_YELLOW + "Monitor already running." + RESET); pause(); continue
                    iface = input("Interface to sniff on (leave blank for default): ").strip() or None
                    try:
                        monitor = SimpleMonitor(iface=iface)
                    except Exception as e:
                        print(FG_RED + "Failed to create monitor: " + str(e) + RESET); pause(); continue
                    try:
                        print(monitor.start())
                    except Exception as e:
                        print(FG_RED + "Failed to start monitor: " + str(e) + RESET)
                    pause()

                # 8) Stop traffic monitor
                elif sub == "8":
                    if monitor:
                        try:
                            print(monitor.stop())
                        except Exception as e:
                            print(FG_RED + "Failed to stop monitor: " + str(e) + RESET)
                    else:
                        print(FG_YELLOW + "Monitor not running." + RESET)
                    pause()

                # 9) Back
                elif sub == "9":
                    break

        # -----------------------
        # 2) Password manager
        # -----------------------
        elif choice == "2":
            styled_section("Password Vault", emoji=EMOJI_LOCK)
            password_manager_cli(username, password)

        # -----------------------
        # 3) Phishing Detector
        # -----------------------
        elif choice == "3":
            # phishing detector loop
            while True:
                styled_section("Phishing Detector", emoji=EMOJI_MAG)
                print(FG_WHITE + " 1) " + FG_CYAN + "Check a URL (with full analysis)" + RESET)
                print(FG_WHITE + " 2) " + FG_CYAN + "View saved suspicious/malicious URLs" + RESET)
                print(FG_WHITE + " 3) " + FG_CYAN + "Back" + RESET)
                sub = get_choice(FG_BLUE + BOLD + "\nChoose [1-3]: " + RESET, ["1", "2", "3"])

                # 1) Full analysis (content fetch + GSB)
                if sub == "1":
                    url = input("URL to check: ").strip()
                    if not url:
                        print(FG_YELLOW + "No URL entered." + RESET); pause(); continue

                    try:
                        res = pd.check_url(url, do_content_check=True, do_gsb_check=True)
                    except Exception as e:
                        print(FG_RED + "Detection failed: " + str(e) + RESET); pause(); continue

                    # Header + verdict banner
                    print()
                    print(FG_WHITE + BOLD + "Result:" + RESET)
                    print(" URL:", FG_CYAN + res.get("url", "N/A") + RESET)
                    print(" Valid URL:", FG_CYAN + str(res.get("valid_url", False)) + RESET)
                    print(" Score (0-1):", FG_MAGENTA + str(round(res.get("score", 0.0), 3)) + RESET)
                    print("\n Final Verdict:", verdict_banner(res.get("verdict", "Unknown")))
                    print(FG_WHITE + " Why: " + RESET + res.get("reason_summary", "No summary available"))

                    # Top reasons
                    if res.get("top_reasons"):
                        print()
                        print(FG_GREEN + BOLD + "Key Reasons:" + RESET)
                        for r in res.get("top_reasons", []):
                            print("  " + FG_YELLOW + "• " + RESET + r)

                    # Technical signals
                    if res.get("issues"):
                        print()
                        print(DIM + "Signals detected: " + RESET)
                        print(DIM + ", ".join(res.get("issues", [])) + RESET)

                    # Ask to save (if suspicious or malicious)
                    if res.get("verdict") in ("Malicious", "Suspicious"):
                        save_choice = get_choice(FG_BLUE + "\nSave this report to your DB? (y/n): " + RESET, ["y", "n"])
                        if save_choice == "y":
                            # resolve host/ip (best-effort)
                            host = None; ip = None
                            try:
                                host = urlparse(res.get("url")).hostname
                                if host:
                                    try:
                                        ip = socket.gethostbyname(host)
                                    except Exception:
                                        ip = None
                            except Exception:
                                pass
                            try:
                                rid = phish_save_report(
                                    url=res.get("url"),
                                    verdict=res.get("verdict"),
                                    score=res.get("score", 0.0),
                                    issues=res.get("issues", []),
                                    explain=res.get("explain", {}),
                                    reason_summary=res.get("reason_summary", ""),
                                    host=host,
                                    ip=ip
                                )
                                print(FG_GREEN + EMOJI_DB + " Saved report id: " + str(rid) + RESET)
                            except Exception as e:
                                print(FG_RED + "Failed to save report: " + str(e) + RESET)
                        else:
                            print(FG_YELLOW + "Not saved." + RESET)
                    else:
                        print(FG_GREEN + "URL considered 'Likely safe' — not offering save." + RESET)

                    pause()

                # 2) View saved reports
                elif sub == "2":
                    clear_screen()
                    styled_section("Saved Phishing Reports", emoji=EMOJI_DB)
                    print("1) All")
                    print("2) Malicious")
                    print("3) Suspicious")
                    print("4) Back")
                    fchoice = get_choice(FG_BLUE + "Choose [1-4]: " + RESET, ["1","2","3","4"])
                    if fchoice == "4":
                        continue
                    filter_map = {"1": None, "2": "Malicious", "3": "Suspicious"}
                    filter_verdict = filter_map[fchoice]

                    total = phish_count(filter_verdict)
                    print(FG_WHITE + f"\nTotal saved reports matching filter: {total}" + RESET)

                    # if more than 5, offer search
                    if total > 5:
                        if get_choice(FG_BLUE + "Search by URL substring? (y/n): " + RESET, ["y","n"]) == "y":
                            substring = input("Enter substring to search: ").strip()
                            rows = phish_search(substring, filter_verdict)
                        else:
                            rows = phish_list(filter_verdict, limit=200)
                    else:
                        rows = phish_list(filter_verdict, limit=200)

                    if not rows:
                        print(FG_YELLOW + "No saved reports found." + RESET)
                        pause(); continue

                    # show list
                    for r in rows:
                        rid, url_r, host_r, ip_r, verdict_r, score_r, created_r = r
                        preview = url_r if len(url_r) <= 80 else url_r[:77] + "..."
                        color = FG_RED if verdict_r == "Malicious" else (FG_YELLOW if verdict_r == "Suspicious" else FG_GREEN)
                        print(f"{BOLD}{rid:4d}{RESET} | {color}{verdict_r:9s}{RESET} | {FG_MAGENTA}score={round(score_r,3)}{RESET} | {preview}")

                    sel = input(FG_CYAN + "\nEnter report id to view details (or press Enter to go back): " + RESET).strip()
                    if not sel:
                        continue
                    if not sel.isdigit():
                        print(FG_YELLOW + "Invalid id." + RESET); pause(); continue
                    sel_id = int(sel)
                    report = phish_get_report(sel_id)
                    if not report:
                        print(FG_YELLOW + "Report not found." + RESET); pause(); continue

                    # detailed view (pretty)
                    clear_screen()
                    styled_section("Report Details", emoji=EMOJI_STAR)
                    color_line("ID", str(report["id"]), key_color=FG_CYAN)
                    color_line("URL", report["url"], key_color=FG_CYAN, value_color=FG_WHITE)
                    color_line("Host", report["host"] or "N/A", key_color=FG_CYAN)
                    color_line("IP", report["ip"] or "N/A", key_color=FG_CYAN)
                    color_line("Verdict", report["verdict"], key_color=FG_CYAN)
                    color_line("Score", str(report["score"]), key_color=FG_CYAN)
                    color_line("Saved at", report["created"], key_color=FG_CYAN)
                    print()
                    print(FG_GREEN + "Reason summary:" + RESET)
                    print(" ", report.get("reason_summary", ""))
                    print()
                    print(FG_YELLOW + "Top issues:" + RESET)
                    for it in report.get("issues", []):
                        print("  -", it)
                    print()
                    print(DIM + "Explain (weights):" + RESET)
                    for k, v in report.get("explain", {}).items():
                        print(f"  {k}: {v}")
                    pause()

                else:
                    break

        # -----------------------
        # 4) Log out
        # -----------------------
        elif choice == "4":
            print(FG_CYAN + EMOJI_BACK + " Logging out..." + RESET)
            time.sleep(0.3)
            break


def main_entry():
    """
    Styled entry point for CyberSentinel CLI.
    Relies on styling helpers:
      styled_header, styled_section, color_line, EMOJI_* constants, verdict_banner, etc.
    And core helpers:
      clear_screen(), get_choice(), login_flow(), signup_flow(), logged_in_menu()
    """

    # Show dependency warning (styled)
    if not CRYPTO_AVAILABLE:
        styled_header("CyberSentinel — Startup")
        styled_section("Missing dependency", emoji=EMOJI_LOCK)
        print(FG_YELLOW + BOLD + EMOJI_WARN + "  cryptography not installed" + RESET)
        print(FG_WHITE + "  The 'cryptography' package is required for encrypted password storage.")
        print(FG_WHITE + "  Install inside your virtual environment with:")
        print(FG_CYAN + "    python -m pip install cryptography" + RESET)
        print()
        print(FG_BLUE + "  Note: firewall features will still work without cryptography." + RESET)
        print()
        input(FG_BLUE + "Press Enter to continue to CyberSentinel…" + RESET)

    # Main loop
    while True:
        styled_header("CyberSentinel")
        styled_section("Welcome", emoji=EMOJI_SHIELD)
        print(FG_WHITE + "  " + FG_CYAN + "1)" + FG_WHITE + " " + BOLD + "Log in" + RESET)
        print(FG_WHITE + "  " + FG_CYAN + "2)" + FG_WHITE + " " + BOLD + "Sign up" + RESET)
        print(FG_WHITE + "  " + FG_CYAN + "3)" + FG_WHITE + " " + BOLD + "Exit" + RESET)

        print()
        print(DIM + "Tip: Use a virtualenv and run the app from your project folder." + RESET)
        choice = get_choice(FG_BLUE + BOLD + "\nChoose [1-3]: " + RESET, ["1", "2", "3"])

        if choice == "1":
            # Log in flow
            styled_section("Sign in", emoji=EMOJI_LOCK)
            username, password = login_flow()
            if username:
                # on successful login, go to main menu
                logged_in_menu(username, password)
            else:
                print(FG_YELLOW + "Login cancelled or failed." + RESET)
                pause()

        elif choice == "2":
            # Sign up flow
            styled_section("Create account", emoji=EMOJI_STAR)
            signup_flow()
            print(FG_GREEN + "Account setup complete (if no errors)." + RESET)
            pause()

        elif choice == "3":
            # Exit nicely
            styled_header("Goodbye")
            print(FG_CYAN + EMOJI_BACK + " Thanks for using CyberSentinel — stay safe!" + RESET)
            print()
            break

        # small pause before redrawing main menu
        time.sleep(0.08)

if __name__ == "__main__":
    try:
        main_entry()
    except KeyboardInterrupt:
        print("\nInterrupted by user. Exiting.")
        sys.exit(0)

