#!/usr/bin/env python3
from __future__ import annotations

import base64
import csv
import json
import os
import queue
import re
import select
import shlex
import signal
import socket
import subprocess
import threading
import time
import urllib.parse
import urllib.request
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
import concurrent.futures
import sys
import uuid

# Prefer IPv4 resolution to avoid slow AAAA DNS timeouts (e.g. in WSL),
# but fall back to system default (IPv6) if IPv4 resolution fails.
# This ensures pure-IPv6 VPS (with NAT64/clatd) can still function.
_orig_getaddrinfo = socket.getaddrinfo
def _ipv4_getaddrinfo(host, port, family=0, type=0, proto=0, flags=0):
    if family == 0:
        if isinstance(host, str) and ":" in host:
            return _orig_getaddrinfo(host, port, socket.AF_INET6, type, proto, flags)
        # Try IPv4 first for speed; fall back to system default (allows IPv6/NAT64)
        try:
            results = _orig_getaddrinfo(host, port, socket.AF_INET, type, proto, flags)
            if results:
                return results
        except socket.gaierror:
            pass
        return _orig_getaddrinfo(host, port, 0, type, proto, flags)
    return _orig_getaddrinfo(host, port, family, type, proto, flags)
socket.getaddrinfo = _ipv4_getaddrinfo

class DualStackHTTPServer(ThreadingHTTPServer):
    def __init__(self, server_address, RequestHandlerClass, bind_and_activate=True):
        host, port = server_address
        if ":" in host or host == "":
            self.address_family = socket.AF_INET6
        else:
            self.address_family = socket.AF_INET
        
        try:
            super().__init__(server_address, RequestHandlerClass, bind_and_activate)
        except OSError as e:
            if self.address_family == socket.AF_INET6:
                fallback_host = "0.0.0.0" if host in ("::", "") else "127.0.0.1"
                print(f"[警告] 绑定 Web 管理后台 IPv6 {host}:{port} 失败 ({e})，正在尝试回退至 IPv4 {fallback_host} ...", flush=True)
                # 关闭第一次失败时可能已创建的 socket
                try:
                    self.socket.close()
                except Exception:
                    pass
                self.address_family = socket.AF_INET
                super().__init__((fallback_host, port), RequestHandlerClass, bind_and_activate)
            else:
                raise e

    def server_bind(self):
        if self.address_family == socket.AF_INET6:
            try:
                self.socket.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 0)
            except OSError:
                pass
        super().server_bind()

import vpn_utils
import proxy_server

def env_int(name: str, default: int, min_value: int | None = None, max_value: int | None = None) -> int:
    raw = os.environ.get(name)
    try:
        value = int(raw) if raw not in (None, "") else default
    except (TypeError, ValueError):
        print(f"[配置警告] 环境变量 {name}={raw!r} 不是有效整数，使用默认值 {default}", flush=True)
        value = default
    if min_value is not None and value < min_value:
        print(f"[配置警告] 环境变量 {name}={value} 小于允许值 {min_value}，使用默认值 {default}", flush=True)
        return default
    if max_value is not None and value > max_value:
        print(f"[配置警告] 环境变量 {name}={value} 大于允许值 {max_value}，使用默认值 {default}", flush=True)
        return default
    return value

def bounded_int(value: Any, default: int, min_value: int | None = None, max_value: int | None = None) -> int:
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        return default
    if min_value is not None and parsed < min_value:
        return default
    if max_value is not None and parsed > max_value:
        return default
    return parsed

API_URL = "https://www.vpngate.net/api/iphone/"
FETCH_INTERVAL_SECONDS = env_int("FETCH_INTERVAL_SECONDS", 1260, 1)
CHECK_INTERVAL_SECONDS = env_int("CHECK_INTERVAL_SECONDS", 1260, 1)
TARGET_VALID_NODES = env_int("TARGET_VALID_NODES", 3, 1)
MAX_SCAN_ROWS = env_int("MAX_SCAN_ROWS", 300, 1)
OPENVPN_TEST_TIMEOUT_SECONDS = env_int("OPENVPN_TEST_TIMEOUT_SECONDS", 35, 1)
OPENVPN_CMD = os.environ.get("OPENVPN_CMD", "openvpn")
OPENVPN_AUTH_USER = os.environ.get("OPENVPN_AUTH_USER", "vpn")
OPENVPN_AUTH_PASS = os.environ.get("OPENVPN_AUTH_PASS", "vpn")
LOCAL_PROXY_HOST = os.environ.get("LOCAL_PROXY_HOST", "127.0.0.1")
LOCAL_PROXY_PORT = env_int("LOCAL_PROXY_PORT", 7928, 1, 65535)
UI_HOST = os.environ.get("UI_HOST", "::")
UI_PORT = env_int("UI_PORT", 8787, 1, 65535)
INVALID_BACKOFF_SECONDS = env_int("INVALID_BACKOFF_SECONDS", 30 * 60, 1)

ROOT_DIR = Path(sys.executable).resolve().parent if globals().get("__compiled__") else Path(__file__).resolve().parent
DATA_DIR = Path(os.environ["VPNGATE_DATA_DIR"]).resolve() if os.environ.get("VPNGATE_DATA_DIR") else ROOT_DIR / "vpngate_data"
CONFIG_DIR = DATA_DIR / "configs"
NODES_FILE = DATA_DIR / "nodes.json"
STATE_FILE = DATA_DIR / "state.json"
AUTH_FILE = DATA_DIR / "vpngate_auth.txt"
UPSTREAM_PROXY_AUTH_FILE = DATA_DIR / "upstream_proxy_auth.txt"
BLACKLIST_FILE = DATA_DIR / "blacklist.json"

lock = threading.RLock()
maintenance_lock = threading.Lock()
active_sessions: dict[str, float] = {}
active_openvpn_process: subprocess.Popen[str] | None = None
active_openvpn_node_id = ""
is_connecting = True
last_active_ping_time = 0.0
last_active_latency = 0
MAX_CHANNELS = 6
CHANNEL_BASE_PORT = 7928
ch_processes = [None] * MAX_CHANNELS
ch_node_ids = [''] * MAX_CHANNELS
ch_connecting = [False] * MAX_CHANNELS
ch_tun_ids = [-1] * MAX_CHANNELS

last_collector_heartbeat = 0.0
last_checker_heartbeat = 0.0
last_pinger_heartbeat = 0.0
server_start_time = time.time()

def ensure_dirs() -> None:
    DATA_DIR.mkdir(exist_ok=True, parents=True)
    CONFIG_DIR.mkdir(exist_ok=True, parents=True)
    if not AUTH_FILE.exists():
        AUTH_FILE.write_text(f"{OPENVPN_AUTH_USER}\n{OPENVPN_AUTH_PASS}\n", encoding="utf-8")
        try:
            AUTH_FILE.chmod(0o600)
        except OSError:
            pass

def upstream_proxy_auth_file() -> str | None:
    username, password = vpn_utils.get_upstream_proxy_auth()
    if username is None:
        return None
    try:
        DATA_DIR.mkdir(exist_ok=True, parents=True)
        UPSTREAM_PROXY_AUTH_FILE.write_text(f"{username}\n{password or ''}\n", encoding="utf-8")
        try:
            UPSTREAM_PROXY_AUTH_FILE.chmod(0o600)
        except OSError:
            pass
        return str(UPSTREAM_PROXY_AUTH_FILE)
    except Exception as exc:
        print(f"[上游代理认证] 写入认证文件失败: {exc}", flush=True)
        return None

def write_json(path: Path, data: Any) -> None:
    with lock:
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        tmp.replace(path)

def read_json(path: Path, default: Any) -> Any:
    with lock:
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return default

import hashlib
import random

def generate_random_password() -> str:
    import string
    chars = string.ascii_letters + string.digits
    while True:
        pwd = "".join(random.choices(chars, k=12))
        # Ensure it contains at least one lowercase, one uppercase, and one digit
        has_lower = any(c.islower() for c in pwd)
        has_upper = any(c.isupper() for c in pwd)
        has_digit = any(c.isdigit() for c in pwd)
        if has_lower and has_upper and has_digit:
            return pwd

def generate_random_username() -> str:
    import string
    chars = string.ascii_letters + string.digits
    while True:
        uname = "".join(random.choices(chars, k=12))
        # Ensure it starts with a letter and contains at least one lowercase, one uppercase, and one digit
        if uname[0].isalpha():
            has_lower = any(c.islower() for c in uname)
            has_upper = any(c.isupper() for c in uname)
            has_digit = any(c.isdigit() for c in uname)
            if has_lower and has_upper and has_digit:
                return uname

def load_ui_config() -> dict[str, Any]:
    with lock:
        auth_file = DATA_DIR / "ui_auth.json"
        config = {
            "username": "",
            "secret_path": "EJsW2EeBo9lY",
            "password": "",
            "host": UI_HOST,
            "port": UI_PORT,
            "proxy_port": LOCAL_PROXY_PORT,
            "routing_mode": "auto",
            "force_country": "",
            "routing_ip_type": "all",
            "connection_enabled": True,
            "fixed_node_id": "",
            "favorite_node_ids": [],
            "fav_fail_fallback": True
        }
        updated = False
        if auth_file.exists():
            try:
                data = json.loads(auth_file.read_text(encoding="utf-8"))
                for key, val in data.items():
                    config[key] = val
                for key in ["host", "port", "proxy_port", "routing_mode", "force_country", "routing_ip_type", "connection_enabled", "fixed_node_id", "favorite_node_ids", "fav_fail_fallback"]:
                    if key not in data:
                        updated = True
            except Exception:
                pass
        
        if not config.get("username"):
            config["username"] = generate_random_username()
            updated = True
            
        if not config.get("password"):
            config["password"] = generate_random_password()
            updated = True

        normalized_port = bounded_int(config.get("port"), UI_PORT, 1, 65535)
        if normalized_port != config.get("port"):
            config["port"] = normalized_port
            updated = True

        normalized_proxy_port = bounded_int(config.get("proxy_port"), LOCAL_PROXY_PORT, 1024, 65535)
        if normalized_proxy_port == normalized_port:
            fallback_proxy_port = LOCAL_PROXY_PORT if LOCAL_PROXY_PORT != normalized_port else 7928
            if fallback_proxy_port == normalized_port:
                fallback_proxy_port = 7929
            normalized_proxy_port = fallback_proxy_port
        if normalized_proxy_port != config.get("proxy_port"):
            config["proxy_port"] = normalized_proxy_port
            updated = True
            
        if not auth_file.exists() or updated:
            try:
                DATA_DIR.mkdir(exist_ok=True, parents=True)
                auth_file.write_text(json.dumps(config, ensure_ascii=False, indent=2), encoding="utf-8")
            except Exception:
                pass
                
        return config

# 初始化时优先从 ui_auth.json 加载保存的代理出站端口和网页端口配置以覆盖环境变量
try:
    _init_cfg = load_ui_config()
    if "proxy_port" in _init_cfg:
        LOCAL_PROXY_PORT = bounded_int(_init_cfg["proxy_port"], LOCAL_PROXY_PORT, 1024, 65535)
    if "port" in _init_cfg:
        UI_PORT = bounded_int(_init_cfg["port"], UI_PORT, 1, 65535)
    if "host" in _init_cfg:
        UI_HOST = _init_cfg["host"]
except Exception:
    pass

def get_session_token(password: str, username: str = "admin") -> str:
    salt = "aimilivpn_secure_salt_2026"
    return hashlib.sha256((username + ":" + password + salt).encode("utf-8")).hexdigest()

_last_cleanup_time = 0.0

def cleanup_old_logs(logs_dir: Path) -> None:
    global _last_cleanup_time
    now = time.time()
    with lock:
        if now - _last_cleanup_time < 3600:
            return
        _last_cleanup_time = now
    try:
        three_days_sec = 3 * 24 * 60 * 60
        for path in logs_dir.glob("*.json"):
            match = re.match(r"^(\d{4}-\d{2}-\d{2})\.json$", path.name)
            if match:
                date_str = match.group(1)
                try:
                    file_time = time.mktime(time.strptime(date_str, "%Y-%m-%d"))
                    today_str = time.strftime("%Y-%m-%d", time.localtime())
                    today_time = time.mktime(time.strptime(today_str, "%Y-%m-%d"))
                    if today_time - file_time >= three_days_sec:
                        with lock:
                            path.unlink()
                        print(f"[清理] 已删除3天前的旧日志文件: {path.name}", flush=True)
                except Exception:
                    if now - path.stat().st_mtime > three_days_sec:
                        with lock:
                            path.unlink()
    except Exception as e:
        print(f"[清理错误] 清理旧日志失败: {e}", flush=True)

def log_to_json(level: str, module: str, message: str) -> None:
    try:
        logs_dir = DATA_DIR / "logs"
        logs_dir.mkdir(exist_ok=True, parents=True)
        date_str = time.strftime("%Y-%m-%d", time.localtime())
        log_file = logs_dir / f"{date_str}.json"
        entry = {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S", time.localtime()),
            "level": level,
            "module": module,
            "message": message
        }
        with lock:
            with open(log_file, "a", encoding="utf-8") as f:
                f.write(json.dumps(entry, ensure_ascii=False) + "\n")
        cleanup_old_logs(logs_dir)
    except Exception as e:
        print(f"[Log Error] Failed to write JSON log: {e}", flush=True)

def set_state(**updates: Any) -> None:
    state = get_state()
    state.update(updates)
    write_json(STATE_FILE, state)

def read_nodes() -> list[dict[str, Any]]:
    raw = read_json(NODES_FILE, [])
    if not isinstance(raw, list):
        return []
    return [item for item in raw if isinstance(item, dict)]

def get_state() -> dict[str, Any]:
    global active_openvpn_node_id, is_connecting
    state = read_json(STATE_FILE, {})
    state.pop("password", None)
    state["active_openvpn_node_id"] = active_openvpn_node_id
    state["is_connecting"] = is_connecting
    state.setdefault("api_url", API_URL)
    state.setdefault("target_valid_nodes", TARGET_VALID_NODES)
    state.setdefault("fetch_interval_seconds", FETCH_INTERVAL_SECONDS)
    state.setdefault("check_interval_seconds", CHECK_INTERVAL_SECONDS)
    _proxy_display = f"[{LOCAL_PROXY_HOST}]" if ":" in LOCAL_PROXY_HOST else LOCAL_PROXY_HOST
    state["local_proxy"] = f"http://{_proxy_display}:{LOCAL_PROXY_PORT}"
    state.setdefault("last_fetch_status", "not_started")
    state.setdefault("last_check_message", "")
    state.setdefault("blacklisted_nodes", 0)
    
    # Pre-populate settings inputs in UI
    ui_cfg = load_ui_config()
    state["username"] = ui_cfg.get("username", "admin")
    state["port"] = ui_cfg.get("port", 8787)
    state["secret_path"] = ui_cfg.get("secret_path", "EJsW2EeBo9lY")
    state["password_set"] = bool(ui_cfg.get("password"))
    state["domain"] = ui_cfg.get("domain", "")
    state["https"] = ui_cfg.get("https", False)
    state["cert_path"] = ui_cfg.get("cert_path", "")
    state["key_path"] = ui_cfg.get("key_path", "")
    state["proxy_port"] = ui_cfg.get("proxy_port", 7928)
    state["channel_ports"] = [CHANNEL_BASE_PORT + i for i in range(MAX_CHANNELS)]
    state["routing_mode"] = ui_cfg.get("routing_mode", "auto")
    state["force_country"] = ui_cfg.get("force_country", "")
    state["routing_ip_type"] = ui_cfg.get("routing_ip_type", "all")
    state["connection_enabled"] = ui_cfg.get("connection_enabled", True)
    state["fixed_node_id"] = ui_cfg.get("fixed_node_id", "")
    state["favorite_node_ids"] = ui_cfg.get("favorite_node_ids", [])
    state["fav_fail_fallback"] = ui_cfg.get("fav_fail_fallback", True)
    
    return state

def safe_name(value: str) -> str:
    value = re.sub(r"[^A-Za-z0-9_.-]+", "_", value.strip())
    return value.strip("._") or "node"

def clear_active_connection_state(message: str) -> None:
    global active_openvpn_process, active_openvpn_node_id
    stop_process(active_openvpn_process)
    active_openvpn_process = None
    active_openvpn_node_id = ""
    with lock:
        nodes = read_nodes()
        for item in nodes:
            item["active"] = False
        write_json(NODES_FILE, nodes)
    set_state(
        active_openvpn_node_id="",
        is_connecting=False,
        active_node_latency="无活动连接",
        last_check_message=message,
    )

def parse_int(value: Any) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0

def proxy_basic_auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Proxy-Authorization: Basic {token}\r\n"

def recv_exact_from_socket(sock: socket.socket, size: int) -> bytes:
    data = b""
    while len(data) < size:
        chunk = sock.recv(size - len(data))
        if not chunk:
            raise RuntimeError("Unexpected EOF while reading proxy response")
        data += chunk
    return data

def read_http_response_head(sock: socket.socket, limit: int = 65536) -> bytes:
    data = b""
    while b"\r\n\r\n" not in data:
        chunk = sock.recv(4096)
        if not chunk:
            break
        data += chunk
        if len(data) > limit:
            raise RuntimeError("Proxy response header too large")
    if b"\r\n\r\n" not in data:
        raise RuntimeError("Incomplete HTTP proxy response header")
    return data

def socks5_address_bytes(host: str) -> tuple[int, bytes]:
    try:
        return 1, socket.inet_aton(host)
    except OSError:
        pass
    try:
        return 4, socket.inet_pton(socket.AF_INET6, host)
    except OSError:
        pass
    host_bytes = host.encode("idna")
    if len(host_bytes) > 255:
        raise RuntimeError("SOCKS5 target host name is too long")
    return 3, bytes([len(host_bytes)]) + host_bytes

def read_socks5_connect_reply(sock: socket.socket) -> None:
    header = recv_exact_from_socket(sock, 4)
    if header[0] != 5:
        raise RuntimeError("Invalid SOCKS5 reply version")
    atyp = header[3]
    if atyp == 1:
        recv_exact_from_socket(sock, 4)
    elif atyp == 3:
        domain_len = recv_exact_from_socket(sock, 1)[0]
        recv_exact_from_socket(sock, domain_len)
    elif atyp == 4:
        recv_exact_from_socket(sock, 16)
    else:
        raise RuntimeError(f"Invalid SOCKS5 reply address type: {atyp}")
    recv_exact_from_socket(sock, 2)
    if header[1] != 0:
        raise RuntimeError(f"SOCKS5 connection request rejected, code={header[1]}")

def format_host_port(host: str, port: int) -> str:
    return f"[{host}]:{port}" if ":" in host and not host.startswith("[") else f"{host}:{port}"

def fetch_api_text_via_proxy(url: str, ptype: str, phost: str, pport: int, use_ssl_verify: bool = True) -> str:
    import socket
    import ssl
    import urllib.parse

    parsed = urllib.parse.urlsplit(url)
    domain = parsed.hostname or "www.vpngate.net"
    port = parsed.port or (443 if parsed.scheme == "https" else 80)
    is_https = parsed.scheme == "https"
    path = parsed.path or "/"
    if parsed.query:
        path += "?" + parsed.query

    is_ipv6 = ":" in phost
    af = socket.AF_INET6 if is_ipv6 else socket.AF_INET
    s = None
    try:
        s = socket.socket(af, socket.SOCK_STREAM)
        s.settimeout(12)
        s.connect((phost, pport))
        proxy_user, proxy_pass = vpn_utils.get_upstream_proxy_auth()
        if ptype == "socks":
            # SOCKS5 Handshake
            if proxy_user is not None:
                s.sendall(b"\x05\x02\x00\x02")
            else:
                s.sendall(b"\x05\x01\x00")
            resp = recv_exact_from_socket(s, 2)
            if len(resp) < 2 or resp[0] != 5:
                raise RuntimeError("SOCKS5 authentication failed or unsupported")
            if resp[1] == 2:
                if proxy_user is None:
                    raise RuntimeError("SOCKS5 proxy requires username/password authentication")
                user_bytes = proxy_user.encode("utf-8")
                pass_bytes = (proxy_pass or "").encode("utf-8")
                if len(user_bytes) > 255 or len(pass_bytes) > 255:
                    raise RuntimeError("SOCKS5 proxy credentials are too long")
                s.sendall(b"\x01" + bytes([len(user_bytes)]) + user_bytes + bytes([len(pass_bytes)]) + pass_bytes)
                auth_resp = recv_exact_from_socket(s, 2)
                if len(auth_resp) < 2 or auth_resp[1] != 0:
                    raise RuntimeError("SOCKS5 username/password authentication failed")
            elif resp[1] != 0:
                raise RuntimeError("SOCKS5 authentication method unsupported")
            # SOCKS5 Connect
            atyp, addr_bytes = socks5_address_bytes(domain)
            req = b"\x05\x01\x00" + bytes([atyp]) + addr_bytes + port.to_bytes(2, 'big')
            s.sendall(req)
            read_socks5_connect_reply(s)
            # If HTTPS, wrap socket with SSL
            if is_https:
                ctx = ssl.create_default_context() if use_ssl_verify else ssl._create_unverified_context()
                s = ctx.wrap_socket(s, server_hostname=domain)
        else: # http proxy
            if is_https:
                # HTTP CONNECT tunnel
                authority = format_host_port(domain, port)
                auth_header = proxy_basic_auth_header(proxy_user, proxy_pass or "") if proxy_user is not None else ""
                req_str = f"CONNECT {authority} HTTP/1.1\r\nHost: {authority}\r\nUser-Agent: Mozilla/5.0 vpngate-openvpn-manager/2.0\r\n{auth_header}Proxy-Connection: Keep-Alive\r\n\r\n"
                s.sendall(req_str.encode('ascii'))
                resp = read_http_response_head(s)
                status_line = resp.split(b"\r\n", 1)[0].decode("utf-8", errors="replace")
                status_parts = status_line.split()
                status_code = int(status_parts[1]) if len(status_parts) >= 2 and status_parts[1].isdigit() else 0
                if status_code != 200:
                    raise RuntimeError(f"HTTP CONNECT tunnel failed: {status_line}")
                # Wrap socket with SSL
                ctx = ssl.create_default_context() if use_ssl_verify else ssl._create_unverified_context()
                s = ctx.wrap_socket(s, server_hostname=domain)
            else:
                # Direct HTTP request through proxy: request URI must be absolute
                pass

        # Send HTTP GET request
        if ptype == "http" and not is_https:
            request_uri = url
        else:
            request_uri = path
            
        req_headers = (
            f"GET {request_uri} HTTP/1.1\r\n"
            f"Host: {domain}\r\n"
            f"User-Agent: Mozilla/5.0 vpngate-openvpn-manager/2.0\r\n"
            f"Accept: text/plain,*/*\r\n"
            f"{proxy_basic_auth_header(proxy_user, proxy_pass or '') if ptype == 'http' and not is_https and proxy_user is not None else ''}"
            f"Connection: close\r\n\r\n"
        )
        s.sendall(req_headers.encode('utf-8'))

        # Read response
        response_data = b""
        while True:
            chunk = s.recv(4096)
            if not chunk:
                break
            response_data += chunk
            if len(response_data) > 10 * 1024 * 1024: # max 10MB safety guard
                break
    finally:
        if s is not None:
            try:
                s.close()
            except Exception:
                pass

    # Parse HTTP response
    header_end = response_data.find(b"\r\n\r\n")
    if header_end == -1:
        raise RuntimeError("Invalid HTTP response format")
    
    headers_part = response_data[:header_end].decode('utf-8', errors='replace')
    body_part = response_data[header_end+4:]

    # Check for HTTP status code
    lines = headers_part.splitlines()
    if not lines:
        raise RuntimeError("Empty response headers")
    status_line = lines[0]
    status_parts = status_line.split()
    if len(status_parts) >= 2:
        try:
            status_code = int(status_parts[1])
            if status_code != 200:
                raise RuntimeError(f"HTTP Server returned status {status_code}: {status_line}")
        except ValueError:
            pass

    # Handle chunked transfer encoding
    is_chunked = False
    for line in lines[1:]:
        if ":" in line:
            k, v = line.split(":", 1)
            if k.strip().lower() == "transfer-encoding" and "chunked" in v.lower():
                is_chunked = True
                break

    if is_chunked:
        decoded = b""
        idx = 0
        while idx < len(body_part):
            c_end = body_part.find(b"\r\n", idx)
            if c_end == -1:
                break
            chunk_size_str = body_part[idx:c_end].split(b";")[0].strip()
            try:
                chunk_size = int(chunk_size_str, 16)
            except ValueError:
                break
            if chunk_size == 0:
                break
            idx = c_end + 2
            decoded += body_part[idx : idx + chunk_size]
            idx += chunk_size + 2
        body_part = decoded

    return body_part.decode('utf-8', errors='replace')

def fetch_api_text(url: str | None = None, use_ssl_verify: bool = True) -> str:
    if url is None:
        url = API_URL
    
    ptype, phost, pport = vpn_utils.get_upstream_proxy()
    if ptype and phost and pport:
        try:
            print(f"[fetch_api_text] 监测到上游代理 ({ptype}://{phost}:{pport})，尝试通过代理获取 API...", flush=True)
            return fetch_api_text_via_proxy(url, ptype, phost, pport, use_ssl_verify)
        except Exception as e:
            print(f"[fetch_api_text] 通过代理获取 API 失败: {e}，尝试使用直连/默认系统代理...", flush=True)
            log_to_json("WARNING", "Main", f"使用代理 {ptype}://{phost}:{pport} 获取 API 失败: {e}")

    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": "Mozilla/5.0 vpngate-openvpn-manager/2.0",
            "Accept": "text/plain,*/*",
        },
    )
    if url.startswith("https://") and not use_ssl_verify:
        import ssl
        ctx = ssl._create_unverified_context()
        with urllib.request.urlopen(request, timeout=12, context=ctx) as response:
            return response.read().decode("utf-8", errors="replace")
    else:
        with urllib.request.urlopen(request, timeout=12) as response:
            return response.read().decode("utf-8", errors="replace")

def parse_vpngate_rows(text: str) -> list[dict[str, str]]:
    lines = [line for line in text.splitlines() if line and not line.startswith("*")]
    if lines and lines[0].startswith("#"):
        lines[0] = lines[0][1:]
    return list(csv.DictReader(lines))

def decode_config(encoded: str) -> str:
    return base64.b64decode(encoded.encode("ascii"), validate=False).decode("utf-8", errors="replace")

def load_blacklist() -> dict[str, dict[str, Any]]:
    now = time.time()
    raw = read_json(BLACKLIST_FILE, {})
    if not isinstance(raw, dict):
        return {}
    cleaned: dict[str, dict[str, Any]] = {}
    changed = False
    for key, entry in raw.items():
        if not isinstance(entry, dict):
            changed = True
            continue
        until = float(entry.get("until", 0) or 0)
        if until and until > now:
            cleaned[str(key)] = entry
        else:
            changed = True
    if changed:
        write_json(BLACKLIST_FILE, cleaned)
    return cleaned

def mark_blacklisted(node: dict[str, Any], message: str) -> None:
    node_id = str(node.get("id") or "").strip()
    if not node_id:
        return
    blacklist = load_blacklist()
    now = time.time()
    blacklist[node_id] = {
        "id": node_id,
        "ip": node.get("ip") or node.get("remote_host") or "",
        "country": node.get("country", ""),
        "reason": message,
        "marked_at": now,
        "until": now + INVALID_BACKOFF_SECONDS,
    }
    write_json(BLACKLIST_FILE, blacklist)

def row_to_node(row: dict[str, str], config_text: str) -> dict[str, Any]:
    ip = row.get("IP", "")
    country_short = row.get("CountryShort", "")
    remote_host, remote_port, proto = vpn_utils.parse_remote(config_text, ip)
    node_id = safe_name("_".join([country_short or "XX", ip or remote_host, str(remote_port), proto]))
    config_path = CONFIG_DIR / f"{node_id}.ovpn"
    
    country_long = row.get("CountryLong", "")
    country_zh = vpn_utils.COUNTRY_TRANSLATIONS.get(country_long, vpn_utils.COUNTRY_TRANSLATIONS.get(country_long.strip(), country_long))
    return {
        "id": node_id,
        "country": country_zh,
        "country_short": country_short,
        "host_name": row.get("HostName", ""),
        "ip": ip,
        "score": parse_int(row.get("Score")),
        "ping": parse_int(row.get("Ping")),
        "speed": parse_int(row.get("Speed")),
        "sessions": parse_int(row.get("NumVpnSessions")),
        "owner": "",
        "asn": "",
        "as_name": "",
        "location": "",
        "ip_type": "",
        "quality": "",
        "latency_ms": 0,
        "config_file": str(config_path),
        "config_text": config_text,
        "proto": proto,
        "remote_host": remote_host,
        "remote_port": remote_port,
        "fetched_at": time.time(),
        "probe_status": "not_checked",
        "probe_message": "",
        "probed_at": 0,
    }

def fetch_candidates() -> list[dict[str, Any]]:
    blacklist = load_blacklist()
    candidates: list[dict[str, Any]] = []
    seen_ips = set()
    
    # 检查本地是否有节点缓存，以确定最大重试尝试次数
    has_cache = len(cached_nodes()) > 0
    max_attempts = 1 if has_cache else 2
    
    # 尝试 URLs 队列: 1. HTTPS(验证证书) 2. HTTPS(不验证证书) 3. HTTP
    attempts_targets = [
        (API_URL, True),
        (API_URL, False)
    ]
    if API_URL.startswith("https://"):
        attempts_targets.append((API_URL.replace("https://", "http://"), True))
        
    log_to_json("INFO", "Main", "开始拉取官方 API 节点列表...")
    
    last_err = None
    for url, verify_ssl in attempts_targets:
        for i in range(max_attempts):
            if i > 0:
                time.sleep(1.5)
            try:
                msg = f"尝试拉取 {url} (SSL验证: {verify_ssl}, 第 {i+1} 次尝试)..."
                print(f"[fetch_candidates] {msg}", flush=True)
                log_to_json("INFO", "Main", msg)
                api_text = fetch_api_text(url, verify_ssl)
                rows = parse_vpngate_rows(api_text)
                for row in rows[:MAX_SCAN_ROWS]:
                    ip = row.get("IP", "")
                    if not ip or ip in seen_ips:
                        continue
                    encoded = row.get("OpenVPN_ConfigData_Base64", "")
                    if not encoded:
                        continue
                    try:
                        config_text = decode_config(encoded)
                        node = row_to_node(row, config_text)
                    except Exception as row_exc:
                        print(f"[fetch_candidates] 跳过损坏的节点配置记录: {row_exc}", flush=True)
                        log_to_json("WARNING", "Main", f"跳过损坏的节点配置记录: {row_exc}")
                        continue
                    entry = blacklist.get(node["id"])
                    if entry and float(entry.get("until", 0) or 0) > time.time():
                        continue
                    candidates.append(node)
                    seen_ips.add(ip)
                if candidates:
                    break
            except Exception as e:
                last_err = e
                print(f"[fetch_candidates] 拉取失败 (URL: {url}, 验证: {verify_ssl}): {e}", flush=True)
                log_to_json("WARNING", "Main", f"拉取失败 (URL: {url}, 验证: {verify_ssl}): {e}")
        if candidates:
            break
            
    if not candidates:
        err_code, diag_msg = vpn_utils.diagnose_api_failure(API_URL)
        full_err_msg = f"获取官方 API 节点最终失败: {last_err} | 诊断结果: {diag_msg}"
        print(f"[错误代码 {err_code}] {full_err_msg}", flush=True)
        log_to_json("ERROR", "Main", f"[错误代码 {err_code}] {full_err_msg}")
        set_state(
            last_fetch_status="error",
            last_fetch_error_code=err_code,
            last_fetch_message=diag_msg
        )
        if last_err:
            raise RuntimeError(diag_msg) from last_err
        else:
            raise RuntimeError(diag_msg)
                
    set_state(
        last_fetch_at=time.time(),
        last_fetch_status="ok",
        last_fetch_message=f"Fetched {len(candidates)} unique candidates across multiple attempts.",
        blacklisted_nodes=len(blacklist),
    )
    log_to_json("INFO", "Main", f"成功获取官方 API 节点，共 {len(candidates)} 个候选节点")
    return candidates

def cached_nodes() -> list[dict[str, Any]]:
    return read_nodes()

_openvpn_version = None

def split_openvpn_command() -> list[str]:
    try:
        return shlex.split(OPENVPN_CMD, posix=(os.name != "nt")) or ["openvpn"]
    except ValueError as exc:
        raise RuntimeError(f"OPENVPN_CMD 配置无法解析: {exc}") from exc

def get_openvpn_version() -> float:
    global _openvpn_version
    if _openvpn_version is not None:
        return _openvpn_version
    try:
        cmd = split_openvpn_command()
        res = subprocess.run(cmd + ["--version"], capture_output=True, text=True, timeout=2)
        match = re.search(r"OpenVPN\s+(\d+\.\d+)", res.stdout or res.stderr)
        if match:
            _openvpn_version = float(match.group(1))
            return _openvpn_version
    except Exception:
        pass
    _openvpn_version = 2.4
    return _openvpn_version

def openvpn_command(config_file: str, route_nopull: bool, dev: str = "tun0") -> list[str]:
    command = split_openvpn_command()
    command.extend(
        [
            "--config",
            config_file,
            "--dev",
            dev,
            "--dev-type",
            "tun",
            "--pull-filter",
            "ignore",
            "route-ipv6",
            "--pull-filter",
            "ignore",
            "ifconfig-ipv6",
            "--route-delay",
            "2",
            "--connect-retry-max",
            "1",
            "--connect-timeout",
            "15",
            "--auth-user-pass",
            str(AUTH_FILE),
            "--auth-nocache",
        ]
    )
    
    version = get_openvpn_version()
    if version >= 2.5:
        command.extend(["--data-ciphers", "AES-128-CBC:AES-256-GCM:AES-128-GCM:CHACHA20-POLY1305"])
    else:
        command.extend(["--ncp-ciphers", "AES-128-CBC:AES-256-GCM:AES-128-GCM:CHACHA20-POLY1305"])

    command.extend(["--verb", "3"])
    
    if os.path.exists("/etc/ssl/certs"):
        command.extend(["--capath", "/etc/ssl/certs"])
    
    try:
        content = Path(config_file).read_text(encoding="utf-8", errors="replace")
        if vpn_utils.is_config_tcp(content):
            ptype, host, port = vpn_utils.get_upstream_proxy()
            auth_file = upstream_proxy_auth_file()
            if ptype == "socks" and host and port:
                command.extend(["--socks-proxy", host, str(port)])
                if auth_file:
                    command.append(auth_file)
            elif ptype == "http" and host and port:
                command.extend(["--http-proxy", host, str(port)])
                if auth_file:
                    command.append(auth_file)
    except Exception:
        pass
        
    if route_nopull:
        command.append("--route-nopull")
    return command

def stop_process(process: subprocess.Popen[str] | None) -> None:
    if process is None or process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=8)
    except subprocess.TimeoutExpired:
        process.kill()

def kill_existing_openvpn_processes() -> None:
    if not sys.platform.startswith("linux"):
        return
    try:
        own_markers = [
            str(DATA_DIR),
            str(CONFIG_DIR),
            str(AUTH_FILE),
            str(UPSTREAM_PROXY_AUTH_FILE),
        ]
        killed_pids: list[int] = []
        proc_root = Path("/proc")
        if not proc_root.exists():
            return
        for proc_dir in proc_root.iterdir():
            if not proc_dir.name.isdigit():
                continue
            pid = int(proc_dir.name)
            if pid == os.getpid():
                continue
            try:
                raw = (proc_dir / "cmdline").read_bytes()
            except OSError:
                continue
            if not raw:
                continue
            args = [part.decode("utf-8", errors="replace") for part in raw.split(b"\0") if part]
            if not args:
                continue
            cmdline = " ".join(args)
            executable = Path(args[0]).name.lower()
            if "openvpn" not in executable and "openvpn" not in cmdline.lower():
                continue
            # Skip: don't kill channel OpenVPN processes
            if any(f"dev tun{100 + chi}" in cmdline for chi in range(MAX_CHANNELS)):
                continue
            if any(marker and marker in cmdline for marker in own_markers):
                try:
                    os.kill(pid, signal.SIGTERM)
                    killed_pids.append(pid)
                except ProcessLookupError:
                    pass
                except PermissionError:
                    print(f"[Cleanup] No permission to terminate OpenVPN PID {pid}", flush=True)
        if killed_pids:
            time.sleep(0.5)
            for pid in killed_pids:
                try:
                    raw = (proc_root / str(pid) / "cmdline").read_bytes()
                    cmdline = " ".join(part.decode("utf-8", errors="replace") for part in raw.split(b"\0") if part)
                    if any(marker and marker in cmdline for marker in own_markers):
                        os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                except (OSError, PermissionError):
                    pass
            print(f"[Cleanup] Terminated AimiliVPN OpenVPN processes: {killed_pids}", flush=True)
    except Exception as e:
        print(f"[Cleanup Error] Failed to kill existing OpenVPN processes: {e}", flush=True)

def update_handshake_status(line_lower: str) -> None:
    status_map = {
        "resolving": ("解析域名", "正在解析服务器域名与 IP 地址..."),
        "udp link local": ("物理连接", "已创建本地套接字，开始尝试发送数据包..."),
        "tcp link local": ("物理连接", "已创建本地套接字，开始尝试发送数据包..."),
        "tls: initial packet": ("证书握手", "已成功发送首包，正在与远程服务器建立 TLS 安全通道..."),
        "verify ok": ("证书校验", "服务器证书校验成功，正在进行身份验证..."),
        "peer connection initiated": ("协商加密", "控制通道已建立，已初始化与服务器的加密对等连接..."),
        "push_request": ("请求配置", "正在向服务器发送 PUSH_REQUEST 请求配置参数与 IP 分配..."),
        "push_reply": ("应用配置", "已接收服务器 PUSH_REPLY，获取到 IP 分配，正在准备配置网卡..."),
        "tun/tap device": ("创建网卡", "正在创建虚拟通道并打开 TUN 虚拟网卡设备..."),
        "do_ifconfig": ("网卡配置", "正在为虚拟网卡配置 IP 地址及相关网络属性..."),
    }
    for key, (short_status, detailed_desc) in status_map.items():
        if key in line_lower:
            set_state(active_node_latency=short_status, last_check_message=detailed_desc)
            break

def run_openvpn_until_ready(config_file: str, keep_alive: bool, route_nopull: bool, timeout: int | None = None, dev: str = "tun0") -> tuple[bool, str, subprocess.Popen[str] | None]:
    limit = timeout if timeout is not None else OPENVPN_TEST_TIMEOUT_SECONDS
    try:
        process = subprocess.Popen(
            openvpn_command(config_file, route_nopull, dev),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            cwd=str(ROOT_DIR),
        )
    except FileNotFoundError:
        return False, "[错误代码 2001] [ERR_OVPN_CMD_NOT_FOUND] 未找到 openvpn 命令。原因: 系统未安装 openvpn，或 PATH 环境变量不正确。", None
    except OSError as exc:
        return False, f"[错误代码 2002] [ERR_OVPN_START_FAILED] openvpn 启动失败: {exc}。原因: 系统权限不足或配置冲突。", None

    lines: queue.Queue[str | None] = queue.Queue()
    startup_done = [False]
    openvpn_logs: list[str] = []

    def reader() -> None:
        assert process.stdout is not None
        for line in process.stdout:
            line_str = line.rstrip()
            if not startup_done[0]:
                openvpn_logs.append(line_str)
                lines.put(line_str)
            else:
                if keep_alive:
                    print(f"[OpenVPN] {line_str}", flush=True)
                    level = "INFO"
                    line_lower = line_str.lower()
                    if "error" in line_lower or "failed" in line_lower or "cannot" in line_lower or "fatal" in line_lower or "permission denied" in line_lower:
                        level = "ERROR"
                    elif "warning" in line_lower or "warn" in line_lower or "deprecated" in line_lower:
                        level = "WARNING"
                    log_to_json(level, "VPN", f"[OpenVPN] {line_str}")
        if not startup_done[0]:
            lines.put(None)

    threading.Thread(target=reader, daemon=True).start()
    started = time.time()
    tail: list[str] = []
    ok = False
    message = "OpenVPN did not complete initialization."
    while time.time() - started < limit:
        try:
            line = lines.get(timeout=0.5)
        except queue.Empty:
            if process.poll() is not None:
                break
            continue
        if line is None:
            break
        if line:
            tail.append(line)
            tail = tail[-50:]
            if keep_alive:
                print(f"[OpenVPN] {line}", flush=True)
        lower = line.lower()
        if keep_alive:
            update_handshake_status(lower)
        if "initialization sequence completed" in lower:
            ok = True
            message = f"OpenVPN connected in {int((time.time() - started) * 1000)} ms."
            break
        if "auth_failed" in lower or "authentication failed" in lower:
            message = "AUTH_FAILED"
            break
        if "cannot ioctl" in lower or "fatal error" in lower:
            message = line[-220:]
            break
    else:
        message = f"OpenVPN timeout after {limit}s."

    # Bulk write accumulated startup logs
    for line_str in openvpn_logs:
        level = "INFO"
        line_lower = line_str.lower()
        if "error" in line_lower or "failed" in line_lower or "cannot" in line_lower or "fatal" in line_lower or "permission denied" in line_lower:
            level = "ERROR"
        elif "warning" in line_lower or "warn" in line_lower or "deprecated" in line_lower:
            level = "WARNING"
        log_to_json(level, "VPN", f"[OpenVPN] {line_str}")

    if not ok:
        err_code, diag_msg = vpn_utils.diagnose_openvpn_failure(tail)
        message = f"[错误代码 {err_code}] {diag_msg} (原始日志尾部: {tail[-1][-100:] if tail else '无'})"
    startup_done[0] = True
    if not keep_alive or not ok:
        stop_process(process)
        process = None
    return ok, message, process


def setup_policy_routing(interface: str = "tun0", table: int = 100) -> None:
    # Clean up any existing rules/routes for this table
    try:
        subprocess.run(["ip", "rule", "del", "table", str(table)], capture_output=True, timeout=2)
    except Exception:
        pass
    try:
        subprocess.run(["ip", "route", "flush", "table", str(table)], capture_output=True, timeout=2)
    except Exception:
        pass
    
    success = False
    for attempt in range(1, 4):
        try:
            subprocess.run(["ip", "route", "add", "default", "dev", interface, "table", str(table)], check=True, timeout=2)
            subprocess.run(["ip", "rule", "add", "oif", interface, "table", str(table)], check=True, timeout=2)
            # rp_filter loose mode (2)
            for proc_path in ["all", "default", interface]:
                try:
                    subprocess.run(["sysctl", "-w", f"net.ipv4.conf.{proc_path}.rp_filter=2"], capture_output=True, timeout=2)
                except Exception:
                    pass
            print(f"[policy_routing] Enabled policy routing for {interface} table {table} (attempt {attempt} success)", flush=True)
            success = True
            # fwmark rule + iptables so proxy outbound uses this routing table
            mark = table
            subprocess.run(["ip", "rule", "add", "fwmark", str(mark), "table", str(table)], capture_output=True, timeout=2)
            proxy_port = CHANNEL_BASE_PORT + (table - 100)
            try:
                subprocess.run(["iptables", "-t", "mangle", "-C", "OUTPUT", "-p", "tcp", "--sport", str(proxy_port), "-j", "MARK", "--set-mark", str(mark)], capture_output=True, timeout=2)
            except Exception:
                try:
                    subprocess.run(["iptables", "-t", "mangle", "-A", "OUTPUT", "-p", "tcp", "--sport", str(proxy_port), "-j", "MARK", "--set-mark", str(mark)], check=True, timeout=5)
                except Exception as e:
                    print(f"[policy_routing] iptables fwmark for port {proxy_port} failed (non-fatal): {e}", flush=True)
            break
        except Exception as e:
            print(f"[policy_routing] Attempt {attempt} failed for {interface} table {table}: {e}", flush=True)
            time.sleep(1)
            
    if not success:
        print(f"[路由配置失败] 无法向路由表 {table} 添加默认路由 (接口 {interface})。请检查 root 权限。", flush=True)
        log_to_json("ERROR", "Routing", f"无法向路由表 {table} 添加默认路由")

def cleanup_policy_routing(table: int = 100) -> None:
    try:
        subprocess.run(["ip", "rule", "del", "table", str(table)], capture_output=True, timeout=2)
        subprocess.run(["ip", "route", "flush", "table", str(table)], capture_output=True, timeout=2)
        print(f"[policy_routing] Cleared policy routing table {table}", flush=True)
        # Remove iptables fwmark for this channel's proxy port
        proxy_port = CHANNEL_BASE_PORT + (table - 100)
        try:
            subprocess.run(["iptables", "-t", "mangle", "-D", "OUTPUT", "-p", "tcp", "--sport", str(proxy_port), "-j", "MARK", "--set-mark", str(table)], capture_output=True, timeout=2)
        except Exception:
            pass
        # Remove fwmark ip rule
        try:
            subprocess.run(["ip", "rule", "del", "fwmark", str(table)], capture_output=True, timeout=2)
        except Exception:
            pass
    except Exception:
        pass

def stop_active_openvpn() -> None:
    global active_openvpn_process, active_openvpn_node_id
    with lock:
        cleanup_policy_routing(100)
        config_to_delete = None
        if active_openvpn_node_id:
            nodes = read_nodes()
            node = next((item for item in nodes if item.get("id") == active_openvpn_node_id), None)
            if node:
                config_to_delete = node.get("config_file")
                
        stop_process(active_openvpn_process)
        active_openvpn_process = None
        active_openvpn_node_id = ""
        kill_existing_openvpn_processes()
        
        if config_to_delete:
            try:
                path = Path(config_to_delete)
                if path.exists():
                    path.unlink()
            except Exception:
                pass

def active_openvpn_running() -> bool:
    return active_openvpn_process is not None and active_openvpn_process.poll() is None

def sort_all_nodes(nodes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    available_nodes = sorted(
        [n for n in nodes if n.get("probe_status") == "available" or n.get("active")],
        key=lambda n: (
            0 if n.get("ip_type") in ("residential", "mobile") else 1,
            parse_int(n.get("latency_ms")) or 999999,
            -parse_int(n.get("score"))
        )
    )
    untested_nodes = sorted(
        [n for n in nodes if n.get("probe_status") == "not_checked" and not n.get("active")],
        key=lambda n: (-parse_int(n.get("score")), parse_int(n.get("ping")))
    )
    unavailable_nodes = sorted(
        [n for n in nodes if n.get("probe_status") == "unavailable" and not n.get("active")],
        key=lambda n: (-parse_int(n.get("score")), -float(n.get("probed_at", 0)))
    )
    return available_nodes + untested_nodes + unavailable_nodes

active_test_indexes = set()
test_indexes_lock = threading.Lock()

def get_free_test_index() -> int:
    with test_indexes_lock:
        for idx in range(MAX_CHANNELS + 2, 100):
            if idx not in active_test_indexes:
                active_test_indexes.add(idx)
                return idx
        raise RuntimeError("没有可用的 OpenVPN 测试网卡编号，请稍后重试")

def release_test_index(idx: int) -> None:
    with test_indexes_lock:
        active_test_indexes.discard(idx)

# Channel TUN allocation — dynamically picks free TUN from pool (200+)
# Routing table uses the same number as the TUN device for 1:1 mapping.
def alloc_channel_tun(channel_idx: int) -> int:
    """Allocate next available channel TUN from the dedicated pool (200+)."""
    with test_indexes_lock:
        for idx in range(200, 300):
            if idx not in active_test_indexes:
                active_test_indexes.add(idx)
                return idx
        raise RuntimeError("No available TUN index for channel connection")


def free_channel_tun(tun_idx: int) -> None:
    with test_indexes_lock:
        active_test_indexes.discard(tun_idx)

def test_config_path(node_id: str) -> Path:
    safe_id = safe_name(node_id)
    return CONFIG_DIR / f".test_{safe_id}_{uuid.uuid4().hex}.ovpn"

def test_node_by_id(node_id: str) -> dict[str, Any]:
    with lock:
        nodes = read_nodes()
        node = next((item for item in nodes if item.get("id") == node_id), None)
        if not node:
            raise ValueError(f"Node not found: {node_id}")
        config_text = node.get("config_text") or ""
        h = str(node.get("remote_host") or node.get("ip"))
        p = parse_int(node.get("remote_port"))
        fallback_ping = parse_int(node.get("ping"))

    temp_path = test_config_path(node_id)
    try:
        CONFIG_DIR.mkdir(exist_ok=True, parents=True)
        temp_path.write_text(config_text, encoding="utf-8")
    except Exception as e:
        raise RuntimeError(f"Failed to write temp config file: {e}")

    latency = vpn_utils.ping_latency_ms(h, p, fallback_ping)
    
    idx = None
    try:
        idx = get_free_test_index()
        ok, message, _ = run_openvpn_until_ready(str(temp_path), keep_alive=False, route_nopull=True, timeout=12, dev=f"tun{idx}")
    finally:
        if idx is not None:
            release_test_index(idx)
        try:
            if temp_path.exists():
                temp_path.unlink()
        except Exception:
            pass

    temp_node = {
        "id": node_id,
        "ip": h,
        "remote_host": h,
        "remote_port": p,
        "owner": "",
        "asn": "",
        "as_name": "",
        "location": "",
        "ip_type": "",
        "quality": "",
    }
    if ok:
        vpn_utils.enrich_ip_info([temp_node])

    with lock:
        nodes = read_nodes()
        node = next((item for item in nodes if item.get("id") == node_id), None)
        if node:
            node["latency_ms"] = latency
            node["probe_status"] = "available" if ok else "unavailable"
            node["probe_message"] = message
            node["probed_at"] = time.time()
            if ok:
                node["owner"] = temp_node["owner"]
                node["asn"] = temp_node["asn"]
                node["as_name"] = temp_node["as_name"]
                node["location"] = temp_node["location"]
                node["ip_type"] = temp_node["ip_type"]
                node["quality"] = temp_node["quality"]
            
            sorted_nodes = sort_all_nodes(nodes)
            write_json(NODES_FILE, sorted_nodes)
            res = next((item for item in sorted_nodes if item.get("id") == node_id), node)
            return res
        else:
            return {}

def test_multiple_nodes(node_ids: list[str]) -> list[dict[str, Any]]:
    with lock:
        nodes = read_nodes()
        to_test = [n for n in nodes if n.get("id") in node_ids]
        
    def test_worker(args: tuple[int, dict[str, Any]]) -> dict[str, Any]:
        idx, n_info = args
        node_id = n_info["id"]
        config_text = n_info.get("config_text") or ""
        h = str(n_info.get("remote_host") or n_info.get("ip"))
        p = parse_int(n_info.get("remote_port"))
        fallback_ping = parse_int(n_info.get("ping"))
        
        temp_path = test_config_path(node_id)
        try:
            CONFIG_DIR.mkdir(exist_ok=True, parents=True)
            temp_path.write_text(config_text, encoding="utf-8")
        except Exception as e:
            return {
                "id": node_id,
                "latency_ms": 0,
                "probe_status": "unavailable",
                "probe_message": f"Failed to write configuration: {e}",
                "probed_at": time.time(),
                "owner": "",
                "asn": "",
                "as_name": "",
                "location": "",
                "ip_type": "",
                "quality": "",
            }
            
        latency = vpn_utils.ping_latency_ms(h, p, fallback_ping)
        tun_idx = None
        try:
            tun_idx = get_free_test_index()
            dev_name = f"tun{tun_idx}"
            ok, message, _ = run_openvpn_until_ready(str(temp_path), keep_alive=False, route_nopull=True, timeout=12, dev=dev_name)
        finally:
            if tun_idx is not None:
                release_test_index(tun_idx)
            try:
                if temp_path.exists():
                    temp_path.unlink()
            except Exception:
                pass
            
        temp_node = {
            "id": node_id,
            "ip": n_info.get("ip") or h,
            "remote_host": h,
            "remote_port": p,
            "latency_ms": latency,
            "probe_status": "available" if ok else "unavailable",
            "probe_message": message,
            "probed_at": time.time(),
            "owner": "",
            "asn": "",
            "as_name": "",
            "location": "",
            "ip_type": "",
            "quality": "",
        }
        return temp_node

    updated_nodes_map = {}
    max_workers = min(5, max(1, len(to_test)))
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(test_worker, (idx, n)): n["id"] for idx, n in enumerate(to_test)}
        for future in concurrent.futures.as_completed(futures):
            nid = futures[future]
            try:
                res = future.result()
                updated_nodes_map[nid] = res
            except Exception as e:
                updated_nodes_map[nid] = {
                    "id": nid,
                    "probe_status": "unavailable",
                    "probe_message": f"Test exception: {e}",
                    "latency_ms": 0
                }
                
    # 批量查询并丰富可用节点的地理及 ISP 信息，防止并发时被定位 API 接口限流
    successful_nodes = [res for res in updated_nodes_map.values() if res.get("probe_status") == "available"]
    if successful_nodes:
        try:
            vpn_utils.enrich_ip_info(successful_nodes)
        except Exception as ee:
            print(f"[test_multiple_nodes] 批量富化 IP 失败: {ee}", flush=True)

    with lock:
        current_nodes = read_nodes()
        for n in current_nodes:
            nid = n.get("id")
            if nid in updated_nodes_map:
                n.update(updated_nodes_map[nid])
        sorted_nodes = sort_all_nodes(current_nodes)
        write_json(NODES_FILE, sorted_nodes)
        
    return list(updated_nodes_map.values())

def auto_switch_node(attempt: int = 0) -> None:
    if attempt >= 3:
        print("[自动切换] 连续切换失败已达 3 次，停止切换以防止主线程死锁，将在后台重新加载节点...", flush=True)
        return
    
    # Skip auto-switch if any channel is actively connected (multi-channel mode)
    with lock:
        for chi in range(MAX_CHANNELS):
            if ch_processes[chi] is not None and ch_processes[chi].poll() is None:
                print(f"[自动切换] 通道 {chi} 正在使用中，跳过旧版单连接自动切换。", flush=True)
                return
    
        
    ui_cfg = load_ui_config()
    connection_enabled = ui_cfg.get("connection_enabled", True)
    if not connection_enabled:
        print("[自动切换] 连接已禁用，不进行自动切换。", flush=True)
        return

    routing_mode = ui_cfg.get("routing_mode", "auto")
    target_country = ui_cfg.get("force_country", "")

    if routing_mode == "fixed_ip":
        print("[自动切换] 当前处于固定 IP 模式，不进行自动连接或切换。", flush=True)
        return

    # Find the next best available node
    with lock:
        nodes = read_nodes()
        candidates = [
            n for n in nodes 
            if n.get("probe_status") == "available" 
            and not n.get("active")
        ]
        
        if routing_mode == "fixed_region" and target_country:
            candidates = [
                n for n in candidates 
                if n.get("country") == target_country 
                or vpn_utils.COUNTRY_TRANSLATIONS.get(n.get("country", ""), n.get("country", "")) == target_country
            ]
        if routing_mode == "favorites":
            fav_ids = set(ui_cfg.get("favorite_node_ids", []))
            fav_candidates = [n for n in candidates if n.get("id") in fav_ids]
            if fav_candidates:
                candidates = fav_candidates
            else:
                fav_fail_fallback = ui_cfg.get("fav_fail_fallback", True)
                if not fav_fail_fallback:
                    candidates = []
            
        # Apply routing_ip_type filter
        routing_ip_type = ui_cfg.get("routing_ip_type", "all")
        if routing_ip_type == "residential":
            candidates = [n for n in candidates if n.get("ip_type") in ("residential", "mobile")]
        elif routing_ip_type == "hosting":
            candidates = [n for n in candidates if n.get("ip_type") == "hosting"]
            
        candidates.sort(key=lambda n: (parse_int(n.get("latency_ms")) or 999999, -parse_int(n.get("score"))))
        
    if candidates:
        next_node = candidates[0]
        msg = f"当前连接已失效或代理连通性检测失败，正在自动切换至最佳备用节点: {next_node['id']}"
        print(f"[自动切换] {msg}", flush=True)
        log_to_json("INFO", "VPN", msg)
        try:
            connect_node(next_node["id"])
        except Exception as e:
            err_msg = f"切换到备用节点 {next_node['id']} 失败: {e}，将尝试下一个..."
            print(f"[自动切换] {err_msg}", flush=True)
            log_to_json("WARNING", "VPN", err_msg)
            auto_switch_node(attempt + 1)
    else:
        msg = "没有可用的备选节点，将自动断开并清理当前连接状态，同时在后台异步获取新节点..."
        if routing_mode == "fixed_region" and target_country:
            msg = f"没有可用的【{target_country}】备选节点，已断开连接，将在后台持续尝试获取新节点..."
        print(f"[自动切换] {msg}", flush=True)
        log_to_json("WARNING", "VPN", msg)
        stop_active_openvpn()
        with lock:
            nodes = read_nodes()
            for item in nodes:
                item["active"] = False
            write_json(NODES_FILE, nodes)
        set_state(active_openvpn_node_id="", last_check_message=msg)
        
        def bg_fetch_and_switch():
            try:
                maintain_valid_nodes(force=False)
                auto_switch_node()
            except Exception as e:
                print(f"[自动切换后台补齐] 获取并测试节点失败: {e}", flush=True)
        
        threading.Thread(target=bg_fetch_and_switch, daemon=True).start()

def connect_channel(channel_idx: int, node_id: str) -> str:
    if channel_idx < 0 or channel_idx >= MAX_CHANNELS:
        raise ValueError(f"Invalid channel: {channel_idx}")
    node_id = str(node_id or "").strip()
    if not node_id:
        raise ValueError("Node id is required")
    with lock:
        if ch_connecting[channel_idx]:
            raise RuntimeError(f"Channel {channel_idx} is already connecting")
        ch_connecting[channel_idx] = True
        ch_node_ids[channel_idx] = node_id
    try:
        nodes = read_nodes()
        node = next((item for item in nodes if item.get("id") == node_id), None)
        if not node:
            raise ValueError(f"Channel {channel_idx}: Node not found: {node_id}")
        config_text = node.get("config_text", "") or ""
        if not config_text:
            cfg_path = Path(node.get("config_file", "") or "")
            if cfg_path.exists():
                config_text = cfg_path.read_text(encoding="utf-8")
        if not config_text:
            raise ValueError(f"No config for node {node_id}")
        # Write config to a temp file (OpenVPN --config requires a file path)
        channel_config_dir = DATA_DIR / "channel_configs"
        channel_config_dir.mkdir(exist_ok=True, parents=True)
        config_path = channel_config_dir / f"ch{channel_idx}.ovpn"
        config_path.write_text(config_text, encoding="utf-8")
        # Allocate a free TUN device dynamically
        tun_idx = alloc_channel_tun(channel_idx)
        ch_tun_ids[channel_idx] = tun_idx
        ok, msg, proc = run_openvpn_until_ready(str(config_path), keep_alive=True, route_nopull=True, dev=f"tun{tun_idx}")
        if not ok or proc is None:
            msg = msg or "OpenVPN failed to connect"
            if ch_tun_ids[channel_idx] >= 0:
                free_channel_tun(ch_tun_ids[channel_idx])
                ch_tun_ids[channel_idx] = -1
            raise RuntimeError(msg)
        ch_processes[channel_idx] = proc
        setup_policy_routing(f"tun{tun_idx}", tun_idx)
        return msg
    finally:
        ch_connecting[channel_idx] = False


def disconnect_channel(channel_idx: int) -> str:
    if channel_idx < 0 or channel_idx >= MAX_CHANNELS:
        raise ValueError(f"Invalid channel: {channel_idx}")
    with lock:
        tun_idx = ch_tun_ids[channel_idx]
        if ch_processes[channel_idx]:
            stop_process(ch_processes[channel_idx])
            ch_processes[channel_idx] = None
            ch_node_ids[channel_idx] = ""
            # Release the allocated TUN device
            if ch_tun_ids[channel_idx] >= 0:
                free_channel_tun(ch_tun_ids[channel_idx])
                ch_tun_ids[channel_idx] = -1
        if tun_idx >= 0:
            cleanup_policy_routing(tun_idx)
    return "disconnected"


def connect_node(node_id: str) -> str:
    global active_openvpn_process, active_openvpn_node_id, is_connecting
    node_id = str(node_id or "").strip()
    if not node_id:
        raise ValueError("Node id is required")
    stopped_existing = False
    with lock:
        if is_connecting:
            print("[连接] 正在建立其他连接中，跳过此请求", flush=True)
            raise RuntimeError("当前已有连接或节点检测任务正在运行，请稍后再试")
        is_connecting = True
        set_state(is_connecting=True, active_node_latency="正在连接", last_check_message=f"正在初始化连接配置: {node_id}")
        
    try:
        log_to_json("INFO", "VPN", f"开始连接节点: {node_id}")

        nodes = read_nodes()
        node = next((item for item in nodes if item.get("id") == node_id), None)
        if not node:
            raise ValueError(f"Node not found: {node_id}")
        
        ui_cfg = load_ui_config()
        ui_cfg["connection_enabled"] = True
        if ui_cfg.get("routing_mode") == "fixed_ip":
            ui_cfg["fixed_node_id"] = node_id
        auth_file = DATA_DIR / "ui_auth.json"
        with lock:
            DATA_DIR.mkdir(exist_ok=True, parents=True)
            auth_file.write_text(json.dumps(ui_cfg, ensure_ascii=False, indent=2), encoding="utf-8")
        
        set_state(active_node_latency="清理连接", last_check_message="正在关闭与清理旧的 VPN 连接及网卡...")
        stop_active_openvpn()
        stopped_existing = True

        set_state(active_node_latency="写入配置", last_check_message="正在写入 OpenVPN 节点配置文件...")
        config_path = Path(node["config_file"])
        try:
            CONFIG_DIR.mkdir(exist_ok=True, parents=True)
            config_path.write_text(node.get("config_text") or "", encoding="utf-8")
        except Exception as e:
            raise RuntimeError(f"Failed to write configuration: {e}")

        set_state(active_node_latency="启动核心", last_check_message="正在启动 OpenVPN Core 核心服务并建立连接...")
        ok, message, process = run_openvpn_until_ready(str(node["config_file"]), keep_alive=True, route_nopull=True)
        if not ok or process is None:
            try:
                if config_path.exists():
                    config_path.unlink()
            except Exception:
                pass
            node["probe_status"] = "unavailable"
            node["probe_message"] = message
            for item in nodes:
                item["active"] = False
            write_json(NODES_FILE, nodes)
            log_to_json("ERROR", "VPN", f"连接节点 {node_id} 失败: {message}")
            print(f"[连接核心失败] 无法与 VPN 节点 {node_id} 建立隧道连接！详情: {message}", flush=True)
            set_state(active_openvpn_node_id="", is_connecting=False, active_node_latency="无活动连接", last_check_message=f"连接失败: {message}")
            with lock:
                active_openvpn_node_id = ""
            raise RuntimeError(message)
            
        with lock:
            active_openvpn_process = process
            active_openvpn_node_id = node_id
        
        set_state(active_node_latency="配置路由", last_check_message="正在配置策略路由规则与流量转发...")
        setup_policy_routing("tun0")
        
        global last_active_ping_time, last_active_latency
        last_active_ping_time = time.time()
        last_active_latency = 0
        
        set_state(active_node_latency="测试延迟", last_check_message="正在直连测试代理出口延迟与可用性...")
        try:
            ip = node.get("ip") or node.get("remote_host")
            port = parse_int(node.get("remote_port"))
            fallback = parse_int(node.get("ping"))
            latency = vpn_utils.ping_latency_ms(ip, port, fallback)
            if latency > 0:
                last_active_latency = latency
        except Exception:
            pass
            
        for item in nodes:
            item["active"] = item.get("id") == node_id
            if item["active"]:
                _ph = f"[{LOCAL_PROXY_HOST}]" if ":" in LOCAL_PROXY_HOST else LOCAL_PROXY_HOST
                item["probe_message"] = f"Active node. HTTP proxy: http://{_ph}:{LOCAL_PROXY_PORT}"
        write_json(NODES_FILE, nodes)
        
        set_state(last_check_message="正在测试本地代理出站联通性与出口 IP...")
        res = check_proxy_health()
        if res["ok"]:
            set_state(
                proxy_ok=True,
                proxy_ip=res["ip"],
                proxy_latency_ms=res["latency_ms"],
                proxy_error=""
            )
        else:
            set_state(
                proxy_ok=False,
                proxy_ip="-",
                proxy_latency_ms=0,
                proxy_error=res.get("error", "未知错误")
            )
            
        latency_str = f"{last_active_latency} ms" if last_active_latency > 0 else "检测超时"
        set_state(active_openvpn_node_id=node_id, is_connecting=False, last_check_message=f"Connected {node_id}", active_node_latency=latency_str)
        log_to_json("INFO", "VPN", f"节点 {node_id} 连接成功，出口网卡 tun0 已启用")
        return f"Connected {node_id}"
    except Exception as exc:
        if stopped_existing or (active_openvpn_node_id == node_id and not active_openvpn_running()):
            clear_active_connection_state(f"连接失败: {exc}")
        else:
            set_state(is_connecting=False, last_check_message=f"连接失败: {exc}")
        raise
    finally:
        with lock:
            is_connecting = False

def maintain_valid_nodes(force: bool = False) -> str:
    global active_openvpn_process, active_openvpn_node_id, is_connecting
    ensure_dirs()
    if not maintenance_lock.acquire(blocking=False):
        msg = "节点维护任务正在运行，请稍后再试"
        set_state(last_check_message=msg)
        return msg
    is_connecting = True
    try:
        if force:
            with lock:
                stop_active_openvpn()
        elif not active_openvpn_running():
            ui_cfg = load_ui_config()
            routing_mode = ui_cfg.get("routing_mode", "auto")
            connection_enabled = ui_cfg.get("connection_enabled", True)
            if connection_enabled:
                if routing_mode == "fixed_ip":
                    target_id = active_openvpn_node_id or ui_cfg.get("fixed_node_id", "")
                    if target_id:
                        nodes = read_nodes()
                        if any(n.get("id") == target_id for n in nodes):
                            print(f"[维护线程] 检测到固定 IP 模式下 OpenVPN 未运行，正在重新拉起同一节点: {target_id}", flush=True)
                            is_connecting = False
                            try:
                                connect_node(target_id)
                            except Exception as e:
                                print(f"[维护线程] 重新拉起固定节点 {target_id} 失败: {e}", flush=True)
                            is_connecting = True
                else:
                    has_active_id = False
                    with lock:
                        if active_openvpn_node_id:
                            has_active_id = True
                    # Don't stop if channels are active
                    with lock:
                        for chi in range(MAX_CHANNELS):
                            if ch_processes[chi] is not None and ch_processes[chi].poll() is None:
                                has_active_id = False
                                break
                    if has_active_id:
                        stop_active_openvpn()
                        print("[维护线程] 检测到当前 OpenVPN 进程已意外退出，准备自动切换节点", flush=True)
                        is_connecting = False
                        auto_switch_node()
                        is_connecting = True

        try:
            set_state(is_connecting=True, last_check_message="正在拉取最新的免费 VPN 节点列表...")
            candidates = fetch_candidates()
        except Exception as exc:
            vpn_utils.check_and_fix_dns()
            diag_msg = str(exc)
            if not any(token in diag_msg for token in ["[ERR_", "错误代码"]):
                err_code, raw_diag = vpn_utils.diagnose_api_failure(API_URL)
                diag_msg = f"[错误代码 {err_code}] 获取节点失败: {exc} | 诊断结果: {raw_diag}"
            set_state(last_fetch_at=time.time(), last_fetch_status="error", last_fetch_message=diag_msg)
            candidates = []

        if not candidates:
            return "没有拉取到新节点"

        with lock:
            active_node = None
            if active_openvpn_node_id:
                current_nodes = read_nodes()
                active_node = next((n for n in current_nodes if n.get("id") == active_openvpn_node_id), None)
                
            merged: list[dict[str, Any]] = []
            seen_ids: set[str] = set()
            
            if active_node:
                merged.append(active_node)
                seen_ids.add(active_node["id"])
                
            for cand in candidates:
                if cand["id"] not in seen_ids:
                    merged.append(cand)
                    seen_ids.add(cand["id"])
                    
            if len(merged) > 1000:
                merged = merged[:1000]
                
            for n in merged:
                config_path = Path(n["config_file"])
                if not config_path.exists():
                    try:
                        config_path.write_text(n["config_text"], encoding="utf-8")
                    except Exception:
                        pass
                        
            write_json(NODES_FILE, merged)

        # Test all non-active nodes from the list
        with lock:
            current_nodes = read_nodes()
            to_test = [n for n in current_nodes if not n.get("active")]
            to_test_ids = [n["id"] for n in to_test]
            
        msg = f"开始对列表中所有候选节点进行周期连通性与延迟测试，待检测节点共 {len(to_test_ids)} 个"
        print(f"[周期检测] {msg}", flush=True)
        log_to_json("INFO", "Main", msg)
        
        set_state(is_connecting=True, last_check_message="正在并发检测所有节点可用性...")
        test_multiple_nodes(to_test_ids)
        is_connecting = False
        
        with lock:
            merged = read_nodes()
            
            # Identify available, unavailable, and active nodes
            available_nodes = [n["id"] for n in merged if n.get("probe_status") == "available"]
            unavailable_nodes = [n["id"] for n in merged if n.get("probe_status") == "unavailable"]
            active_node = next((n["id"] for n in merged if n.get("active")), "无")
            
            status_report = (
                f"周期节点检测完成。实时同步状态: 获取到候选节点共 {len(merged)} 个。 "
                f"其中【可用节点】{len(available_nodes)} 个: {available_nodes[:15]}...; "
                f"【不可用节点】{len(unavailable_nodes)} 个; "
                f"当前【正在正常运行的活动连接节点】为: {active_node}。"
            )
            print(f"[周期检测] {status_report}", flush=True)
            log_to_json("INFO", "Main", status_report)
            
            if active_node != "无" and not active_openvpn_running():
                warn_msg = f"[诊断警告] 活动节点 {active_node} 被标记为活动状态，但 OpenVPN 进程实际并未正常运行！"
                print(warn_msg, flush=True)
                log_to_json("WARNING", "Main", warn_msg)
            
            if not active_openvpn_running():
                ui_cfg = load_ui_config()
                connection_enabled = ui_cfg.get("connection_enabled", True)
                if connection_enabled:
                    routing_mode = ui_cfg.get("routing_mode", "auto")
                    target_country = ui_cfg.get("force_country", "")
                    
                    if routing_mode != "fixed_ip":
                        available_candidates = [n for n in merged if n.get("probe_status") == "available"]
                        if routing_mode == "fixed_region" and target_country:
                            available_candidates = [
                                n for n in available_candidates 
                                if n.get("country") == target_country 
                                or vpn_utils.COUNTRY_TRANSLATIONS.get(n.get("country", ""), n.get("country", "")) == target_country
                            ]
                        elif routing_mode == "favorites":
                            fav_ids = set(ui_cfg.get("favorite_node_ids", []))
                            fav_candidates = [n for n in available_candidates if n.get("id") in fav_ids]
                            if fav_candidates:
                                available_candidates = fav_candidates
                            else:
                                fav_fail_fallback = ui_cfg.get("fav_fail_fallback", True)
                                if not fav_fail_fallback:
                                    available_candidates = []
                        
                        # Apply routing_ip_type filter for auto-connect
                        routing_ip_type = ui_cfg.get("routing_ip_type", "all")
                        if routing_ip_type == "residential":
                            available_candidates = [n for n in available_candidates if n.get("ip_type") in ("residential", "mobile")]
                        elif routing_ip_type == "hosting":
                            available_candidates = [n for n in available_candidates if n.get("ip_type") == "hosting"]
                        
                        if available_candidates:
                            auto_switch_node()

        valid_nodes_count = len([n for n in merged if n.get("probe_status") == "available"])
        message = f"Fetched {len(candidates)} nodes. Tested {len(to_test_ids)} non-active nodes."
        set_state(
            last_check_at=time.time(),
            last_check_message=message,
            active_openvpn_node_id=active_openvpn_node_id,
            valid_nodes=valid_nodes_count,
        )
        return message
    except Exception as e:
        raise e
    finally:
        is_connecting = False
        maintenance_lock.release()


def collector_loop() -> None:
    global last_collector_heartbeat
    while True:
        last_collector_heartbeat = time.time()
        success = False
        try:
            print("[守护线程] 开始执行节点拉取与可用性检测周期任务...", flush=True)
            log_to_json("INFO", "Main", "开始执行节点拉取与可用性检测周期任务...")
            res = maintain_valid_nodes(force=False)
            if "没有拉取到新节点" not in res:
                success = True
            log_to_json("INFO", "Main", f"周期同步与检测任务完成，结果: {res}")
        except Exception as exc:
            err_msg = f"周期节点同步任务执行异常: {exc}"
            print(f"[错误] {err_msg}", flush=True)
            log_to_json("ERROR", "Main", err_msg)
            set_state(last_check_at=time.time(), last_check_message=f"check error: {exc}")
            
        if not active_openvpn_running() and not success:
            sleep_time = 30
        else:
            sleep_time = CHECK_INTERVAL_SECONDS
            
        time.sleep(sleep_time)

LOGIN_HTML = r"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>AimiliVPN - 安全登录</title>
  <link href="https://fonts.googleapis.com/css2?family=Outfit:wght@300;400;500;600;700&display=swap" rel="stylesheet">
  <style>
    :root {
      --bg-dark: #090d16;
      --bg-surface: rgba(15, 23, 42, 0.45);
      --border-color: rgba(255, 255, 255, 0.08);
      --text-primary: #f8fafc;
      --text-secondary: #94a3b8;
      --primary: #6366f1;
      --primary-gradient: linear-gradient(135deg, #6366f1 0%, #4f46e5 100%);
      --primary-hover: linear-gradient(135deg, #4f46e5 0%, #3730a3 100%);
      --success: #10b981;
      --danger: #f43f5e;
    }

    body {
      margin: 0;
      padding: 0;
      font-family: 'Outfit', -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
      background-color: var(--bg-dark);
      background-image: 
        radial-gradient(at 0% 0%, rgba(99, 102, 241, 0.15) 0px, transparent 50%),
        radial-gradient(at 100% 0%, rgba(16, 185, 129, 0.08) 0px, transparent 50%);
      height: 100vh;
      display: flex;
      align-items: center;
      justify-content: center;
      overflow: hidden;
    }

    .login-container {
      width: 100%;
      max-width: 400px;
      padding: 24px;
      box-sizing: border-box;
    }

    .login-card {
      background: var(--bg-surface);
      backdrop-filter: blur(16px);
      -webkit-backdrop-filter: blur(16px);
      border: 1px solid var(--border-color);
      border-radius: 20px;
      padding: 40px 32px;
      box-shadow: 0 20px 40px rgba(0, 0, 0, 0.3);
      text-align: center;
      transition: all 0.3s cubic-bezier(0.4, 0, 0.2, 1);
    }

    .brand-logo {
      width: 64px;
      height: 64px;
      background: rgba(99, 102, 241, 0.1);
      border: 1px solid rgba(99, 102, 241, 0.25);
      border-radius: 16px;
      display: flex;
      align-items: center;
      justify-content: center;
      margin: 0 auto 24px auto;
      color: var(--primary);
      position: relative;
    }

    .brand-logo::after {
      content: '';
      position: absolute;
      width: 100%;
      height: 100%;
      border-radius: 16px;
      border: 1px solid var(--success);
      opacity: 0.5;
      animation: ripple 2s infinite ease-out;
    }

    @keyframes ripple {
      0% { transform: scale(1); opacity: 0.5; }
      100% { transform: scale(1.3); opacity: 0; }
    }

    .login-title {
      font-size: 24px;
      font-weight: 700;
      color: var(--text-primary);
      margin: 0 0 8px 0;
      letter-spacing: 0.5px;
    }

    .login-subtitle {
      font-size: 14px;
      color: var(--text-secondary);
      margin: 0 0 32px 0;
    }

    .form-group {
      margin-bottom: 20px;
      text-align: left;
    }

    .form-label {
      display: block;
      font-size: 13px;
      font-weight: 500;
      color: var(--text-secondary);
      margin-bottom: 8px;
      margin-left: 4px;
    }

    .input-wrapper {
      position: relative;
    }

    .input-field {
      width: 100%;
      height: 48px;
      background: rgba(255, 255, 255, 0.03);
      border: 1px solid var(--border-color);
      border-radius: 10px;
      padding: 0 16px;
      box-sizing: border-box;
      color: var(--text-primary);
      font-family: inherit;
      font-size: 15px;
      outline: none;
      transition: all 0.2s ease;
    }

    .input-field:focus {
      border-color: var(--primary);
      box-shadow: 0 0 0 3px rgba(99, 102, 241, 0.2);
      background: rgba(15, 23, 42, 0.6);
    }

    .error-message {
      color: var(--danger);
      font-size: 13px;
      margin-top: 8px;
      min-height: 18px;
      text-align: left;
      margin-left: 4px;
      display: none;
    }

    .login-btn {
      width: 100%;
      height: 48px;
      background: var(--primary-gradient);
      border: none;
      border-radius: 10px;
      color: white;
      font-family: inherit;
      font-size: 15px;
      font-weight: 600;
      cursor: pointer;
      transition: all 0.2s ease;
      display: flex;
      align-items: center;
      justify-content: center;
      gap: 8px;
      box-shadow: 0 4px 12px rgba(99, 102, 241, 0.25);
    }

    .login-btn:hover {
      background: var(--primary-hover);
      transform: translateY(-1px);
      box-shadow: 0 6px 16px rgba(99, 102, 241, 0.35);
    }

    .login-btn:active {
      transform: translateY(1px);
    }

    .login-btn:disabled {
      opacity: 0.6;
      cursor: not-allowed;
      transform: none !important;
    }
  </style>
</head>
<body>
  <div class="login-container">
    <div class="login-card">
      <div class="brand-logo">
        <svg xmlns="http://www.w3.org/2000/svg" width="28" height="28" fill="none" viewBox="0 0 24 24" stroke="currentColor" stroke-width="2">
          <path stroke-linecap="round" stroke-linejoin="round" d="M12 15v2m-6 4h12a2 2 0 002-2v-6a2 2 0 00-2-2H6a2 2 0 00-2 2v6a2 2 0 002 2zm10-10V7a4 4 0 00-8 0v4h8z" />
        </svg>
      </div>
      <h2 class="login-title">AimiliVPN</h2>
      <p class="login-subtitle">请输入您的管理账号和安全密码以继续</p>
      
      <form id="login_form" onsubmit="handleLogin(event)">
        <div class="form-group">
          <label class="form-label" for="username">管理账号</label>
          <div class="input-wrapper">
            <input type="text" id="username" name="username" class="input-field" placeholder="请输入管理账号" required autocomplete="username">
          </div>
        </div>
        <div class="form-group" style="margin-top: 16px;">
          <label class="form-label" for="password">安全密码</label>
          <div class="input-wrapper">
            <input type="password" id="password" name="password" class="input-field" placeholder="请输入安全密码" required autocomplete="current-password">
          </div>
          <div id="error_text" class="error-message"></div>
        </div>
        
        <button type="submit" id="submit_btn" class="login-btn">
          <span>登录</span>
        </button>
      </form>
    </div>
  </div>

  <script>
    async function handleLogin(e) {
      e.preventDefault();
      const uname = document.getElementById("username").value.trim();
      const pwd = document.getElementById("password").value.trim();
      const errorText = document.getElementById("error_text");
      const submitBtn = document.getElementById("submit_btn");
      
      errorText.style.display = "none";
      submitBtn.disabled = true;
      submitBtn.querySelector("span").textContent = "正在验证...";
      
      try {
        const response = await fetch("./api/login", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ username: uname, password: pwd })
        });
        
        const data = await response.json();
        if (response.ok && data.ok) {
          window.location.reload();
        } else {
          errorText.textContent = data.error || "账号或密码不正确，请重新输入";
          errorText.style.display = "block";
          submitBtn.disabled = false;
          submitBtn.querySelector("span").textContent = "登录";
        }
      } catch (err) {
        errorText.textContent = "连接服务器失败，请稍后重试";
        errorText.style.display = "block";
        submitBtn.disabled = false;
        submitBtn.querySelector("span").textContent = "登录";
      }
    }
  </script>
</body>
</html>
"""

INDEX_HTML = r"""<!doctype html>
<!doctype html>
<html lang="zh-CN">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>AimiliVPN 节点管理系统</title>
<style>
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800&family=JetBrains+Mono:wght@400;500;600&display=swap');
*{margin:0;padding:0;box-sizing:border-box}
:root{
--bg-deep:#090c14;--bg-page:#0e1423;--bg-surface:rgba(16,21,40,0.65);--bg-elevated:rgba(22,29,54,0.82);--bg-glass:rgba(255,255,255,0.03);
--border-subtle:rgba(255,255,255,0.05);--border-default:rgba(255,255,255,0.08);--border-strong:rgba(255,255,255,0.13);
--text-primary:#f1f5f9;--text-secondary:#8b92a8;--text-tertiary:#5c6378;
--accent-gold:#f59e0b;--accent-gold-light:#fbbf24;--accent-gold-dark:#d97706;
--accent-cyan:#06b6d4;--accent-cyan-light:#22d3ee;--accent-emerald:#10b981;--accent-emerald-light:#34d399;
--accent-rose:#f43f5e;--accent-purple:#a78bfa;--accent-purple-light:#c4b5fd;--accent-orange:#fb923c;
--glow-gold:rgba(245,158,11,0.12);--glow-cyan:rgba(6,182,212,0.12);--glow-emerald:rgba(16,185,129,0.12);--glow-purple:rgba(167,139,250,0.12);
--radius-sm:8px;--radius-md:12px;--radius-lg:16px;--radius-xl:20px;--shadow-card:0 4px 24px rgba(0,0,0,0.3);--shadow-elevated:0 8px 40px rgba(0,0,0,0.4)
}
body{
margin:0;font-family:'Inter',-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;
background:var(--bg-page);background-image:radial-gradient(ellipse 80% 50% at 50% -20%,rgba(245,158,11,0.04) 0%,transparent 60%),radial-gradient(ellipse 60% 40% at 80% 40%,rgba(167,139,250,0.03) 0%,transparent 50%),radial-gradient(ellipse 50% 30% at 20% 80%,rgba(6,182,212,0.03) 0%,transparent 50%);
background-attachment:fixed;color:var(--text-primary);min-height:100vh;-webkit-font-smoothing:antialiased;line-height:1.5
}
::selection{background:rgba(245,158,11,0.2);color:#fff}

/* ===== Header ===== */
header{
padding:12px 32px;background:rgba(9,12,20,0.8);backdrop-filter:blur(24px);-webkit-backdrop-filter:blur(24px);
border-bottom:1px solid var(--border-subtle);display:flex;justify-content:space-between;align-items:center;gap:16px;
position:sticky;top:0;z-index:100
}
.brand{display:flex;align-items:center;gap:14px}
.brand-icon{
width:36px;height:36px;border-radius:10px;background:linear-gradient(135deg,#f59e0b,#d97706);
display:flex;align-items:center;justify-content:center;flex-shrink:0;box-shadow:0 4px 12px rgba(245,158,11,0.25)
}
.brand-icon svg{width:20px;height:20px;color:#0d1221}
.brand-text{display:flex;flex-direction:column}
.brand-title{font-size:18px;font-weight:800;letter-spacing:-0.3px;background:linear-gradient(135deg,#fbbf24 0%,#f59e0b 50%,#d97706 100%);-webkit-background-clip:text;-webkit-text-fill-color:transparent;line-height:1.2}
.brand-subtitle{font-size:11px;color:var(--text-tertiary);font-weight:500;letter-spacing:0.3px}
.status-badge{display:inline-flex;align-items:center;gap:6px;font-size:12px;color:var(--text-secondary);font-weight:500}
.status-badge .dot{width:7px;height:7px;border-radius:50%;background:var(--accent-emerald);box-shadow:0 0 8px rgba(16,185,129,0.5);display:inline-block}
.header-actions{display:flex;align-items:center;gap:8px}
.header-actions button,.header-actions .btn-telegram{
height:34px;border-radius:var(--radius-sm);padding:0 14px;font-weight:600;font-size:12px;
cursor:pointer;transition:all 0.2s cubic-bezier(0.4,0,0.2,1);
display:inline-flex;align-items:center;justify-content:center;gap:6px;
background:var(--bg-glass);border:1px solid var(--border-default);color:var(--text-primary);white-space:nowrap;text-decoration:none;font-family:inherit
}
.header-actions button:hover,.header-actions .btn-telegram:hover{background:rgba(255,255,255,0.06);border-color:var(--border-strong)}
.btn-telegram{background:rgba(43,162,223,0.1)!important;border-color:rgba(43,162,223,0.25)!important;color:#60b0e0!important}
.btn-telegram:hover{background:rgba(43,162,223,0.2)!important;border-color:rgba(43,162,223,0.4)!important}

/* ===== Channel Section ===== */
.channel-section{padding:20px 32px 0;max-width:1400px;margin:0 auto}
.channel-section-header{display:flex;align-items:center;justify-content:space-between;margin-bottom:14px}
.channel-section-title{font-size:14px;font-weight:700;text-transform:uppercase;letter-spacing:1px;color:var(--accent-gold-light);display:flex;align-items:center;gap:10px}
.channel-section-title svg{width:18px;height:18px}
.channel-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;margin-bottom:24px}
.channel-port-label{font-size:10px;font-weight:600;color:var(--accent-purple-light);background:rgba(167,139,250,0.1);padding:1px 6px;border-radius:4px;font-family:'JetBrains Mono',monospace}.channel-select-btn{background:rgba(99,102,241,0.08);border:1px solid rgba(99,102,241,0.2);border-radius:8px;padding:12px 8px;color:var(--text-primary);font-size:13px;font-weight:500;cursor:pointer;transition:all 0.15s ease;text-align:center}
.channel-select-btn:hover{background:rgba(99,102,241,0.18);border-color:var(--accent);transform:translateY(-1px)}
.channel-select-btn:active{transform:translateY(0)}
.channel-select-btn{background:rgba(99,102,241,0.08);border:1px solid rgba(99,102,241,0.2);border-radius:8px;padding:12px 8px;color:var(--text-primary);font-size:13px;font-weight:500;cursor:pointer;transition:all 0.15s ease;text-align:center}
.channel-select-btn:hover{background:rgba(99,102,241,0.18);border-color:var(--accent);transform:translateY(-1px)}
.channel-select-btn:active{transform:translateY(0)}
.channel-card{
background:var(--bg-surface);backdrop-filter:blur(12px);-webkit-backdrop-filter:blur(12px);
border:1px solid var(--border-default);border-radius:var(--radius-md);padding:12px 14px;
transition:all 0.3s cubic-bezier(0.4,0,0.2,1);position:relative;overflow:hidden;display:flex;flex-direction:column;gap:5px
}
.channel-card::before{content:'';position:absolute;top:0;left:0;right:0;height:2px;background:linear-gradient(90deg,transparent,rgba(167,139,250,0.3),transparent);opacity:0;transition:opacity 0.3s ease}
.channel-card:hover{border-color:rgba(255,255,255,0.12);transform:translateY(-2px);box-shadow:0 8px 24px rgba(0,0,0,0.25)}
.channel-card:hover::before{opacity:1}
.channel-card.active{border-color:rgba(16,185,129,0.25);background:linear-gradient(135deg,rgba(16,185,129,0.06) 0%,rgba(16,21,40,0.5) 100%)}
.channel-card.active::before{background:linear-gradient(90deg,transparent,rgba(16,185,129,0.4),transparent);opacity:1}
.channel-card-header{display:flex;align-items:center;justify-content:space-between}
.channel-card-title{font-size:11px;font-weight:700;color:var(--text-secondary);letter-spacing:0.3px}
.channel-card-status{width:7px;height:7px;border-radius:50%;display:inline-block;flex-shrink:0}
.channel-card-status.online{background:var(--accent-emerald);box-shadow:0 0 8px rgba(16,185,129,0.5)}
.channel-card-status.offline{background:#5c6378}
.channel-card-status.connecting{background:var(--accent-gold);animation:pulse 1.2s infinite}
.channel-card-ip{font-family:'JetBrains Mono',monospace;font-size:12px;font-weight:600;color:var(--text-primary);letter-spacing:-0.2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.channel-card-details{display:flex;align-items:center;gap:6px;flex-wrap:wrap;font-size:10px;color:var(--text-tertiary)}
.channel-card-asn{padding:1px 6px;border-radius:4px;background:rgba(167,139,250,0.08);color:var(--accent-purple-light);border:1px solid rgba(167,139,250,0.12);font-family:'JetBrains Mono',monospace;font-size:9px;font-weight:500;white-space:nowrap}
.channel-card-metrics{display:flex;align-items:center;gap:8px;font-family:'JetBrains Mono',monospace;font-size:10px}
.channel-card-metrics .metric-item{display:flex;align-items:center;gap:3px}
.channel-card-metrics .metric-label{font-size:8px;font-weight:600;text-transform:uppercase;color:var(--text-tertiary);font-family:'Inter',sans-serif;letter-spacing:0.3px}
.channel-card-metrics .speed-val{color:var(--text-secondary);font-weight:500}
.channel-card-metrics .speed-bar{height:3px;border-radius:2px;background:rgba(255,255,255,0.05);overflow:hidden;width:36px;flex-shrink:0}
.channel-card-metrics .speed-bar-fill{height:100%;border-radius:2px;background:linear-gradient(90deg,var(--accent-cyan),var(--accent-emerald));transition:width 0.5s ease}
.channel-card-metrics .latency-val{font-weight:600;padding:1px 5px;border-radius:3px;font-size:9px}
.channel-card-metrics .latency-good{background:rgba(16,185,129,0.08);color:var(--accent-emerald-light)}
.channel-card-metrics .latency-medium{background:rgba(245,158,11,0.08);color:var(--accent-gold-light)}
.channel-card-metrics .latency-poor{background:rgba(244,63,94,0.08);color:#fb7185}
.channel-num{width:18px;height:18px;border-radius:5px;background:rgba(167,139,250,0.1);border:1px solid rgba(167,139,250,0.15);color:var(--accent-purple-light);font-size:9px;font-weight:700;display:flex;align-items:center;justify-content:center;flex-shrink:0}
.channel-lock-options{display:flex;gap:4px;align-items:center}
.channel-lock-options select{flex:1;min-width:0;height:22px;background:rgba(255,255,255,0.03);border:1px solid var(--border-subtle);border-radius:4px;padding:0 4px;color:var(--text-secondary);font-family:inherit;font-size:9px;font-weight:500;outline:none;cursor:pointer;-webkit-appearance:none;appearance:none;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='8' height='8' viewBox='0 0 24 24' fill='none' stroke='%235c6378' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpolyline points='6 9 12 15 18 9'%3E%3C/polyline%3E%3C/svg%3E");background-repeat:no-repeat;background-position:right 3px center;padding-right:14px;transition:all 0.2s ease}
.channel-lock-options select:focus{border-color:var(--accent-gold);box-shadow:0 0 0 2px var(--glow-gold)}
.channel-lock-options select option{background:#161e34;color:#f1f5f9;font-size:10px}
.channel-lock-options .lock-label{font-size:8px;font-weight:600;text-transform:uppercase;letter-spacing:0.5px;color:var(--text-tertiary);white-space:nowrap;flex-shrink:0}
.channel-lock-options .lock-select-country{color:var(--accent-gold-light)}
.channel-lock-options .lock-select-asn{color:var(--accent-cyan-light)}
.channel-card-footer{display:flex;align-items:center;justify-content:space-between;padding-top:5px;border-top:1px solid var(--border-subtle)}
.channel-conn-status{display:flex;align-items:center;gap:5px;font-size:10px;font-weight:600}
.channel-conn-status .dot-sm{width:5px;height:5px;border-radius:50%;display:inline-block}
.channel-conn-status .dot-sm.connected{background:var(--accent-emerald);box-shadow:0 0 5px rgba(16,185,129,0.6)}
.channel-conn-status .dot-sm.disconnected{background:var(--text-tertiary)}
.channel-conn-status .text-connected{color:var(--accent-emerald-light)}
.channel-conn-status .text-disconnected{color:var(--text-tertiary)}
.channel-disconnect-btn{height:22px;padding:0 8px;border-radius:4px;font-size:9px;font-weight:600;cursor:pointer;transition:all 0.2s ease;font-family:inherit;background:rgba(244,63,94,0.08);color:#fb7185;border:1px solid rgba(244,63,94,0.15);display:inline-flex;align-items:center;gap:3px;white-space:nowrap}
.channel-disconnect-btn:hover{background:linear-gradient(135deg,#f43f5e,#e11d48);color:white;border-color:transparent;box-shadow:0 3px 8px rgba(244,63,94,0.25)}
.channel-connect-btn{height:22px;padding:0 8px;border-radius:4px;font-size:9px;font-weight:600;cursor:pointer;transition:all 0.2s ease;font-family:inherit;background:rgba(6,182,212,0.08);color:var(--accent-cyan-light);border:1px solid rgba(6,182,212,0.15);display:inline-flex;align-items:center;gap:3px;white-space:nowrap}
.channel-connect-btn:hover{background:linear-gradient(135deg,#06b6d4,#0891b2);color:white;border-color:transparent;box-shadow:0 3px 8px rgba(6,182,212,0.25)}

/* ===== Main ===== */
main{padding:0 32px 40px;max-width:1400px;margin:0 auto}

/* ===== Toolbar ===== */
.toolbar{background:var(--bg-surface);backdrop-filter:blur(12px);-webkit-backdrop-filter:blur(12px);border:1px solid var(--border-default);border-radius:var(--radius-md);padding:14px 18px;margin-bottom:20px;display:flex;gap:12px;flex-wrap:wrap;align-items:center}
.toolbar select{min-width:160px;height:40px;background:rgba(255,255,255,0.03);border:1px solid var(--border-default);border-radius:var(--radius-sm);padding:0 12px;color:var(--text-primary);font-family:inherit;font-size:13px;outline:none;transition:all 0.2s ease;cursor:pointer;-webkit-appearance:none;appearance:none;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='12' height='12' viewBox='0 0 24 24' fill='none' stroke='%238b92a8' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpolyline points='6 9 12 15 18 9'%3E%3C/polyline%3E%3C/svg%3E");background-repeat:no-repeat;background-position:right 12px center;padding-right:36px}
.toolbar select:focus{border-color:var(--accent-gold);box-shadow:0 0 0 3px var(--glow-gold)}
.toolbar select option{background:#161e34;color:#f1f5f9}
.toolbar input{flex:1;min-width:200px;height:40px;background:rgba(255,255,255,0.03);border:1px solid var(--border-default);border-radius:var(--radius-sm);padding:0 16px;color:var(--text-primary);font-family:inherit;font-size:13px;transition:all 0.2s ease;outline:none}
.toolbar input::placeholder{color:var(--text-tertiary)}
.toolbar input:focus{border-color:var(--accent-gold);box-shadow:0 0 0 3px var(--glow-gold);background:rgba(255,255,255,0.05)}
.toolbar-actions{display:flex;gap:8px;align-items:center;margin-left:auto}

/* ===== Table ===== */
.table-wrapper{background:var(--bg-surface);backdrop-filter:blur(12px);-webkit-backdrop-filter:blur(12px);border:1px solid var(--border-default);border-radius:var(--radius-lg);overflow:hidden;box-shadow:var(--shadow-card)}
.table-container{overflow-x:auto}
table{width:100%;border-collapse:collapse;text-align:left}
thead th{padding:12px 18px;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:0.8px;color:var(--text-tertiary);background:rgba(255,255,255,0.02);border-bottom:1px solid var(--border-default);white-space:nowrap;user-select:none}
tbody td{padding:12px 18px;font-size:13px;border-bottom:1px solid var(--border-subtle);color:var(--text-secondary);transition:background 0.15s ease}
tbody tr:last-child td{border-bottom:none}
tbody tr{transition:background 0.15s ease}
tbody tr:hover td{background:rgba(255,255,255,0.02)}
.active-row{background:rgba(16,185,129,0.04)!important;outline:1.5px solid rgba(16,185,129,0.25);outline-offset:-1px;position:relative}
.active-row td{border-bottom-color:rgba(16,185,129,0.1)}
.mono{font-family:'JetBrains Mono',monospace;font-size:12px}

/* ===== Badges ===== */
.badge{padding:3px 10px;border-radius:6px;font-size:11px;font-weight:600;display:inline-flex;align-items:center;gap:5px;border:1px solid transparent;white-space:nowrap}
.badge-available{background:rgba(16,185,129,0.08);color:var(--accent-emerald-light);border-color:rgba(16,185,129,0.15)}
.badge-unavailable{background:rgba(244,63,94,0.08);color:#fb7185;border-color:rgba(244,63,94,0.15)}
.badge-pending{background:rgba(245,158,11,0.08);color:var(--accent-gold-light);border-color:rgba(245,158,11,0.15)}
.badge-current{background:rgba(6,182,212,0.08);color:var(--accent-cyan-light);border-color:rgba(6,182,212,0.15)}
.badge-pulse{width:5px;height:5px;border-radius:50%;background:currentColor;animation:pulse 1.5s infinite;display:inline-block}
@keyframes pulse{0%,100%{transform:scale(0.9);opacity:1}50%{transform:scale(1.8);opacity:0.3}}

/* ===== Latency ===== */
.latency-val{font-family:'JetBrains Mono',monospace;font-size:12px;font-weight:500;padding:2px 8px;border-radius:4px}
.latency-good{background:rgba(16,185,129,0.08);color:var(--accent-emerald-light)}
.latency-medium{background:rgba(245,158,11,0.08);color:var(--accent-gold-light)}
.latency-poor{background:rgba(244,63,94,0.08);color:#fb7185}

/* ===== Buttons ===== */
.table-actions{display:flex;gap:8px}
.connect-btn{height:28px;padding:0 12px;border-radius:6px;font-size:11px;font-weight:600;cursor:pointer;transition:all 0.2s ease;font-family:inherit;background:rgba(6,182,212,0.08);color:var(--accent-cyan-light);border:1px solid rgba(6,182,212,0.2)}
.connect-btn:hover:not(:disabled){background:linear-gradient(135deg,#06b6d4,#0891b2);color:white;border-color:transparent;box-shadow:0 4px 10px rgba(6,182,212,0.25)}
.test-btn{height:28px;padding:0 12px;border-radius:6px;font-size:11px;font-weight:600;cursor:pointer;transition:all 0.2s ease;font-family:inherit;background:rgba(16,185,129,0.08);color:var(--accent-emerald-light);border:1px solid rgba(16,185,129,0.2)}
.test-btn:hover:not(:disabled){background:linear-gradient(135deg,#10b981,#059669);color:white;border-color:transparent;box-shadow:0 4px 10px rgba(16,185,129,0.25)}
.test-btn:disabled,.connect-btn:disabled{opacity:0.35;cursor:not-allowed}

/* ===== Buttons (global)==== */
.btn-primary{height:40px;border-radius:var(--radius-sm);padding:0 20px;font-weight:600;font-size:13px;cursor:pointer;transition:all 0.2s ease;font-family:inherit;display:inline-flex;align-items:center;justify-content:center;gap:6px;background:linear-gradient(135deg,#f59e0b,#d97706);color:#0d1221;border:none;box-shadow:0 4px 14px rgba(245,158,11,0.25)}
.btn-primary:hover{box-shadow:0 6px 20px rgba(245,158,11,0.35);transform:translateY(-1px)}
.btn-danger{height:40px;border-radius:var(--radius-sm);padding:0 20px;font-weight:600;font-size:13px;cursor:pointer;transition:all 0.2s ease;font-family:inherit;display:inline-flex;align-items:center;justify-content:center;gap:6px;background:linear-gradient(135deg,#f43f5e,#e11d48);color:white;border:none;box-shadow:0 4px 14px rgba(244,63,94,0.2)}
.btn-danger:hover{box-shadow:0 6px 20px rgba(244,63,94,0.35);transform:translateY(-1px)}
button:disabled{opacity:0.4;cursor:not-allowed;transform:none!important;box-shadow:none!important}

/* ===== Modals ===== */
.modal{display:none;position:fixed;z-index:10000;inset:0;background:rgba(9,12,20,0.75);backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px);align-items:center;justify-content:center;padding:20px}
.modal-content{background:rgba(16,21,40,0.92);border:1px solid var(--border-default);border-radius:var(--radius-xl);width:100%;max-width:500px;padding:32px;box-shadow:var(--shadow-elevated);position:relative;animation:modalFadeIn 0.25s cubic-bezier(0.4,0,0.2,1);max-height:85vh;overflow-y:auto}
@keyframes modalFadeIn{from{transform:scale(0.95) translateY(8px);opacity:0}to{transform:scale(1) translateY(0);opacity:1}}
.modal-title{font-size:18px;font-weight:700;color:var(--text-primary);margin-bottom:24px;display:flex;align-items:center;gap:10px}
.modal-close{position:absolute;top:16px;right:20px;font-size:20px;color:var(--text-tertiary);cursor:pointer;background:none;border:none;font-family:inherit;transition:color 0.2s;padding:4px;line-height:1}
.modal-close:hover{color:var(--text-primary)}
.form-group{margin-bottom:20px}
.form-label{display:block;font-size:12px;font-weight:600;color:var(--text-secondary);margin-bottom:6px}
.input-field{width:100%;height:42px;background:rgba(255,255,255,0.03);border:1px solid var(--border-default);border-radius:var(--radius-sm);padding:0 14px;color:var(--text-primary);font-family:inherit;font-size:14px;outline:none;transition:all 0.2s ease}
.input-field:focus{border-color:var(--accent-gold);box-shadow:0 0 0 3px var(--glow-gold);background:rgba(255,255,255,0.05)}
.form-error{display:none;background:rgba(244,63,94,0.08);color:#fb7185;padding:10px 14px;border-radius:var(--radius-sm);font-size:12px;margin-bottom:16px;line-height:1.4}
.form-success{display:none;background:rgba(16,185,129,0.08);color:var(--accent-emerald-light);padding:10px 14px;border-radius:var(--radius-sm);font-size:12px;margin-bottom:16px;line-height:1.4}
.modal-actions{display:flex;gap:10px;justify-content:flex-end;margin-top:24px}
.btn-secondary{height:40px;border-radius:var(--radius-sm);padding:0 20px;font-weight:600;font-size:13px;cursor:pointer;transition:all 0.2s ease;font-family:inherit;display:inline-flex;align-items:center;justify-content:center;gap:6px;background:var(--bg-glass);border:1px solid var(--border-default);color:var(--text-primary)}
.btn-secondary:hover{background:rgba(255,255,255,0.06);border-color:var(--border-strong)}
.option-group{display:grid;grid-template-columns:repeat(3,1fr);gap:8px}
@media(max-width:480px){.option-group{grid-template-columns:1fr}}
.option-card{background:rgba(255,255,255,0.02);border:1px solid var(--border-default);border-radius:var(--radius-sm);padding:12px;cursor:pointer;transition:all 0.2s ease;user-select:none;text-align:left}
.option-card:hover{background:rgba(255,255,255,0.04);border-color:rgba(255,255,255,0.12)}
.option-card.active{background:rgba(245,158,11,0.06);border-color:var(--accent-gold);box-shadow:0 0 12px var(--glow-gold)}
.option-card-title{font-size:12px;font-weight:600;color:var(--text-primary);margin-bottom:3px}
.option-card-desc{font-size:10px;color:var(--text-tertiary);line-height:1.3}

/* ===== Dropdown ===== */
.dropdown{position:relative;display:inline-block}
.dropdown-content{display:none;position:absolute;right:0;top:100%;margin-top:6px;min-width:180px;background:rgba(16,21,40,0.95);border:1px solid var(--border-default);border-radius:var(--radius-sm);overflow:hidden;z-index:200;box-shadow:var(--shadow-elevated)}
.dropdown-content a{display:block;padding:10px 16px;color:var(--text-secondary);font-size:12px;text-decoration:none;transition:all 0.15s ease;cursor:pointer}
.dropdown-content a:hover{background:rgba(255,255,255,0.04);color:var(--text-primary)}

/* ===== Gateway styles ===== */
.gateway-card{background:rgba(255,255,255,0.02);border:1px solid var(--border-subtle);border-radius:var(--radius-sm);padding:12px;margin-bottom:8px}
.gateway-card-top{display:flex;justify-content:space-between;align-items:center;margin-bottom:4px}
.gateway-name{font-size:13px;font-weight:600;color:var(--text-primary)}
.gateway-details{font-size:11px;color:var(--text-tertiary);margin-top:4px}
.gateway-error{font-size:11px;color:#fb7185;margin-top:4px}

/* ===== Logs styles ===== */
.log-filter-row{display:flex;gap:10px;margin-bottom:16px;align-items:center}
.log-filter-row select{height:36px;background:rgba(255,255,255,0.03);border:1px solid var(--border-default);border-radius:var(--radius-sm);padding:0 12px;color:var(--text-primary);font-family:inherit;font-size:12px;outline:none;cursor:pointer;-webkit-appearance:none;appearance:none;padding-right:30px;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='10' height='10' viewBox='0 0 24 24' fill='none' stroke='%238b92a8' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpolyline points='6 9 12 15 18 9'%3E%3C/polyline%3E%3C/svg%3E");background-repeat:no-repeat;background-position:right 10px center}
.log-terminal{background:#060a18;border:1px solid var(--border-subtle);border-radius:var(--radius-sm);padding:14px;height:400px;overflow-y:auto;font-family:'JetBrains Mono',monospace;font-size:11px;line-height:1.6;white-space:pre-wrap;word-break:break-all}
.log-terminal::-webkit-scrollbar{width:4px}
.log-terminal::-webkit-scrollbar-thumb{background:rgba(255,255,255,0.08);border-radius:2px}

/* ===== Blocked prefix styles ===== */
.blocked-section{margin-top:12px;padding:12px;background:rgba(255,255,255,0.02);border-radius:var(--radius-sm)}
.blocked-label{font-size:11px;font-weight:600;color:var(--text-secondary);margin-bottom:6px}
.blocked-pills{display:flex;flex-wrap:wrap;gap:4px;margin-bottom:8px}
.blocked-pill{display:inline-flex;align-items:center;gap:4px;padding:2px 8px;background:rgba(244,63,94,0.08);border:1px solid rgba(244,63,94,0.15);border-radius:4px;font-size:10px;color:#fb7185;font-family:'JetBrains Mono',monospace}
.blocked-pill-remove{cursor:pointer;font-size:12px;line-height:1;opacity:0.6}
.blocked-pill-remove:hover{opacity:1}
.blocked-empty{font-size:10px;color:var(--text-tertiary)}
.blocked-input-row{display:flex;gap:6px}
.blocked-input{flex:1;height:28px;background:rgba(255,255,255,0.03);border:1px solid var(--border-subtle);border-radius:4px;padding:0 8px;color:var(--text-primary);font-family:inherit;font-size:11px;outline:none;font-family:'JetBrains Mono',monospace}
.blocked-input:focus{border-color:var(--accent-gold);box-shadow:0 0 0 2px var(--glow-gold)}
.blocked-add-btn{height:28px;padding:0 10px;border-radius:4px;font-size:10px;font-weight:600;cursor:pointer;transition:all 0.2s ease;font-family:inherit;background:rgba(245,158,11,0.08);color:var(--accent-gold-light);border:1px solid rgba(245,158,11,0.15);white-space:nowrap}
.blocked-add-btn:hover{background:linear-gradient(135deg,#f59e0b,#d97706);color:#0d1221;border-color:transparent}

/* ===== Channel panel (hidden) ===== */
#channelPanel{display:none}

/* ===== Responsive ===== */
@media(max-width:1200px){.channel-grid{grid-template-columns:repeat(3,1fr)}}
@media(max-width:992px){.channel-grid{grid-template-columns:repeat(3,1fr)}}
@media(max-width:768px){
header{padding:10px 16px;flex-wrap:wrap}.channel-section{padding:16px 16px 0}main{padding:0 16px 32px}
.channel-grid{grid-template-columns:repeat(2,1fr)}.toolbar{flex-direction:column}.toolbar-actions{margin-left:0;width:100%}.toolbar-actions .btn-primary{flex:1}
}
@media(max-width:480px){.channel-grid{grid-template-columns:1fr}}
</style>
</head>
<body>

<!-- ===== Header ===== -->
<header>
<div class="brand">
<div class="brand-icon">
<svg viewBox="0 0 24 24" fill="currentColor"><path d="M12 2L2 7l10 5 10-5-10-5zM2 17l10 5 10-5M2 12l10 5 10-5"/></svg>
</div>
<div class="brand-text">
<span class="brand-title">VPN Gate</span>
<span class="brand-subtitle">AIMILI · 智能路由</span>
</div>
<span class="status-badge" id="systemStatus"><span class="dot"></span>系统运行中</span>
</div>
<div class="header-actions">
<a href="https://t.me/AimiliVPN" target="_blank" class="btn-telegram">
<svg width="14" height="14" viewBox="0 0 24 24" fill="currentColor"><path d="M11.944 0A12 12 0 0 0 0 12a12 12 0 0 0 12 12 12 12 0 0 0 12-12A12 12 0 0 0 12 0a12 12 0 0 0-.056 0zm4.962 7.224c.1-.002.321.023.465.14a.506.506 0 0 1 .171.325c.016.093.036.306.02.472-.18 1.898-.962 6.502-1.36 8.627-.168.9-.499 1.201-.82 1.23-.696.065-1.225-.46-1.9-.902-1.056-.693-1.653-1.124-2.678-1.8-1.185-.78-.417-1.21.258-1.91.177-.184 3.247-2.977 3.307-3.23.007-.032.014-.15-.056-.212s-.174-.041-.249-.024c-.106.024-1.793 1.14-5.061 3.345-.48.33-.913.49-1.302.48-.428-.008-1.252-.241-1.865-.44-.752-.245-1.349-.374-1.297-.789.027-.216.325-.437.893-.663 3.498-1.524 5.83-2.529 6.998-3.014 3.332-1.386 4.025-1.627 4.476-1.635z"/></svg>
Telegram 群组
</a>
<div class="dropdown">
<button onclick="toggleDropdown()">
<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="3"/><path d="M12 1v2M12 21v2M4.22 4.22l1.42 1.42M18.36 18.36l1.42 1.42M1 12h2M21 12h2M4.22 19.78l1.42-1.42M18.36 5.64l1.42-1.42"/></svg>
</button>
<div class="dropdown-content" id="adminDropdown">
<a onclick="openCredentialsModal()">账号凭据</a>
<a onclick="openNetworkModal()">网络设置</a>
<a onclick="openGatewayModal()">服务状态</a>
<a onclick="openLogsModal()">运行日志</a>
<a onclick="openVpsModal()">推荐 VPS</a>
<a onclick="logoutAdmin()" style="color:#fb7185">退出登录</a>
</div>
</div>
</div>
</header>
<!-- ===== Domain URL Bar ===== -->
<div id="domainBar" style="display:none;padding:6px 16px;background:rgba(99,102,241,0.06);border-bottom:1px solid var(--border-default);font-size:12px;color:var(--text-tertiary)">
  <svg viewBox="0 0 24 24" width="12" height="12" fill="none" stroke="currentColor" stroke-width="2" style="vertical-align:middle;margin-right:4px"><path d="M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71"/><path d="M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71"/></svg>
  <span id="domainUrl"></span>
</div>

<!-- ===== Channel Section ===== -->
<section class="channel-section">
<div class="channel-section-header">
<span class="channel-section-title">
<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="2" y="2" width="20" height="8" rx="2" ry="2"/><rect x="2" y="14" width="20" height="8" rx="2" ry="2"/><line x1="6" y1="6" x2="6.01" y2="6"/><line x1="6" y1="18" x2="6.01" y2="18"/></svg>
多通道状态
</span>
</div>
<div class="channel-grid" id="channelGrid"></div>
</section>

<!-- ===== Main ===== -->
<main>
<div class="toolbar">
<select id="countryFilter"><option value="">节点池</option></select>
<input type="text" id="excludeFilter" placeholder="排除IP前缀, 如 203.104" oninput="renderTable()" />
<input type="text" id="searchInput" placeholder="搜索节点名称、IP 或标签..." oninput="renderTable()" />
<div class="toolbar-actions">
<button class="btn-primary" onclick="testAllNodes()">全部测试</button>
</div>
</div>
<div class="table-wrapper">
<div class="table-container">
<table>
<thead><tr><th>节点名称</th><th>国家</th><th>出口 IP</th><th>ASN</th><th>延迟</th><th>节点速度</th><th>状态</th><th>操作</th></tr></thead>
<tbody id="tableBody"></tbody>
</table>
</div>
</div>
</main>

<!-- ===== Credentials Modal ===== -->
<div class="modal" id="credentialsModal">
<div class="modal-content">
<button class="modal-close" onclick="closeCredentialsModal()">&times;</button>
<div class="modal-title">账号凭据设置</div>
<div class="form-error" id="credentialsError"></div>
<div class="form-success" id="credentialsSuccess"></div>
<form id="credentialsForm" onsubmit="saveCredentials(event)">
<div class="form-group"><label class="form-label">用户名</label><input class="input-field" id="credUsername" required /></div>
<div class="form-group"><label class="form-label">密码</label><input class="input-field" id="credPassword" type="password" /></div>
<div class="form-group"><label class="form-label">网页管理端口</label><input class="input-field" id="credPort" type="number" value="8787" /></div>
<div class="form-group"><label class="form-label">登录安全后缀</label><input class="input-field" id="credSuffix" placeholder="仅英文和数字" /></div>
<div class="form-group"><label class="form-label">绑定域名（可选）</label><input class="input-field" id="credDomain" placeholder="例: admin.example.com" /></div>
<div class="form-group" style="display:flex;align-items:center;gap:8px"><label class="form-label" style="white-space:nowrap">启用 HTTPS</label><input type="checkbox" id="credHttps" style="width:18px;height:18px;accent-color:var(--accent)" /> <span style="font-size:11px;color:var(--text-tertiary)">需要 SSL 证书文件</span></div>
<div class="form-group"><label class="form-label">证书文件路径</label><input class="input-field" id="credCertPath" placeholder="/etc/ssl/certs/cert.pem" /></div>
<div class="form-group"><label class="form-label">密钥文件路径</label><input class="input-field" id="credKeyPath" placeholder="/etc/ssl/certs/key.pem" /></div>
<div class="modal-actions">
<button type="button" class="btn-secondary" onclick="closeCredentialsModal()">取消</button>
<button type="submit" class="btn-primary" id="credentialsSubmitBtn">保存修改</button>
</div>
</form>
</div>
</div>

<!-- ===== Network Modal ===== -->
<div class="modal" id="networkModal">
<div class="modal-content">
<button class="modal-close" onclick="closeNetworkModal()">&times;</button>
<div class="modal-title">网络设置</div>
<div class="form-error" id="networkError"></div>
<div class="form-success" id="networkSuccess"></div>
<form id="networkForm" onsubmit="saveNetwork(event)">
<div class="form-group"><label class="form-label">代理出口端口</label><input class="input-field" id="netProxyPort" type="number" min="1024" max="65535" value="7928" /></div>
<div class="form-group"><label class="form-label">路由模式</label><div class="option-group" id="routingModeGroup">
<div class="option-card active" data-value="auto" onclick="selectOptionCard('routingMode','auto')"><div class="option-card-title">智能路由</div><div class="option-card-desc">自动选择最优 IP</div></div>
<div class="option-card" data-value="fixed_region" onclick="selectOptionCard('routingMode','fixed_region')"><div class="option-card-title">区域锁定</div><div class="option-card-desc">锁定到指定国家</div></div>
<div class="option-card" data-value="sequential" onclick="selectOptionCard('routingMode','sequential')"><div class="option-card-title">顺序路由</div><div class="option-card-desc">逐节点换 IP</div></div>
</div><input type="hidden" id="netRoutingMode" value="auto" /></div>
<div class="form-group" id="forceCountryGroup" style="display:none"><label class="form-label">锁定目标国家</label><select class="input-field" id="netForceCountry"><option value="">请选择...</option></select></div>
<div class="form-group"><label class="form-label">IP 类型偏好</label><div class="option-group" id="routingIpTypeGroup">
<div class="option-card active" data-value="all" onclick="selectOptionCard('routingIpType','all')"><div class="option-card-title">全部类型</div><div class="option-card-desc">IPv4 和 IPv6</div></div>
<div class="option-card" data-value="ipv4" onclick="selectOptionCard('routingIpType','ipv4')"><div class="option-card-title">仅 IPv4</div><div class="option-card-desc">只使用 IPv4</div></div>
<div class="option-card" data-value="ipv6" onclick="selectOptionCard('routingIpType','ipv6')"><div class="option-card-title">仅 IPv6</div><div class="option-card-desc">只使用 IPv6</div></div>
</div><input type="hidden" id="netRoutingIpType" value="all" /></div>
<div class="modal-actions">
<button type="button" class="btn-secondary" onclick="closeNetworkModal()">取消</button>
<button type="submit" class="btn-primary" id="networkSubmitBtn">保存修改</button>
</div>
</form>
</div>
</div>

<!-- ===== VPS Modal ===== -->
<div class="modal" id="vpsModal">
<div class="modal-content">
<button class="modal-close" onclick="closeVpsModal()">&times;</button>
<div class="modal-title">推荐 VPS</div>
<p style="color:var(--text-secondary);font-size:13px;line-height:1.6">
推荐使用以下 VPS 服务商部署节点：<br/><br/>
&#8226; <strong style="color:var(--text-primary)">Vultr</strong> — 全球 32 个数据中心，最低 $2.5/月<br/>
&#8226; <strong style="color:var(--text-primary)">Hetzner</strong> — 欧洲优质线路，性价比高<br/>
&#8226; <strong style="color:var(--text-primary)">Oracle Cloud</strong> — 免费永久套餐（需抢购）<br/>
&#8226; <strong style="color:var(--text-primary)">BandwagonHost</strong> — 中国优化线路<br/>
&#8226; <strong style="color:var(--text-primary)">RackNerd</strong> — 低价年付方案<br/><br/>
建议选择延迟 < 150ms 的节点以获得最佳体验。
</p>
<div class="modal-actions"><button type="button" class="btn-secondary" onclick="closeVpsModal()">关闭</button></div>
</div>
</div>


<!-- ===== Channel Selector Modal ===== -->
<div class="modal" id="channelSelectModal">
<div class="modal-content" style="max-width:400px">
<button class="modal-close" onclick="closeChannelSelectModal()">&times;</button>
<div class="modal-title" id="channelSelectTitle">选择目标通道</div>
<p style="color:var(--text-secondary);font-size:13px;margin:0 0 16px 0" id="channelSelectNodeInfo"></p>
<div id="channelSelectList" style="display:grid;grid-template-columns:repeat(3,1fr);gap:8px"></div>
<div class="modal-actions" style="margin-top:12px">
<button type="button" class="btn-secondary" onclick="closeChannelSelectModal()">取消</button>
</div>
</div>
</div>
<!-- ===== Gateway Modal ===== -->
<div class="modal" id="gatewayModal">
<div class="modal-content">
<button class="modal-close" onclick="closeGatewayModal()">&times;</button>
<div class="modal-title">网关服务状态</div>
<div id="gatewayServicesList"></div>
<div class="modal-actions"><button type="button" class="btn-secondary" onclick="closeGatewayModal()">关闭</button></div>
</div>
</div>

<!-- ===== Logs Modal ===== -->
<div class="modal" id="logsModal">
<div class="modal-content" style="max-width:720px">
<button class="modal-close" onclick="closeLogsModal()">&times;</button>
<div class="modal-title">运行日志</div>
<div class="log-filter-row">
<select id="logFilterSelect" onchange="filterAndRenderLogs()"><option value="all">全部</option><option value="proxy">代理</option><option value="vpn">VPN</option><option value="system">系统</option></select>
<button class="btn-secondary" onclick="copyLogContent()" style="height:36px;font-size:11px">复制</button>
<button class="btn-secondary" onclick="exportLogContent()" style="height:36px;font-size:11px">导出</button>
</div>
<div class="log-terminal" id="logTerminalContainer"><div style="color:var(--text-tertiary);text-align:center;margin-top:150px">暂无日志</div></div>
</div>
</div>

<script>
// ===== Utility Functions =====
function $(id) { return document.getElementById(id); }
function esc(s) { if (!s) return ''; return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }

var COUNTRY_MAP = {
  'JP':'日本','US':'美国','SG':'新加坡','KR':'韩国','GB':'英国','DE':'德国',
  'FR':'法国','CA':'加拿大','AU':'澳大利亚','NL':'荷兰','HK':'香港','TW':'台湾',
  'IN':'印度','BR':'巴西','RU':'俄罗斯','CH':'瑞士','SE':'瑞典','NO':'挪威',
  'IT':'意大利','ES':'西班牙','Unknown':'未知'
};
function translateCountry(code) { return COUNTRY_MAP[code] || code || ''; }

var COUNTRIES = [
  {name:'自动',short:''},{name:'日本',short:'JP'},{name:'美国',short:'US'},{name:'韩国',short:'KR'},
  {name:'新加坡',short:'SG'},{name:'英国',short:'GB'},{name:'德国',short:'DE'},{name:'法国',short:'FR'},
  {name:'加拿大',short:'CA'},{name:'澳大利亚',short:'AU'},{name:'荷兰',short:'NL'},{name:'香港',short:'HK'},
  {name:'台湾',short:'TW'},{name:'印度',short:'IN'},{name:'巴西',short:'BR'},{name:'俄罗斯',short:'RU'},
  {name:'瑞士',short:'CH'},{name:'瑞典',short:'SE'},{name:'挪威',short:'NO'},{name:'意大利',short:'IT'},{name:'西班牙',short:'ES'}
];

function getCountryOptions() { var cm={}; (nodes.length?nodes:sampleNodes).forEach(function(n){ var c=n.country||''; if(c)cm[c]=1; }); var keys=Object.keys(cm).sort(); return ['','自动'].concat(keys); }
var asnOptions = ['','自动','AS4713','AS16509','AS15169','AS8075','AS45102','AS16276','AS24940','AS12876','AS4766'];

// ===== State =====
var nodes = [];
var state = {};
var channels = [];
var testingNodeIds = new Set();
var rawLogsCache = [];
var gatewayPollInterval = null;
var logsPollInterval = null;
var channelPollInterval = null;

// ===== Sample / Fallback data =====
var sampleChannels = [];
for (var si = 0; si < 6; si++) {
  sampleChannels.push({
    index: si, exit_ip: '203.104.'+(209+Math.floor(si/3))+'.'+(15+si*7),
    asn: 'AS'+(4000+si*113), asn_org: ['NTT Communications','Amazon AWS','Google Cloud','Microsoft Azure','SoftBank','KDDI'][si],
    speed: (Math.random()*45+5).toFixed(1), speed_unit:'MB/s', latency: Math.floor(Math.random()*180+25),
    online: false, connecting:false, country:['日本','美国','新加坡','韩国','英国','德国'][si],
    lock_country:'', lock_asn:'', port:7928+si
  });
}
var sampleNodes = [
  {name:'日本 · JP-1',country:'日本',ip:'203.104.209.15',asn:'AS4713',asn_org:'NTT Communications',latency:42,speed:28.4,status:'available'},
  {name:'日本 · JP-2',country:'日本',ip:'203.104.209.22',asn:'AS4713',asn_org:'NTT Communications',latency:45,speed:26.1,status:'available'},
  {name:'美国 · US-1',country:'美国',ip:'198.51.100.10',asn:'AS16509',asn_org:'Amazon AWS',latency:128,speed:18.7,status:'available'},
  {name:'美国 · US-2',country:'美国',ip:'198.51.100.25',asn:'AS15169',asn_org:'Google Cloud',latency:135,speed:15.2,status:'available'},
  {name:'新加坡 · SG-1',country:'新加坡',ip:'103.25.59.10',asn:'AS45102',asn_org:'Tencent Cloud',latency:68,speed:32.1,status:'available'},
  {name:'新加坡 · SG-2',country:'新加坡',ip:'103.25.59.18',asn:'AS45102',asn_org:'Tencent Cloud',latency:72,speed:29.8,status:'available'},
  {name:'韩国 · KR-1',country:'韩国',ip:'121.78.105.30',asn:'AS4766',asn_org:'Korea Telecom',latency:55,speed:35.6,status:'available'},
  {name:'韩国 · KR-2',country:'韩国',ip:'121.78.105.38',asn:'AS4766',asn_org:'Korea Telecom',latency:58,speed:33.2,status:'pending'},
  {name:'英国 · GB-1',country:'英国',ip:'51.15.72.10',asn:'AS12876',asn_org:'Online SAS',latency:182,speed:11.4,status:'available'},
  {name:'德国 · DE-1',country:'德国',ip:'78.46.82.15',asn:'AS24940',asn_org:'Hetzner Online',latency:195,speed:9.8,status:'unavailable'}
];

// ===== Data Loading =====
async function load() {
  try {
    var r = await fetch('./api/nodes');
    var d = await r.json();
    nodes = d.nodes || [];
    nodes = nodes.map(function(n){ if(n.latency==null&&n.latency_ms!=null)n.latency=n.latency_ms; if(n.latency==null&&n.ping!=null)n.latency=n.ping; if(!n.name)n.name=n.host_name||n.id||''; if(!n.status)n.status=n.probe_status||(n.active?'available':'pending'); return n; });
    state = d.state || {};
    updateDomainBar(state);
    $('systemStatus').innerHTML = '<span class=\"dot\"></span>系统运行中';
    updateCountryFilter();
    renderChannels();
    renderTable();
  } catch(e) {
    // Fallback to sample data
    nodes = sampleNodes;
    state = {};
    updateCountryFilter();
    renderChannels();
    renderTable();
  }
}


function updateDomainBar(s) {
  var bar = $('domainBar');
  var urlEl = $('domainUrl');
  if (!bar || !urlEl) return;
  var domain = s && s.domain || '';
  var https = s && s.https || false;
  var port = s && s.port || 8787;
  var suffix = s && s.secret_path || '';
  if (domain) {
    var proto = https ? 'https' : 'http';
    var portStr = (proto==='https'&&port===443)||(proto==='http'&&port===80) ? '' : ':'+port;
    urlEl.innerHTML = '<span style="color:var(--text-secondary)">访问地址: </span><a href="'+proto+'://'+domain+portStr+'/'+suffix+'/" target="_blank" style="color:var(--accent);text-decoration:none">'+proto+'://'+domain+portStr+'/'+suffix+'/</a>';
    bar.style.display = 'block';
  } else {
    bar.style.display = 'none';
  }
}
function updateCountryFilter() {

  var sel = $('countryFilter');
  if (!sel) return;
  var countMap = {};
  var list = (nodes.length ? nodes : sampleNodes);
  list.forEach(function(n) {
    var c = n.country || '';
    if (c) countMap[c] = (countMap[c]||0)+1;
  });
  var countries = Object.keys(countMap).sort();
  var html = '<option value="">节点池</option>';
  countries.forEach(function(c) {
    html += '<option value="'+esc(c)+'">'+esc(c)+' ('+countMap[c]+'个节点)</option>';
  });
  sel.innerHTML = html;
}

// ===== Render Channels =====
function buildCountrySelect(selected) {
  var h = '';
  for (var i=0;i<getCountryOptions().length;i++) {
    var v=getCountryOptions()[i], label=v||'自动', val=v||'', sel=(val===selected)?' selected':'';
    h += '<option value="'+val+'"'+sel+'>'+label+'</option>';
  }
  return h;
}
function buildAsnSelectForChannel(selected, countryFilter) {
  var list = (nodes.length ? nodes : sampleNodes);
  if (countryFilter) list = list.filter(function(n){ return (n.country||"")===countryFilter; });
  var asnMap = {};
  list.forEach(function(n){ var a = n.asn||""; if(a) asnMap[a]=(asnMap[a]||0)+1; });
  var asns = Object.keys(asnMap).sort();
  var h = "<option value=\"\">自动</option>";
  asns.forEach(function(a){ var cnt=asnMap[a]>1?"("+asnMap[a]+"个)":""; var s=(a===selected)?" selected":""; h+="<option value=\""+a+"\""+s+">"+a+cnt+"</option>"; });
  if(!asns.length) h += "<option value=\"\" disabled>无可用ASN</option>";
  return h;
}
function buildNodeSelectForChannel(countryFilter, asnFilter, selected) {
  var list = (nodes.length ? nodes : sampleNodes);
  if (countryFilter) list = list.filter(function(n){ return (n.country||"")===countryFilter; });
  if (asnFilter) list = list.filter(function(n){ return (n.asn||"")===asnFilter; });
  var h = "<option value=\"\">自动选择</option>";
  list.forEach(function(n){ var s=(n.name===selected||n.id===selected)?" selected":""; var label=n.name||n.ip||""; h+="<option value=\""+esc(n.name)+"\""+s+">"+esc(label)+" ("+esc(n.ip||"")+")</option>"; });
  if(!list.length) h += "<option value=\"\" disabled>无匹配节点</option>";
  return h;
}

function renderChannels() {
  var grid = $('channelGrid');
  if (!grid) return;
  var chList = (channels.length ? channels : sampleChannels);
  var html = '';
  for (var i=0;i<Math.min(chList.length,6);i++) {
    var ch = chList[i] || {index:i,online:false};
    var statusClass = ch.online ? 'online' : (ch.connecting ? 'connecting' : 'offline');
    var activeClass = (i===0&&ch.online) ? 'active' : '';
    var speedVal = ch.online ? (ch.speed||'-') : '-';
    var speedUnit = ch.online ? (ch.speed_unit||'') : '';
    var barWidth = ch.online ? Math.min(100,Math.floor(parseFloat(speedVal)*3)) : 0;
    var ipDisplay = ch.online ? (ch.exit_ip||'--.--.--.--') : '--.--.--.--';
    var asnDisplay = ch.online ? ((ch.asn||'')+' · '+(ch.asn_org||'')) : '--';
    var latencyDisplay = ch.online ? (ch.latency>0?ch.latency:'-') : '-';
    var latencyClass = '';
    if (ch.online && ch.latency!=null) {
      latencyClass = ch.latency>0 ? (ch.latency<80 ? 'latency-good' : (ch.latency<160 ? 'latency-medium' : 'latency-poor')) : '';
    }
    var country = ch.country || '';
    html += '<div class="channel-card '+activeClass+'">'+
      '<div class="channel-card-header"><div style="display:flex;align-items:center;gap:6px"><span class="channel-num">'+i+'</span><span class="channel-card-title">通道'+i+'</span><span class="channel-port-label">:'+(ch.port||(7928+i))+'</span></div><span class="channel-card-status '+statusClass+'"></span></div>'+
      '<div class="channel-card-ip" title="'+ipDisplay+'"><span style="font-size:9px;color:var(--text-tertiary);font-weight:400;font-family:Inter,sans-serif;margin-right:4px">出口IP </span>'+ipDisplay+'</div>'+
      '<div class="channel-card-details"><span class="channel-card-asn">'+asnDisplay+'</span>'+(ch.online&&country?'<span style="color:var(--text-tertiary)">'+esc(country)+'</span>':'')+'</div>'+
      '<div class="channel-card-metrics"><span class="metric-item"><span class="metric-label">时延</span><span class="latency-val '+latencyClass+'">'+latencyDisplay+' ms</span></span>'+
      '<span class="metric-item"><span class="metric-label">速度</span><span class="speed-val">'+speedVal+'</span><span style="font-size:8px;color:var(--text-tertiary)">'+speedUnit+'</span><span class="speed-bar"><span class="speed-bar-fill" style="width:'+barWidth+'%"></span></span></span></div>'+
      '<div class="channel-lock-options"><span class="lock-label lock-select-country">国家</span><select onchange="setChannelCountry('+i+',this.value)">'+buildCountrySelect(ch.lock_country||'')+'</select>'+
      '<span class="lock-label lock-select-asn">ASN</span><select onchange="setChannelAsn('+i+',this.value)">'+buildAsnSelectForChannel(ch.lock_asn||'',ch.lock_country||'')+'</select><span class="lock-label" style="font-size:8px;color:var(--text-tertiary)">节点</span><select onchange="setChannelNode('+i+',this.value)">'+buildNodeSelectForChannel(ch.lock_country||'',ch.lock_asn||'',ch.lock_node||'')+'</select></div>'+
      '<div class="channel-card-footer"><div class="channel-conn-status"><span class="dot-sm '+(ch.online?'connected':'disconnected')+'"></span><span class="'+(ch.online?'text-connected':'text-disconnected')+'">'+(ch.online?'已连接':'未连接')+'</span></div>'+
      (ch.online?'<button class="channel-disconnect-btn" onclick="disconnectChannel('+i+')">断开</button>':'<button class="channel-connect-btn" onclick="connectChannel('+i+')">连接</button>')+
      '</div></div>';
  }
  grid.innerHTML = html;
}

// ===== Render Table =====
function renderTable() {
  if (!window.filteredNodes && !nodes.length) nodes = sampleNodes;
  var list = nodes.length ? nodes : sampleNodes;
  var filterVal = $('countryFilter') ? $('countryFilter').value : '';
  var searchVal = $('searchInput') ? $('searchInput').value.toLowerCase().trim() : '';
  if (filterVal) list = list.filter(function(n){ return (n.country||'')===filterVal; });
  var excludeVal = $('excludeFilter') ? $('excludeFilter').value.trim() : '';
  if (excludeVal) {
    var prefixes = excludeVal.split(',').map(function(s){ return s.trim(); }).filter(function(s){ return s; });
    if (prefixes.length) list = list.filter(function(n){
      var ip = n.ip||'';
      for (var j=0;j<prefixes.length;j++) { if (ip.indexOf(prefixes[j])===0) return false; }
      return true;
    });
  }
  if (searchVal) list = list.filter(function(n){ return (n.name||'').toLowerCase().indexOf(searchVal)>=0||(n.ip||'').indexOf(searchVal)>=0; });
  var tbody = $('tableBody');
  if (!tbody) return;
  var html = '';
  for (var i=0;i<list.length;i++) {
    var n=list[i];
    var isActive = n.is_current || (i===0 && !nodes.length);
    var statusLabel='', statusBadgeClass='';
    if (n.status==='available'||n.status==='online') { statusLabel='可用'; statusBadgeClass='badge-available'; }
    else if (n.status==='unavailable'||n.status==='offline') { statusLabel='不可用'; statusBadgeClass='badge-unavailable'; }
    else if (n.status==='pending') { statusLabel='待测'; statusBadgeClass='badge-pending'; }
    else { statusLabel='可用'; statusBadgeClass='badge-available'; }
    var latencyClass = n.latency>0 ? (n.latency<80 ? 'latency-good' : (n.latency<160 ? 'latency-medium' : 'latency-poor')) : '';
    var asnDisplay = (n.asn||'')+' · '+(n.asn_org||'');
    var isTesting = testingNodeIds.has(n.name);
    html += '<tr class="'+(isActive?'active-row':'')+'">'+
      '<td style="font-weight:600;color:var(--text-primary)">'+esc(n.name||'')+'</td>'+
      '<td>'+esc(n.country||'')+'</td>'+
      '<td class="mono">'+esc(n.ip||'')+'</td>'+
      '<td class="mono" style="font-size:11px;color:var(--text-tertiary)">'+esc(asnDisplay)+'</td>'+
      '<td><span class="latency-val '+latencyClass+'">'+(n.latency>0?n.latency:'-')+' ms</span></td>'+
      '<td style="font-family:\'JetBrains Mono\',monospace;font-weight:500;color:var(--text-primary)">'+(n.speed!=null?n.speed:'-')+' MB/s</td>'+
      '<td><span class="badge '+statusBadgeClass+'">'+(statusLabel==='可用'?'<span class="badge-pulse"></span>':'')+statusLabel+'</span></td>'+
      '<td><div class="table-actions">'+
      '<button class="connect-btn"'+(n.status==='unavailable'||n.status==='offline'||isTesting?' disabled':'')+' onclick="openChannelSelectModal(\''+esc(n.id||n.name)+'\',\''+esc(n.name||n.ip||'')+'\',\''+esc(n.country||'')+'\',\''+esc(n.asn||'')+'\')">连接</button>'+
      '<button class="test-btn"'+(n.status==='unavailable'||n.status==='offline'||isTesting?' disabled':'')+' onclick="testNode(\''+esc(n.name)+'\')">'+(isTesting?'测速中...':'测速')+'</button>'+
      '</div></td></tr>';
  }
  tbody.innerHTML = html;
}

// ===== Node Actions =====
async function selectNode(name) {
  try {
    var r = await fetch('./api/select_node',{
      method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({id:name})
    });
    var d = await r.json();
    if (d.error) { alert('连接失败: '+d.error); return; }
    await load();
  } catch(e) { alert('连接请求失败，请检查网络'); }
}


// ===== Channel Selector Modal =====
var _selNode = null;

function openChannelSelectModal(nid, label, country, asn) {
  _selNode = {id:nid, label:label, country:country, asn:asn};
  $("channelSelectTitle").textContent = "选择目标通道";
  $("channelSelectNodeInfo").innerHTML = "节点: <strong>"+esc(label)+"</strong> ("+esc(country)+(asn?" \u00b7 "+esc(asn):"")+")";
  var box = $("channelSelectList");
  box.innerHTML = "";
  for (var ci=0; ci<6; ci++) {
    var b = document.createElement("button");
    b.className = "channel-select-btn";
    b.textContent = "通道 "+ci;
    b.onclick = (function(i){ return function(){ _assignChannel(i); }; })(ci);
    box.appendChild(b);
  }
  $("channelSelectModal").style.display = "flex";
}

function closeChannelSelectModal() {
  $("channelSelectModal").style.display = "none";
  _selNode = null;
}

function _assignChannel(idx) {
  var n = _selNode; if (!n) return;
  var cl = channels.length ? channels : sampleChannels;
  if (!cl[idx]) return;
  cl[idx].lock_country = n.country||"";
  cl[idx].lock_asn = n.asn||"";
  cl[idx].lock_node = n.id||"";
  closeChannelSelectModal();
  renderChannels();
  setTimeout(function(){ connectChannel(idx); }, 300);
}
async function testNode(name) {
  if (testingNodeIds.has(name)) return;
  testingNodeIds.add(name);
  renderTable();
  try {
    var r = await fetch('./api/test_node',{
      method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({id:name})
    });
    var d = await r.json();
    if (d.ok) { await load(); }
  } catch(e) {}
  testingNodeIds.delete(name);
  renderTable();
}

async function testAllNodes() {
  var list = nodes.length ? nodes : sampleNodes;
  for (var i=0;i<list.length;i++) {
    if (list[i].status==='unavailable'||list[i].status==='offline') continue;
    await testNode(list[i].name);
  }
}

function setChannelNode(idx, val) {
  var chList = channels.length ? channels : sampleChannels;
  if (chList[idx]) chList[idx].lock_node = val;
}
// ===== Channel Actions =====
async function connectChannel(idx) {
  var chList = channels.length ? channels : sampleChannels;
  if (!chList[idx]) return;
  var ch = chList[idx];
  var list = nodes.length ? nodes : sampleNodes;
  // Filter nodes by channel's country/ASN/node settings
  if (ch.lock_country) list = list.filter(function(n){ return (n.country||'')===ch.lock_country; });
  if (ch.lock_asn) list = list.filter(function(n){ return (n.asn||'')===ch.lock_asn; });
  if (ch.lock_node) list = list.filter(function(n){ return (n.name===ch.lock_node||n.id===ch.lock_node); });
  if (!list.length) { alert('没有匹配的节点，请检查国家/ASN/节点选择'); return; }
  var target = list[0];
  ch.connecting = true;
  ch.online = false;
  renderChannels();
  try {
    var r = await fetch('./api/connect', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({channel: idx, id: target.id||target.name})
    });
    var d = await r.json();
    if (d.ok) {
      ch.online = true;
      ch.connecting = false;
      ch.speed = target.speed || '-';
      ch.latency = target.latency || 0;
      ch.exit_ip = target.ip || '';
      ch.asn = target.asn || '';
      ch.asn_org = target.asn_org || '';
      ch.country = target.country || '';
    } else {
      alert('连接失败: '+(d.error||'未知错误'));
      ch.connecting = false;
    }
  } catch(e) {
    alert('连接请求失败');
    ch.connecting = false;
  }
  renderChannels();
}

function disconnectChannel(idx) {
  var chList = channels.length ? channels : sampleChannels;
  if (chList[idx]) {
    chList[idx].online = false;
    chList[idx].connecting = false;
    renderChannels();
  }
  fetch('./api/disconnect_channel', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({channel:idx})}).catch(function(){})
}

function setChannelCountry(idx, val) {
  var chList = channels.length ? channels : sampleChannels;
  if (chList[idx]) chList[idx].lock_country = val;
  renderChannels();
  // Real API: fetch('./api/set_channel_country', {method:'POST', body: JSON.stringify({channel:idx, country:val})});
}

function setChannelAsn(idx, val) {
  var chList = channels.length ? channels : sampleChannels;
  if (chList[idx]) chList[idx].lock_asn = val;
  renderChannels();
  // Real API: fetch('./api/set_channel_asn', {method:'POST', body: JSON.stringify({channel:idx, asn:val})});
}

// ===== Multi-channel =====
async function updateChannels() {
  try {
    var r = await fetch('./api/channels');
    var d = await r.json();
    channels = d.channels || [];
    renderChannels();
  } catch(e) {}
}

async function setChannelCountryRemote(channel, country) {
  try {
    await fetch('./api/set_channel_country', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({channel:channel, country:country})
    });
  } catch(e) {}
}

// ===== Admin Dropdown =====
function toggleDropdown() {
  var dd = $('adminDropdown');
  dd.style.display = dd.style.display==='block' ? 'none' : 'block';
}
document.addEventListener('click', function(e) {
  var dd=$('adminDropdown');
  if(dd&&!e.target.closest('.dropdown')) dd.style.display='none';
});

async function logoutAdmin() {
  try {
    var r = await fetch('./api/logout', {method:'POST'});
    if (r.ok) window.location.reload();
  } catch(e) { window.location.reload(); }
}

// ===== Credentials Modal =====
function openCredentialsModal() {
  $('credentialsError').style.display='none';
  $('credentialsSuccess').style.display='none';
  $('credentialsForm').reset();
  if (state) {
    $('credUsername').value = state.username||'';
    $('credPassword').value = '';
    $('credPort').value = state.port||8787;
    $('credSuffix').value = state.secret_path||'';
    $('credDomain').value = state.domain||'';
    $('credHttps').checked = state.https||false;
    $('credCertPath').value = state.cert_path||'';
    $('credKeyPath').value = state.key_path||'';
  }
  $('credentialsModal').style.display='flex';
  $('adminDropdown').style.display='none';
}
function closeCredentialsModal() { $('credentialsModal').style.display='none'; }

async function saveCredentials(e) {
  e.preventDefault();
  var errorEl=$('credentialsError'), successEl=$('credentialsSuccess'), btn=$('credentialsSubmitBtn');
  errorEl.style.display='none'; successEl.style.display='none';
  var username=$('credUsername').value.trim(), password=$('credPassword').value.trim();
  var port=parseInt($('credPort').value), suffix=$('credSuffix').value.trim();
  var domain=$('credDomain').value.trim();
  var https=$('credHttps').checked;
  var certPath=$('credCertPath').value.trim();
  var keyPath=$('credKeyPath').value.trim();
  if (!username||(!password&&!(state&&state.password_set))) {
    errorEl.textContent='用户名不能为空；首次设置时密码不能为空';
    errorEl.style.display='block'; return;
  }
  if (isNaN(port)||port<1||port>65535) {
    errorEl.textContent='端口范围必须在 1 到 65535 之间';
    errorEl.style.display='block'; return;
  }
  if (!/^[A-Za-z0-9]+$/.test(suffix)) {
    errorEl.textContent='登录安全后缀仅能由英文字母和数字组成';
    errorEl.style.display='block'; return;
  }
  btn.disabled=true; btn.textContent='正在保存...';
  try {
    var r = await fetch('./api/update_credentials', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body:JSON.stringify({username:username,password:password,port:port,secret_path:suffix,domain:domain,https:https,cert_path:certPath,key_path:keyPath})
    });
    var d = await r.json();
    if (r.ok&&d.ok) {
      successEl.textContent=d.restart_needed?'保存成功！端口或路径已变更，页面将自动跳转...':'保存成功，已即时生效！';
      successEl.style.display='block';
      setTimeout(function(){
        if(d.restart_needed){window.location.reload();}
        else{closeCredentialsModal();load();}
      }, d.restart_needed?4000:1500);
    } else {
      errorEl.textContent=d.error||'保存失败，请检查输入';
      errorEl.style.display='block'; btn.disabled=false; btn.textContent='保存修改';
    }
  } catch(err) {
    errorEl.textContent='连接服务器失败，请稍后重试';
    errorEl.style.display='block'; btn.disabled=false; btn.textContent='保存修改';
  }
}

// ===== Network Modal =====
function openNetworkModal() {
  $('networkError').style.display='none';
  $('networkSuccess').style.display='none';
  $('networkForm').reset();
  if (state) {
    $('netProxyPort').value = state.proxy_port||7928;
    var mode = state.routing_mode||'auto';
    var ipType = state.routing_ip_type||'all';
    selectOptionCard('routingMode',mode);
    selectOptionCard('routingIpType',ipType);
  }
  var frcSel = $('netForceCountry');
  if (frcSel) {
    var countMap={};
    (nodes.length?nodes:sampleNodes).forEach(function(n){
      var c=n.country||''; if(c)countMap[c]=(countMap[c]||0)+1;
    });
    var html='<option value="">请选择要锁定的国家...</option>';
    Object.keys(countMap).sort().forEach(function(c){
      html+='<option value="'+esc(c)+'">'+esc(c)+' ('+countMap[c]+'个节点)</option>';
    });
    frcSel.innerHTML=html;
  }
  $('networkModal').style.display='flex';
  $('adminDropdown').style.display='none';
}
function closeNetworkModal() { $('networkModal').style.display='none'; }

async function saveNetwork(e) {
  e.preventDefault();
  var errorEl=$('networkError'), successEl=$('networkSuccess'), btn=$('networkSubmitBtn');
  errorEl.style.display='none'; successEl.style.display='none';
  var proxyPort=parseInt($('netProxyPort').value);
  var routingMode=$('netRoutingMode').value;
  var forceCountry=$('netForceCountry').value;
  var routingIpType=$('netRoutingIpType').value;
  if (isNaN(proxyPort)||proxyPort<1024||proxyPort>65535) {
    errorEl.textContent='代理出口端口范围必须在 1024 到 65535 之间'; errorEl.style.display='block'; return;
  }
  btn.disabled=true; btn.textContent='正在保存...';
  try {
    var r = await fetch('./api/update_settings', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body:JSON.stringify({proxy_port:proxyPort,routing_mode:routingMode,force_country:forceCountry,routing_ip_type:routingIpType})
    });
    var d = await r.json();
    if (r.ok&&d.ok) {
      successEl.textContent='配置保存成功，已即时生效！';
      successEl.style.display='block';
      setTimeout(function(){ closeNetworkModal(); load(); }, 1500);
    } else {
      errorEl.textContent=d.error||'保存失败';
      errorEl.style.display='block'; btn.disabled=false; btn.textContent='保存修改';
    }
  } catch(err) {
    errorEl.textContent='连接服务器失败'; errorEl.style.display='block';
    btn.disabled=false; btn.textContent='保存修改';
  }
}

function selectOptionCard(group, value) {
  var container = $(group==='routingMode'?'routingModeGroup':'routingIpTypeGroup');
  if (!container) return;
  var cards = container.querySelectorAll('.option-card');
  cards.forEach(function(c){ c.classList.remove('active'); });
  cards.forEach(function(c){
    if(c.getAttribute('data-value')===value) c.classList.add('active');
  });
  var hidden = $(group==='routingMode'?'netRoutingMode':'netRoutingIpType');
  if (hidden) hidden.value = value;
  if (group==='routingMode') {
    $('forceCountryGroup').style.display = value==='fixed_region'?'block':'none';
  }
}

// ===== VPS Modal =====
function openVpsModal() { $('vpsModal').style.display='flex'; $('adminDropdown').style.display='none'; }
function closeVpsModal() { $('vpsModal').style.display='none'; }

// ===== Gateway Modal =====
function openGatewayModal() {
  $('adminDropdown').style.display='none';
  $('gatewayModal').style.display='flex';
  loadGatewayStatus();
  if (gatewayPollInterval) clearInterval(gatewayPollInterval);
  gatewayPollInterval = setInterval(loadGatewayStatus, 3000);
}
function closeGatewayModal() {
  $('gatewayModal').style.display='none';
  if (gatewayPollInterval) { clearInterval(gatewayPollInterval); gatewayPollInterval=null; }
}
async function loadGatewayStatus() {
  try {
    var r = await fetch('./api/gateway_status');
    var d = await r.json();
    if (d.ok&&d.services) renderGatewayServices(d.services);
  } catch(e) {}
}
function renderGatewayServices(services) {
  var container = $('gatewayServicesList');
  if (!container) return;
  var html = '';
  services.forEach(function(s){
    var statusText = s.status==='running'?'正在运行':'已停止';
    var badgeClass = s.status==='running'?'badge badge-available':'badge badge-unavailable';
    var pulse = s.status==='running'?'<span class="badge-pulse"></span>':'';
    html += '<div class="gateway-card"><div class="gateway-card-top"><span class="gateway-name">'+esc(s.name)+'</span><span class="'+badgeClass+'">'+pulse+statusText+'</span></div>'+
      '<div class="gateway-details">'+esc(s.details||'-')+'</div>'+
      (s.error?'<div class="gateway-error">&#9888;&#65039; 诊断原因: '+esc(s.error)+'</div>':'')+'</div>';
  });
  container.innerHTML = html;
}

// ===== Logs Modal =====
function openLogsModal() {
  $('adminDropdown').style.display='none';
  $('logsModal').style.display='flex';
  loadLogs();
  if (logsPollInterval) clearInterval(logsPollInterval);
  logsPollInterval = setInterval(loadLogs, 2500);
}
function closeLogsModal() {
  $('logsModal').style.display='none';
  if (logsPollInterval) { clearInterval(logsPollInterval); logsPollInterval=null; }
}
async function loadLogs() {
  try {
    var r = await fetch('./api/logs');
    var d = await r.json();
    if (d.logs) { rawLogsCache = d.logs; filterAndRenderLogs(); }
  } catch(e) {}
}
function filterAndRenderLogs() {
  var filterVal = $('logFilterSelect').value;
  var term = $('logTerminalContainer');
  if (!term) return;
  var filtered = rawLogsCache;
  if (filterVal==='proxy') filtered=rawLogsCache.filter(function(l){return l.module==='Proxy';});
  else if (filterVal==='vpn') filtered=rawLogsCache.filter(function(l){return l.module==='VPN';});
  else if (filterVal==='system') filtered=rawLogsCache.filter(function(l){return !['Proxy','VPN'].includes(l.module);});
  if (!filtered.length) {
    term.innerHTML='<div style="color:var(--text-tertiary);text-align:center;margin-top:150px">暂无该类型日志。</div>';
    return;
  }
  var linesHtml = filtered.map(function(l){
    var color='#a5b4fc';
    if(l.module==='Proxy') color='#38bdf8';
    if(l.module==='VPN') color='#34d399';
    if(l.level==='WARNING') color='#fbbf24';
    if(l.level==='ERROR') color='#f43f5e';
    return '<div style="color:'+color+';margin-bottom:4px">['+esc(l.timestamp)+'] ['+esc(l.level)+'] ['+esc(l.module)+'] '+esc(l.message)+'</div>';
  }).join('');
  var isAtBottom = term.scrollHeight-term.clientHeight<=term.scrollTop+50;
  term.innerHTML = linesHtml;
  if (isAtBottom) term.scrollTop = term.scrollHeight;
}
function copyLogContent() {
  var term=$('logTerminalContainer'); if(!term)return;
  var text=term.innerText||term.textContent;
  if(!text||text.includes('暂无')){alert('当前没有可供复制的日志。');return;}
  navigator.clipboard.writeText(text).then(function(){alert('日志内容已成功复制到剪贴板！');})
  .catch(function(){var ta=document.createElement('textarea');ta.value=text;document.body.appendChild(ta);ta.select();document.execCommand('copy');document.body.removeChild(ta);alert('日志内容已复制到剪贴板！');});
}
function exportLogContent() {
  var term=$('logTerminalContainer'); if(!term)return;
  var text=term.innerText||term.textContent;
  if(!text||text.includes('暂无')){alert('当前没有可供导出的日志。');return;}
  var blob=new Blob([text],{type:'text/plain;charset=utf-8'});
  var url=URL.createObjectURL(blob);
  var a=document.createElement('a');a.href=url;
  var dateStr=new Date().toISOString().slice(0,10);
  a.download='vpngate_log_'+dateStr+'.txt';
  document.body.appendChild(a);a.click();document.body.removeChild(a);URL.revokeObjectURL(url);
}

// ===== Initial Load =====
load();

// ===== Auto-refresh =====
setInterval(async function() {
  if (!state||!state.is_connecting&&(!testingNodeIds||!testingNodeIds.size)&&document.visibilityState==='visible') {
    try {
      var r=await fetch('./api/nodes');
      var d=await r.json();
      if (d.channels) { d.channels.forEach(function(ch,i){ if(sampleChannels[i]){ sampleChannels[i].online=ch.online; sampleChannels[i].connecting=ch.connecting; sampleChannels[i].port=ch.port||(7928+i); } }); } if (d.nodes) { nodes=(d.nodes||[]).map(function(n){ var nn=Object.assign({},n); if(nn.latency==null&&nn.latency_ms!=null)nn.latency=nn.latency_ms; if(nn.latency==null&&nn.ping!=null)nn.latency=nn.ping; if(!nn.name)nn.name=nn.host_name||nn.id||''; if(!nn.status)nn.status=nn.probe_status||(nn.active?'available':'pending'); return nn; }); state=d.state||{}; updateDomainBar(state); updateCountryFilter(); renderTable(); }
    } catch(e) {}
  }
}, 10000);

// Fallback channel refresh
setInterval(function() {
  if (channels.length) { updateChannels(); }
  else {
    // Simulate sample channel speed/latency changes
    var idx = Math.floor(Math.random()*10);
    if (sampleChannels[idx]&&sampleChannels[idx].online) {
      sampleChannels[idx].speed = (Math.random()*40+5).toFixed(1);
      sampleChannels[idx].latency = Math.floor(Math.random()*180+25);
      renderChannels();
    }
  }
}, 5000);

setTimeout(updateChannels, 2000);
</script>
</body>
</html>

</body></html>"""

def check_proxy_health() -> dict[str, Any]:
    # 1. 检测代理服务端口是否在监听
    is_ipv6 = ":" in LOCAL_PROXY_HOST
    af = socket.AF_INET6 if is_ipv6 else socket.AF_INET
    s = None
    try:
        s = socket.socket(af, socket.SOCK_STREAM)
        s.settimeout(1.5)
        connect_host = LOCAL_PROXY_HOST
        if connect_host in ("::", "0.0.0.0", ""):
            connect_host = "::1" if is_ipv6 else "127.0.0.1"
        try:
            s.connect((connect_host, LOCAL_PROXY_PORT))
        except Exception as e:
            if connect_host == "::1":
                s.close()
                s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                s.settimeout(1.5)
                s.connect(("127.0.0.1", LOCAL_PROXY_PORT))
            else:
                raise e
    except Exception as e:
        diag = vpn_utils.diagnose_local_obstructions(LOCAL_PROXY_PORT, host=LOCAL_PROXY_HOST)
        diag_msg = diag[1] if diag else f"端口 {LOCAL_PROXY_PORT} 连接失败，原因: {e}"
        return {
            "ok": False,
            "error": f"代理服务未运行 ({diag_msg})"
        }
    finally:
        if s is not None:
            try:
                s.close()
            except Exception:
                pass

    # 2. 检测虚拟网卡 tun0 是否存在 (Linux 下)
    tun_path = Path("/sys/class/net/tun0")
    if sys.platform.startswith("linux") and not tun_path.exists():
        return {
            "ok": False,
            "error": "[错误代码 3004] [ERR_ROUTE_DEV_NOT_FOUND] VPN 虚拟网卡 (tun0) 未启用，请确保当前已成功连接 VPN 节点"
        }

    # 3. 使用 curl 通过本地 SOCKS5 代理接口测试 IP 与实际延迟
    def _curl_check_ip(url: str) -> dict[str, Any] | None:
        proxy_hosts = []
        if LOCAL_PROXY_HOST == "::":
            proxy_hosts = ["[::1]", "127.0.0.1"]
        elif LOCAL_PROXY_HOST == "0.0.0.0":
            proxy_hosts = ["127.0.0.1"]
        elif ":" in LOCAL_PROXY_HOST:
            proxy_hosts = [f"[{LOCAL_PROXY_HOST}]", "127.0.0.1"]
        else:
            proxy_hosts = [LOCAL_PROXY_HOST]

        for p_host in proxy_hosts:
            proxy_url = f"socks5h://{p_host}:{LOCAL_PROXY_PORT}"
            proxy_user, proxy_pass = proxy_server.get_proxy_credentials()
            cmd = [
                "curl", "-s",
                "-w", "\n%{time_total} %{http_code}",
                "-x", proxy_url,
                url,
                "--max-time", "5"
            ]
            if proxy_user is not None and proxy_pass is not None:
                cmd.extend(["--proxy-user", f"{proxy_user}:{proxy_pass}"])
            try:
                res = subprocess.run(cmd, capture_output=True, text=True, timeout=6)
                if res.returncode == 0:
                    lines = res.stdout.strip().splitlines()
                    if len(lines) >= 2:
                        ip = lines[0].strip()
                        time_info = lines[1].strip().split()
                        if len(time_info) == 2:
                            total_time_str, http_code = time_info
                            if http_code == "200" and ip:
                                latency_ms = int(float(total_time_str) * 1000)
                                return {"ok": True, "ip": ip, "latency_ms": latency_ms}
            except Exception:
                pass
        return None

    try:
        result = _curl_check_ip("http://ip.sb")
        if result:
            return result
        result = _curl_check_ip("http://api.ipify.org")
        if result:
            return result
            
        # 此时外网测试失败，检测本地代理端口是否依然能连通。若仍能连通，直接抛出出口测试失败，不调用占用诊断
        port_still_listening = False
        test_sock = None
        try:
            test_sock = socket.socket(af, socket.SOCK_STREAM)
            test_sock.settimeout(1.0)
            connect_host = LOCAL_PROXY_HOST
            if connect_host in ("::", "0.0.0.0", ""):
                connect_host = "::1" if is_ipv6 else "127.0.0.1"
            try:
                test_sock.connect((connect_host, LOCAL_PROXY_PORT))
                port_still_listening = True
            except Exception:
                if connect_host == "::1":
                    test_sock.close()
                    test_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                    test_sock.settimeout(1.0)
                    test_sock.connect(("127.0.0.1", LOCAL_PROXY_PORT))
                    port_still_listening = True
        except Exception:
            pass
        finally:
            if test_sock is not None:
                try:
                    test_sock.close()
                except Exception:
                    pass

        if not port_still_listening:
            diag = vpn_utils.diagnose_local_obstructions(LOCAL_PROXY_PORT, host=LOCAL_PROXY_HOST)
            if diag:
                return {"ok": False, "error": f"出口连接测试失败 | 本机诊断结果: {diag[1]}"}
            
        return {"ok": False, "error": "出口连接测试失败 (ip.sb 和 api.ipify.org 均无法连通，可能是节点已失效或 VPS 防火墙限制了 UDP/TCP 出站端口)"}
    except Exception as e:
        return {"ok": False, "error": f"出口连接测试异常: {e}"}

def background_proxy_checker() -> None:
    global last_checker_heartbeat, is_connecting
    time.sleep(30)
    while True:
        last_checker_heartbeat = time.time()
        try:
            if is_connecting:
                time.sleep(5)
                continue

            res = check_proxy_health()
            if res["ok"]:
                set_state(
                    proxy_ok=True,
                    proxy_ip=res["ip"],
                    proxy_latency_ms=res["latency_ms"],
                    proxy_error=""
                )
                log_to_json("INFO", "Proxy", f"代理可用，IP: {res['ip']}, 延迟: {res['latency_ms']} ms")
            else:
                error_msg = res.get("error", "未知错误")
                if active_openvpn_node_id:
                    print(f"[警告] {LOCAL_PROXY_PORT} 端口本地代理当前不可用！原因: {error_msg}", flush=True)
                    log_to_json("WARNING", "Proxy", f"代理不可用: {error_msg}")
                set_state(
                    proxy_ok=False,
                    proxy_ip="-",
                    proxy_latency_ms=0,
                    proxy_error=error_msg
                )

                # If we intended to have an active VPN node but proxy failed, trigger auto-switch
                if active_openvpn_node_id:
                    ui_cfg = load_ui_config()
                    routing_mode = ui_cfg.get("routing_mode", "auto")
                    if routing_mode != "fixed_ip":
                        with lock:
                            nodes = read_nodes()
                            active_node = next((n for n in nodes if n.get("id") == active_openvpn_node_id), None)
                            if active_node:
                                mark_blacklisted(active_node, f"代理连通性检测失败: {error_msg}")
                                active_node["probe_status"] = "unavailable"
                                write_json(NODES_FILE, nodes)
                        auto_switch_node()
                    else:
                        print(f"[代理守护线程] 固定 IP 模式下代理不可用，正在尝试重启连接同一节点: {active_openvpn_node_id}", flush=True)
                        is_connecting = False
                        try:
                            connect_node(active_openvpn_node_id)
                        except Exception as e:
                            print(f"[代理守护线程] 重启固定节点失败: {e}", flush=True)
        except Exception as e:
            print(f"[错误] 代理后台检测发生异常: {e}", flush=True)
            log_to_json("ERROR", "Proxy", f"检测守护线程发生异常: {e}")
        time.sleep(30)

def active_node_pinger() -> None:
    global last_pinger_heartbeat
    while True:
        last_pinger_heartbeat = time.time()
        try:
            if active_openvpn_running() and active_openvpn_node_id:
                nodes = read_nodes()
                node = next((n for n in nodes if n.get("id") == active_openvpn_node_id), None)
                if node:
                    ip = node.get("ip") or node.get("remote_host")
                    port = parse_int(node.get("remote_port"))
                    fallback = parse_int(node.get("ping"))
                    if ip:
                        latency = vpn_utils.ping_latency_ms(ip, port, fallback)
                        if latency > 0:
                            set_state(active_node_latency=f"{latency} ms")
                        else:
                            set_state(active_node_latency="检测超时")
                    else:
                        set_state(active_node_latency="检测超时")
                else:
                    set_state(active_node_latency="检测超时")
            elif is_connecting:
                set_state(active_node_latency="测试中...")
            else:
                set_state(active_node_latency="无活动连接")
        except Exception as e:
            print(f"[ERROR] active_node_pinger error: {e}", flush=True)
        time.sleep(10)


class Handler(BaseHTTPRequestHandler):
    def get_secret_path(self) -> str:
        ui_cfg = load_ui_config()
        return ui_cfg.get("secret_path", "EJsW2EeBo9lY")

    def is_authorized(self) -> bool:
        ui_cfg = load_ui_config()
        pwd = ui_cfg.get("password")
        if not pwd:
            print("[Auth] 管理后台密码为空，已拒绝访问。请检查 ui_auth.json。", flush=True)
            return False
        
        cookie_header = self.headers.get("Cookie", "")
        cookies = {}
        if cookie_header:
            for item in cookie_header.split(";"):
                item = item.strip()
                if "=" in item:
                    k, v = item.split("=", 1)
                    cookies[k.strip()] = v.strip()
        
        session_token = cookies.get("session")
        if not session_token:
            return False
            
        with lock:
            exp_time = active_sessions.get(session_token)
            if exp_time is not None and exp_time > time.time():
                return True
        return False

    def validate_path(self) -> str:
        secret_path = self.get_secret_path()
        request_path = urllib.parse.urlsplit(self.path).path
        if not secret_path:
            return request_path
        if request_path == f"/{secret_path}":
            self.send_response(HTTPStatus.FOUND)
            self.send_header("Location", f"/{secret_path}/")
            self.end_headers()
            return ""
        prefix = f"/{secret_path}/"
        if request_path.startswith(prefix):
            return "/" + request_path[len(prefix):]
        self.send_response(HTTPStatus.NOT_FOUND)
        self.end_headers()
        return ""

    def log_message(self, format: str, *args: Any) -> None:
        print(f"[{self.log_date_time_string()}] {format % args}", flush=True)

    def send_bytes(self, body: bytes, content_type: str, status: HTTPStatus = HTTPStatus.OK) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, data: Any, status: HTTPStatus = HTTPStatus.OK) -> None:
        self.send_bytes(json.dumps(data, ensure_ascii=False).encode("utf-8"), "application/json; charset=utf-8", status)

    def read_request_body(self, max_bytes: int = 65536) -> bytes:
        length = parse_int(self.headers.get("Content-Length"))
        if length < 0:
            raise ValueError("Content-Length 无效")
        if length > max_bytes:
            raise ValueError(f"请求体过大，最大允许 {max_bytes} 字节")
        return self.rfile.read(length) if length > 0 else b""

    def read_json_body(self, max_bytes: int = 65536) -> dict[str, Any]:
        body = self.read_request_body(max_bytes)
        if not body:
            return {}
        data = json.loads(body.decode("utf-8"))
        if not isinstance(data, dict):
            raise ValueError("请求 JSON 必须是对象")
        return data

    def do_GET(self) -> None:
        effective_path = self.validate_path()
        if effective_path == "": return
        
        if not self.is_authorized():
            if effective_path in ("/", "/index.html"):
                self.send_bytes(LOGIN_HTML.encode("utf-8"), "text/html; charset=utf-8")
                return
            else:
                self.send_json({"error": "Unauthorized"}, HTTPStatus.UNAUTHORIZED)
                return
                
        if effective_path in ("/", "/index.html"):
            self.send_bytes(INDEX_HTML.encode("utf-8"), "text/html; charset=utf-8")
        elif effective_path == "/api/nodes":
            global last_active_ping_time, last_active_latency, active_openvpn_node_id
            nodes = read_nodes()
            active_node = next((n for n in nodes if active_openvpn_node_id and n.get("id") == active_openvpn_node_id), None)
            for n in nodes:
                n["active"] = (active_openvpn_node_id and n.get("id") == active_openvpn_node_id)
            if active_node:
                ip = active_node.get("ip") or active_node.get("remote_host")
                if ip:
                    now = time.time()
                    if now - last_active_ping_time > 15.0:
                        last_active_ping_time = now
                        def bg_ping(ip_addr: str, port: int, fallback: int) -> None:
                            global last_active_latency
                            try:
                                latency = vpn_utils.ping_latency_ms(ip_addr, port, fallback)
                                if latency > 0:
                                    last_active_latency = latency
                            except Exception:
                                pass
                        threading.Thread(
                            target=bg_ping, 
                            args=(ip, parse_int(active_node.get("remote_port")), parse_int(active_node.get("ping"))),
                            daemon=True
                        ).start()
                    if last_active_latency > 0:
                        active_node["latency_ms"] = last_active_latency
            stripped_nodes = []
            for n in nodes:
                stripped = n.copy()
                if "config_text" in stripped:
                    del stripped["config_text"]
                stripped_nodes.append(stripped)
            ch_status = [{"index":i,"node_id":ch_node_ids[i],"online":ch_processes[i] is not None and ch_processes[i].poll() is None,"connecting":ch_connecting[i],"port":CHANNEL_BASE_PORT+i,"tun":ch_tun_ids[i]} for i in range(MAX_CHANNELS)]
            self.send_json({"nodes": stripped_nodes, "state": get_state(), "channels": ch_status})
        elif effective_path.startswith("/configs/"):
            filename = urllib.parse.unquote(effective_path.removeprefix("/configs/"))
            with lock:
                nodes = read_nodes()
                node = next((n for n in nodes if Path(n.get("config_file", "")).name == filename), None)
            if node and node.get("config_text"):
                self.send_bytes(node["config_text"].encode("utf-8"), "application/x-openvpn-profile")
            else:
                self.send_json({"error": "not found"}, HTTPStatus.NOT_FOUND)
        elif effective_path == "/api/gateway_status":
            web_ui_status = {
                "name": "Web 管理服务",
                "status": "running",
                "details": f"监听地址: {load_ui_config().get('host', UI_HOST)}:{load_ui_config().get('port', UI_PORT)}",
                "error": ""
            }
            proxy_ok = False
            proxy_err = ""
            is_ipv6 = ":" in LOCAL_PROXY_HOST
            af = socket.AF_INET6 if is_ipv6 else socket.AF_INET
            s = None
            try:
                s = socket.socket(af, socket.SOCK_STREAM)
                s.settimeout(0.5)
                connect_host = LOCAL_PROXY_HOST
                if connect_host in ("::", "0.0.0.0", ""):
                    connect_host = "::1" if is_ipv6 else "127.0.0.1"
                try:
                    s.connect((connect_host, LOCAL_PROXY_PORT))
                    proxy_ok = True
                except Exception:
                    if connect_host == "::1":
                        s.close()
                        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                        s.settimeout(0.5)
                        s.connect(("127.0.0.1", LOCAL_PROXY_PORT))
                        proxy_ok = True
                    else:
                        raise
            except Exception as e:
                diag = vpn_utils.diagnose_local_obstructions(LOCAL_PROXY_PORT, host=LOCAL_PROXY_HOST)
                proxy_err = diag[1] if diag else f"本地代理网关无法连通: {e}"
            finally:
                if s is not None:
                    try:
                        s.close()
                    except Exception:
                        pass
            proxy_gateway_status = {
                "name": "本地代理网关",
                "status": "running" if proxy_ok else "stopped",
                "details": f"监听地址: {LOCAL_PROXY_HOST}:{LOCAL_PROXY_PORT}",
                "error": proxy_err
            }
            ovpn_ok = active_openvpn_running()
            ovpn_err = ""
            ovpn_details = "未连接"
            if ovpn_ok:
                ovpn_details = f"已连接节点: {active_openvpn_node_id}"
                if sys.platform.startswith("linux"):
                    if not Path("/sys/class/net/tun0").exists():
                        ovpn_err = "[警告] 虚拟网卡 (tun0) 未启用，可能存在策略路由配置问题。"
            else:
                if active_openvpn_node_id:
                    ovpn_err = "连接已中断或 OpenVPN 核心程序异常退出。"
                    ovpn_details = f"尝试连接节点 {active_openvpn_node_id} 失败"
            openvpn_status = {
                "name": "OpenVPN 核心连接",
                "status": "running" if ovpn_ok else "stopped",
                "details": ovpn_details,
                "error": ovpn_err
            }
            now = time.time()
            server_uptime = now - server_start_time
            collector_ok = (last_collector_heartbeat > 0.0 and now - last_collector_heartbeat < (CHECK_INTERVAL_SECONDS * 1.5)) or (server_uptime < 15.0)
            collector_status = {
                "name": "节点同步守护线程",
                "status": "running" if collector_ok else "stopped",
                "details": f"上次心跳: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(last_collector_heartbeat)) if last_collector_heartbeat > 0 else '等待启动'}",
                "error": "" if collector_ok else "线程可能已异常终止，导致无法在后台拉取和测速新节点。"
            }
            checker_ok = (last_checker_heartbeat > 0.0 and now - last_checker_heartbeat < 90.0) or (server_uptime < 35.0)
            checker_status = {
                "name": "出口检测守护线程",
                "status": "running" if checker_ok else "stopped",
                "details": f"上次心跳: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(last_checker_heartbeat)) if last_checker_heartbeat > 0 else '等待启动'}",
                "error": "" if checker_ok else "线程可能已挂起或终止，导致无法实时获取代理出口状态。"
            }
            pinger_ok = (last_pinger_heartbeat > 0.0 and now - last_pinger_heartbeat < 30.0) or (server_uptime < 15.0)
            pinger_status = {
                "name": "延迟测速守护线程",
                "status": "running" if pinger_ok else "stopped",
                "details": f"上次心跳: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(last_pinger_heartbeat)) if last_pinger_heartbeat > 0 else '等待启动'}",
                "error": "" if pinger_ok else "线程可能已中止，无法实时刷新活动节点的 Ping 延迟。"
            }
            self.send_json({
                "ok": True,
                "services": [
                    web_ui_status,
                    proxy_gateway_status,
                    openvpn_status,
                    collector_status,
                    checker_status,
                    pinger_status
                ]
            })
        elif effective_path == "/api/logs":
            logs_dir = DATA_DIR / "logs"
            date_str = time.strftime("%Y-%m-%d", time.localtime())
            log_file = logs_dir / f"{date_str}.json"
            entries = []
            if log_file.exists():
                try:
                    with lock:
                        with open(log_file, "r", encoding="utf-8") as f:
                            for line in f:
                                line = line.strip()
                                if line:
                                    try:
                                        entries.append(json.loads(line))
                                    except Exception:
                                        pass
                except Exception as e:
                    print(f"[API Logs] Error reading log file: {e}", flush=True)
            self.send_json({"logs": entries})
        else:
            self.send_json({"error": "not found"}, HTTPStatus.NOT_FOUND)

    def do_POST(self) -> None:
        effective_path = self.validate_path()
        if effective_path == "": return
        
        if effective_path == "/api/login":
            try:
                payload = self.read_json_body()
                input_pwd = str(payload.get("password") or "")
                input_uname = str(payload.get("username") or "")
                
                ui_cfg = load_ui_config()
                expected_pwd = ui_cfg.get("password", "")
                expected_uname = ui_cfg.get("username", "admin")
                
                if expected_pwd and input_pwd == expected_pwd and input_uname == expected_uname:
                    token = uuid.uuid4().hex
                    with lock:
                        active_sessions[token] = time.time() + 30 * 24 * 3600
                    body = json.dumps({"ok": True}).encode("utf-8")
                    self.send_response(HTTPStatus.OK)
                    self.send_header("Content-Type", "application/json; charset=utf-8")
                    self.send_header("Content-Length", str(len(body)))
                    self.send_header("Cache-Control", "no-store")
                    secret_path = self.get_secret_path()
                    cookie_path = f"/{secret_path}/" if secret_path else "/"
                    self.send_header("Set-Cookie", f"session={token}; Path={cookie_path}; HttpOnly; SameSite=Lax; Max-Age=2592000")
                    self.end_headers()
                    self.wfile.write(body)
                else:
                    self.send_json({"ok": False, "error": "用户名或密码不正确，请重新输入"}, HTTPStatus.FORBIDDEN)
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
            return

        if effective_path == "/api/logout":
            try:
                cookie_header = self.headers.get("Cookie", "")
                cookies = {}
                if cookie_header:
                    for item in cookie_header.split(";"):
                        item = item.strip()
                        if "=" in item:
                            k, v = item.split("=", 1)
                            cookies[k.strip()] = v.strip()
                session_token = cookies.get("session")
                if session_token:
                    with lock:
                        active_sessions.pop(session_token, None)
                secret_path = self.get_secret_path()
                cookie_path = f"/{secret_path}/" if secret_path else "/"
                body = json.dumps({"ok": True}).encode("utf-8")
                self.send_response(HTTPStatus.OK)
                self.send_header("Content-Type", "application/json; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "no-store")
                self.send_header("Set-Cookie", f"session=; Path={cookie_path}; HttpOnly; SameSite=Lax; Max-Age=0; Expires=Thu, 01 Jan 1970 00:00:00 GMT")
                self.end_headers()
                self.wfile.write(body)
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
            return

        if not self.is_authorized():
            self.send_json({"error": "Unauthorized"}, HTTPStatus.UNAUTHORIZED)
            return

        if effective_path == "/api/update_credentials":
            try:
                payload = self.read_json_body()
                new_username = str(payload.get("username") or "").strip()
                new_password = str(payload.get("password") or "").strip()
                new_port = payload.get("port")
                new_suffix = str(payload.get("secret_path") or "").strip()
                new_domain = str(payload.get("domain") or "").strip()
                new_https = bool(payload.get("https", False))
                new_cert_path = str(payload.get("cert_path") or "").strip()
                new_key_path = str(payload.get("key_path") or "").strip()
                
                ui_cfg = load_ui_config()
                if not new_username or (not new_password and not ui_cfg.get("password")):
                    self.send_json({"ok": False, "error": "用户名不能为空；首次设置时密码不能为空"}, HTTPStatus.BAD_REQUEST)
                    return
                
                try:
                    new_port_int = int(new_port)
                    if not (1 <= new_port_int <= 65535):
                        raise ValueError()
                except (TypeError, ValueError):
                    self.send_json({"ok": False, "error": "网页管理端口范围必须是 1 至 65535"}, HTTPStatus.BAD_REQUEST)
                    return

                if not new_suffix or not re.match(r"^[A-Za-z0-9]+$", new_suffix):
                    self.send_json({"ok": False, "error": "安全后缀仅能由英文字母和数字组成"}, HTTPStatus.BAD_REQUEST)
                    return

                expected_username = ui_cfg.get("username", "")
                expected_password = ui_cfg.get("password", "")
                expected_port = ui_cfg.get("port", 8787)
                expected_suffix = ui_cfg.get("secret_path", "EJsW2EeBo9lY")
                expected_domain = ui_cfg.get("domain", "")
                expected_https = ui_cfg.get("https", False)
                expected_cert_path = ui_cfg.get("cert_path", "")
                expected_key_path = ui_cfg.get("key_path", "")

                ui_cfg["username"] = new_username
                if new_password:
                    ui_cfg["password"] = new_password
                ui_cfg["port"] = new_port_int
                ui_cfg["secret_path"] = new_suffix
                ui_cfg["domain"] = new_domain
                ui_cfg["https"] = new_https
                ui_cfg["cert_path"] = new_cert_path
                ui_cfg["key_path"] = new_key_path
                
                auth_file = DATA_DIR / "ui_auth.json"
                reauth_required = new_username != expected_username or (new_password and new_password != expected_password)
                with lock:
                    DATA_DIR.mkdir(exist_ok=True, parents=True)
                    auth_file.write_text(json.dumps(ui_cfg, ensure_ascii=False, indent=2), encoding="utf-8")
                    if reauth_required:
                        active_sessions.clear()
                
                restart_needed = (new_port_int != expected_port or new_suffix != expected_suffix or new_domain != expected_domain or new_https != expected_https or new_cert_path != expected_cert_path or new_key_path != expected_key_path)
                if restart_needed:
                    self.send_json({"ok": True, "restart_needed": True, "reauth_required": reauth_required, "message": "配置更新成功，网页管理端口或路径已变更，将在 2 秒内重启..."})
                    
                    def restart_server():
                        time.sleep(2)
                        print("[系统] 管理后台安全配置更新，进程即将退出以触发自动重启...", flush=True)
                        os._exit(0)
                    
                    threading.Thread(target=restart_server, daemon=True).start()
                else:
                    self.send_json({"ok": True, "restart_needed": False, "reauth_required": reauth_required, "message": "账号密码配置更新成功，已即时生效！"})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
            return

        elif effective_path == "/api/update_settings":
            try:
                payload = self.read_json_body()
                
                new_proxy_port = payload.get("proxy_port")
                routing_mode = str(payload.get("routing_mode") or "auto").strip()
                force_country = str(payload.get("force_country") or "").strip()
                routing_ip_type = str(payload.get("routing_ip_type") or "all").strip()
                
                try:
                    new_proxy_port_int = int(new_proxy_port)
                    if not (1024 <= new_proxy_port_int <= 65535):
                        raise ValueError()
                except (TypeError, ValueError):
                    self.send_json({"ok": False, "error": "代理出站端口范围必须是 1024 至 65535"}, HTTPStatus.BAD_REQUEST)
                    return
                
                if routing_mode not in ("auto", "fixed_ip", "fixed_region", "favorites"):
                    self.send_json({"ok": False, "error": "无效的路由配置模式"}, HTTPStatus.BAD_REQUEST)
                    return
                if routing_ip_type not in ("all", "residential", "hosting"):
                    self.send_json({"ok": False, "error": "无效的IP出站类型过滤"}, HTTPStatus.BAD_REQUEST)
                    return
                
                ui_cfg = load_ui_config()
                expected_proxy_port = ui_cfg.get("proxy_port", 7928)
                
                if new_proxy_port_int == ui_cfg.get("port", 8787):
                    self.send_json({"ok": False, "error": "代理出站端口不能与网页管理端口相同"}, HTTPStatus.BAD_REQUEST)
                    return
                
                ui_cfg["proxy_port"] = new_proxy_port_int
                ui_cfg["routing_mode"] = routing_mode
                ui_cfg["force_country"] = force_country
                ui_cfg["routing_ip_type"] = routing_ip_type
                
                auth_file = DATA_DIR / "ui_auth.json"
                with lock:
                    DATA_DIR.mkdir(exist_ok=True, parents=True)
                    auth_file.write_text(json.dumps(ui_cfg, ensure_ascii=False, indent=2), encoding="utf-8")
                
                restart_needed = (new_proxy_port_int != expected_proxy_port)
                if restart_needed:
                    self.send_json({"ok": True, "restart_needed": True, "message": "配置更新成功，代理出站端口变更，将在 2 秒内重启..."})
                    
                    def restart_server():
                        time.sleep(2)
                        print("[系统] 代理出站端口变更，进程即将退出以触发自动重启...", flush=True)
                        os._exit(0)
                    
                    threading.Thread(target=restart_server, daemon=True).start()
                else:
                    self.send_json({"ok": True, "restart_needed": False, "message": "配置更新成功，已即时生效！"})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
            return

        elif effective_path == "/api/update_routing":
            try:
                payload = self.read_json_body()
                routing_mode = str(payload.get("routing_mode") or "auto").strip()
                force_country = str(payload.get("force_country") or "").strip()
                routing_ip_type = str(payload.get("routing_ip_type") or "all").strip()
                fav_fail_fallback = bool(payload.get("fav_fail_fallback", True))
                
                if routing_mode not in ("auto", "fixed_ip", "fixed_region", "favorites"):
                    self.send_json({"ok": False, "error": "无效的路由配置模式"}, HTTPStatus.BAD_REQUEST)
                    return
                if routing_ip_type not in ("all", "residential", "hosting"):
                    self.send_json({"ok": False, "error": "无效的IP出站类型过滤"}, HTTPStatus.BAD_REQUEST)
                    return
                
                ui_cfg = load_ui_config()
                ui_cfg["routing_mode"] = routing_mode
                ui_cfg["force_country"] = force_country
                ui_cfg["routing_ip_type"] = routing_ip_type
                ui_cfg["fav_fail_fallback"] = fav_fail_fallback
                ui_cfg.pop("enable_force_country", None)
                
                auth_file = DATA_DIR / "ui_auth.json"
                with lock:
                    DATA_DIR.mkdir(exist_ok=True, parents=True)
                    auth_file.write_text(json.dumps(ui_cfg, ensure_ascii=False, indent=2), encoding="utf-8")
                
                self.send_json({"ok": True, "message": "出站路由配置更新成功，已即时生效！"})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
            return

        elif effective_path == "/api/toggle_favorite":
            try:
                payload = self.read_json_body()
                node_id = str(payload.get("id") or "").strip()
                
                ui_cfg = load_ui_config()
                fav_ids = ui_cfg.get("favorite_node_ids", [])
                if not isinstance(fav_ids, list):
                    fav_ids = []
                
                if node_id in fav_ids:
                    fav_ids.remove(node_id)
                else:
                    fav_ids.append(node_id)
                
                ui_cfg["favorite_node_ids"] = fav_ids
                auth_file = DATA_DIR / "ui_auth.json"
                with lock:
                    DATA_DIR.mkdir(exist_ok=True, parents=True)
                    auth_file.write_text(json.dumps(ui_cfg, ensure_ascii=False, indent=2), encoding="utf-8")
                
                self.send_json({"ok": True, "favorite_node_ids": fav_ids})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
            return

        if effective_path == "/api/check":
            try:
                self.send_json({"ok": True, "message": maintain_valid_nodes(force=True)})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
        elif effective_path == "/api/refresh_nodes":
            try:
                if maintenance_lock.locked():
                    self.send_json({"ok": True, "message": "节点维护任务正在运行，请稍后再试", "running": True})
                else:
                    threading.Thread(target=maintain_valid_nodes, args=(False,), daemon=True).start()
                    self.send_json({"ok": True, "message": "已在后台启动节点更新流程", "running": False})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
        elif effective_path == "/api/test_nodes":
            try:
                payload = self.read_json_body(max_bytes=262144)
                node_ids = payload.get("ids", [])
                tested_nodes = test_multiple_nodes(node_ids)
                self.send_json({"ok": True, "nodes": tested_nodes})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
        elif effective_path == "/api/disconnect_channel":
            try:
                payload = self.read_json_body()
                channel_idx = int(payload.get("channel", 0))
                result = disconnect_channel(channel_idx)
                self.send_json({"ok": True, "message": result})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, 500)
        
        elif effective_path == "/api/disconnect":
            try:
                ui_cfg = load_ui_config()
                ui_cfg["connection_enabled"] = False
                auth_file = DATA_DIR / "ui_auth.json"
                with lock:
                    DATA_DIR.mkdir(exist_ok=True, parents=True)
                    auth_file.write_text(json.dumps(ui_cfg, ensure_ascii=False, indent=2), encoding="utf-8")
                
                stop_active_openvpn()
                with lock:
                    nodes = read_nodes()
                    for item in nodes:
                        item["active"] = False
                    write_json(NODES_FILE, nodes)
                global last_active_ping_time, last_active_latency
                last_active_ping_time = 0.0
                last_active_latency = 0
                set_state(active_openvpn_node_id="", last_check_message="手动断开连接", active_node_latency="无活动连接")
                self.send_json({"ok": True})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
        elif effective_path == "/api/connect":
            try:
                payload = self.read_json_body()
                channel_idx = int(payload.get("channel", 0))
                node_id = str(payload.get("id") or "")
                if node_id:
                    result = connect_channel(channel_idx, node_id)
                else:
                    result = connect_node(str(payload.get("id") or ""))
                self.send_json({"ok": True, "message": result})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
        elif effective_path == "/api/test_node":
            try:
                payload = self.read_json_body()
                node_id = str(payload.get("id") or "")
                updated_node = test_node_by_id(node_id)
                self.send_json({"ok": True, "node": updated_node})
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
        elif effective_path == "/api/test_proxy":
            try:
                self.read_request_body()
                result = check_proxy_health()
                if result["ok"]:
                    set_state(
                        proxy_ok=True,
                        proxy_ip=result["ip"],
                        proxy_latency_ms=result["latency_ms"],
                        proxy_error=""
                    )
                else:
                    set_state(
                        proxy_ok=False,
                        proxy_ip="-",
                        proxy_latency_ms=0,
                        proxy_error=result.get("error", "未知错误")
                    )
                self.send_json(result)
            except Exception as exc:
                self.send_json({"ok": False, "error": str(exc)}, HTTPStatus.INTERNAL_SERVER_ERROR)
        else:
            self.send_json({"error": "not found"}, HTTPStatus.NOT_FOUND)

class Tee:
    def __init__(self, file_path: str):
        Path(file_path).parent.mkdir(exist_ok=True, parents=True)
        self.file = open(file_path, "a", encoding="utf-8")
        self.stdout = sys.stdout

    def write(self, data: str) -> None:
        self.stdout.write(data)
        self.file.write(data)
        self.file.flush()

    def flush(self) -> None:
        self.stdout.flush()
        self.file.flush()

    def isatty(self) -> bool:
        return self.stdout.isatty()

    def __getattr__(self, attr: str) -> Any:
        return getattr(self.stdout, attr)

def main() -> None:
    ensure_dirs()
    kill_existing_openvpn_processes()
    
    log_file = DATA_DIR / "vpngate.log"
    tee = Tee(str(log_file))
    sys.stdout = tee
    sys.stderr = tee

    write_json(
        STATE_FILE,
        {
            "api_url": API_URL,
            "target_valid_nodes": TARGET_VALID_NODES,
            "fetch_interval_seconds": FETCH_INTERVAL_SECONDS,
            "check_interval_seconds": CHECK_INTERVAL_SECONDS,
            "local_proxy": f"http://{'[' + LOCAL_PROXY_HOST + ']' if ':' in LOCAL_PROXY_HOST else LOCAL_PROXY_HOST}:{LOCAL_PROXY_PORT}",
            "active_openvpn_node_id": "",
            "last_fetch_status": "starting",
            "last_check_message": "服务已启动，正在初始化网络并获取候选 VPN 节点...",
            "is_connecting": True,
            "active_node_latency": "正在准备",
            "blacklisted_nodes": 0,
        },
    )
    for chi in range(MAX_CHANNELS):
        threading.Thread(target=proxy_server.start_proxy_server, args=('127.0.0.1', CHANNEL_BASE_PORT + chi), daemon=True).start()
    
    # Wait for the gateway to officially start
    print("[网关] 正在启动代理网关...", flush=True)
    gateway_ready = False
    is_ipv6 = ":" in LOCAL_PROXY_HOST
    af = socket.AF_INET6 if is_ipv6 else socket.AF_INET
    for _ in range(30):
        s = None
        try:
            s = socket.socket(af, socket.SOCK_STREAM)
            s.settimeout(0.5)
            connect_host = LOCAL_PROXY_HOST
            if connect_host in ("::", "0.0.0.0", ""):
                connect_host = "::1" if is_ipv6 else "127.0.0.1"
            try:
                s.connect((connect_host, LOCAL_PROXY_PORT))
                gateway_ready = True
                break
            except Exception:
                if connect_host == "::1":
                    try:
                        s.close()
                        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                        s.settimeout(0.5)
                        s.connect(("127.0.0.1", LOCAL_PROXY_PORT))
                        gateway_ready = True
                        break
                    except Exception:
                        pass
                raise
        except Exception:
            time.sleep(0.5)
        finally:
            if s is not None:
                try:
                    s.close()
                except Exception:
                    pass
            
    if gateway_ready:
        print("[网关] 代理网关已成功启动监听，启动同步与检测脚本...", flush=True)
    else:
        print("[警告] 代理网关启动超时，继续执行脚本...", flush=True)

    threading.Thread(target=collector_loop, daemon=True).start()
    threading.Thread(target=background_proxy_checker, daemon=True).start()
    threading.Thread(target=active_node_pinger, daemon=True).start()
    
    ui_cfg = load_ui_config()
    ui_host = ui_cfg.get("host", UI_HOST)
    ui_port = bounded_int(ui_cfg.get("port"), UI_PORT, 1, 65535)
    
    print(f"UI: http://{ui_host}:{ui_port}/", flush=True)
    print(f"Proxy: http://{LOCAL_PROXY_HOST}:{LOCAL_PROXY_PORT}", flush=True)
    DualStackHTTPServer((ui_host, ui_port), Handler).serve_forever()

if __name__ == "__main__":
    main()
