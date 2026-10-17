#!/usr/bin/env python3
"""Modbus Tester — RTU  (PySide6 desktop edition)

Desktop port of the Streamlit "Modbus Tester". Same tabs, same layout and the
same Modbus logic (range discovery, background polling, FC05/06/15/16 writes
with read-back, connection guard, TX/RX spy), but as a native Qt application.

Live Data tab: every tag can be bound to a device address / function code /
address / access. Configured tags show their live value on the card:
  FC 1,2,3,4                 -> read only
  FC 5,6 + Read              -> read only (read back with FC01 / FC03)
  FC 5,6 + Write, Read/Write -> read back AND editable (click the card to write
                                a single coil / single holding register)

Live Data extras:
  * Undo / Redo of deleted tags, Sort (access / function code), Delete All tags
  * The Sort button sits beside the "Live Data" title and works in BOTH views
    (cards and the Edit-tag table)
  * Select tag / Delete tag work on the cards and on the Edit-tag table rows; the tag dialog
    has its own Delete button
  * An address belongs to one tag only (address is a primary key)
  * Colour-coded cards (green = OK, red = read error, grey = unconfigured, white = waiting)
    and a state filter (all / configured / unconfigured / OK / errors)
  * Drag-and-drop card re-ordering (the order is saved in modbus_tester_tags.json)
  * Keyboard shortcuts: Ctrl+Z undo, Ctrl+Y / Ctrl+Shift+Z redo, Delete = delete
    the selected tags (cards or Edit-tag table rows)
  * Edit-tag table: sortable columns (stable ordering) + tag-name search
  * Download the tag table as Word / Excel / CSV
  * Upload a tag table from Excel / Word / CSV (columns: address, tag name, function code or
    name, optional device address); blank cells get default values. A format guide
    describing the required file contents is shown before the file picker opens.
  * Own "Live scan rate (ms)" setting for the Live Data refresh

Polling improvements in this version:
  * The scan rate is the time between the START of two polls (the time a poll
    takes is subtracted), so the real rate matches the setting
  * Rates down to 100 ms are honoured (previously silently raised to 250 ms)
  * Automatic back-off while the device does not answer (no hammering of a dead bus)
  * The actual scan time is shown in the status strip
  * Live Data stops a cycle early when the device stops answering instead of
    waiting for one time-out per block

Install:  pip install PySide6 pymodbus pyserial
Optional: pip install openpyxl python-docx      (Excel / Word download + upload)
Run:      python modbus_tester_pyside6.py

Settings are stored in modbus_tester_state.json next to this file (same file
and keys as the Streamlit version, so your saved settings and write tables are
picked up automatically). Live Data tag configuration is stored in
modbus_tester_tags.json.
"""

import csv
import html
import inspect
import io
import json
import os
import re
import struct
import sys
import threading
import time
from datetime import datetime
from pathlib import Path
from PySide6.QtGui import QIcon

from pymodbus.client import ModbusSerialClient
from PySide6.QtCore import (
    QAbstractTableModel,
    QItemSelectionModel,
    QMimeData,
    QModelIndex,
    QObject,
    QRegularExpression,
    Qt,
    QTimer,
    Signal,
    Slot,
)
from PySide6.QtGui import (
    QColor,
    QDrag,
    QFontDatabase,
    QKeySequence,
    QPainter,
    QPalette,
    QRegularExpressionValidator,
    QShortcut,
)
from PySide6.QtWidgets import (
    QAbstractItemView,
    QAbstractSpinBox,
    QApplication,
    QDialog,
    QDialogButtonBox,
    QFileDialog,
    QFormLayout,
    QButtonGroup,
    QComboBox,
    QFrame,
    QGridLayout,
    QHBoxLayout,
    QHeaderView,
    QLabel,
    QMainWindow,
    QLineEdit,
    QMenu,
    QMessageBox,
    QPlainTextEdit,
    QPushButton,
    QRadioButton,
    QScrollArea,
    QSizePolicy,
    QSpinBox,
    QStackedWidget,
    QStyledItemDelegate,
    QTableView,
    QTableWidget,
    QTableWidgetItem,
    QTabWidget,
    QVBoxLayout,
    QWidget,
)

# ============================================================
# FILES / PERSISTENT STORAGE
# ============================================================

if getattr(sys, "frozen", False):  # PyInstaller etc.
    APP_DIR = Path(sys.executable).resolve().parent
else:
    APP_DIR = Path(__file__).resolve().parent
STATE_FILE = APP_DIR / "modbus_tester_state.json"
TAG_CONFIG_FILE = APP_DIR / "modbus_tester_tags.json"

DEFAULT_PORT = "COM1" if os.name == "nt" else "/dev/ttyUSB0"
FALLBACK_PORTS = (
    ["COM1", "COM2", "COM3", "COM4"] if os.name == "nt" else ["/dev/ttyUSB0", "/dev/ttyUSB1", "/dev/ttyS0", "/dev/ttyACM0"]
)


def load_state():
    try:
        if STATE_FILE.exists():
            data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
            return data if isinstance(data, dict) else {}
    except Exception:
        pass
    return {}


def list_serial_ports():
    try:
        from serial.tools import list_ports

        return [p.device for p in list_ports.comports()]
    except Exception:
        return []


# ============================================================
# THREAD-SAFE RUNTIME STORE
# (single source of truth for counters, status, table data, logs;
#  written by the UI thread, the poller thread and the write/read workers)
# ============================================================


class Runtime:
    def __init__(self):
        self.lock = threading.RLock()
        self.polls = 0
        self.valid_responses = 0
        self.read_status = "Not read"
        self.write_status = "—"
        self.last_update = "—"
        self.poll_ms = 0  # duration of the last background poll
        self.data = {}  # address -> displayed value
        self.data_signature = None
        self.data_version = 0
        self.spy_log = []
        self.raw_log = []
        self.log_version = 0
        self.raw_version = 0
        self.link_level = "idle"  # ok | warn | error | info | idle
        self.link_status = "No request sent yet"
        self.link_time = "—"

    # ---- logs -------------------------------------------------
    def log(self, message):
        with self.lock:
            self._log_unlocked(message)

    def _log_unlocked(self, message):
        self.spy_log.append(f"{datetime.now():%H:%M:%S} {message}")
        del self.spy_log[:-500]
        self.log_version += 1

    def raw(self, line):
        with self.lock:
            self.raw_log.append(line)
            del self.raw_log[:-1000]
            self.raw_version += 1

    def clear_log(self):
        with self.lock:
            self.spy_log = []
            self.log_version += 1

    def clear_raw(self):
        with self.lock:
            self.raw_log = []
            self.raw_version += 1

    # ---- status -----------------------------------------------
    def set_link(self, level, text):
        with self.lock:
            self.link_level = level
            self.link_status = text
            self.link_time = datetime.now().strftime("%H:%M:%S")

    def set_read_status(self, text):
        with self.lock:
            self.read_status = text

    def set_write_status(self, text):
        with self.lock:
            self.write_status = text

    def bump_valid(self):
        with self.lock:
            self.valid_responses += 1

    def reset_counters(self):
        with self.lock:
            self.polls = 0
            self.valid_responses = 0

    # ---- table data -------------------------------------------
    def store_rows(self, rows, *, replace, signature=None):
        with self.lock:
            if replace:
                self.data = {}
            for row in rows:
                self.data[int(row["Address"])] = row["Value"]
            if signature is not None:
                self.data_signature = signature
            self.data_version += 1

    def clear_data(self):
        with self.lock:
            self.data = {}
            self.last_update = "—"
            self.data_version += 1


RT = Runtime()
MODBUS_LOCK = threading.RLock()  # serialises every request on the serial bus
RANGE_CACHE = {}  # discovered "readable segments", guarded by MODBUS_LOCK


# ============================================================
# PERSISTENT MODBUS CLIENT
# ============================================================


def record_raw_serial_bytes(sending, data):
    """Capture Modbus RTU frames exposed by PyModbus' packet-trace hook."""
    try:
        raw = bytes(data or b"")
        direction = "TX" if sending else "RX"
        stamp = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        ascii_text = "".join(chr(b) if 32 <= b <= 126 else "." for b in raw)
        RT.raw(f"{stamp} {direction}  HEX: {raw.hex(' ').upper()}  ASCII: {ascii_text}")
    except Exception:
        pass
    return data


def get_modbus_client(port, baudrate, bytesize, parity, stopbits, timeout):
    options = dict(
        port=port,
        baudrate=int(baudrate),
        bytesize=int(bytesize),
        parity=parity,
        stopbits=int(stopbits),
        timeout=float(timeout),
        retries=0,
    )
    # PyModbus versions differ: pass the packet hook only when supported.
    try:
        if "trace_packet" in inspect.signature(ModbusSerialClient).parameters:
            options["trace_packet"] = record_raw_serial_bytes
    except (TypeError, ValueError):
        pass
    client = ModbusSerialClient(**options)
    try:
        client.trace_packet = record_raw_serial_bytes
    except Exception:
        pass
    return client


# ============================================================
# MODBUS READ HELPERS
# ============================================================

READ_METHODS = {
    "1": "read_coils",
    "2": "read_discrete_inputs",
    "3": "read_holding_registers",
    "4": "read_input_registers",
}

# value type -> (16-bit registers used, struct code)
_TYPE_WIDTHS = {
    "Unsigned 32-bit (UInt32)": (2, "I"),
    "Signed 32-bit (Int32)": (2, "i"),
    "Float 32-bit (Float32)": (2, "f"),
    "Unsigned 64-bit (UInt64)": (4, "Q"),
    "Signed 64-bit (Int64)": (4, "q"),
    "Float 64-bit (Float64)": (4, "d"),
}

_EXCEPTION_NAMES = {
    1: "Illegal function", 2: "Illegal data address", 3: "Illegal data value",
    4: "Slave device failure", 5: "Acknowledge", 6: "Slave device busy",
    8: "Memory parity error", 10: "Gateway path unavailable",
    11: "Gateway target failed to respond",
}


def to_protocol_address(address, kind=None):
    """Convert the UI's one-based address to Modbus's zero-based offset."""
    address = int(address)
    if not 1 <= address <= 65536:
        raise ValueError("Address must be from 1 to 65536.")
    return address - 1


def modbus_call(method, device_id, **kwargs):
    """Call a PyModbus method across API versions with safe unit-ID compatibility."""
    try:
        parameters = inspect.signature(method).parameters
    except (TypeError, ValueError):
        parameters = {}

    if "device_id" in parameters:
        candidates = ["device_id"]
    elif "slave" in parameters:
        candidates = ["slave"]
    elif "unit" in parameters:
        candidates = ["unit"]
    elif "unit_id" in parameters:
        candidates = ["unit_id"]
    else:
        candidates = ["device_id", "slave", "unit", "unit_id"]

    last_type_error = None
    with MODBUS_LOCK:
        for unit_name in candidates:
            try:
                return method(**{unit_name: int(device_id)}, **kwargs)
            except TypeError as exc:
                message = str(exc).lower()
                is_keyword_binding_error = (
                    "unexpected keyword" in message
                    or "invalid keyword" in message
                    or ("keyword argument" in message and unit_name.lower() in message)
                )
                if len(candidates) == 1 or not is_keyword_binding_error:
                    raise
                last_type_error = exc
        if last_type_error is not None:
            raise last_type_error
    raise RuntimeError("Unable to determine the PyModbus unit-ID argument.")


def _exception_text(response):
    code = getattr(response, "exception_code", None)
    if code is not None:
        return f"Modbus exception {code} ({_EXCEPTION_NAMES.get(code, 'unknown')})"
    return str(response)


def _ensure_port_open(client):
    """Return True if the serial port is open, trying to reopen it once if not."""
    try:
        if getattr(client, "connected", False):
            return True
        return bool(client.connect())
    except Exception:
        return False


def _value_width(value_type, kind):
    if str(kind) not in ("3", "4"):
        return 1
    return _TYPE_WIDTHS.get(value_type, (1, None))[0]


def _value_bits(value_type, kind):
    if str(kind) not in ("3", "4"):
        return 1
    return _value_width(value_type, kind) * 16


def decode_register_values(values, value_type, kind):
    """Decode common device-specific interpretations of 16-bit Modbus registers."""
    if str(kind) not in ("3", "4") or value_type in ("Raw register value", "Unsigned 16-bit (UInt16)"):
        return [(i, int(v)) for i, v in enumerate(values)]
    if value_type == "Boolean (0/1)":
        return [(i, bool(v)) for i, v in enumerate(values)]
    if value_type == "Signed 16-bit (Int16)":
        return [(i, (int(v) - 65536 if int(v) >= 32768 else int(v))) for i, v in enumerate(values)]
    if value_type == "ASCII (2 bytes per register)":
        result = []
        for i, v in enumerate(values):
            raw = int(v).to_bytes(2, "big")
            result.append((i, "".join(chr(b) if 32 <= b <= 126 else "." for b in raw)))
        return result
    if value_type not in _TYPE_WIDTHS:
        return [(i, int(v)) for i, v in enumerate(values)]
    width, code = _TYPE_WIDTHS[value_type]
    decoded = []
    for start in range(0, len(values) - width + 1, width):
        raw = b"".join(int(v).to_bytes(2, "big") for v in values[start:start + width])
        number = struct.unpack(">" + code, raw)[0]
        if code == "f":
            number = float(f"{number:.7g}")
        elif code == "d":
            number = float(f"{number:.15g}")
        decoded.append((start, number))
    return decoded


def format_value(value, kind, value_type, data_format):
    """Format one decoded value for display (hex/binary widths follow the data type)."""
    if isinstance(value, (float, str)):
        return value
    if not isinstance(value, (int, bool)):
        return value
    is_register = str(kind) in ("3", "4")
    bits = _value_bits(value_type, kind)
    mask = (1 << bits) - 1
    number = int(value)
    if data_format == "Hexadecimal":
        return f"0x{number & mask:0{max(1, bits // 4)}X}" if is_register else f"0x{number:X}"
    if data_format == "Binary":
        return f"{number & mask:0{bits}b}" if is_register else str(number)
    if data_format == "ASCII":
        if is_register:
            raw = (number & mask).to_bytes(bits // 8, byteorder="big", signed=False)
            return "".join(chr(b) if 32 <= b <= 126 else "." for b in raw)
        return "1" if bool(number) else "0"
    return number


def _build_rows(values, *, kind, address, value_type, data_format, base_offset=0):
    decoded = decode_register_values(values, value_type, kind)
    return [
        {"Address": address + base_offset + offset,
         "Value": format_value(v, kind, value_type, data_format)}
        for offset, v in decoded
    ]


_RANGE_TTL = 60.0  # seconds a discovered "readable segments" map is trusted
_SEARCH_MAX_REQUESTS = 300
_SEARCH_MAX_SECONDS = 15.0


def _read_chunk(method, device_id, protocol_address, offset, n, is_bits):
    """One request. Returns ("ok", values) | ("exc", text) | ("io", text)."""
    try:
        response = modbus_call(method, device_id, address=protocol_address + offset, count=n)
    except Exception as exc:
        return "io", f"{type(exc).__name__}: {exc}"
    if response is None:
        return "io", "No response"
    if response.isError():
        if getattr(response, "exception_code", None) is not None:
            return "exc", _exception_text(response)
        return "io", str(response)
    return "ok", (list(response.bits[:n]) if is_bits else list(response.registers[:n]))


def _discover_segments(method, device_id, protocol_address, count, width, is_bits):
    """Bisect a range the device rejected and keep every part that IS readable."""
    segments = []
    state = {"requests": 1, "abort": None}
    deadline = time.monotonic() + _SEARCH_MAX_SECONDS

    def span(offset, n):
        if state["abort"]:
            return
        units = n // width
        if units < 1:
            return
        if not (offset == 0 and n == count):
            if state["requests"] >= _SEARCH_MAX_REQUESTS or time.monotonic() > deadline:
                state["abort"] = "Address search limit reached"
                return
            state["requests"] += 1
            status, payload = _read_chunk(method, device_id, protocol_address, offset, n, is_bits)
            if status == "ok":
                segments.append((offset, payload))
                return
            if status == "io":
                state["abort"] = payload
                return
        if units == 1:
            return
        half = (units // 2) * width
        span(offset, half)
        span(offset + half, n - half)

    span(0, count)
    segments.sort(key=lambda seg: seg[0])
    return segments, state["abort"]


def fetch_read_rows(client, *, device_id, kind, address, count, value_type,
                    data_format, allow_fallback=False):
    """Read and decode one request (manual reads and the background poller).

    Returns (rows, error_text, unused_registers). Raises ValueError for invalid
    requests and RuntimeError when the serial port cannot be opened.
    """
    kind = str(kind)
    address = int(address)
    count = int(count)
    if kind not in READ_METHODS:
        raise ValueError(f"Unsupported read function: {kind}")
    if count < 1:
        raise ValueError("Length must be at least 1")
    if count > (2000 if kind in ("1", "2") else 125):
        raise ValueError("Requested length exceeds the Modbus protocol limit")
    if address < 1 or address > 65536 or address + count - 1 > 65536:
        raise ValueError("Address range exceeds 1–65536")

    is_bits = kind in ("1", "2")
    width = _value_width(value_type, kind)
    method = getattr(client, READ_METHODS[kind])
    protocol_address = to_protocol_address(address, kind)
    cache_key = (id(client), int(device_id), kind, address, count, width)
    rows, error = [], None

    def build(segments):
        out = []
        for offset, values in segments:
            out.extend(_build_rows(values, kind=kind, address=address, value_type=value_type,
                                   data_format=data_format, base_offset=offset))
        return out

    with MODBUS_LOCK:
        if not _ensure_port_open(client):
            raise RuntimeError("Serial port is not open. Reconnect in Modbus Settings.")

        entry = RANGE_CACHE.get(cache_key)
        if entry and time.monotonic() - entry["ts"] > _RANGE_TTL:
            RANGE_CACHE.pop(cache_key, None)
            entry = None

        # 1) Known readable segments: only those are requested (fast polling).
        if entry and entry["segments"]:
            collected = []
            for offset, n in entry["segments"]:
                status, payload = _read_chunk(method, device_id, protocol_address, offset, n, is_bits)
                if status != "ok":
                    collected = None
                    break
                collected.append((offset, payload))
            if collected is not None:
                rows = build(collected)
                RT.set_link("warn", f"Device ID {device_id} responded; part of the requested range is outside the device's addresses and was skipped.")
            else:
                RANGE_CACHE.pop(cache_key, None)
                entry = None

        if not rows:
            if entry is not None:
                error = entry.get("error") or "No readable addresses"
            else:
                # 2) Whole range in one request.
                status, payload = _read_chunk(method, device_id, protocol_address, 0, count, is_bits)
                if status == "ok":
                    RANGE_CACHE.pop(cache_key, None)
                    rows = build([(0, payload)])
                    RT.set_link("ok", f"Valid — device ID {device_id} answered FC{int(kind):02d} (start {address}, length {count}).")
                else:
                    error = payload
                    # 3) Device rejected the range: find the readable addresses in it.
                    if status == "exc" and allow_fallback:
                        segments, abort = _discover_segments(
                            method, device_id, protocol_address, count, width, is_bits)
                        rows = build(segments)
                        if abort is None:
                            RANGE_CACHE[cache_key] = {
                                "segments": [(o, len(v)) for o, v in segments],
                                "ts": time.monotonic(), "error": error,
                            }
                        if rows:
                            RT.set_link("warn", f"Device ID {device_id} responded ({error}) for part of the range; the available addresses are shown.")
                            error = None
                        elif abort:
                            error = abort

    if not rows and error:
        if str(error).startswith("Modbus exception"):
            RT.set_link("warn", f"{error}. The device responded, so serial settings and device ID are valid, but it rejected the request: check start address, length and register table.")
        else:
            RT.set_link("error", f"No valid response from device ID {device_id}: {error}. Check device ID, baud rate, parity, stop bits, port and wiring.")

    leftover = (count % width) if (width > 1 and not is_bits) else 0
    return rows, error, leftover


def _signature(device_id, kind, address, count, value_type, data_format):
    return (int(device_id), str(kind), int(address), int(count), value_type, data_format)


def _cfg_signature(cfg):
    return _signature(cfg["device_id"], cfg["kind"], cfg["address"], cfg["count"],
                      cfg.get("value_type", "Raw register value"), cfg["data_format"])


def do_read(*, client, device_id, kind, address, count, data_format,
            value_type="Raw register value", status_prefix="Read", merge_existing=False):
    """One read request that updates the shared table/status. Returns (ok, message, n)."""
    kind = str(kind)
    address = int(address)
    count = int(count)
    try:
        with MODBUS_LOCK:
            try:
                rows, error, leftover = fetch_read_rows(
                    client, device_id=device_id, kind=kind, address=address, count=count,
                    value_type=value_type, data_format=data_format, allow_fallback=True,
                )
            except ValueError as exc:
                RT.set_link("error", f"Invalid request parameters: {exc}")
                return False, str(exc), 0

            if not rows:
                return False, f"No readable addresses in requested range. {error or ''}".strip(), 0

            signature = None if merge_existing else _signature(
                device_id, kind, address, count, value_type, data_format)
            RT.store_rows(rows, replace=not merge_existing, signature=signature)
            RT.bump_valid()
            with RT.lock:
                RT.last_update = datetime.now().strftime("%H:%M:%S")

            expected = count if kind in ("1", "2") else max(1, count // _value_width(value_type, kind))
            if len(rows) < expected:
                status = f"{status_prefix} partial — {len(rows)}/{expected} readable addresses"
                message = f"{len(rows)} readable values; unsupported addresses skipped"
            else:
                status = f"{status_prefix} OK — {len(rows)} values"
                message = f"{len(rows)} values"
                if leftover:
                    status += f" ({leftover} trailing register(s) unused by this data type)"
            RT.set_read_status(status)
            return True, message, len(rows)
    except Exception as exc:
        RT.set_link("error", f"Request failed: {type(exc).__name__}: {exc}")
        return False, f"{type(exc).__name__}: {exc}", 0


# ============================================================
# WRITE HELPERS (run on a worker thread)
# ============================================================


def perform_single_writes(client, device_id, is_coil, entries, readback_format):
    """FC05/FC06 one address at a time, each followed by a read-back."""
    successes = 0
    errors = []
    fc = "05" if is_coil else "06"

    with MODBUS_LOCK:
        port_ok = _ensure_port_open(client)
    if not port_ok:
        RT.set_link("error", "Write blocked: the serial port is not open.")
        RT.log(f"WRITE ERROR FC{fc} serial port is not open")
        return "Write failed — see details", ["Serial port is not open. Reconnect in Modbus Settings."]

    for addr_num, val_num in entries:
        try:
            method = getattr(client, "write_coil" if is_coil else "write_register")
            with MODBUS_LOCK:
                response = modbus_call(
                    method, int(device_id),
                    address=to_protocol_address(addr_num, "1" if is_coil else "3"),
                    value=bool(val_num) if is_coil else val_num,
                )
            if response is None or response.isError():
                fail = _exception_text(response) if response is not None else "no response"
                RT.set_link("warn" if str(fail).startswith("Modbus exception") else "error",
                            f"Write FC{fc} to address {addr_num} rejected: {fail}")
                RT.log(f"WRITE ERROR FC{fc} unit={device_id} address={addr_num} {fail}")
                errors.append(f"Address {addr_num}: write failed ({fail})")
                continue
            RT.set_link("ok", f"Valid — device ID {device_id} acknowledged write FC{fc} at address {addr_num}.")
            successes += 1
            RT.log(f"WRITE OK FC{fc} unit={device_id} address={addr_num} value={val_num}")
            # Read back one raw register/coil regardless of the Read tab's data type.
            ok, message, _ = do_read(
                client=client, device_id=int(device_id),
                kind="1" if is_coil else "3", address=addr_num, count=1,
                data_format=readback_format, value_type="Raw register value",
                status_prefix="Write read-back", merge_existing=True,
            )
            if not ok:
                errors.append(f"Address {addr_num}: write succeeded, read-back failed ({message})")
        except Exception as exc:
            RT.set_link("error", f"Write to address {addr_num} failed: {type(exc).__name__}: {exc}. Check device ID, baud rate, parity, stop bits and wiring.")
            RT.log(f"WRITE ERROR address={addr_num} {type(exc).__name__}: {exc}")
            errors.append(f"Address {addr_num}: {type(exc).__name__}: {exc}")

    if successes and not errors:
        status = f"Write OK — {successes} entries written and read table updated"
    elif successes:
        status = f"Partial write — {successes} succeeded; review errors"
    else:
        status = "Write failed — see details"
    return status, errors


def perform_multi_write(client, device_id, is_coil, start, end, entries, readback_format="Decimal"):
    """FC15/FC16 contiguous write; falls back to sequential FC05/FC06; reads back the range."""
    errors = []
    expected_kind = "FC15" if is_coil else "FC16"
    try:
        with MODBUS_LOCK:
            if not _ensure_port_open(client):
                raise RuntimeError("Serial port is not open. Reconnect in Modbus Settings.")
        protocol_start = to_protocol_address(int(start), "1" if is_coil else "3")
        payload_values = [bool(v) for _, v in entries] if is_coil else [v for _, v in entries]
        method_name = "write_coils" if is_coil else "write_registers"
        method = getattr(client, method_name, None)
        bulk_error = None
        bulk_ok = False
        if method is not None:
            RT.log(f"WRITE TX {expected_kind} unit={device_id} ui_start={start} "
                   f"protocol_offset={protocol_start} count={len(payload_values)}")
            try:
                with MODBUS_LOCK:
                    response = modbus_call(method, int(device_id), address=protocol_start,
                                           values=payload_values)
                if response is not None and hasattr(response, "isError") and not response.isError():
                    bulk_ok = True
                    RT.set_link("ok", f"Valid — device ID {device_id} acknowledged write {expected_kind} (start {start}, count {len(payload_values)}).")
                else:
                    exception_code = getattr(response, "exception_code", None) if response is not None else None
                    code_text = f" (Modbus exception code {exception_code})" if exception_code is not None else ""
                    bulk_error = f"{response!s}{code_text}" if response is not None else "no response"
            except Exception as exc:
                bulk_error = f"{type(exc).__name__}: {exc}"
        else:
            bulk_error = f"PyModbus client has no {method_name} method"

        if bulk_ok:
            RT.log(f"WRITE OK {expected_kind} unit={device_id} start={start} count={len(entries)} end={end}")
        else:
            single_method_name = "write_coil" if is_coil else "write_register"
            single_method = getattr(client, single_method_name, None)
            if single_method is None:
                raise RuntimeError(f"{expected_kind} failed ({bulk_error}); fallback method {single_method_name} is unavailable.")
            fallback_code = "FC05" if is_coil else "FC06"
            RT.set_link("warn", f"{expected_kind} rejected ({bulk_error}); trying sequential {fallback_code} writes.")
            RT.log(f"WARN {expected_kind} failed ({bulk_error}); falling back to sequential {fallback_code} writes")
            failures = []
            fallback_successes = 0
            for address_ui, value in entries:
                address_protocol = to_protocol_address(address_ui, "1" if is_coil else "3")
                try:
                    with MODBUS_LOCK:
                        one = modbus_call(single_method, int(device_id), address=address_protocol,
                                          value=bool(value) if is_coil else int(value))
                    if one is None or not hasattr(one, "isError") or one.isError():
                        failures.append(f"Address {address_ui}: {str(one) if one is not None else 'no response'}")
                    else:
                        fallback_successes += 1
                        RT.log(f"WRITE OK {fallback_code} unit={device_id} address={address_ui} value={value}")
                except Exception as one_exc:
                    failures.append(f"Address {address_ui}: {type(one_exc).__name__}: {one_exc}")
            if failures:
                message = (f"{expected_kind} failed ({bulk_error}); sequential {fallback_code} fallback "
                           f"wrote {fallback_successes}/{len(entries)} values. " + "; ".join(failures))
                if fallback_successes == 0:
                    raise RuntimeError(message)
                errors.append(message)
            else:
                RT.set_link("ok", f"Valid — device ID {device_id} acknowledged sequential {fallback_code} writes.")
                RT.log(f"WRITE OK sequential {fallback_code} fallback unit={device_id} start={start} count={len(entries)} end={end}")

        # Read the range back once (FC03/FC01 even if only FC06/FC05 could write),
        # using the same data format as the Read Data tab.
        ok, msg, read_count = do_read(
            client=client, device_id=int(device_id), kind="1" if is_coil else "3",
            address=int(start), count=len(entries), data_format=readback_format,
            value_type="Raw register value", status_prefix="Write read-back", merge_existing=True,
        )
        if not ok:
            errors.append(f"Write succeeded, but range read-back failed ({msg}).")
        elif read_count < len(entries):
            errors.append(f"Write succeeded; read-back returned {read_count}/{len(entries)} values.")
        status = (f"Write OK — {len(entries)} values sent; read table updated"
                  if not errors else f"Write sent, but {len(errors)} read-back/error issue(s) occurred")
    except Exception as exc:
        RT.set_link("error", f"Write {expected_kind} failed: {type(exc).__name__}: {exc}")
        RT.log(f"WRITE ERROR {expected_kind} {type(exc).__name__}: {exc}")
        errors.append(f"{expected_kind}: {type(exc).__name__}: {exc}")
        status = "Write failed — see details"
    return status, errors


# ============================================================
# LIVE DATA TAG HELPERS
# (tag value read / write, request batching, tag configuration file)
# ============================================================

# Live Data function code -> function used to READ the tag's value.
# FC05 (write coil) is read back with FC01, FC06 (write register) with FC03.
_TAG_READ_KIND = {"1": "1", "2": "2", "3": "3", "4": "4", "5": "1", "6": "3"}
_TAG_ACCESS = ("Read", "Write", "Read/Write")
_TAG_MAX_GAP = 3     # addresses we are willing to read "for free" between two tags
_TAG_MAX_SPAN = 100  # max addresses in one batched request (protocol limit is 125)


def read_tag_value(client, cfg):
    """Read ONE value for a Live Data tag using the same code path as the Read Data tab."""
    fc = str(cfg["function_code"])
    rows, error, _unused = fetch_read_rows(
        client,
        device_id=int(cfg["device_address"]),
        kind=_TAG_READ_KIND[fc],
        address=int(cfg["address"]),
        count=1,
        value_type="Raw register value",
        data_format="Decimal",
        allow_fallback=False,
    )
    if not rows:
        raise RuntimeError(error or "No value returned")
    return int(rows[0]["Value"])


def write_tag_value(client, cfg, value):
    """FC05 (single coil) / FC06 (single register) write for a Live Data tag, then read back."""
    fc = str(cfg["function_code"])
    if fc not in ("5", "6"):
        raise ValueError("Only function codes 5 and 6 can be written")
    is_coil = fc == "5"
    device_id = int(cfg["device_address"])
    address = int(cfg["address"])
    value = int(value)
    if is_coil and value not in (0, 1):
        raise ValueError("Coil value must be 0 or 1")
    if not is_coil and not 0 <= value <= 65535:
        raise ValueError("Register value must be 0–65535")

    method = client.write_coil if is_coil else client.write_register
    with MODBUS_LOCK:
        if not _ensure_port_open(client):
            raise RuntimeError("Serial port is not open. Reconnect in Modbus Settings.")
        response = modbus_call(
            method, device_id,
            address=to_protocol_address(address),
            value=bool(value) if is_coil else value,
        )
    if response is None or response.isError():
        fail = _exception_text(response) if response is not None else "no response"
        RT.set_link("warn" if str(fail).startswith("Modbus exception") else "error",
                    f"Write FC0{fc} to address {address} rejected: {fail}")
        RT.log(f"WRITE ERROR FC0{fc} unit={device_id} address={address} {fail}")
        raise RuntimeError(f"Write rejected: {fail}")

    RT.set_link("ok", f"Valid — device ID {device_id} acknowledged write FC0{fc} at address {address}.")
    RT.log(f"WRITE OK FC0{fc} unit={device_id} address={address} value={value}")
    RT.bump_valid()
    try:
        return read_tag_value(client, cfg)  # read-back confirms what the device now holds
    except Exception:
        return value


def group_tag_reads(jobs, max_gap=_TAG_MAX_GAP, max_span=_TAG_MAX_SPAN):
    """Merge tag reads into as few Modbus requests as possible.

    jobs: list of (tag_id, cfg). Tags are grouped per (device, read-function) and sorted by
    address; neighbours closer than max_gap addresses share one request (capped at max_span).
    Returns blocks: {"device","kind","start","end","tids":[(tag_id, address), ...]}.
    """
    groups = {}
    for tid, cfg in jobs:
        key = (int(cfg["device_address"]), _TAG_READ_KIND[str(cfg["function_code"])])
        groups.setdefault(key, []).append((int(cfg["address"]), tid))
    blocks = []
    for (device, kind), items in groups.items():
        items.sort()
        current = None
        for address, tid in items:
            if (current is not None
                    and address - current["end"] - 1 <= max_gap
                    and max(address, current["end"]) - current["start"] + 1 <= max_span):
                current["end"] = max(current["end"], address)
                current["tids"].append((tid, address))
            else:
                current = {"device": device, "kind": kind, "start": address,
                           "end": address, "tids": [(tid, address)]}
                blocks.append(current)
    return blocks


def read_tag_block(client, block):
    """One request for a whole block. Returns {address: int value}."""
    rows, error, _unused = fetch_read_rows(
        client,
        device_id=block["device"],
        kind=block["kind"],
        address=block["start"],
        count=block["end"] - block["start"] + 1,
        value_type="Raw register value",
        data_format="Decimal",
        allow_fallback=False,
    )
    if not rows:
        raise RuntimeError(error or "No value returned")
    return {int(r["Address"]): int(r["Value"]) for r in rows}


def normalize_tag_config(raw):
    """Validate one stored tag configuration; returns a clean dict or None."""
    try:
        fc = str(raw["function_code"])
        if fc not in _TAG_READ_KIND:
            return None
        device = int(raw["device_address"])
        address = int(raw["address"])
        if not (1 <= device <= 247 and 1 <= address <= 65536):
            return None
        # Access is imported tag metadata and must be preserved exactly as a
        # canonical permission label, independent of capitalization in the file.
        # Do not silently replace imported Write / Read-Write with Read based on FC.
        # Actual write operations remain guarded separately by FC05/FC06 checks.
        access = parse_access(raw.get("access", "Read")) or "Read"
        return {"device_address": device, "function_code": fc, "address": address,
                "access": access, "tag_name": str(raw.get("tag_name", ""))}
    except (KeyError, TypeError, ValueError, AttributeError):
        return None


def load_tag_file(path):
    """Returns (live_tags [(id, name)], configurations {id: cfg}). Raises on a bad file."""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    entries = data["tags"]
    tags, configs, seen = [], {}, set()
    for entry in entries:
        tag_id = int(entry["id"])
        name = str(entry["name"]).strip()
        if not name or tag_id in seen:
            continue
        seen.add(tag_id)
        tags.append((tag_id, name))
        cfg = normalize_tag_config(entry.get("config") or {}) if entry.get("config") else None
        if cfg:
            cfg["tag_name"] = name
            configs[tag_id] = cfg
    if not tags:
        raise ValueError("No tags found in file")
    return tags, configs


def save_tag_file(path, live_tags, configurations):
    # The order of live_tags (including drag-and-drop re-ordering) is the order in the file.
    payload = {
        "version": 1,
        "tags": [{"id": tid, "name": name, "config": configurations.get(tid)}
                 for tid, name in live_tags],
    }
    path = Path(path)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    os.replace(tmp, path)


# ============================================================
# TAG TABLE FILES (Excel / Word / CSV upload) AND THE UNIQUE-ADDRESS RULE
# ============================================================


class TagFileError(Exception):
    """An uploaded tag file cannot be read or lacks the required columns."""


# Header names accepted for every column (compared as lower-case letters and digits only).
_TAG_FIELD_ALIASES = {
    "name": {"tagname", "tagnames", "tag", "tags", "name", "parameter", "parametername",
             "signal", "signalname", "point", "pointname", "variable", "variablename",
             "metric", "metricname"},
    "address": {"address", "addr", "tagaddress", "registeraddress", "registeraddr",
                "regaddress", "regaddr", "modbusaddress", "startaddress", "dataaddress",
                "register", "reg", "registerno", "registernumber"},
    "function": {"functioncode", "functioncodes", "function", "functions", "functionname",
                 "functionnames", "fc", "fcode", "func", "funccode", "functiontype",
                 "modbusfunction", "functioncodename"},
    "device": {"deviceaddress", "deviceaddr", "deviceid", "device", "deviceno", "slaveid",
               "slaveaddress", "slaveaddr", "slave", "unitid", "unit", "unitaddress",
               "modbusslaveid", "nodeid", "nodeaddress"},
    "access": {"access", "accessmode", "accesstype", "rw", "readwrite", "permission",
               "permissions", "mode"},
}
_REQUIRED_TAG_FIELDS = ("name", "address", "function")
_FIELD_LABELS = {"name": "Tag name", "address": "Address",
                 "function": "Function code (or function name)"}
_EMPTY_CELLS = {"", "—", "–", "-", "n/a", "nan", "null"}   # all count as "blank"


def _norm_header(text):
    return re.sub(r"[^a-z0-9]+", "", str(text).casefold())


def _clean_cell(value):
    if value is None:
        return ""
    if isinstance(value, float) and value.is_integer():
        value = int(value)
    text = str(value).replace("\xa0", " ").strip()
    return "" if text.lower() in _EMPTY_CELLS else text


def _parse_int(text):
    text = str(text).strip()
    if not text:
        return None
    try:
        if text.lower().startswith("0x"):
            return int(text, 16)
        number = float(text)
    except (ValueError, OverflowError):
        return None
    if number != number or number in (float("inf"), float("-inf")):
        return None
    return int(number) if number.is_integer() else None


# "3", "03", "FC03", "FC 3 - Read Holding Registers", "Function code 3 - ..." ...
_FC_NUMBER = re.compile(
    r"(?:fc|function(?:\s*code)?)?\s*[:#]?\s*0*(\d{1,2})(?:[\s\-–—:(].*)?", re.IGNORECASE | re.DOTALL)


def parse_function_code(text):
    """Function code ("1".."6") from a number or a function name, or None."""
    s = str(text or "").strip().casefold()
    if not s:
        return None
    match = _FC_NUMBER.fullmatch(s)
    if match:
        code = str(int(match.group(1)))
        return code if code in _TAG_READ_KIND else None
    if "multiple" in s:
        return None                      # FC15 / FC16 are not tag functions
    if "discrete" in s:
        return "2"
    if "coil" in s:
        return "5" if any(word in s for word in ("write", "force", "single")) else "1"
    if "input" in s and "reg" in s:
        return "4"
    if "holding" in s or "register" in s:
        return "6" if any(word in s for word in ("write", "preset", "single")) else "3"
    return None


def parse_access(text):
    """Normalize uploaded access data without regard to capitalization or separators.

    Examples accepted include R/r, W/w, R/W, W/R, RW/WR, Read/Write,
    Write/Read, Read-Write, Read only, and their uppercase/lowercase variants.
    Returns the canonical UI label or None when the value is not recognized.
    """
    # casefold() handles case-insensitive matching robustly; removing separators
    # means values such as "R / W", "r-w", and "READ_WRITE" map consistently.
    raw = str(text or "").strip().casefold()
    key = re.sub(r"[^a-z0-9]+", "", raw)
    if not key:
        return None

    dual_aliases = {
        "rw", "wr", "readwrite", "writeread", "readandwrite", "writeandread",
        "readorwrite", "writeorread", "readwriteaccess", "writereadaccess",
    }
    read_aliases = {"r", "read", "readonly", "ro", "readaccess"}
    write_aliases = {"w", "write", "writeonly", "wo", "writeaccess"}

    if key in dual_aliases:
        return "Read/Write"
    if key in read_aliases:
        return "Read"
    if key in write_aliases:
        return "Write"
    return None


def _find_header_row(rows, scan_rows=30):
    """Best header row among the first rows: (score, row_index, {field: column}) or None."""
    best = None
    for index, row in enumerate(rows[:scan_rows]):
        mapping = {}
        for column, cell in enumerate(row):
            key = _norm_header(_clean_cell(cell))
            if not key:
                continue
            for field, aliases in _TAG_FIELD_ALIASES.items():
                if key in aliases and field not in mapping:
                    mapping[field] = column
                    break
        if not mapping:
            continue
        score = sum(1 for field in _REQUIRED_TAG_FIELDS if field in mapping)
        if best is None or score > best[0]:
            best = (score, index, mapping)
    return best


def _extract_records(rows, header_index, mapping):
    records = []
    for row in rows[header_index + 1:]:
        cells = [_clean_cell(cell) for cell in row]
        record = {field: (cells[column] if column < len(cells) else "")
                  for field, column in mapping.items()}
        if not any(record.values()):
            continue                     # blank line
        if (_norm_header(record.get("name", "")) in _TAG_FIELD_ALIASES["name"]
                and _norm_header(record.get("address", "")) in _TAG_FIELD_ALIASES["address"]):
            continue                     # header repeated on a later page / sheet
        records.append(record)
    return records


def _read_xlsx_tables(path):
    try:
        from openpyxl import load_workbook
    except ImportError:
        raise TagFileError("Excel upload needs openpyxl.\n\nInstall it with:\npip install openpyxl") from None
    try:
        workbook = load_workbook(path, read_only=True, data_only=True)
    except Exception as exc:  # noqa: BLE001
        raise TagFileError(f"Could not open the Excel file: {exc}") from None
    try:
        return [(sheet.title, [list(row) for row in sheet.iter_rows(values_only=True)])
                for sheet in workbook.worksheets]
    finally:
        workbook.close()


def _read_docx_tables(path):
    try:
        from docx import Document
    except ImportError:
        raise TagFileError("Word upload needs python-docx.\n\nInstall it with:\npip install python-docx") from None
    try:
        document = Document(str(path))
    except Exception as exc:  # noqa: BLE001
        raise TagFileError(f"Could not open the Word file: {exc}") from None
    if not document.tables:
        raise TagFileError("The Word document has no table. Put the tags in a table with "
                           "Address, Tag name and Function code columns.")
    return [(f"Table {number}", [[cell.text for cell in row.cells] for row in table.rows])
            for number, table in enumerate(document.tables, start=1)]


def _read_csv_tables(path):
    raw = Path(path).read_bytes()
    if raw.startswith((b"\xff\xfe", b"\xfe\xff")):
        text = raw.decode("utf-16", errors="replace")
    else:
        try:
            text = raw.decode("utf-8-sig")
        except UnicodeDecodeError:
            text = raw.decode("cp1252", errors="replace")
    sample = [line for line in text.splitlines() if line.strip()][:10]
    delimiter = max((",", ";", "\t", "|"), key=lambda d: sum(line.count(d) for line in sample))
    if not sum(line.count(delimiter) for line in sample):
        delimiter = ","
    return [("CSV file", list(csv.reader(io.StringIO(text, newline=""), delimiter=delimiter)))]


def read_tag_file_tables(path, fmt):
    """Every sheet / table / CSV of the file as [(title, rows)] where rows are lists of cells."""
    reader = {"xlsx": _read_xlsx_tables, "docx": _read_docx_tables, "csv": _read_csv_tables}[fmt]
    return reader(path)


def extract_tag_records(tables):
    """Scan the whole file (every sheet / table) for tag rows.

    Returns (records, columns_found). Raises TagFileError when no table has the
    three required columns: address, tag name and function code (or function name).
    """
    records, columns = [], set()
    best_score, best_mapping, best_header = -1, {}, []
    for _title, rows in tables:
        found = _find_header_row(rows)
        if found is None:
            continue
        score, index, mapping = found
        if score < len(_REQUIRED_TAG_FIELDS):
            if score > best_score:
                best_score, best_mapping = score, mapping
                best_header = [_clean_cell(c) for c in rows[index] if _clean_cell(c)]
            continue
        columns.update(mapping)
        records.extend(_extract_records(rows, index, mapping))
    if not columns:
        message = ("The file must have a header row with these columns: "
                   + ", ".join(_FIELD_LABELS.values()) + ".")
        if best_score >= 0:
            missing = [label for field, label in _FIELD_LABELS.items() if field not in best_mapping]
            message += "\n\nMissing column(s): " + ", ".join(missing) + "."
            if best_header:
                message += "\nColumns found: " + ", ".join(best_header) + "."
        else:
            message += "\n\nNo header row was found."
        raise TagFileError(message)
    if not records:
        raise TagFileError("The file has the required columns but no tag rows below the header.")
    return records, columns


def build_tag_set(records, default_device):
    """Turn scanned rows into (tags, configs, file_device, report).

    Blank or invalid cells get default values:
      tag name -> "Unknown tag N", function code -> FC03, address -> next free address,
      device address -> default_device, access -> Read (Read/Write for FC05 / FC06).
    An address can belong to one tag only (primary key): when a later row repeats an
    address, that tag is added without a configuration and listed in report["duplicates"].
    file_device is the first valid device address found in the file (None if there is none).
    """
    report = {"tags": len(records), "configured": 0, "name": 0, "function": 0, "address": 0,
              "duplicates": [], "device_conflicts": 0}
    parsed, file_device = [], None
    for position, rec in enumerate(records, start=1):
        address = _parse_int(rec.get("address", ""))
        if address is not None and not 1 <= address <= 65536:
            address = None
        device = _parse_int(rec.get("device", ""))
        if device is not None and not 1 <= device <= 247:
            device = None
        if device is not None:
            if file_device is None:
                file_device = device
            elif device != file_device:
                report["device_conflicts"] += 1
        parsed.append({
            "position": position,
            "name": rec.get("name", ""),
            "code": parse_function_code(rec["function"]) if rec.get("function") else None,
            "address": address,
            "access": parse_access(rec.get("access", "")),
            "skip": False,
        })

    used = set()                          # addresses taken explicitly by the file
    for item in parsed:
        if item["address"] is None:
            continue
        if item["address"] in used:
            label = item["name"] or f"Unknown tag {item['position']}"
            report["duplicates"].append((label, item["address"]))
            item["address"], item["skip"] = None, True
        else:
            used.add(item["address"])
    next_free = 1                         # default address for blank cells
    for item in parsed:
        if item["skip"] or item["address"] is not None:
            continue
        while next_free in used:
            next_free += 1
        if next_free > 65536:
            item["skip"] = True
            continue
        item["address"] = next_free
        used.add(next_free)
        report["address"] += 1

    device = file_device or int(default_device)
    tags, configs = [], {}
    for tag_id, item in enumerate(parsed, start=1):
        name = item["name"]
        if not name:
            name = f"Unknown tag {item['position']}"
            report["name"] += 1
        tags.append((tag_id, name))
        if item["skip"]:
            continue
        code = item["code"]
        if code is None:
            code = "3"
            report["function"] += 1
        access = item["access"] or ("Read/Write" if code in ("5", "6") else "Read")
        cfg = normalize_tag_config({"device_address": device, "function_code": code,
                                    "address": item["address"], "access": access,
                                    "tag_name": name})
        if cfg:
            configs[tag_id] = cfg
    report["configured"] = len(configs)
    return tags, configs, file_device, report


def dedupe_tag_addresses(live_tags, configs):
    """Address is a primary key: the first tag keeps it, later tags lose their configuration.

    Modifies configs in place; returns [(tag name, address), ...] of the tags that lost it.
    """
    seen, dropped = set(), []
    for tag_id, name in live_tags:
        cfg = configs.get(tag_id)
        if not cfg:
            continue
        if cfg["address"] in seen:
            configs.pop(tag_id)
            dropped.append((name, cfg["address"]))
        else:
            seen.add(cfg["address"])
    return dropped


# ============================================================
# BACKGROUND POLLING (serial worker thread, non-blocking UI)
# ============================================================

_MIN_SCAN_MS = 50          # lowest scan interval the poller will honour
_MAX_BACKOFF_S = 5.0       # longest extra wait while the device is not answering


def background_read_once(client, cfg):
    """Read one poll and publish it to the shared store. Never touches Qt."""
    kind = str(cfg["kind"])
    device_id = int(cfg["device_id"])
    address = int(cfg["address"])
    count = int(cfg["count"])
    value_type = cfg.get("value_type", "Raw register value")

    rows, error, _leftover = fetch_read_rows(
        client, device_id=device_id, kind=kind, address=address, count=count,
        value_type=value_type, data_format=cfg["data_format"], allow_fallback=True,
    )
    if error or not rows:
        raise RuntimeError(error or "No values decoded")

    signature = _cfg_signature(cfg)
    with RT.lock:
        # A changed request (address, length, table, type, format, unit) starts a
        # fresh table; otherwise merge so write read-backs stay visible.
        replace = RT.data_signature != signature
        RT.store_rows(rows, replace=replace, signature=signature)
        RT.valid_responses += 1
        RT.last_update = datetime.now().strftime("%H:%M:%S")
        previous_status = RT.read_status
        expected = count if kind in ("1", "2") else max(1, count // _value_width(value_type, kind))
        if len(rows) < expected:
            new_status = f"Auto read partial — {len(rows)}/{expected} readable addresses (ID {device_id})"
        else:
            new_status = f"Auto read OK — {len(rows)} values (ID {device_id})"
        RT.read_status = new_status
        # Log state changes only, so a fast poll does not flood the log.
        if str(previous_status).split(" —")[0] != new_status.split(" —")[0]:
            RT._log_unlocked(f"{new_status.split(' —')[0].upper()} unit={device_id}, function={kind}, "
                             f"ui_address={address}, count={count}, readable={len(rows)}")


class PollController:
    """One resilient background poller; idle waits are interruptible and errors never kill it.

    Timing: the scan rate is the time between the START of two polls, so the time a
    poll takes is subtracted from the wait. While the device keeps failing the wait
    grows (back-off, capped) so a dead bus is not hammered; the first good answer or
    any change of the poll settings returns to the normal rate immediately.
    """

    def __init__(self):
        self.on = False
        self.cfg = None
        self.client = None
        self.wake = threading.Event()
        self._shutdown = False
        self._thread = None
        self._start_lock = threading.Lock()

    def start(self, wake=True):
        self.on = True
        with self._start_lock:
            if self._thread is None or not self._thread.is_alive():
                self._shutdown = False
                self._thread = threading.Thread(target=self._run, daemon=True, name="ModbusRTUPoller")
                self._thread.start()
                wake = True
        if wake:
            self.wake.set()

    def stop(self):
        """Pause polling; an in-flight serial call finishes by its own timeout."""
        self.on = False
        self.wake.set()

    def shutdown(self):
        self._shutdown = True
        self.on = False
        self.wake.set()

    def _pause(self, seconds):
        if self.wake.wait(seconds):
            self.wake.clear()

    def _run(self):
        failures = 0
        last_cfg = None
        while not self._shutdown:
            if not self.on:
                failures = 0
                self._pause(0.25)
                continue
            cfg = self.cfg
            client = self.client
            if not cfg or client is None:
                RT.set_read_status("Auto poll waiting — device disconnected")
                self._pause(0.25)
                continue
            if cfg != last_cfg:
                failures = 0          # new settings: try again at the normal rate
                last_cfg = dict(cfg)
            started = time.monotonic()
            try:
                with RT.lock:
                    RT.polls += 1
                background_read_once(client, dict(cfg))
                failures = 0
            except Exception as exc:
                failures += 1
                with RT.lock:
                    message = f"Auto read error: {type(exc).__name__}: {exc}"
                    if RT.read_status != message:
                        RT._log_unlocked(f"AUTO READ ERROR {type(exc).__name__}: {exc}")
                    RT.read_status = message
            elapsed = time.monotonic() - started
            with RT.lock:
                RT.poll_ms = int(elapsed * 1000)
            period = max(_MIN_SCAN_MS, int((self.cfg or cfg).get("scan_rate", 1000))) / 1000.0
            delay = period - elapsed                       # start-to-start timing
            if failures:
                delay = max(delay, min(failures * period, _MAX_BACKOFF_S))
            self._pause(max(0.02, delay))


POLLER = PollController()


# ============================================================
# SMALL QT HELPERS
# ============================================================


class AsyncRunner(QObject):
    """Run a function on a worker thread and deliver its result on the UI thread."""

    _done = Signal(int, object)

    def __init__(self, parent=None):
        super().__init__(parent)
        self._callbacks = {}
        self._next_id = 0
        self._done.connect(self._on_done)

    def run(self, fn, callback):
        """callback(ok, value_or_exception) is called on the UI thread."""
        self._next_id += 1
        task_id = self._next_id
        self._callbacks[task_id] = callback

        def worker():
            try:
                outcome = (True, fn())
            except BaseException as exc:  # noqa: BLE001
                outcome = (False, exc)
            try:
                self._done.emit(task_id, outcome)
            except RuntimeError:
                pass  # window already closed

        threading.Thread(target=worker, daemon=True, name="ModbusOp").start()

    @Slot(int, object)
    def _on_done(self, task_id, outcome):
        callback = self._callbacks.pop(task_id, None)
        if callback is not None:
            callback(*outcome)


class ReadTableModel(QAbstractTableModel):
    HEADERS = ("Address", "Value")

    def __init__(self, parent=None):
        super().__init__(parent)
        self._rows = []

    def rowCount(self, parent=QModelIndex()):
        return 0 if parent.isValid() else len(self._rows)

    def columnCount(self, parent=QModelIndex()):
        return 0 if parent.isValid() else 2

    def data(self, index, role=Qt.ItemDataRole.DisplayRole):
        if index.isValid() and role == Qt.ItemDataRole.DisplayRole:
            return str(self._rows[index.row()][index.column()])
        return None

    def headerData(self, section, orientation, role=Qt.ItemDataRole.DisplayRole):
        if role == Qt.ItemDataRole.DisplayRole and orientation == Qt.Orientation.Horizontal:
            return self.HEADERS[section]
        return None

    def set_rows(self, rows):
        """rows: list of (address, value) sorted by address."""
        same_shape = len(rows) == len(self._rows) and all(a[0] == b[0] for a, b in zip(rows, self._rows))
        if same_shape:
            self._rows = rows
            if rows:
                self.dataChanged.emit(self.index(0, 0), self.index(len(rows) - 1, 1))
        else:
            self.beginResetModel()
            self._rows = rows
            self.endResetModel()


class DigitDelegate(QStyledItemDelegate):
    """Cell editor that only accepts whole numbers (up to 5 digits)."""

    def createEditor(self, parent, option, index):
        editor = QLineEdit(parent)
        editor.setValidator(QRegularExpressionValidator(QRegularExpression(r"\d{0,5}"), editor))
        return editor


class SortItem(QTableWidgetItem):
    """Table item that sorts numbers numerically, text alphabetically; '—' goes last.

    Equal values keep their original row order (stable sort) so rows with the same
    Access / Function code do not appear shuffled.
    """

    def __init__(self, text="", order=0):
        super().__init__(text)
        self._order = order

    @staticmethod
    def _key(text):
        text = str(text).strip()
        if text in ("", "—"):
            return (2, 0.0, "")
        try:
            return (0, float(text), "")
        except ValueError:
            pass
        if text.upper().startswith("FC") and text[2:].isdigit():
            return (0, float(text[2:]), "")
        return (1, 0.0, text.casefold())

    def __lt__(self, other):
        mine, theirs = self._key(self.text()), self._key(other.text())
        if mine != theirs:
            return mine < theirs
        return self._order < getattr(other, "_order", 0)


class TagCard(QPushButton):
    """Live Data card. Can be dragged onto another card to re-order the tags."""

    MIME = "application/x-modbus-tag-id"
    dropped = Signal(int, int)  # (dragged tag id, target tag id)

    def __init__(self, tag_id, parent=None):
        super().__init__(parent)
        self.tag_id = tag_id
        self._press_pos = None
        self._drop_hover = False
        self.setAcceptDrops(True)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._press_pos = event.position().toPoint()
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if (event.buttons() & Qt.MouseButton.LeftButton and self._press_pos is not None
                and (event.position().toPoint() - self._press_pos).manhattanLength()
                >= QApplication.startDragDistance()):
            hot_spot = self._press_pos
            self._press_pos = None
            drag = QDrag(self)
            mime = QMimeData()
            mime.setData(self.MIME, str(self.tag_id).encode("ascii"))
            drag.setMimeData(mime)
            pixmap = self.grab()
            drag.setPixmap(pixmap)
            drag.setHotSpot(hot_spot)
            drag.exec(Qt.DropAction.MoveAction)
            self.setDown(False)
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        self._press_pos = None
        super().mouseReleaseEvent(event)

    def dragEnterEvent(self, event):
        if event.mimeData().hasFormat(self.MIME):
            event.acceptProposedAction()
            self._drop_hover = True
            self.update()
        else:
            event.ignore()

    def dragLeaveEvent(self, event):
        self._drop_hover = False
        self.update()
        super().dragLeaveEvent(event)

    def dropEvent(self, event):
        self._drop_hover = False
        self.update()
        if not event.mimeData().hasFormat(self.MIME):
            event.ignore()
            return
        try:
            source_id = int(bytes(event.mimeData().data(self.MIME)).decode("ascii"))
        except ValueError:
            event.ignore()
            return
        event.acceptProposedAction()
        self.dropped.emit(source_id, self.tag_id)

    def paintEvent(self, event):
        super().paintEvent(event)
        if self._drop_hover:
            painter = QPainter(self)
            painter.fillRect(0, 0, 6, self.height(), QColor("#2676a8"))
            painter.end()


class Banner(QLabel):
    """Inline notice in the style of st.info / st.warning / st.error / st.success."""

    _STYLES = {
        "info": "background:#e8f1fa;color:#1f5f8b;border:1px solid #b9d3e8;",
        "success": "background:#e6f4ea;color:#1a7f37;border:1px solid #b7dfc2;",
        "warning": "background:#fff4e0;color:#8a5a00;border:1px solid #f0d49a;",
        "error": "background:#fdecea;color:#a93226;border:1px solid #f0b8b1;",
    }

    def __init__(self, parent=None):
        super().__init__(parent)
        self._level = None
        self._text = None
        self.setWordWrap(True)
        self.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        self.setVisible(False)

    def show_message(self, level, text):
        if level != self._level:
            self._level = level
            self.setStyleSheet(
                "QLabel{" + self._STYLES.get(level, self._STYLES["info"]) +
                "border-radius:8px;padding:8px 12px;}"
            )
        if text != self._text:
            self._text = text
            self.setText(text)
        if self.isHidden():
            self.setVisible(True)

    def clear_banner(self):
        self._text = None
        self._level = None
        self.setVisible(False)


class MetricCard(QFrame):
    def __init__(self, title, parent=None):
        super().__init__(parent)
        self.setObjectName("metric")
        self.setFixedHeight(124)
        self.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(14, 10, 14, 10)
        self._title = QLabel(title)
        self._title.setObjectName("metricTitle")
        self._value = QLabel("0")
        self._value.setObjectName("metricValue")
        lay.addWidget(self._title)
        lay.addWidget(self._value)
        lay.addStretch(1)

    def set_value(self, text):
        if self._value.text() != text:
            self._value.setText(text)


def heading(text, level=4):
    label = QLabel(text)
    label.setObjectName(f"h{level}")
    return label


def caption(text):
    label = QLabel(text)
    label.setObjectName("caption")
    label.setWordWrap(True)
    return label


def labeled(text, widget, tip=None):
    box = QWidget()
    lay = QVBoxLayout(box)
    lay.setContentsMargins(0, 0, 0, 0)
    lay.setSpacing(3)
    label = QLabel(text)
    label.setObjectName("fieldLabel")
    lay.addWidget(label)
    lay.addWidget(widget)
    if tip:
        widget.setToolTip(tip)
        label.setToolTip(tip)
    return box


def make_spin(low, high, step=1):
    spin = QSpinBox()
    spin.setRange(low, high)
    spin.setSingleStep(step)
    spin.setKeyboardTracking(False)  # emit only when the typed value is committed
    return spin


def make_card():
    frame = QFrame()
    frame.setObjectName("card")
    return frame


def scroll_wrap(widget):
    area = QScrollArea()
    area.setWidgetResizable(True)
    area.setFrameShape(QFrame.Shape.NoFrame)
    area.setWidget(widget)
    widget.setAutoFillBackground(False)
    area.viewport().setAutoFillBackground(False)
    return area


# ============================================================
# STYLE (light blue "legacy" theme from the Streamlit version)
# ============================================================

STYLESHEET = """
QMainWindow, QWidget#central {
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #f5f8fc, stop:1 #eef3f9);
}
QWidget { color: #172033; font-family: "Inter", "Segoe UI", "Arial", sans-serif; font-size: 13px; }
QToolTip { color: #172033; background: #ffffff; border: 1px solid #c6d4e3; padding: 4px; }

QLabel#legacyTitle {
    background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #123a63, stop:1 #2676a8);
    color: #ffffff; border-radius: 12px; padding: 14px 20px;
    font-size: 23px; font-weight: 700;
}
QLabel#statusStrip {
    background: #ffffff; border: 1px solid #d8e2ee; border-radius: 10px; padding: 10px 14px;
}
QFrame#metric { background: #ffffff; border: 1px solid #d8e2ee; border-radius: 12px; }
QLabel#metricTitle { color: #61748b; font-size: 12px; }
QLabel#metricValue { font-size: 30px; font-weight: 600; color: #172033; }

QFrame#card {
    background: rgba(255, 255, 255, 0.72); border: 1px solid #d8e2ee; border-radius: 12px;
}
QLabel#h4 { font-size: 17px; font-weight: 700; color: #172033; }
QLabel#h5 { font-size: 14px; font-weight: 700; color: #172033; }
QLabel#caption { color: #61748b; font-size: 12px; }
QLabel#fieldLabel { color: #34495e; font-size: 12px; }
QLabel#smallNote { color: #61748b; font-size: 12px; }

QPushButton {
    border: 1px solid #c6d4e3; border-radius: 9px; background: #ffffff; color: #17324d;
    min-height: 36px; padding: 0 14px; font-weight: 600;
}
QPushButton:hover { border-color: #287bb1; color: #0d4771; background: #f7fbff; }
QPushButton:disabled { color: #9aa9b9; background: #f1f4f8; border-color: #dde5ee; }
QPushButton[primary="true"] { background: #2676a8; border-color: #2676a8; color: #ffffff; }
QPushButton[primary="true"]:hover { background: #1f6592; border-color: #1f6592; color: #ffffff; }
QPushButton[primary="true"]:disabled { background: #a9c4d8; border-color: #a9c4d8; color: #ffffff; }

QTabWidget::pane { border: 0; top: 4px; }
QTabBar::tab {
    background: transparent; padding: 8px 18px; color: #51657c; font-weight: 600;
    border-bottom: 2px solid transparent; margin-right: 2px;
}
QTabBar::tab:selected { color: #123a63; border-bottom: 2px solid #2676a8; }
QTabBar::tab:hover:!selected { color: #123a63; }

QTableView, QTableWidget {
    background: #ffffff; border: 1px solid #d8e2ee; border-radius: 10px;
    gridline-color: #e6edf5; alternate-background-color: #f7fafd;
    selection-background-color: #d6e8f5; selection-color: #172033;
}
QHeaderView::section {
    background: #eef3f9; color: #34495e; border: 0; border-bottom: 1px solid #d8e2ee;
    padding: 6px 8px; font-weight: 600;
}
QPlainTextEdit {
    background: #ffffff; border: 1px solid #d8e2ee; border-radius: 10px; padding: 6px;
    font-size: 12px; selection-background-color: #d6e8f5; selection-color: #172033;
}
QRadioButton { spacing: 8px; padding: 2px 0; }
QScrollArea { background: transparent; }
QMenu { background: #ffffff; border: 1px solid #c6d4e3; padding: 4px; }
QMenu::item { padding: 6px 22px; border-radius: 6px; }
QMenu::item:selected { background: #d6e8f5; color: #123a63; }
QMenu::item:disabled { color: #9aa9b9; }
"""


def apply_light_palette(app):
    pal = QPalette()
    roles = {
        QPalette.ColorRole.Window: "#f5f8fc",
        QPalette.ColorRole.WindowText: "#172033",
        QPalette.ColorRole.Base: "#ffffff",
        QPalette.ColorRole.AlternateBase: "#f7fafd",
        QPalette.ColorRole.Text: "#172033",
        QPalette.ColorRole.Button: "#ffffff",
        QPalette.ColorRole.ButtonText: "#17324d",
        QPalette.ColorRole.ToolTipBase: "#ffffff",
        QPalette.ColorRole.ToolTipText: "#172033",
        QPalette.ColorRole.Highlight: "#2676a8",
        QPalette.ColorRole.HighlightedText: "#ffffff",
        QPalette.ColorRole.PlaceholderText: "#8a9bb0",
    }
    for role, color in roles.items():
        pal.setColor(role, QColor(color))
    app.setPalette(pal)


# ============================================================
# CONSTANTS FOR THE UI
# ============================================================

BAUD_OPTIONS = [1200, 2400, 4800, 9600, 19200, 38400, 57600, 115200]
DATA_BITS_OPTIONS = [7, 8]
PARITY_OPTIONS = ["NONE", "EVEN", "ODD"]
STOP_BITS_OPTIONS = [1, 2]
PARITY_CODES = {"NONE": "N", "EVEN": "E", "ODD": "O"}

DATA_TYPE_OPTIONS = ["3 : Holding registers", "4 : Input registers", "1 : Coils", "2 : Discrete inputs"]
DATA_FORMAT_OPTIONS = ["Decimal", "Hexadecimal", "Binary", "ASCII"]
VALUE_TYPE_OPTIONS = [
    "Boolean (0/1)", "Unsigned 16-bit (UInt16)", "Signed 16-bit (Int16)",
    "ASCII (2 bytes per register)", "Unsigned 32-bit (UInt32)",
    "Signed 32-bit (Int32)", "Float 32-bit (Float32)", "Raw register value",
]
SINGLE_WRITE_KINDS = ["Holding register — FC06 (single)", "Coil — FC05 (single)"]
MULTI_WRITE_KINDS = [
    "Multiple coils — FC15 (contiguous)",
    "Multiple holding registers — FC16 (contiguous)",
]
WRITE_MODES = ["1. Write single registers/coils", "2. Write multiple registers and coils"]

# Display-only tag names for the first-version Tags tab.
TAG_NAMES = ['Tag name', 'Modbus slave ID', 'Reset alarm', 'Display test', 'Display intensity', 'Reserved', 'Reserved', 'Reserved', 'Reserved', 'Reserved', 'Reserved', 'Input offset (CF)', 'Input gain (CG)', 'Output offset (OF)', 'Output gain (OG)', 'Tolerance (TOL)', 'Alarm 1 (AL1 / LO)', 'Alarm 2 (AL2 / HI)', 'Enable', 'Inhibit', 'Reserved', 'Input offset (CF)', 'Input gain (CG)', 'Output offset (OF)', 'Output gain (OG)', 'Tolerance (TOL)', 'Alarm 1 (AL1 / LO)', 'Alarm 2 (AL2 / HI)', 'Enable', 'Inhibit', 'Reserved', 'Inhibit status', 'Alarm status', 'LED status', 'Relay status', 'CH1 reading', 'CH1 decimal point', 'CH1 range (TOP)', 'Reserved', 'Reserved', 'CH2 reading', 'CH2 decimal point', 'CH2 range (TOP)', 'Reserved', 'Reserved']

TAG_FUNCTION_NAMES = [
    ("1", "FC01 - Read Coils"),
    ("2", "FC02 - Read Discrete Inputs"),
    ("3", "FC03 - Read Holding Registers"),
    ("4", "FC04 - Read Input Registers"),
    ("5", "FC05 - Write Single Coil"),
    ("6", "FC06 - Write Single Holding Register"),
]

LINK_COLORS = {"ok": "#1a7f37", "warn": "#b7791f", "error": "#c0392b",
               "info": "#2676a8", "idle": "#61748b"}


def normalize_choice(value, options, default):
    """Map a stored value (including legacy labels) onto a valid option."""
    if value in options:
        return value
    text = str(value or "").lower()
    if text.startswith("2"):
        return options[-1]
    if "coil" in text:
        for option in options:
            if "coil" in option.lower():
                return option
    if "register" in text:
        for option in options:
            if "register" in option.lower():
                return option
    return default


def clamp_int(value, low, high, default):
    try:
        return max(low, min(high, int(value)))
    except (TypeError, ValueError):
        return default


def badge(level, text):
    safe = html.escape(str(text), quote=True)
    return f'<span style="color:{LINK_COLORS.get(level, "#61748b")};font-weight:600">● {safe}</span>'


def clip(text, limit):
    text = str(text)
    return text if len(text) <= limit else text[: limit - 1] + "…"


# ============================================================
# MAIN WINDOW
# ============================================================


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(" MODBUS TESTER")
        self.resize(1480, 940)
        self.setMinimumSize(1120, 720)

        self.saved = load_state()
        self.client = None
        self.connected = False
        self.client_key = None
        self.auto_poll = False
        self.read_busy = False
        self.write_busy = False
        self.connect_busy = False
        self.conn_message = None  # (level, text) shown on the Settings tab when not connected

        self._loading = True
        self._cache = {}
        self._data_ver = -1
        self._log_ver = -1
        self._raw_ver = -1
        self._last_payload = None
        self.save_error = ""

        self.runner = AsyncRunner(self)
        self._save_timer = QTimer(self)
        self._save_timer.setSingleShot(True)
        self._save_timer.setInterval(400)
        self._save_timer.timeout.connect(self.save_state_now)

        self._build_ui()
        self._load_widgets()
        self._connect_signals()
        self._loading = False

        self.publish_poll_cfg()
        self.refresh_all()
        self._timer = QTimer(self)
        self._timer.setInterval(250)
        self._timer.timeout.connect(self.refresh_all)
        self._timer.start()
        self._tag_live_timer = QTimer(self)
        self._tag_live_timer.setInterval(500)
        self._tag_live_timer.timeout.connect(self._poll_live_tag_values)
        self._tag_live_timer.start()
        self._init_live_extras()
        self._setup_shortcuts()

    # --------------------------------------------------------
    # UI construction
    # --------------------------------------------------------
    def _build_ui(self):
        central = QWidget()
        central.setObjectName("central")
        self.setCentralWidget(central)
        root = QVBoxLayout(central)
        root.setContentsMargins(18, 14, 18, 10)
        root.setSpacing(10)

        title = QLabel("UNIPHOS MODBUS TESTER-RTU")
        title.setObjectName("legacyTitle")
        title.setAlignment(Qt.AlignmentFlag.AlignCenter)   # title text centred in the strip
        root.addWidget(title)
        root.addLayout(self._build_top_row())

        self.tabs = QTabWidget()
        self.tabs.addTab(self._build_settings_tab(), "Modbus Settings")
        self.tabs.addTab(self._build_tags_tab(), "Live Data")
        self.tabs.addTab(self._build_read_tab(), "Read Data")
        self.tabs.addTab(self._build_write_tab(), "Write Data")
        self.tabs.addTab(self._build_log_tab(), "Communication Log")
        self.tabs.addTab(self._build_spy_tab(), "Communication Spy")
        root.addWidget(self.tabs, 1)

        footer = QLabel(
            "RTU only · Ensure the selected COM port is not being used by another application. "
            "Use the correct unit ID, baud rate, parity, data bits and stop bits for your device."
        )
        footer.setObjectName("smallNote")
        footer.setWordWrap(True)
        root.addWidget(footer)
        self.save_error_label = QLabel("")
        self.save_error_label.setObjectName("smallNote")
        self.save_error_label.setVisible(False)
        root.addWidget(self.save_error_label)

    def _strip_label(self):
        label = QLabel()
        label.setObjectName("statusStrip")
        label.setTextFormat(Qt.TextFormat.RichText)
        label.setWordWrap(True)
        label.setFixedHeight(124)
        label.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        label.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop)
        return label

    def _build_top_row(self):
        row = QHBoxLayout()
        row.setSpacing(12)
        self.conn_label = self._strip_label()
        self.status_label = self._strip_label()
        self.polls_metric = MetricCard("Polls")
        self.valid_metric = MetricCard("Valid responses")
        self.clear_counters_btn = QPushButton("Clear counters")
        clear_box = QWidget()
        clear_box.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        cl = QVBoxLayout(clear_box)
        cl.setContentsMargins(0, 0, 0, 0)
        cl.addWidget(self.clear_counters_btn)
        cl.addStretch(1)
        row.addWidget(self.conn_label, 21)
        row.addWidget(self.status_label, 21)
        row.addWidget(self.polls_metric, 8)
        row.addWidget(self.valid_metric, 9)
        row.addWidget(clear_box, 9)
        return row

    # ---- Settings tab --------------------------------------
    def _build_settings_tab(self):
        inner = QWidget()
        inner.setMaximumWidth(640)
        lay = QVBoxLayout(inner)
        lay.setContentsMargins(4, 6, 4, 6)
        lay.setSpacing(8)

        lay.addWidget(heading("Modbus"))
        lay.addWidget(caption("Protocol: RTU (serial)"))
        lay.addWidget(heading("RS settings"))

        self.port_combo = QComboBox()
        self.port_combo.setEditable(True)
        self.refresh_ports_btn = QPushButton("↻ Refresh")
        self.refresh_ports_btn.setToolTip("Rescan the available serial ports")
        port_row = QWidget()
        pr = QHBoxLayout(port_row)
        pr.setContentsMargins(0, 0, 0, 0)
        pr.addWidget(self.port_combo, 1)
        pr.addWidget(self.refresh_ports_btn)
        lay.addWidget(labeled("Serial port", port_row))

        self.baud_combo = QComboBox()
        self.baud_combo.addItems([str(b) for b in BAUD_OPTIONS])
        lay.addWidget(labeled("Baud rate", self.baud_combo))

        self.data_bits_combo = QComboBox()
        self.data_bits_combo.addItems([str(b) for b in DATA_BITS_OPTIONS])
        lay.addWidget(labeled("Data bits", self.data_bits_combo))

        self.parity_combo = QComboBox()
        self.parity_combo.addItems(PARITY_OPTIONS)
        lay.addWidget(labeled("Parity", self.parity_combo))

        self.stop_bits_combo = QComboBox()
        self.stop_bits_combo.addItems([str(b) for b in STOP_BITS_OPTIONS])
        lay.addWidget(labeled("Stop bits", self.stop_bits_combo))

        self.timeout_spin = make_spin(100, 10000, 100)
        lay.addWidget(labeled("Time out (ms)", self.timeout_spin))

        note = QLabel("Connection parameters are applied when Connect is pressed.")
        note.setObjectName("smallNote")
        lay.addWidget(note)

        btn_row = QHBoxLayout()
        self.connect_btn = QPushButton("Connect")
        self.disconnect_btn = QPushButton("Disconnect")
        btn_row.addWidget(self.connect_btn)
        btn_row.addWidget(self.disconnect_btn)
        lay.addLayout(btn_row)

        self.conn_banner = Banner()
        lay.addWidget(self.conn_banner)
        self.conn_caption = caption("")
        lay.addWidget(self.conn_caption)
        lay.addStretch(1)

        page = QWidget()
        outer = QHBoxLayout(page)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.addWidget(inner, 0)
        outer.addStretch(1)
        return scroll_wrap(page)

    # ---- Live Data tab --------------------------------------
    def _build_tags_tab(self):
        page = QWidget()
        outer = QHBoxLayout(page)
        outer.setContentsMargins(8, 6, 8, 4)
        outer.setSpacing(12)

        # Keep a per-window list so deleting a card does not alter the source
        # tag list or any existing Modbus communication functionality.
        self.live_tags = list(enumerate(TAG_NAMES, start=1))
        self.selected_tag_ids = set()
        self.tag_selection_mode = False
        self.tag_configurations = {}
        self.tag_live_values = {}
        self._tag_poll_busy = False
        self.tag_errors = {}
        self.tag_cards = {}
        self._tag_write_busy = False
        self.tag_undo_stack = []     # each entry: list of (position, tag_id, name, config)
        self.tag_redo_stack = []
        self.tag_sort = None         # None | ("access", "Read") | ("function", "3")
        self._shown_tag_ids = []     # ids of the cards currently visible (after search/filter)
        self._table_tag_ids = []     # ids of the rows currently in the Edit-tag table
        self._table_filling = False  # True while the Edit-tag table is rebuilt / its selection reset

        # ---------------- sidebar (scrollable so every button stays reachable) ----------------
        sidebar = QFrame()
        sidebar.setObjectName("card")
        sidebar.setFixedWidth(196)
        sidebar_outer = QVBoxLayout(sidebar)
        sidebar_outer.setContentsMargins(4, 6, 4, 6)
        side_inner = QWidget()
        side_inner.setStyleSheet("QPushButton { min-height: 28px; padding: 0 8px; }")
        sidebar_layout = QVBoxLayout(side_inner)
        sidebar_layout.setContentsMargins(6, 6, 6, 6)
        sidebar_layout.setSpacing(8)
        side_scroll = scroll_wrap(side_inner)
        side_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        sidebar_outer.addWidget(side_scroll)

        sidebar_title = QLabel("Tag Actions")
        sidebar_title.setStyleSheet("font-size: 15px; font-weight: 700;")
        sidebar_layout.addWidget(sidebar_title)

        # Shared device address: kept in sync with the Read Data and Write Data tabs.
        self.live_device_spin = make_spin(1, 247)
        sidebar_layout.addWidget(labeled(
            "Device address", self.live_device_spin,
            "Synchronized with the Device address in the Read Data and Write Data tabs. "
            "All Live Data tags use this device."))

        # Display format of the Live Data values (cards and Edit-tag table). Independent
        # of the Data format on the Read Data tab.
        self.live_format_combo = QComboBox()
        self.live_format_combo.addItems(DATA_FORMAT_OPTIONS)
        self.live_format_combo.setCurrentText("Decimal")
        sidebar_layout.addWidget(labeled(
            "Data format", self.live_format_combo,
            "How register values are shown on the Live Data cards and in the Edit-tag table. "
            "Not linked to the Data format on the Read Data tab."))

        # How often the Live Data values are refreshed.
        self.live_scan_spin = make_spin(100, 60000, 100)
        sidebar_layout.addWidget(labeled(
            "Live scan rate (ms)", self.live_scan_spin,
            "How often the Live Data tags are read while this tab is visible. "
            "If a read cycle takes longer than this, the next one starts right after it."))

        self.edit_tag_button = QPushButton("Edit tag")
        self.edit_tag_button.clicked.connect(self._edit_tag_placeholder)
        sidebar_layout.addWidget(self.edit_tag_button)

        self.add_tag_button = QPushButton("Add tag")
        self.add_tag_button.clicked.connect(self._add_unknown_tag)
        sidebar_layout.addWidget(self.add_tag_button)

        self.select_tag_button = QPushButton("Select tag")
        self.select_tag_button.setCheckable(True)
        self.select_tag_button.setToolTip("Select cards (or Edit-tag table rows), then press Delete tag")
        self.select_tag_button.clicked.connect(self._toggle_tag_selection)
        sidebar_layout.addWidget(self.select_tag_button)

        self.delete_tag_button = QPushButton("Delete tag")
        self.delete_tag_button.setToolTip("Delete the selected tags (Delete key)")
        self.delete_tag_button.clicked.connect(self._delete_selected_tags)
        sidebar_layout.addWidget(self.delete_tag_button)

        self.save_configuration_button = QPushButton("Save configuration")
        self.save_configuration_button.clicked.connect(self._save_configuration_placeholder)
        sidebar_layout.addWidget(self.save_configuration_button)

        self.upload_files_button = QPushButton("Upload files")
        self.upload_files_button.setToolTip("Upload a tag table from an Excel, Word or CSV file")
        upload_menu = QMenu(self.upload_files_button)
        for label, fmt in (("Excel (.xlsx)", "xlsx"), ("Word (.docx)", "docx"), ("CSV (.csv)", "csv")):
            action = upload_menu.addAction(label)
            action.triggered.connect(lambda _=False, f=fmt: self._upload_tag_file(f))
        self.upload_files_button.setMenu(upload_menu)
        sidebar_layout.addWidget(self.upload_files_button)

        self.download_tag_button = QPushButton("Download")
        self.download_tag_button.setToolTip("Download the Edit-tag table as Word, Excel or CSV")
        download_menu = QMenu(self.download_tag_button)
        for label, fmt in (("Word (.docx)", "docx"), ("Excel (.xlsx)", "xlsx"), ("CSV (.csv)", "csv")):
            action = download_menu.addAction(label)
            action.triggered.connect(lambda _=False, f=fmt: self._download_tag_table(f))
        self.download_tag_button.setMenu(download_menu)
        sidebar_layout.addWidget(self.download_tag_button)

        self.tag_selection_status = QLabel("Selection mode is off.")
        self.tag_selection_status.setWordWrap(True)
        self.tag_selection_status.setObjectName("smallNote")
        sidebar_layout.addWidget(self.tag_selection_status)

        sidebar_layout.addStretch(1)
        outer.addWidget(sidebar)

        # ---------------- main Live Data area ----------------
        content = QWidget()
        content_layout = QVBoxLayout(content)
        content_layout.setContentsMargins(0, 0, 0, 0)
        content_layout.setSpacing(8)

        content_layout.addWidget(heading("Live Data"))

        content_layout.addWidget(caption(
            "Tag metrics are shown as cards. Use Select tag, choose one or more cards, "
            "then use Delete tag to remove them from this view. Drag a card onto another card to re-order."
        ))

        self.tag_toolbar = QWidget()
        toolbar = QHBoxLayout(self.tag_toolbar)
        toolbar.setContentsMargins(0, 0, 0, 0)
        toolbar.setSpacing(8)
        self.undo_tag_button = QPushButton("Undo")
        self.undo_tag_button.setToolTip("Restore the last deleted tag(s)  (Ctrl+Z)")
        self.undo_tag_button.clicked.connect(self._undo_tag_delete)
        self.redo_tag_button = QPushButton("Redo")
        self.redo_tag_button.setToolTip("Delete again what Undo restored  (Ctrl+Y)")
        self.redo_tag_button.clicked.connect(self._redo_tag_delete)
        # Sort sits right beside Redo in the card toolbar only (the toolbar is hidden
        # while the Edit-tag table is shown).
        self.sort_tag_button = QPushButton("Sort")
        self.sort_tag_button.setToolTip("Show only tags with a chosen access or function code")
        self._build_sort_menu()
        self.delete_all_tags_button = QPushButton("Delete All tags")
        self.delete_all_tags_button.clicked.connect(self._delete_all_tags)
        for button in (self.undo_tag_button, self.redo_tag_button, self.sort_tag_button,
                       self.delete_all_tags_button):
            toolbar.addWidget(button)
        toolbar.addStretch(1)
        self.tag_legend = QLabel(
            '<span style="color:#2e8b57">●</span> OK &nbsp;&nbsp;'
            '<span style="color:#c0392b">●</span> Error &nbsp;&nbsp;'
            '<span style="color:#8a96a3">●</span> Unconfigured &nbsp;&nbsp;'
            '<span style="color:#9bb7cf">●</span> Waiting')
        self.tag_legend.setObjectName("smallNote")
        self.tag_legend.setTextFormat(Qt.TextFormat.RichText)
        toolbar.addWidget(self.tag_legend)
        content_layout.addWidget(self.tag_toolbar)

        # search + state filter row (hidden while the Edit-tag table is shown)
        self.tag_filter_row = QWidget()
        filter_layout = QHBoxLayout(self.tag_filter_row)
        filter_layout.setContentsMargins(0, 0, 0, 0)
        filter_layout.setSpacing(8)
        self.tag_search = QLineEdit()
        self.tag_search.setPlaceholderText("Search tag names...")
        filter_layout.addWidget(self.tag_search, 1)
        self.tag_filter_combo = QComboBox()
        for label, key in (("Show all tags", "all"), ("Show only configured", "configured"),
                           ("Show only unconfigured", "unconfigured"), ("Show only OK", "ok"),
                           ("Show only errors", "error")):
            self.tag_filter_combo.addItem(label, key)
        self.tag_filter_combo.setToolTip("Filter the cards by state")
        filter_layout.addWidget(self.tag_filter_combo)
        content_layout.addWidget(self.tag_filter_row)

        self.tag_scroll = QScrollArea()
        self.tag_scroll.setWidgetResizable(True)
        self.tag_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.tag_content = QWidget()
        self.tag_grid = QGridLayout(self.tag_content)
        self.tag_grid.setContentsMargins(2, 2, 2, 2)
        self.tag_grid.setHorizontalSpacing(12)
        self.tag_grid.setVerticalSpacing(12)
        self.tag_scroll.setWidget(self.tag_content)
        content_layout.addWidget(self.tag_scroll, 1)

        # Table shown when Edit tag is clicked: lists every current metric
        # alongside its tag ID and (if configured) its Modbus binding / live value.
        self.tag_metrics_table = QTableWidget(0, 2)
        self.tag_metrics_table.setHorizontalHeaderLabels(["Index No.", "Tag Name"])
        self.tag_metrics_table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
        self.tag_metrics_table.verticalHeader().setVisible(False)
        self.tag_metrics_table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tag_metrics_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tag_metrics_table.setAlternatingRowColors(True)
        self.tag_metrics_table.cellClicked.connect(self._on_tag_table_cell_clicked)
        self.tag_metrics_table.setToolTip("Click a tag name to edit or delete it. Click a column header to sort. "
                                          "Use Select tag to choose several rows.")
        self.tag_metrics_table.itemSelectionChanged.connect(self._on_tag_table_selection_changed)
        self.tag_metrics_table.hide()

        self.tag_table_search = QLineEdit()
        self.tag_table_search.setPlaceholderText("Search tag names...")
        self.tag_table_search.setClearButtonEnabled(True)
        self.tag_table_search.textChanged.connect(self._apply_tag_table_filter)
        self.tag_table_search.hide()
        content_layout.addWidget(self.tag_table_search)

        header = self.tag_metrics_table.horizontalHeader()
        header.setSortIndicator(0, Qt.SortOrder.AscendingOrder)
        header.setSortIndicatorShown(True)
        header.sortIndicatorChanged.connect(lambda *_: QTimer.singleShot(0, self._apply_tag_table_filter))
        content_layout.addWidget(self.tag_metrics_table, 1)

        outer.addWidget(content, 1)

        self.tag_search.textChanged.connect(self._refresh_tag_cards)
        self._refresh_tag_cards()
        self._update_tag_toolbar_state()
        return page

    # ---------- one-time Live Data setup (called at the end of __init__) ----------
    def _init_live_extras(self):
        self.tag_no_batch = set()          # blocks the device rejected -> read tag by tag
        self._tag_save_timer = QTimer(self)
        self._tag_save_timer.setSingleShot(True)
        self._tag_save_timer.setInterval(600)
        self._tag_save_timer.timeout.connect(lambda: self._save_tag_config(False))

        # Debounce the search box so typing does not relayout the grid on every key.
        self._tag_search_timer = QTimer(self)
        self._tag_search_timer.setSingleShot(True)
        self._tag_search_timer.setInterval(150)
        self._tag_search_timer.timeout.connect(lambda: self._refresh_tag_cards(self.tag_search.text()))
        try:
            self.tag_search.textChanged.disconnect(self._refresh_tag_cards)
        except (TypeError, RuntimeError):
            pass
        self.tag_search.textChanged.connect(lambda *_: self._tag_search_timer.start())
        self.tag_filter_combo.currentIndexChanged.connect(
            lambda *_: self._refresh_tag_cards(self.tag_search.text()))

        # Small performance read-out under the sidebar status text.
        self.tag_stats_label = QLabel("Live: idle")
        self.tag_stats_label.setObjectName("smallNote")
        self.tag_stats_label.setWordWrap(True)
        layout = self.tag_selection_status.parentWidget().layout()
        if layout is not None:
            layout.insertWidget(layout.indexOf(self.tag_selection_status) + 1, self.tag_stats_label)

        self._tag_live_timer.setInterval(int(self.live_scan_spin.value()))
        self.tabs.currentChanged.connect(lambda *_: QTimer.singleShot(0, self._poll_live_tag_values))
        self.live_format_combo.currentTextChanged.connect(lambda *_: self._update_tag_card_values())
        self._load_tag_config(startup=True)

    # ---------- keyboard shortcuts ----------
    def _setup_shortcuts(self):
        bindings = [
            ("Ctrl+Z", self._shortcut_undo),
            ("Ctrl+Y", self._shortcut_redo),
            ("Ctrl+Shift+Z", self._shortcut_redo),
            ("Delete", self._shortcut_delete),
        ]
        self._shortcuts = []
        for sequence, handler in bindings:
            shortcut = QShortcut(QKeySequence(sequence), self)
            shortcut.setContext(Qt.ShortcutContext.WindowShortcut)
            shortcut.activated.connect(handler)
            self._shortcuts.append(shortcut)

    def _shortcuts_active(self):
        """The Live Data tab is on screen and the user is not typing in an input field."""
        if not self._live_tab_active():
            return False
        focus = QApplication.focusWidget()
        return not isinstance(focus, (QLineEdit, QAbstractSpinBox, QPlainTextEdit))

    def _shortcut_undo(self):
        if self._shortcuts_active():
            self._undo_tag_delete()

    def _shortcut_redo(self):
        if self._shortcuts_active():
            self._redo_tag_delete()

    def _shortcut_delete(self):
        if self._shortcuts_active() and self.tag_selection_mode:
            self._delete_selected_tags()

    # ---------- Live Data helpers ----------
    @staticmethod
    def _tag_is_editable(cfg):
        """Only FC5/FC6 tags whose access is Write or Read/Write may be edited."""
        return (bool(cfg)
                and str(cfg.get("function_code")) in ("5", "6")
                and cfg.get("access") in ("Write", "Read/Write"))

    def _format_tag_value(self, cfg, value):
        try:
            number = int(value)
        except (TypeError, ValueError):
            return str(value)
        if str(cfg.get("function_code")) in ("1", "2", "5"):
            return str(number)
        combo = getattr(self, "live_format_combo", None)
        fmt = combo.currentText() if combo is not None else "Decimal"
        return str(format_value(number, "3", "Raw register value", fmt))

    def _live_tab_active(self):
        tabs = getattr(self, "tabs", None)
        return tabs is not None and tabs.tabText(tabs.currentIndex()) == "Live Data"

    def _tag_configs_changed(self):
        """Call after any add/edit/delete: forget batching hints and schedule an auto-save."""
        if hasattr(self, "tag_no_batch"):
            self.tag_no_batch.clear()
        timer = getattr(self, "_tag_save_timer", None)
        if timer is not None:
            timer.start()

    def _tag_state(self, tag_id):
        """unconfigured | error | ok | pending"""
        if not self.tag_configurations.get(tag_id):
            return "unconfigured"
        if self.tag_errors.get(tag_id):
            return "error"
        if self.tag_live_values.get(tag_id) is not None:
            return "ok"
        return "pending"

    def _passes_filter(self, tag_id, mode):
        if mode in (None, "all"):
            return True
        state = self._tag_state(tag_id)
        if mode == "configured":
            return state != "unconfigured"
        if mode == "unconfigured":
            return state == "unconfigured"
        return state == mode          # "ok" | "error"

    def _filter_mode(self):
        combo = getattr(self, "tag_filter_combo", None)
        return combo.currentData() if combo is not None else "all"

    # ---------- save / load tag configuration ----------
    def _save_tag_config(self, show=True):
        try:
            save_tag_file(TAG_CONFIG_FILE, self.live_tags, self.tag_configurations)
        except Exception as exc:  # noqa: BLE001
            self.tag_selection_status.setText(f"Could not save tag configuration: {exc}")
            return
        if show:
            configured = len(self.tag_configurations)
            self.tag_selection_status.setText(
                f"Saved {len(self.live_tags)} tag(s) ({configured} configured) to {TAG_CONFIG_FILE.name}. "
                "Card order is saved too.")

    def _load_tag_config(self, startup=False, path=None):
        path = Path(path) if path else TAG_CONFIG_FILE
        if not path.exists():
            if not startup:
                self.tag_selection_status.setText(f"File not found: {path.name}")
            return
        try:
            tags, configs = load_tag_file(path)
        except Exception as exc:  # noqa: BLE001
            self.tag_selection_status.setText(f"Could not load {path.name}: {exc}")
            return
        shared_device = int(self.live_device_spin.value())
        for cfg in configs.values():
            cfg["device_address"] = shared_device   # tags always follow the shared device address
        dropped = dedupe_tag_addresses(tags, configs)   # an address belongs to one tag only
        self.live_tags = tags
        self.tag_configurations = configs
        self.tag_live_values.clear()
        self.tag_errors.clear()
        self.selected_tag_ids.clear()
        self.tag_no_batch.clear()
        self.tag_undo_stack.clear()      # an imported file must not mix with old undo history
        self.tag_redo_stack.clear()
        self._refresh_tag_cards(self.tag_search.text())
        self._edit_tag_placeholder_refresh_table()
        self._update_tag_toolbar_state()
        note = (f" {len(dropped)} tag(s) repeated an address already used by another tag and were left unconfigured."
                if dropped else "")
        self.tag_selection_status.setText(
            f"Loaded {len(tags)} tag(s) ({len(configs)} configured) from {path.name}.{note}")
        QTimer.singleShot(0, self._poll_live_tag_values)

    def _save_configuration_placeholder(self):
        self._save_tag_config(True)

    # ---------- upload tag table (Excel / Word / CSV) ----------
    _UPLOAD_FORMAT_NOTES = {
        "xlsx": ("Excel (.xlsx / .xlsm)",
                 "Every sheet is scanned. Put the header row in the first 30 rows of a sheet; "
                 "one tag per row below it. Cell values (not formulas) are read."),
        "docx": ("Word (.docx)",
                 "The tags must be in a <b>table</b> (first row = header). Every table in the "
                 "document is scanned. Text outside tables is ignored."),
        "csv": ("CSV (.csv / .txt)",
                "First row = header. Comma, semicolon, tab or | separators are detected "
                "automatically. UTF-8 or Windows-1252 encoding."),
    }

    def _show_upload_format_guide(self, fmt):
        """Tell the user what the tag file must contain. Returns True to continue."""
        title, where = self._UPLOAD_FORMAT_NOTES[fmt]
        text = (
            f"<b>{title}: what the file must contain</b><br><br>"
            f"{where}<br><br>"
            "<b>Required columns</b> (header names are not case-sensitive):"
            "<ul>"
            "<li><b>Address</b> &ndash; Modbus address, whole number 1&ndash;65536 "
            "(also accepts: Addr, Register, Register Address)</li>"
            "<li><b>Tag name</b> &ndash; text (also: Name, Parameter, Signal, Point)</li>"
            "<li><b>Function code</b> &ndash; 1&ndash;6, <i>FC03</i>, or a name such as "
            "<i>Read Holding Registers</i> (also: FC, Function)</li>"
            "</ul>"
            "<b>Optional columns</b>:"
            "<ul>"
            "<li><b>Device address</b> &ndash; 1&ndash;247 (also: Slave ID, Unit ID). "
            "The first valid value becomes the shared device address.</li>"
            "<li><b>Access</b> &ndash; Read, Write or Read/Write (also R, W, RW). "
            "Write access only takes effect for FC05 / FC06.</li>"
            "</ul>"
            "<b>Function codes</b>: 1 = Read Coils, 2 = Read Discrete Inputs, "
            "3 = Read Holding Registers, 4 = Read Input Registers, "
            "5 = Write Single Coil, 6 = Write Single Register.<br><br>"
            "<b>Blank cells get defaults</b>: tag name &rarr; &quot;Unknown tag N&quot;, "
            "function code &rarr; FC03, address &rarr; next free address, "
            "access &rarr; Read (Read/Write for FC05/FC06).<br><br>"
            "<b>Note</b>: an address can belong to one tag only. If an address is repeated, "
            "the later tag is added without a configuration.<br><br>"
            "<b>Example</b>:<br>"
            "<table border='1' cellspacing='0' cellpadding='3'>"
            "<tr><th>Address</th><th>Tag name</th><th>Function code</th>"
            "<th>Device address</th><th>Access</th></tr>"
            "<tr><td>1</td><td>Reset alarm</td><td>6</td><td>1</td><td>Read/Write</td></tr>"
            "<tr><td>36</td><td>CH1 reading</td><td>3</td><td>1</td><td>Read</td></tr>"
            "</table>"
        )
        box = QMessageBox(self)
        box.setIcon(QMessageBox.Icon.Information)
        box.setWindowTitle("Upload files - required format")
        box.setTextFormat(Qt.TextFormat.RichText)
        box.setText(text)
        choose = box.addButton("Choose file...", QMessageBox.ButtonRole.AcceptRole)
        box.addButton(QMessageBox.StandardButton.Cancel)
        box.setDefaultButton(choose)
        box.exec()
        return box.clickedButton() is choose

    def _upload_tag_file(self, fmt):
        """Upload files > Excel / Word / CSV: scan the file and map it into the tag table."""
        file_filter, label = {
            "xlsx": ("Excel workbook (*.xlsx *.xlsm)", "Excel"),
            "docx": ("Word document (*.docx)", "Word"),
            "csv": ("CSV file (*.csv *.txt)", "CSV"),
        }[fmt]
        # Show what the file must contain before the file picker opens.
        if not self._show_upload_format_guide(fmt):
            self.tag_selection_status.setText("Upload cancelled.")
            return
        filename, _f = QFileDialog.getOpenFileName(
            self, f"Upload {label} tag file", str(APP_DIR), file_filter)
        if not filename:
            return
        path = Path(filename)
        try:
            records, _columns = extract_tag_records(read_tag_file_tables(path, fmt))
        except TagFileError as exc:
            self.tag_selection_status.setText(f"Upload failed: {str(exc).splitlines()[0]}")
            QMessageBox.warning(self, "Upload files", str(exc))
            return
        except Exception as exc:  # noqa: BLE001
            self.tag_selection_status.setText(f"Upload failed: {exc}")
            QMessageBox.warning(self, "Upload files",
                                f"Could not read {path.name}:\n{type(exc).__name__}: {exc}")
            return

        tags, configs, file_device, report = build_tag_set(records, int(self.live_device_spin.value()))
        if self.live_tags:
            answer = QMessageBox.question(
                self, "Upload files",
                f"Replace the {len(self.live_tags)} current tag(s) with the {len(tags)} tag(s) "
                f"found in {path.name}?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.Yes)
            if answer != QMessageBox.StandardButton.Yes:
                self.tag_selection_status.setText("Upload cancelled.")
                return
        self._apply_uploaded_tags(path.name, tags, configs, file_device, report)

    def _apply_uploaded_tags(self, file_name, tags, configs, file_device, report):
        # A device address in the file becomes the shared one: the spin box keeps the
        # Read Data, Write Data and Live Data device addresses identical.
        if file_device is not None and file_device != int(self.live_device_spin.value()):
            self.live_device_spin.setValue(file_device)
        shared_device = int(self.live_device_spin.value())
        for cfg in configs.values():
            cfg["device_address"] = shared_device

        self.live_tags = tags
        self.tag_configurations = configs
        self.tag_live_values.clear()
        self.tag_errors.clear()
        self.tag_no_batch.clear()
        self.selected_tag_ids.clear()
        self.tag_undo_stack.clear()          # undo history of the old tag set no longer applies
        self.tag_redo_stack.clear()
        self.tag_search.clear()
        self.tag_filter_combo.setCurrentIndex(0)
        self._refresh_tag_cards("")
        self._edit_tag_placeholder_refresh_table()
        self._update_tag_toolbar_state()
        self._tag_configs_changed()          # auto-saves the new set
        QTimer.singleShot(0, self._poll_live_tag_values)   # fetch the live values right away

        self.tag_selection_status.setText(
            f"Uploaded {len(tags)} tag(s) from {file_name}: {len(configs)} configured.")
        notes = []
        if file_device is not None:
            notes.append(f"Device address {file_device} from the file is now used in "
                         "Live Data, Read Data and Write Data.")
        if report["device_conflicts"]:
            notes.append(f"{report['device_conflicts']} row(s) named a different device address. "
                         f"The app uses one shared device address ({shared_device}), so they were ignored.")
        defaults = []
        if report["name"]:
            defaults.append(f"{report['name']} blank tag name(s) -> 'Unknown tag N'")
        if report["function"]:
            defaults.append(f"{report['function']} blank function code(s) -> FC03 (Read Holding Registers)")
        if report["address"]:
            defaults.append(f"{report['address']} blank address(es) -> next free address")
        if defaults:
            notes.append("Defaults used for blank cells: " + "; ".join(defaults) + ".")
        if report["duplicates"]:
            listed = ", ".join(f"'{name}' (address {address})" for name, address in report["duplicates"][:8])
            extra = len(report["duplicates"]) - 8
            notes.append("An address can belong to one tag only. These tags repeat an earlier "
                         "address and were added without a configuration: " + listed
                         + (f" and {extra} more." if extra > 0 else "."))
        if notes:
            QMessageBox.information(
                self, "Upload files",
                f"Uploaded {len(tags)} tag(s) from {file_name} ({len(configs)} configured).\n\n"
                + "\n\n".join(notes))

    # ---------- undo / redo / delete all / sort ----------
    def _update_tag_toolbar_state(self):
        self.undo_tag_button.setEnabled(bool(self.tag_undo_stack))
        self.redo_tag_button.setEnabled(bool(self.tag_redo_stack))
        self.delete_all_tags_button.setEnabled(bool(self.live_tags))

    def _after_tag_list_changed(self):
        self._refresh_tag_cards(self.tag_search.text())
        self._edit_tag_placeholder_refresh_table()
        self._tag_configs_changed()
        self._update_tag_toolbar_state()

    def _remove_tags(self, tag_ids, record=True):
        """Remove tags (and remember them for Undo). Returns the removed entries."""
        ids = set(tag_ids)
        removed = [(pos, tid, name, self.tag_configurations.get(tid))
                   for pos, (tid, name) in enumerate(self.live_tags) if tid in ids]
        if not removed:
            return []
        for _pos, tid, _name, _cfg in removed:
            self.tag_configurations.pop(tid, None)
            self.tag_live_values.pop(tid, None)
            self.tag_errors.pop(tid, None)
        self.live_tags = [(t, n) for t, n in self.live_tags if t not in ids]
        self.selected_tag_ids.difference_update(ids)
        if record:
            self.tag_undo_stack.append(removed)
            self.tag_redo_stack.clear()
        self._after_tag_list_changed()
        return removed

    def _delete_all_tags(self):
        if not self.live_tags:
            self.tag_selection_status.setText("There are no tags to delete.")
            return
        removed = self._remove_tags([tid for tid, _n in self.live_tags])
        self.tag_selection_status.setText(
            f"Deleted all {len(removed)} tag(s). Use Undo to restore them.")

    def _undo_tag_delete(self):
        if not self.tag_undo_stack:
            self.tag_selection_status.setText("Nothing to undo.")
            return
        removed = self.tag_undo_stack.pop()
        shared_device = int(self.live_device_spin.value())
        existing = {tid for tid, _n in self.live_tags}
        restored = 0
        unconfigured = 0
        for pos, tid, name, cfg in sorted(removed, key=lambda r: r[0]):
            if tid in existing:
                continue
            self.live_tags.insert(min(pos, len(self.live_tags)), (tid, name))
            existing.add(tid)
            if cfg:
                cfg = dict(cfg)
                cfg["device_address"] = shared_device
                if self._address_owner(cfg["address"]) is None:
                    self.tag_configurations[tid] = cfg
                else:
                    unconfigured += 1      # address was taken meanwhile: restore the name only
            restored += 1
        self.tag_redo_stack.append(removed)
        self._after_tag_list_changed()
        note = (f" {unconfigured} restored without its address (already used by another tag)."
                if unconfigured else "")
        self.tag_selection_status.setText(f"Undo: restored {restored} tag(s).{note}")
        QTimer.singleShot(0, self._poll_live_tag_values)

    def _redo_tag_delete(self):
        if not self.tag_redo_stack:
            self.tag_selection_status.setText("Nothing to redo.")
            return
        entry = self.tag_redo_stack.pop()
        removed = self._remove_tags([tid for _p, tid, _n, _c in entry], record=False)
        self.tag_undo_stack.append(removed or entry)
        self._update_tag_toolbar_state()
        self.tag_selection_status.setText(f"Redo: deleted {len(removed)} tag(s) again.")

    def _build_sort_menu(self):
        menu = QMenu(self.sort_tag_button)
        access_menu = menu.addMenu("Access")
        for access in _TAG_ACCESS:                      # Read, Write, Read/Write
            action = access_menu.addAction(access)
            action.triggered.connect(lambda _=False, a=access: self._set_tag_sort(("access", a)))
        function_menu = menu.addMenu("Function code")
        for code, label in TAG_FUNCTION_NAMES:
            action = function_menu.addAction(label)
            action.triggered.connect(lambda _=False, c=code: self._set_tag_sort(("function", c)))
        menu.addSeparator()
        none_action = menu.addAction("None")
        none_action.triggered.connect(lambda _=False: self._set_tag_sort(None))
        self.sort_tag_button.setMenu(menu)

    def _set_tag_sort(self, mode):
        self.tag_sort = mode
        if mode is None:
            self.sort_tag_button.setText("Sort")
            self.tag_selection_status.setText("Sorting removed. Original order restored.")
        else:
            kind, wanted = mode
            label = wanted if kind == "access" else f"FC{int(wanted):02d}"
            self.sort_tag_button.setText(f"Sort: {label}")
            self.tag_selection_status.setText(
                f"Showing only tags matching {'access permission' if kind == 'access' else 'function code'}: "
                f"{label}. Choose Sort → None to show all tags.")
        self._refresh_tag_cards(self.tag_search.text())
        self._edit_tag_placeholder_refresh_table()      # the Edit-tag table follows the same Sort

    def _sorted_live_tags(self):
        """Filter Live Data cards / table rows to the selected access or function code.

        Access filters are exact matches: Read shows only Read, Write only Write,
        and Read/Write only Read/Write. Function-code filters show only tags configured
        with that exact function code. Unconfigured tags are excluded whenever a
        sort/filter choice is active.
        """
        mode = self.tag_sort
        if not mode:
            return list(self.live_tags)

        kind, wanted = mode
        filtered = []
        for item in self.live_tags:
            cfg = self.tag_configurations.get(item[0])
            if not cfg:
                continue
            if kind == "access":
                access = cfg.get("access", "Read")
                # Access selection must match the configured permission exactly.
                # Do not include dual-access tags when Read or Write alone is selected.
                matches = access == wanted
            else:
                matches = str(cfg.get("function_code")) == str(wanted)
            if matches:
                filtered.append(item)
        return filtered

    # ---------- add / edit table ----------
    def _add_unknown_tag(self):
        # Add a placeholder card to this Live Data view only. IDs of deleted tags are not
        # reused while they can still be restored with Undo / Redo.
        known_ids = [t for t, _n in self.live_tags] + \
                    [tid for entry in (self.tag_undo_stack + self.tag_redo_stack) for _p, tid, _n, _c in entry]
        next_tag_id = max(known_ids, default=0) + 1
        self.live_tags.append((next_tag_id, "Unknown tag"))
        self.tag_search.clear()
        self._refresh_tag_cards("")
        self._edit_tag_placeholder_refresh_table()
        self._tag_configs_changed()
        self._update_tag_toolbar_state()
        self.tag_selection_status.setText(f"Added Unknown tag (TAG {next_tag_id:02d}).")

    def _edit_tag_placeholder(self):
        # Toggle the main Live Data workspace to the tag table (click a tag name to edit it).
        if self.tag_metrics_table.isVisible():
            self.tag_metrics_table.hide()
            self.tag_table_search.hide()
            self.tag_scroll.show()
            self.tag_filter_row.show()
            self.tag_toolbar.show()
            self._sync_card_checks()             # selection made in the table shows on the cards
            self.edit_tag_button.setText("Edit tag")
            self.tag_selection_status.setText("Showing Live Data metric cards.")
            return
        self._fill_tag_metrics_table()
        self.tag_scroll.hide()
        self.tag_filter_row.hide()
        self.tag_toolbar.hide()
        self.tag_table_search.show()
        self.tag_metrics_table.show()
        self.edit_tag_button.setText("Back to Live Data")
        self.tag_selection_status.setText(
            f"Showing {len(self._table_tag_ids)} of {len(self.live_tags)} tags. "
            "Click a tag name to edit or delete it, or use Select tag to choose several rows.")

    _TAG_TABLE_HEADERS = ["Index No.", "Tag Name", "Device", "Function code", "Address", "Access", "Value"]

    def _fill_tag_metrics_table(self):
        table = self.tag_metrics_table
        header = table.horizontalHeader()
        shown = list(self.live_tags)                 # the table always lists every tag
        position = {tid: index for index, (tid, _n) in enumerate(self.live_tags, start=1)}
        self._table_tag_ids = [tid for tid, _n in shown]
        self._table_filling = True                  # keep the selection signal quiet while rebuilding
        table.setUpdatesEnabled(False)
        try:
            table.setSortingEnabled(False)          # never insert while sorting is active
            table.setColumnCount(len(self._TAG_TABLE_HEADERS))
            table.setHorizontalHeaderLabels(self._TAG_TABLE_HEADERS)
            table.setRowCount(len(shown))
            for row, (tag_id, tag_name) in enumerate(shown):
                cfg = self.tag_configurations.get(tag_id)
                cells = [
                    str(position[tag_id]),
                    tag_name,
                    str(cfg["device_address"]) if cfg else "—",
                    f"FC{int(cfg['function_code']):02d}" if cfg else "—",
                    str(cfg["address"]) if cfg else "—",
                    str(cfg["access"]) if cfg else "—",
                    self._tag_value_text(tag_id),
                ]
                for col, text in enumerate(cells):
                    item = SortItem(text, row)
                    if col == 1:
                        item.setData(Qt.ItemDataRole.UserRole, tag_id)   # survives sorting
                        item.setToolTip("Click to edit this tag configuration")
                    table.setItem(row, col, item)
            header.setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
            header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
            header.setSortIndicatorShown(True)
            table.setSortingEnabled(True)           # re-applies the header's current sort
        finally:
            table.setUpdatesEnabled(True)
            self._table_filling = False
        self._apply_tag_table_filter()
        self._restore_table_selection()

    def _tag_value_text(self, tag_id):
        cfg = self.tag_configurations.get(tag_id)
        value = self.tag_live_values.get(tag_id)
        if not cfg or value is None:
            return "—"
        return self._format_tag_value(cfg, value)

    def _update_tag_table_values(self):
        table = self.tag_metrics_table
        if not table.isVisible() or table.rowCount() != len(self._table_tag_ids):
            return
        pending = []
        for row in range(table.rowCount()):
            name_item, value_item = table.item(row, 1), table.item(row, 6)
            if name_item is None or value_item is None:
                continue
            text = self._tag_value_text(name_item.data(Qt.ItemDataRole.UserRole))
            if value_item.text() != text:
                pending.append((value_item, text))
        if not pending:
            return
        table.setSortingEnabled(False)
        for item, text in pending:
            item.setText(text)
        table.setSortingEnabled(True)
        self._apply_tag_table_filter()

    def _on_tag_table_cell_clicked(self, row, column):
        # Selecting the Tag Name cell opens settings for that particular tag.
        if column != 1 or self.tag_selection_mode:   # in selection mode a click only selects the row
            return
        item = self.tag_metrics_table.item(row, 1)
        if item is None:
            return
        tag_id = item.data(Qt.ItemDataRole.UserRole)   # row numbers change when the table is sorted
        name = next((n for t, n in self.live_tags if t == tag_id), None)
        if name is not None:
            self._edit_one_tag(tag_id, name)

    def _apply_tag_table_filter(self, *_):
        table = self.tag_metrics_table
        box = getattr(self, "tag_table_search", None)
        query = box.text().strip().casefold() if box is not None else ""
        for row in range(table.rowCount()):
            item = table.item(row, 1)
            hide = bool(query) and (item is None or query not in item.text().casefold())
            table.setRowHidden(row, hide)

    def _address_owner(self, address, exclude_id=None):
        """Name of the tag that already uses this address, or None when the address is free."""
        names = dict(self.live_tags)
        for tid, cfg in self.tag_configurations.items():
            if tid == exclude_id or tid not in names or not cfg:
                continue
            if int(cfg["address"]) == int(address):
                return names[tid]
        return None

    def _next_free_address(self, exclude_id=None):
        names = dict(self.live_tags)
        used = {int(cfg["address"]) for tid, cfg in self.tag_configurations.items()
                if tid != exclude_id and tid in names and cfg}
        candidate = 1
        while candidate in used and candidate < 65536:
            candidate += 1
        return candidate

    def _edit_one_tag(self, tag_id, tag_name):
        old_config = dict(self.tag_configurations.get(tag_id, {}))
        dialog = QDialog(self)
        dialog.setWindowTitle(f"Edit tag: {tag_name}")
        dialog.setMinimumWidth(430)
        form = QFormLayout(dialog)

        # Read-only: always the shared device address (Live Data / Read Data / Write Data).
        shared_device = int(self.live_device_spin.value())
        device = QSpinBox()
        device.setRange(1, 247)
        device.setValue(shared_device)
        device.setEnabled(False)
        device.setToolTip("Synchronized with the Device address in Live Data, Read Data and "
                          "Write Data. Change it there.")
        form.addRow("Device address", device)

        function = QComboBox()
        for label, code in [
            ("Function code 1 - Read Coils", "1"),
            ("Function code 2 - Read Discrete Inputs", "2"),
            ("Function code 3 - Read Holding Registers", "3"),
            ("Function code 4 - Read Input Registers", "4"),
            ("Function code 5 - Write Single Coil", "5"),
            ("Function code 6 - Write Single Holding Register", "6"),
        ]:
            function.addItem(label, code)
        idx = function.findData(str(old_config.get("function_code", "3")))
        function.setCurrentIndex(idx if idx >= 0 else 2)
        form.addRow("Function code", function)

        # A new tag starts on the first address no other tag uses.
        address = QSpinBox()
        address.setRange(1, 65536)
        address.setValue(clamp_int(old_config["address"], 1, 65536, 1) if old_config.get("address")
                         else self._next_free_address(tag_id))
        form.addRow("Address", address)

        access = QComboBox()
        form.addRow("Access", access)

        def update_access_options(*_args):
            code = str(function.currentData())
            previous = access.currentText() or str(old_config.get("access", "Read"))
            access.blockSignals(True)
            access.clear()
            if code in ("1", "2", "3", "4"):
                access.addItem("Read")          # FC1-4 are always read-only
            else:
                access.addItems(["Read", "Write", "Read/Write"])
                access.setCurrentText(previous if previous in ("Read", "Write", "Read/Write") else "Read")
            access.blockSignals(False)

        function.currentIndexChanged.connect(update_access_options)
        update_access_options()

        name = QLineEdit(tag_name)
        form.addRow("Tag name", name)

        conflict_label = QLabel("")
        conflict_label.setWordWrap(True)
        conflict_label.setStyleSheet("color: #a93226; font-size: 12px;")
        conflict_label.setVisible(False)
        form.addRow(conflict_label)

        save_button = QPushButton("Save")
        save_button.setDefault(True)
        cancel_button = QPushButton("Cancel")
        delete_button = QPushButton("Delete")
        delete_button.setToolTip("Delete this tag (same as Delete tag). Ctrl+Z restores it.")
        delete_button.setStyleSheet(
            "QPushButton { color: #a93226; }"
            "QPushButton:hover { color: #a93226; border-color: #c0392b; background: #fdecea; }")
        button_row = QHBoxLayout()
        button_row.addStretch(1)
        for button in (save_button, cancel_button, delete_button):
            button_row.addWidget(button)
        form.addRow(button_row)

        def refresh_conflict(*_args):
            # Address is a primary key: one address can belong to one tag only.
            owner = self._address_owner(address.value(), tag_id)
            if owner is None:
                conflict_label.setVisible(False)
                save_button.setEnabled(True)
            else:
                conflict_label.setText(
                    f"Address {address.value()} is already used by '{owner}'. "
                    "Each address can belong to only one tag.")
                conflict_label.setVisible(True)
                save_button.setEnabled(False)

        deleted = []

        def on_save():
            refresh_conflict()
            if save_button.isEnabled():
                dialog.accept()

        def on_delete():
            deleted.append(True)
            dialog.reject()

        address.valueChanged.connect(refresh_conflict)
        save_button.clicked.connect(on_save)
        cancel_button.clicked.connect(dialog.reject)
        delete_button.clicked.connect(on_delete)
        refresh_conflict()

        result = dialog.exec()
        if deleted:                                   # same as the Delete tag button
            self._remove_tags([tag_id])
            self.tag_selection_status.setText(
                f"Deleted tag '{tag_name}'. Press Ctrl+Z (Undo) to restore it.")
            return
        if result != QDialog.DialogCode.Accepted:
            return
        new_name = name.text().strip()
        if not new_name:
            self.tag_selection_status.setText("Tag name cannot be empty.")
            return
        owner = self._address_owner(address.value(), tag_id)
        if owner is not None:                         # the dialog already blocks this
            self.tag_selection_status.setText(
                f"Address {address.value()} is already used by '{owner}'. Nothing was saved.")
            return

        new_config = {
            "device_address": shared_device,
            "function_code": str(function.currentData()),
            "address": address.value(),
            "access": access.currentText(),
            "tag_name": new_name,
        }
        compare_keys = ("device_address", "function_code", "address")
        if any(old_config.get(k) != new_config[k] for k in compare_keys):
            self.tag_live_values.pop(tag_id, None)   # old reading no longer applies
            self.tag_errors.pop(tag_id, None)
        self.tag_configurations[tag_id] = new_config
        self.live_tags = [(tid, new_name if tid == tag_id else tname) for tid, tname in self.live_tags]
        self._refresh_tag_cards(self.tag_search.text())
        self._edit_tag_placeholder_refresh_table()
        self._tag_configs_changed()
        self.tag_selection_status.setText(f"Saved configuration for '{new_name}'.")
        QTimer.singleShot(0, self._poll_live_tag_values)   # show its value right away

    def _edit_tag_placeholder_refresh_table(self):
        if self.tag_metrics_table.isVisible():
            self._fill_tag_metrics_table()

    # ---------- selection / delete (cards and Edit-tag table rows) ----------
    def _selected_visible_ids(self):
        """Selected tags that are currently shown (search / filter never deletes hidden ones)."""
        table = self.tag_metrics_table
        if table.isVisible():                       # Edit-tag table: visible rows only
            ids = []
            for row in range(table.rowCount()):
                if table.isRowHidden(row):
                    continue
                item = table.item(row, 1)
                tag_id = item.data(Qt.ItemDataRole.UserRole) if item is not None else None
                if tag_id in self.selected_tag_ids:
                    ids.append(tag_id)
            return ids
        return [tid for tid in self._shown_tag_ids if tid in self.selected_tag_ids]

    def _sync_card_checks(self):
        for tag_id, card in self.tag_cards.items():
            card.setCheckable(self.tag_selection_mode)
            card.setChecked(self.tag_selection_mode and tag_id in self.selected_tag_ids)

    def _set_selection_mode(self, on):
        on = bool(on)
        self.tag_selection_mode = on
        if not on:
            self.selected_tag_ids.clear()
        self.select_tag_button.setChecked(on)
        self.select_tag_button.setText("Cancel selection" if on else "Select tag")
        table = self.tag_metrics_table
        self._table_filling = True              # do not treat the reset below as a user selection
        try:
            table.clearSelection()
            table.setSelectionMode(QAbstractItemView.SelectionMode.MultiSelection if on
                                   else QAbstractItemView.SelectionMode.ExtendedSelection)
        finally:
            self._table_filling = False
        # Cards are reused: just flip their checkable/checked state, no rebuild.
        self._sync_card_checks()

    def _toggle_tag_selection(self, checked):
        self._set_selection_mode(checked)
        self.tag_selection_status.setText(
            "Click cards (or table rows) to select tags." if self.tag_selection_mode
            else "Selection mode is off.")

    def _on_tag_card_clicked(self, tag_id, checked):
        if not self.tag_selection_mode:
            return
        if checked:
            self.selected_tag_ids.add(tag_id)
        else:
            self.selected_tag_ids.discard(tag_id)
        self.tag_selection_status.setText(f"{len(self._selected_visible_ids())} tag(s) selected.")

    def _on_tag_table_selection_changed(self):
        if self._table_filling or not self.tag_selection_mode:
            return
        table = self.tag_metrics_table
        ids = set()
        for index in table.selectionModel().selectedRows():
            item = table.item(index.row(), 1)
            if item is not None:
                ids.add(item.data(Qt.ItemDataRole.UserRole))
        self.selected_tag_ids = ids
        self.tag_selection_status.setText(f"{len(self._selected_visible_ids())} tag(s) selected.")

    def _restore_table_selection(self):
        """Re-select the rows of self.selected_tag_ids after the table was rebuilt."""
        if not self.tag_selection_mode or not self.selected_tag_ids:
            return
        table = self.tag_metrics_table
        model, selection = table.model(), table.selectionModel()
        flags = QItemSelectionModel.SelectionFlag.Select | QItemSelectionModel.SelectionFlag.Rows
        self._table_filling = True
        try:
            for row in range(table.rowCount()):
                item = table.item(row, 1)
                if item is not None and item.data(Qt.ItemDataRole.UserRole) in self.selected_tag_ids:
                    selection.select(model.index(row, 0), flags)
        finally:
            self._table_filling = False

    def _delete_selected_tags(self):
        ids = self._selected_visible_ids()
        if not ids:
            self.tag_selection_status.setText(
                "Select one or more tags first: click Select tag, then click cards (or table rows).")
            return
        removed = self._remove_tags(ids)
        self.tag_selection_status.setText(
            f"Deleted {len(removed)} tag(s). Use Undo (Ctrl+Z) to restore.")

    # ---------- drag-and-drop re-ordering ----------
    def _on_tag_dropped(self, source_id, target_id):
        if source_id == target_id:
            return
        if self.tag_sort:
            self.tag_selection_status.setText(
                "Set Sort to 'None' to re-order cards by drag and drop.")
            return
        ids = [t for t, _n in self.live_tags]
        if source_id not in ids or target_id not in ids:
            return
        source_index, target_index = ids.index(source_id), ids.index(target_id)
        item = self.live_tags.pop(source_index)
        self.live_tags.insert(target_index, item)
        self._refresh_tag_cards(self.tag_search.text())
        self._edit_tag_placeholder_refresh_table()
        self._tag_configs_changed()            # auto-saves the new order to the configuration file
        self.tag_selection_status.setText(f"Moved '{item[1]}' to position {target_index + 1} (order saved).")

    # ---------- card click -> write ----------
    def _on_live_card_clicked(self, tag_id, checked=False):
        if self.tag_selection_mode:
            self._on_tag_card_clicked(tag_id, checked)
            return
        cfg = self.tag_configurations.get(tag_id)
        name = next((n for t, n in self.live_tags if t == tag_id), "tag")
        if not cfg:
            self.tag_selection_status.setText(
                f"'{name}' is not configured. Use Edit tag, then click its tag name.")
            return
        if self._tag_is_editable(cfg):
            self._edit_live_tag_value(tag_id)
        else:
            self.tag_selection_status.setText(
                f"'{name}' is read-only (FC{int(cfg['function_code']):02d}, access {cfg['access']}).")

    def _edit_live_tag_value(self, tag_id):
        cfg = dict(self.tag_configurations.get(tag_id, {}))
        if not self._tag_is_editable(cfg):
            return
        if self._tag_write_busy:
            self.tag_selection_status.setText("A tag write is already in progress.")
            return
        ok, msg = self.connection_guard()
        if not ok:
            self.tag_selection_status.setText(
                "Connect to the Modbus device before writing a tag value."
                if msg == "Not connected" else msg)
            return

        is_coil = str(cfg["function_code"]) == "5"
        tag_name = cfg.get("tag_name", "tag")
        dialog = QDialog(self)
        dialog.setWindowTitle(f"Write value — {tag_name}")
        dialog.setMinimumWidth(320)
        form = QFormLayout(dialog)
        try:
            current = int(self.tag_live_values.get(tag_id, 0))
        except (TypeError, ValueError):
            current = 0
        if is_coil:
            editor = QComboBox()
            editor.addItem("0  (OFF)", 0)
            editor.addItem("1  (ON)", 1)
            editor.setCurrentIndex(1 if current else 0)
            get_value = lambda: int(editor.currentData())  # noqa: E731
        else:
            editor = QSpinBox()
            editor.setRange(0, 65535)
            editor.setValue(max(0, min(65535, current)))
            get_value = lambda: int(editor.value())  # noqa: E731
        form.addRow("Value", editor)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        form.addRow(buttons)
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return

        new_value = get_value()
        client = self.client
        self._tag_write_busy = True
        self.tag_selection_status.setText(f"Writing {new_value} to '{tag_name}'...")

        def job():
            return write_tag_value(client, cfg, new_value)

        def done(ok_flag, result):
            self._tag_write_busy = False
            if ok_flag:
                self.tag_live_values[tag_id] = result
                self.tag_errors.pop(tag_id, None)
                self._update_tag_card_values({tag_id})
                RT.set_write_status(f"Tag write OK — {tag_name} = {result}")
                self.tag_selection_status.setText(f"Wrote {new_value} to '{tag_name}' (device now reads {result}).")
            else:
                RT.set_write_status(f"Tag write failed — {tag_name}")
                self.tag_selection_status.setText(f"Tag write failed: {result}")

        self.runner.run(job, done)

    # ---------- live polling of configured tags (batched) ----------
    def _poll_live_tag_values(self):
        if self._tag_poll_busy:
            return
        if not self.connected or self.client is None:
            # Disconnected: stop showing stale readings.
            if self.tag_live_values or self.tag_errors:
                self.tag_live_values.clear()
                self.tag_errors.clear()
                self._update_tag_card_values()
                if self._filter_mode() in ("ok", "error"):
                    self._refresh_tag_cards(self.tag_search.text())
            return
        # Only talk to the device for live values while the Live Data tab is visible.
        if not self._live_tab_active():
            return
        ok, _msg = self.connection_guard()
        if not ok or self._tag_write_busy:
            return
        visible = {tag_id for tag_id, _name in self.live_tags}
        jobs = [(tid, dict(cfg)) for tid, cfg in self.tag_configurations.items()
                if tid in visible and str(cfg.get("function_code")) in _TAG_READ_KIND]
        if not jobs:
            return

        client = self.client
        snapshots = dict(jobs)
        blocks = group_tag_reads(jobs)
        no_batch = self.tag_no_batch
        self._tag_poll_busy = True

        def device_replied(exc):
            """True when the device answered with a Modbus exception (the bus itself works)."""
            return "Modbus exception" in str(exc)

        def single_reads(tids, results, stats):
            """Read tags one by one. Returns an error text when the device stopped answering."""
            for index, (tid, _addr) in enumerate(tids):
                stats["requests"] += 1
                with RT.lock:
                    RT.polls += 1
                try:
                    results[tid] = ("ok", read_tag_value(client, snapshots[tid]))
                    RT.bump_valid()
                except Exception as exc:  # noqa: BLE001
                    message = f"{type(exc).__name__}: {exc}"
                    results[tid] = ("err", message)
                    if not device_replied(exc):
                        # No answer at all: do not wait one time-out per remaining tag.
                        for rest, _a in tids[index + 1:]:
                            results[rest] = ("err", message)
                        return message
            return None

        def job():
            started = time.monotonic()
            results, stats = {}, {"requests": 0}
            dead = None   # set once the device stops answering; the rest of the cycle is skipped
            for block in blocks:
                if dead is not None:
                    for tid, _addr in block["tids"]:
                        results[tid] = ("err", dead)
                    continue
                key = (block["device"], block["kind"], block["start"], block["end"])
                if len(block["tids"]) == 1 or key in no_batch:
                    dead = single_reads(block["tids"], results, stats) or dead
                    continue
                stats["requests"] += 1
                with RT.lock:
                    RT.polls += 1
                try:
                    values = read_tag_block(client, block)
                except Exception as exc:  # noqa: BLE001
                    unique = len({addr for _tid, addr in block["tids"]})
                    if device_replied(exc) and block["end"] - block["start"] + 1 > unique:
                        # The device rejected a block that spans addresses nobody asked for.
                        # Remember that and read these tags one by one from now on. (A mere
                        # time-out does NOT disable batching.)
                        no_batch.add(key)
                        dead = single_reads(block["tids"], results, stats) or dead
                    else:
                        message = f"{type(exc).__name__}: {exc}"
                        for tid, _addr in block["tids"]:
                            results[tid] = ("err", message)
                        if not device_replied(exc):
                            dead = message
                    continue
                RT.bump_valid()
                for tid, addr in block["tids"]:
                    if addr in values:
                        results[tid] = ("ok", values[addr])
                    else:
                        results[tid] = ("err", "No value returned")
            if any(state == "ok" for state, _p in results.values()):
                with RT.lock:
                    RT.last_update = datetime.now().strftime("%H:%M:%S")
            stats["ms"] = int((time.monotonic() - started) * 1000)
            stats["tags"] = len(jobs)
            return results, stats

        def done(ok_flag, result):
            self._tag_poll_busy = False
            if not ok_flag or self.client is not client:
                return
            results, stats = result
            changed = set()
            for tid, (state, payload) in results.items():
                if self.tag_configurations.get(tid) != snapshots.get(tid):
                    continue  # tag was re-configured while reading
                if state == "ok":
                    if self.tag_live_values.get(tid) != payload or tid in self.tag_errors:
                        changed.add(tid)
                    self.tag_live_values[tid] = payload
                    self.tag_errors.pop(tid, None)
                else:
                    if tid in self.tag_live_values or self.tag_errors.get(tid) != payload:
                        changed.add(tid)
                    self.tag_live_values.pop(tid, None)
                    self.tag_errors[tid] = payload
            if changed:
                self._update_tag_card_values(changed)
                if self._filter_mode() in ("ok", "error"):
                    self._refresh_tag_cards(self.tag_search.text())   # state filter may now match differently
            text = (f"Live: {stats['tags']} tag(s) · {stats['requests']} request(s) · "
                    f"{stats['ms']} ms")
            if self.tag_stats_label.text() != text:
                self.tag_stats_label.setText(text)

        self.runner.run(job, done)

    # ---------- download table ----------
    def _download_tag_table(self, fmt):
        self._fill_tag_metrics_table()                 # make sure the table is current
        table = self.tag_metrics_table
        headers = list(self._TAG_TABLE_HEADERS)
        rows = []
        for r in range(table.rowCount()):              # visible rows, in the order shown
            if table.isRowHidden(r):
                continue
            rows.append([table.item(r, c).text() if table.item(r, c) else ""
                         for c in range(len(headers))])
        if not rows:
            self.tag_selection_status.setText("No tag data to download.")
            return
        ext, kind = {"csv": (".csv", "CSV file (*.csv)"),
                     "xlsx": (".xlsx", "Excel workbook (*.xlsx)"),
                     "docx": (".docx", "Word document (*.docx)")}[fmt]
        default = str(APP_DIR / f"live_data_tags_{datetime.now():%Y%m%d_%H%M%S}{ext}")
        filename, _f = QFileDialog.getSaveFileName(self, "Download tag table", default, kind)
        if not filename:
            return
        if not filename.lower().endswith(ext):
            filename += ext
        try:
            if fmt == "csv":
                with open(filename, "w", newline="", encoding="utf-8-sig") as fh:
                    writer = csv.writer(fh)
                    writer.writerow(headers)
                    writer.writerows(rows)
            elif fmt == "xlsx":
                try:
                    from openpyxl import Workbook
                    from openpyxl.styles import Font
                except ImportError:
                    QMessageBox.information(self, "Excel export",
                                            "Excel export needs openpyxl.\n\nInstall it with:\npip install openpyxl")
                    return
                wb = Workbook()
                ws = wb.active
                ws.title = "Tags"
                ws.append(headers)
                for cell in ws[1]:
                    cell.font = Font(bold=True)
                for row in rows:
                    ws.append([int(v) if v.isdigit() else v for v in row])
                for col in ws.columns:
                    ws.column_dimensions[col[0].column_letter].width = \
                        max(len(str(c.value or "")) for c in col) + 3
                wb.save(filename)
            else:
                try:
                    from docx import Document
                except ImportError:
                    QMessageBox.information(self, "Word export",
                                            "Word export needs python-docx.\n\nInstall it with:\npip install python-docx")
                    return
                doc = Document()
                doc.add_heading("Live Data - Tag Table", level=1)
                grid = doc.add_table(rows=1, cols=len(headers))
                grid.style = "Table Grid"
                for i, head in enumerate(headers):
                    grid.rows[0].cells[i].text = head
                for row in rows:
                    cells = grid.add_row().cells
                    for i, value in enumerate(row):
                        cells[i].text = value
                doc.save(filename)
        except Exception as exc:  # noqa: BLE001
            self.tag_selection_status.setText(f"Download failed: {exc}")
            return
        self.tag_selection_status.setText(f"Downloaded {len(rows)} row(s) to {Path(filename).name}.")

    # ---------- cards ----------
    _CARD_BASE_STYLE = (
        "QPushButton { text-align: center; padding: 8px; %s }"
        "QPushButton:checked { border: 2px solid #2471a3; background: #eaf4fb; }"
        "QPushButton:disabled { color: #17324d; }"
    )
    # card colour by state: green = OK, red = read error, grey = unconfigured, light = waiting
    _STATE_STYLES = {
        "unconfigured": "background: #eceff3; color: #6b7785; border: 1px solid #c9d1da;",
        "pending": "background: #ffffff; border: 1px solid #9bb7cf;",
        "ok": "background: #e8f6ed; border: 1px solid #2e8b57;",
        "error": "background: #fdecea; color: #c0392b; border: 1px solid #c0392b;",
    }
    _STATE_LABELS = {"unconfigured": "Not configured", "pending": "Waiting for value",
                     "ok": "OK", "error": "Read error"}

    def _make_card(self, tag_id):
        card = TagCard(tag_id, self.tag_content)   # parented, so hidden cards never leak
        card.setObjectName("card")
        card.setMinimumHeight(72)
        card.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        card.clicked.connect(
            lambda checked=False, current_id=tag_id: self._on_live_card_clicked(current_id, checked))
        card.dropped.connect(self._on_tag_dropped)
        return card

    def _apply_card(self, tag_id, tag_name):
        card = self.tag_cards.get(tag_id)
        if card is None:
            return
        cfg = self.tag_configurations.get(tag_id)
        state = self._tag_state(tag_id)
        if not cfg:
            text = tag_name
            tip = "Not configured. Use Edit tag, then click the tag name.\nDrag to re-order."
        else:
            editable = self._tag_is_editable(cfg)
            error = self.tag_errors.get(tag_id)
            value = self.tag_live_values.get(tag_id)
            shown = "—" if value is None else self._format_tag_value(cfg, value)
            text = f"{tag_name}\nValue: {shown}" + ("   ✎" if editable else "")
            tip = (f"State: {self._STATE_LABELS[state]}\n"
                   f"Device {cfg['device_address']} · FC{int(cfg['function_code']):02d} · "
                   f"Address {cfg['address']} · {cfg['access']}"
                   + ("\nClick to write a new value" if editable else "\nRead-only")
                   + "\nDrag to re-order")
            if error:
                tip += f"\nLast read error: {error}"
        if card.text() != text:
            card.setText(text)
        if card.toolTip() != tip:
            card.setToolTip(tip)
        style = self._CARD_BASE_STYLE % self._STATE_STYLES[state]
        if card.styleSheet() != style:
            card.setStyleSheet(style)

    def _update_tag_card_values(self, tag_ids=None):
        """Repaint only the given tags (all when None)."""
        names = dict(self.live_tags)
        for tag_id in (names if tag_ids is None else tag_ids):
            if tag_id in names:
                self._apply_card(tag_id, names[tag_id])
        self._update_tag_table_values()

    def _refresh_tag_cards(self, search_text=""):
        """Create/remove/relayout cards. Existing cards are reused, never rebuilt."""
        content = self.tag_content
        content.setUpdatesEnabled(False)
        try:
            live_ids = {tag_id for tag_id, _tag in self.live_tags}
            for tag_id in [t for t in self.tag_cards if t not in live_ids]:
                card = self.tag_cards.pop(tag_id)
                self.tag_grid.removeWidget(card)
                card.deleteLater()
            for tag_id, _tag in self.live_tags:
                if tag_id not in self.tag_cards:
                    self.tag_cards[tag_id] = self._make_card(tag_id)

            while self.tag_grid.count():
                self.tag_grid.takeAt(0)             # detach layout items; widgets stay alive
            for row in range(self.tag_grid.rowCount()):
                self.tag_grid.setRowStretch(row, 0)

            query = str(search_text).strip().casefold()
            mode = self._filter_mode()
            shown = set()
            order = []
            columns = 3
            position = 0
            for tag_id, tag in self._sorted_live_tags():
                if query not in tag.casefold():
                    continue
                if not self._passes_filter(tag_id, mode):
                    continue
                card = self.tag_cards[tag_id]
                card.setCheckable(self.tag_selection_mode)
                card.setChecked(self.tag_selection_mode and tag_id in self.selected_tag_ids)
                self.tag_grid.addWidget(card, position // columns, position % columns)
                card.show()
                shown.add(tag_id)
                order.append(tag_id)
                position += 1
            self._shown_tag_ids = order
            for tag_id, card in self.tag_cards.items():
                if tag_id not in shown:
                    card.hide()
            for tag_id, tag in self.live_tags:
                self._apply_card(tag_id, tag)
            self.tag_grid.setRowStretch((position + columns - 1) // columns, 1)
        finally:
            content.setUpdatesEnabled(True)

    # ---- Read tab ------------------------------------------
    def _build_read_tab(self):
        page = QWidget()
        outer = QVBoxLayout(page)
        outer.setContentsMargins(0, 4, 0, 0)
        outer.addWidget(heading("Read Data"))
        row = QHBoxLayout()
        row.setSpacing(18)

        card = make_card()
        cl = QVBoxLayout(card)
        cl.setContentsMargins(16, 14, 16, 16)
        cl.setSpacing(8)
        cl.addWidget(heading("Request / read data"))

        self.read_device_spin = make_spin(1, 247)
        cl.addWidget(labeled("Device address", self.read_device_spin))
        self.data_type_combo = QComboBox()
        self.data_type_combo.addItems(DATA_TYPE_OPTIONS)
        cl.addWidget(labeled("Register table / Function code", self.data_type_combo))
        self.start_spin = make_spin(1, 65536)
        cl.addWidget(labeled("Start address (1, 2, 3, ...)", self.start_spin))
        self.length_spin = make_spin(1, 125)
        cl.addWidget(labeled("Length", self.length_spin))
        self.data_format_combo = QComboBox()
        self.data_format_combo.addItems(DATA_FORMAT_OPTIONS)
        cl.addWidget(labeled("Data format", self.data_format_combo))
        self.value_type_combo = QComboBox()
        self.value_type_combo.addItems(VALUE_TYPE_OPTIONS)
        cl.addWidget(labeled(
            "Data type", self.value_type_combo,
            "32-bit values use two consecutive 16-bit registers. Device byte/word order must match."))
        self.scan_spin = make_spin(100, 60000, 100)
        cl.addWidget(labeled(
            "Scan rate (ms)", self.scan_spin,
            "Time between the START of two automatic polls. The time a poll takes is "
            "included, so the real rate matches this value (a poll that takes longer than "
            "this simply starts the next one right away). The actual poll time is shown in "
            "the status strip."))

        grid = QGridLayout()
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(8)
        self.read_btn = QPushButton("Read")
        self.read_btn.setProperty("primary", True)
        self.read_btn.setToolTip("Perform one read request without enabling continuous polling.")
        self.start_poll_btn = QPushButton("Start Auto Polling")
        self.start_poll_btn.setToolTip("Enable background polling using the current scan rate.")
        self.stop_poll_btn = QPushButton("Stop Auto Polling")
        self.clear_table_btn = QPushButton("Clear read table")
        self.clear_table_btn.setToolTip("Remove all rows from the read table.")
        grid.addWidget(self.read_btn, 0, 0)
        grid.addWidget(self.start_poll_btn, 0, 1)
        grid.addWidget(self.stop_poll_btn, 1, 0)
        grid.addWidget(self.clear_table_btn, 1, 1)
        cl.addLayout(grid)
        self.read_notice = Banner()
        cl.addWidget(self.read_notice)
        cl.addStretch(1)

        left = scroll_wrap(card)
        left.setMinimumWidth(340)

        right = QWidget()
        rl = QVBoxLayout(right)
        rl.setContentsMargins(0, 0, 0, 0)
        rl.setSpacing(8)
        read_title_row = QHBoxLayout()
        read_title_row.setContentsMargins(0, 0, 0, 0)
        read_title_row.addWidget(heading("Read table"))
        # Download button beside the "Read table" title: Excel / Word / CSV.
        self.download_read_btn = QPushButton("Download")
        self.download_read_btn.setToolTip(
            "Download the read table (Device address, Function code, Address, Value) "
            "as Excel, Word or CSV")
        self.download_read_btn.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
        read_download_menu = QMenu(self.download_read_btn)
        for label, fmt in (("Excel (.xlsx)", "xlsx"), ("Word (.docx)", "docx"), ("CSV (.csv)", "csv")):
            action = read_download_menu.addAction(label)
            action.triggered.connect(lambda _=False, f=fmt: self._download_read_table(f))
        self.download_read_btn.setMenu(read_download_menu)
        read_title_row.addWidget(self.download_read_btn)
        read_title_row.addStretch(1)
        rl.addLayout(read_title_row)
        rl.addWidget(caption("Latest successful read response. A successful write also updates this table after read-back."))
        self.read_status_banner = Banner()
        rl.addWidget(self.read_status_banner)
        self.read_table_banner = Banner()
        rl.addWidget(self.read_table_banner)
        self.read_model = ReadTableModel(self)
        self.read_view = QTableView()
        self.read_view.setModel(self.read_model)
        self.read_view.setAlternatingRowColors(True)
        self.read_view.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.read_view.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.read_view.verticalHeader().setVisible(False)
        self.read_view.verticalHeader().setDefaultSectionSize(28)
        self.read_view.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
        rl.addWidget(self.read_view, 1)

        row.addWidget(left, 9)
        row.addWidget(right, 16)
        outer.addLayout(row, 1)
        return page

    # ---- Write tab -----------------------------------------
    def _build_write_tab(self):
        page = QWidget()
        outer = QVBoxLayout(page)
        outer.setContentsMargins(0, 4, 0, 0)
        outer.addWidget(heading("Write Data"))
        row = QHBoxLayout()
        row.setSpacing(18)

        # ---- sidebar
        card = make_card()
        sl = QVBoxLayout(card)
        sl.setContentsMargins(16, 14, 16, 16)
        sl.setSpacing(8)
        sl.addWidget(heading("Write operation", 5))
        self.mode_single = QRadioButton(WRITE_MODES[0])
        self.mode_multi = QRadioButton(WRITE_MODES[1])
        self.mode_group = QButtonGroup(self)
        self.mode_group.addButton(self.mode_single)
        self.mode_group.addButton(self.mode_multi)
        sl.addWidget(self.mode_single)
        sl.addWidget(self.mode_multi)
        sl.addSpacing(6)
        sl.addWidget(heading("Write settings", 5))
        self.write_device_spin = make_spin(1, 247)
        sl.addWidget(labeled("Device address", self.write_device_spin))

        self.target_stack = QStackedWidget()
        p0 = QWidget()
        l0 = QVBoxLayout(p0)
        l0.setContentsMargins(0, 0, 0, 0)
        self.single_kind_combo = QComboBox()
        self.single_kind_combo.addItems(SINGLE_WRITE_KINDS)
        single_target_row = QHBoxLayout()
        single_target_label = QLabel("Write target")
        single_target_label.setMinimumWidth(95)
        single_target_row.addWidget(single_target_label)
        single_target_row.addWidget(self.single_kind_combo, 1)
        l0.addLayout(single_target_row)
        l0.addStretch(1)       # keep the row at the top instead of centred in a tall page
        p1 = QWidget()
        l1 = QVBoxLayout(p1)
        l1.setContentsMargins(0, 0, 0, 0)
        l1.setSpacing(8)
        self.multi_kind_combo = QComboBox()
        self.multi_kind_combo.addItems(MULTI_WRITE_KINDS)
        multi_target_row = QHBoxLayout()
        multi_target_label = QLabel("Write target")
        multi_target_label.setMinimumWidth(95)
        multi_target_row.addWidget(multi_target_label)
        multi_target_row.addWidget(self.multi_kind_combo, 1)
        l1.addLayout(multi_target_row)
        self.multi_start_spin = make_spin(1, 65536)
        l1.addWidget(labeled("Starting address", self.multi_start_spin))
        self.multi_end_spin = make_spin(1, 65536)
        l1.addWidget(labeled(
            "Ending address", self.multi_end_spin,
            "The ending address is included in the write range. Maximum range: 50 addresses."))
        self.target_stack.addWidget(p0)
        self.target_stack.addWidget(p1)
        sl.addWidget(self.target_stack)

        self.send_write_btn = QPushButton("Send write request")
        self.send_write_btn.setProperty("primary", True)
        self.clear_write_btn = QPushButton("Clear table data")
        sl.addSpacing(4)
        sl.addWidget(self.send_write_btn)
        sl.addWidget(self.clear_write_btn)
        sl.addStretch(1)
        left = scroll_wrap(card)
        left.setMinimumWidth(330)

        # ---- main workspace
        main = QWidget()
        ml = QVBoxLayout(main)
        ml.setContentsMargins(0, 0, 0, 0)
        ml.setSpacing(8)
        self.write_errors = Banner()
        ml.addWidget(self.write_errors)
        self.main_stack = QStackedWidget()

        s_page = QWidget()
        sp = QVBoxLayout(s_page)
        sp.setContentsMargins(0, 0, 0, 0)
        sp.setSpacing(8)
        sp.addWidget(heading("Write table · maximum 50 entries", 5))
        sp.addWidget(caption("Enter an address and value for each row. Register values: 0–65535; coil values: 0 or 1."))
        self.single_table = QTableWidget(50, 3)
        self.single_table.setHorizontalHeaderLabels(["Sr no", "Write address", "Write value"])
        self._style_write_table(self.single_table)
        self.single_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeMode.Fixed)
        self.single_table.setColumnWidth(0, 70)
        self.single_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        self.single_table.horizontalHeader().setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        digit = DigitDelegate(self.single_table)
        self.single_table.setItemDelegateForColumn(1, digit)
        self.single_table.setItemDelegateForColumn(2, digit)
        sp.addWidget(self.single_table, 1)

        m_page = QWidget()
        mp = QVBoxLayout(m_page)
        mp.setContentsMargins(0, 0, 0, 0)
        mp.setSpacing(8)
        mp.addWidget(heading("Write data table · maximum 50 entries", 5))
        self.multi_warning = Banner()
        mp.addWidget(self.multi_warning)
        mp.addWidget(caption("The table displays every address from Starting address through Ending address, inclusive. Enter values only in the Value column."))
        self.multi_table = QTableWidget(0, 2)
        self.multi_table.setHorizontalHeaderLabels(["Address", "Value"])
        self._style_write_table(self.multi_table)
        self.multi_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        self.multi_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        self.multi_table.setItemDelegateForColumn(1, DigitDelegate(self.multi_table))
        mp.addWidget(self.multi_table, 1)

        self.main_stack.addWidget(s_page)
        self.main_stack.addWidget(m_page)
        ml.addWidget(self.main_stack, 1)

        row.addWidget(left, 85)
        row.addWidget(main, 180)
        outer.addLayout(row, 1)
        return page

    @staticmethod
    def _style_write_table(table):
        table.verticalHeader().setVisible(False)
        table.verticalHeader().setDefaultSectionSize(30)
        table.setAlternatingRowColors(True)
        table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)

    # ---- Log / Spy tabs ------------------------------------
    def _mono(self):
        font = QFontDatabase.systemFont(QFontDatabase.SystemFont.FixedFont)
        font.setPointSize(10)
        return font

    def _build_log_tab(self):
        page = QWidget()
        lay = QVBoxLayout(page)
        lay.setContentsMargins(0, 4, 0, 0)
        lay.addWidget(heading("Communication Log"))
        lay.addWidget(caption("Readable application events: connection changes, Modbus requests, write results, and errors."))
        self.log_view = QPlainTextEdit()
        self.log_view.setReadOnly(True)
        self.log_view.setFont(self._mono())
        self.log_view.setLineWrapMode(QPlainTextEdit.LineWrapMode.NoWrap)
        self.log_view.setPlaceholderText("No communication events yet.")
        lay.addWidget(self.log_view, 1)
        self.clear_log_btn = QPushButton("Clear communication log")
        lay.addWidget(self.clear_log_btn, 0, Qt.AlignmentFlag.AlignLeft)
        return page

    def _build_spy_tab(self):
        page = QWidget()
        lay = QVBoxLayout(page)
        lay.setContentsMargins(0, 4, 0, 0)
        lay.addWidget(heading("Communication Spy"))
        lay.addWidget(caption("Raw Modbus RTU frames from the PyModbus packet-trace hook. TX = transmitted bytes; RX = received bytes. Non-printable bytes appear as dots in ASCII."))
        self.spy_view = QPlainTextEdit()
        self.spy_view.setReadOnly(True)
        self.spy_view.setFont(self._mono())
        self.spy_view.setLineWrapMode(QPlainTextEdit.LineWrapMode.NoWrap)
        self.spy_view.setPlaceholderText(
            "No raw frames captured yet. Connect, then click Read or Start Auto Polling. "
            "Raw capture depends on packet-trace support in your installed PyModbus version.")
        lay.addWidget(self.spy_view, 1)
        self.clear_spy_btn = QPushButton("Clear raw serial trace")
        lay.addWidget(self.clear_spy_btn, 0, Qt.AlignmentFlag.AlignLeft)
        return page

    # --------------------------------------------------------
    # Load saved settings into the widgets
    # --------------------------------------------------------
    def populate_ports(self, preferred=None):
        ports = list_serial_ports()
        current = (preferred or self.port_combo.currentText() or (ports[0] if ports else DEFAULT_PORT)).strip()
        options = ports if ports else list(FALLBACK_PORTS)
        if current not in options:
            options = [current] + options
        self.port_combo.blockSignals(True)
        self.port_combo.clear()
        self.port_combo.addItems(options)
        self.port_combo.setCurrentText(current)
        self.port_combo.blockSignals(False)

    @staticmethod
    def _set_combo(combo, value, options=None):
        text = str(value)
        index = combo.findText(text)
        combo.setCurrentIndex(index if index >= 0 else 0)

    def _load_widgets(self):
        s = self.saved
        self.populate_ports(str(s.get("port") or "") or None)

        baud = int(s.get("baud", 9600)) if str(s.get("baud", 9600)).isdigit() else 9600
        self._set_combo(self.baud_combo, baud if baud in BAUD_OPTIONS else 9600)
        bits = clamp_int(s.get("data_bits", 8), 7, 8, 8)
        self._set_combo(self.data_bits_combo, bits if bits in DATA_BITS_OPTIONS else 8)
        parity = s.get("parity", "NONE")
        self._set_combo(self.parity_combo, parity if parity in PARITY_OPTIONS else "NONE")
        stop = clamp_int(s.get("stop_bits", 1), 1, 2, 1)
        self._set_combo(self.stop_bits_combo, stop if stop in STOP_BITS_OPTIONS else 1)
        self.timeout_spin.setValue(clamp_int(s.get("timeout_ms", 1000), 100, 10000, 1000))

        device_id = clamp_int(s.get("device_id", 1), 1, 247, 1)
        self.read_device_spin.setValue(device_id)
        self.write_device_spin.setValue(device_id)
        self.live_device_spin.setValue(device_id)
        self.live_scan_spin.setValue(clamp_int(s.get("live_scan_rate", 500), 100, 60000, 500))
        live_fmt = s.get("live_data_format", "Decimal")
        self._set_combo(self.live_format_combo, live_fmt if live_fmt in DATA_FORMAT_OPTIONS else "Decimal")

        data_type = s.get("data_type", "3 : Holding registers")
        # Version 2 used the function-code labels in reverse for registers.
        if data_type == "3 : Input registers":
            data_type = "4 : Input registers"
        elif data_type == "4 : Holding registers":
            data_type = "3 : Holding registers"
        self._set_combo(self.data_type_combo, data_type if data_type in DATA_TYPE_OPTIONS else DATA_TYPE_OPTIONS[0])

        start = clamp_int(s.get("start_address", 1), 0, 10**9, 1)
        if start >= 40001:
            start -= 40000
        elif start >= 30001:
            start -= 30000
        self.start_spin.setValue(max(1, min(start, 65536)))

        is_bits = self.data_type_combo.currentText().startswith(("1 :", "2 :"))
        self.length_spin.setMaximum(2000 if is_bits else 125)
        self.length_spin.setValue(clamp_int(s.get("length", 10), 1, 2000 if is_bits else 125, 10))

        fmt = s.get("data_format", "Decimal")
        self._set_combo(self.data_format_combo, fmt if fmt in DATA_FORMAT_OPTIONS else "Decimal")
        vtype = s.get("value_type", "Raw register value")
        self._set_combo(self.value_type_combo, vtype if vtype in VALUE_TYPE_OPTIONS else "Raw register value")
        self.scan_spin.setValue(clamp_int(s.get("scan_rate", 1000), 100, 60000, 1000))

        # ---- write tab
        mode = normalize_choice(s.get("write_mode"), WRITE_MODES, WRITE_MODES[0])
        (self.mode_multi if mode == WRITE_MODES[1] else self.mode_single).setChecked(True)
        self._set_combo(self.single_kind_combo,
                        normalize_choice(s.get("write_kind"), SINGLE_WRITE_KINDS, SINGLE_WRITE_KINDS[0]))
        self._set_combo(self.multi_kind_combo,
                        normalize_choice(s.get("multi_write_kind"), MULTI_WRITE_KINDS, MULTI_WRITE_KINDS[1]))
        self.multi_start_spin.setValue(clamp_int(s.get("multi_write_start_address", 1), 1, 65536, 1))
        self.multi_end_spin.setValue(clamp_int(s.get("multi_write_end_address", 10), 1, 65536, 10))
        self.saved.setdefault("single_write_rows", {})
        self.saved.setdefault("multi_write_values", {})
        self._populate_single_table()
        self.rebuild_multi_table()
        self._apply_mode()

    def _populate_single_table(self):
        rows = self.saved.get("single_write_rows", {}) or {}
        table = self.single_table
        table.blockSignals(True)
        for r in range(50):
            saved_row = rows.get(str(r + 1), {}) or {}
            sr = QTableWidgetItem(str(r + 1))
            sr.setFlags(Qt.ItemFlag.ItemIsEnabled)
            sr.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            table.setItem(r, 0, sr)
            for col, key in ((1, "address"), (2, "value")):
                text = str(saved_row.get(key, "") or "").strip()
                item = QTableWidgetItem(text if text.isdecimal() else "")
                item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
                table.setItem(r, col, item)
        table.blockSignals(False)

    def rebuild_multi_table(self):
        start = int(self.multi_start_spin.value())
        end = int(self.multi_end_spin.value())
        count = end - start + 1
        if count < 1:
            self.multi_warning.show_message("warning", "Ending address must be greater than or equal to Starting address.")
            visible = 0
        elif count > 50:
            self.multi_warning.show_message("warning", "The address range can contain at most 50 entries. Reduce the range to 50 addresses or fewer.")
            visible = 50
        else:
            self.multi_warning.clear_banner()
            visible = count
        values = self.saved.get("multi_write_values", {}) or {}
        table = self.multi_table
        table.blockSignals(True)
        table.setRowCount(visible)
        for r in range(visible):
            address = start + r
            a_item = QTableWidgetItem(str(address))
            a_item.setFlags(Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsSelectable)
            a_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            table.setItem(r, 0, a_item)
            text = str(values.get(str(address), "") or "").strip()
            v_item = QTableWidgetItem(text if text.isdecimal() else "")
            v_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            table.setItem(r, 1, v_item)
        table.blockSignals(False)

    def _apply_mode(self):
        multi = self.mode_multi.isChecked()
        self.target_stack.setCurrentIndex(1 if multi else 0)
        self.main_stack.setCurrentIndex(1 if multi else 0)
        # A QStackedWidget is as tall as its tallest page. Let only the visible page
        # count, so single mode does not inherit the extra height of the multi-write page.
        for index in range(self.target_stack.count()):
            page = self.target_stack.widget(index)
            current = index == self.target_stack.currentIndex()
            page.setSizePolicy(QSizePolicy.Policy.Preferred,
                               QSizePolicy.Policy.Preferred if current else QSizePolicy.Policy.Ignored)
        self.target_stack.updateGeometry()

    # --------------------------------------------------------
    # Signals
    # --------------------------------------------------------
    def _connect_signals(self):
        self.clear_counters_btn.clicked.connect(self.on_clear_counters)
        self.refresh_ports_btn.clicked.connect(lambda: self.populate_ports())
        self.connect_btn.clicked.connect(self.on_connect)
        self.disconnect_btn.clicked.connect(self.on_disconnect)

        for widget in (self.port_combo, self.baud_combo, self.data_bits_combo,
                       self.parity_combo, self.stop_bits_combo):
            if isinstance(widget, QComboBox):
                widget.currentTextChanged.connect(self.on_rs_changed)
        self.port_combo.editTextChanged.connect(self.on_rs_changed)
        self.timeout_spin.valueChanged.connect(self.on_rs_changed)

        self.read_device_spin.valueChanged.connect(self.on_read_device_changed)
        self.write_device_spin.valueChanged.connect(self.on_write_device_changed)
        self.live_device_spin.valueChanged.connect(self.on_live_device_changed)
        self.live_scan_spin.valueChanged.connect(self.on_live_scan_changed)
        self.live_format_combo.currentTextChanged.connect(lambda *_: self.schedule_save())
        for combo in (self.data_type_combo, self.data_format_combo, self.value_type_combo):
            combo.currentTextChanged.connect(self.on_read_settings_changed)
        for spin in (self.start_spin, self.length_spin, self.scan_spin):
            spin.valueChanged.connect(self.on_read_settings_changed)

        self.read_btn.clicked.connect(self.on_read)
        self.start_poll_btn.clicked.connect(self.on_start_auto)
        self.stop_poll_btn.clicked.connect(self.on_stop_auto)
        self.clear_table_btn.clicked.connect(self.on_clear_read_table)

        self.mode_single.toggled.connect(self.on_mode_changed)
        self.mode_multi.toggled.connect(self.on_mode_changed)
        self.single_kind_combo.currentTextChanged.connect(lambda *_: self.schedule_save())
        self.multi_kind_combo.currentTextChanged.connect(lambda *_: self.schedule_save())
        self.multi_start_spin.valueChanged.connect(self.on_multi_range_changed)
        self.multi_end_spin.valueChanged.connect(self.on_multi_range_changed)
        self.single_table.itemChanged.connect(self.on_single_item_changed)
        self.multi_table.itemChanged.connect(self.on_multi_item_changed)
        self.send_write_btn.clicked.connect(self.on_send_write)
        self.clear_write_btn.clicked.connect(self.on_clear_write_table)

        self.clear_log_btn.clicked.connect(self.on_clear_log)
        self.clear_spy_btn.clicked.connect(self.on_clear_spy)

    # --------------------------------------------------------
    # Persistence
    # --------------------------------------------------------
    def schedule_save(self):
        if not self._loading:
            self._save_timer.start()

    def collect_state(self):
        s = self.saved
        return {
            # Communication settings
            "port": self.port_combo.currentText().strip(),
            "baud": int(self.baud_combo.currentText()),
            "data_bits": int(self.data_bits_combo.currentText()),
            "parity": self.parity_combo.currentText(),
            "stop_bits": int(self.stop_bits_combo.currentText()),
            "timeout_ms": int(self.timeout_spin.value()),
            # Modbus settings
            "device_id": int(self.read_device_spin.value()),
            "data_type": self.data_type_combo.currentText(),
            "start_address": int(self.start_spin.value()),
            "length": int(self.length_spin.value()),
            "scan_rate": int(self.scan_spin.value()),
            "live_scan_rate": int(self.live_scan_spin.value()),
            "live_data_format": self.live_format_combo.currentText(),
            "data_format": self.data_format_combo.currentText(),
            "value_type": self.value_type_combo.currentText(),
            # Write settings
            "write_kind": self.single_kind_combo.currentText(),
            "multi_write_kind": self.multi_kind_combo.currentText(),
            "write_mode": WRITE_MODES[1] if self.mode_multi.isChecked() else WRITE_MODES[0],
            "multi_write_start_address": int(self.multi_start_spin.value()),
            "multi_write_end_address": int(self.multi_end_spin.value()),
            "write_address": clamp_int(s.get("write_address", 1), 1, 65536, 1),
            "write_value": clamp_int(s.get("write_value", 0), 0, 65535, 0),
            "single_write_rows": s.get("single_write_rows", {}),
            "multi_write_values": s.get("multi_write_values", {}),
            # Runtime is intentionally not persisted: every launch starts clean.
            "auto_poll": False,
            "was_connected": False,
        }

    def save_state_now(self):
        try:
            payload = json.dumps(self.collect_state(), indent=2)
            if payload != self._last_payload or not STATE_FILE.exists():
                tmp = STATE_FILE.with_suffix(".tmp")
                tmp.write_text(payload, encoding="utf-8")
                os.replace(tmp, STATE_FILE)
                self._last_payload = payload
            self.save_error = ""
        except Exception as exc:
            self.save_error = f"{type(exc).__name__}: {exc}"

    def persist_single_table(self):
        rows = {}
        for r in range(50):
            rows[str(r + 1)] = {
                "address": self._cell_text(self.single_table, r, 1),
                "value": self._cell_text(self.single_table, r, 2),
            }
        self.saved["single_write_rows"] = rows
        self.schedule_save()

    @staticmethod
    def _cell_text(table, row, col):
        item = table.item(row, col)
        return item.text().strip() if item is not None else ""

    # --------------------------------------------------------
    # Connection state / guard
    # --------------------------------------------------------
    def current_rs_params(self):
        try:
            return (
                self.port_combo.currentText().strip(),
                int(self.baud_combo.currentText()),
                int(self.data_bits_combo.currentText()),
                PARITY_CODES.get(self.parity_combo.currentText(), "N"),
                int(self.stop_bits_combo.currentText()),
                int(self.timeout_spin.value()),
            )
        except (TypeError, ValueError):
            return None

    def connection_guard(self):
        """(ok, message). Reads/writes are allowed only with the settings used at Connect."""
        if not self.connected or self.client is None:
            return False, "Not connected"
        current = self.current_rs_params()
        if self.client_key is not None and current is not None and tuple(self.client_key) != current:
            return False, ("RS settings changed after connecting. Disconnect and Connect again "
                           "to apply them; reading and writing are blocked until then.")
        return True, ""

    def current_read_signature(self):
        try:
            return _signature(
                self.read_device_spin.value(),
                self.data_type_combo.currentText().split(" :")[0],
                self.start_spin.value(), self.length_spin.value(),
                self.value_type_combo.currentText(), self.data_format_combo.currentText(),
            )
        except (TypeError, ValueError):
            return None

    def on_rs_changed(self, *_):
        if self._loading:
            return
        self.schedule_save()
        ok, msg = self.connection_guard()
        if self.auto_poll and self.connected and not ok:
            self.auto_poll = False
            POLLER.stop()
            RT.set_read_status(msg)
            RT.log("AUTO POLLING STOPPED — RS settings changed after connecting")

    def on_connect(self):
        if self.connected or self.connect_busy:
            return
        params = self.current_rs_params()
        if params is None or not params[0]:
            self.conn_message = ("error", "Choose or type a serial port first.")
            return
        port, baud, bits, parity, stop, timeout_ms = params
        self.connect_busy = True
        self.conn_message = None
        RT.set_read_status(f"Connecting to {port}...")

        def job():
            client = get_modbus_client(port, baud, bits, parity, stop, timeout_ms / 1000.0)
            try:
                opened = bool(client.connect())
            except Exception:
                try:
                    client.close()
                except Exception:
                    pass
                raise
            if not opened:
                try:
                    client.close()
                except Exception:
                    pass
            return client, opened

        self.runner.run(job, lambda ok, res: self._after_connect(ok, res, params))

    def _after_connect(self, ok, result, params):
        self.connect_busy = False
        port = params[0]
        if ok and result[1]:
            client = result[0]
            self.client = client
            self.connected = True
            self.client_key = params
            RANGE_CACHE.clear()
            POLLER.client = client
            self.auto_poll = False
            POLLER.stop()
            RT.set_read_status(f"Connected — {port}")
            RT.set_link("info", f"Serial port {port} opened. Press Read to verify the device answers with these parameters.")
            RT.log(f"Connected to {port} (RTU)")
            QTimer.singleShot(0, self._poll_live_tag_values)  # show Live Data tag values right away
        elif ok:
            self.client = None
            self.connected = False
            self.auto_poll = False
            msg = (f"Connection failed: could not open {port}. Check the COM port, USB cable, "
                   "driver, and whether another program is using the port.")
            RT.set_read_status(msg)
            RT.set_link("error", f"Could not open {port}: check the port name, cable, driver and that no other program uses it.")
            RT.log(f"Connection failed — {port}")
            self.conn_message = ("error", msg)
        else:
            self.client = None
            self.connected = False
            self.auto_poll = False
            exc = result
            RT.set_read_status(f"Connection error on {port}: {type(exc).__name__}: {exc}")
            RT.set_link("error", f"Connection error on {port}: {type(exc).__name__}: {exc}")
            RT.log(f"CONNECTION ERROR on {port}: {type(exc).__name__}: {exc}")
            self.conn_message = ("error", f"Connection error on {port}: {type(exc).__name__}: {exc}")
        self.save_state_now()

    def on_disconnect(self):
        if not self.connected:
            return
        client = self.client
        self.auto_poll = False
        POLLER.stop()
        POLLER.client = None
        self.client = None
        self.connected = False
        self.client_key = None
        self.conn_message = None
        RANGE_CACHE.clear()
        RT.set_read_status("Disconnected")
        RT.set_link("info", "Disconnected")
        RT.log("Disconnected")

        def close_job():
            try:
                if client is not None:
                    with MODBUS_LOCK:
                        client.close()
            except Exception as exc:
                RT.log(f"DISCONNECT ERROR {exc}")

        threading.Thread(target=close_job, daemon=True, name="ModbusClose").start()
        self.save_state_now()

    # --------------------------------------------------------
    # Read tab actions
    # --------------------------------------------------------
    def _commit_spins(self):
        for spin in (self.timeout_spin, self.read_device_spin, self.write_device_spin,
                     self.live_device_spin, self.live_scan_spin, self.start_spin,
                     self.length_spin, self.scan_spin, self.multi_start_spin, self.multi_end_spin):
            spin.interpretText()

    def build_poll_cfg(self):
        return {
            "device_id": int(self.read_device_spin.value()),
            "kind": self.data_type_combo.currentText().split(" :")[0],
            "address": int(self.start_spin.value()),
            "count": int(self.length_spin.value()),
            "data_format": self.data_format_combo.currentText(),
            "value_type": self.value_type_combo.currentText(),
            "scan_rate": int(self.scan_spin.value()),
        }

    def publish_poll_cfg(self):
        """Publish the current Read Data settings to the persistent poller."""
        cfg = self.build_poll_cfg()
        changed = POLLER.cfg != cfg
        POLLER.cfg = cfg
        if self.auto_poll and self.connected and self.client is not None:
            POLLER.client = self.client
            if changed:
                POLLER.wake.set()
        return changed

    def on_read_device_changed(self, value):
        self._sync_device(value, self.write_device_spin, self.live_device_spin)

    def on_write_device_changed(self, value):
        self._sync_device(value, self.read_device_spin, self.live_device_spin)

    def on_live_device_changed(self, value):
        self._sync_device(value, self.read_device_spin, self.write_device_spin)

    def on_live_scan_changed(self, value):
        """Apply a new Live Data refresh interval immediately."""
        if self._loading:
            return
        timer = getattr(self, "_tag_live_timer", None)
        if timer is not None:
            timer.setInterval(int(value))
        self.schedule_save()

    def _sync_device(self, value, *others):
        """Keep the Read, Write and Live Data device addresses identical."""
        if self._loading:
            return
        for other in others:
            other.blockSignals(True)
            other.setValue(value)
            other.blockSignals(False)
        self.publish_poll_cfg()
        self.schedule_save()
        self._apply_device_to_tags(value)

    def _apply_device_to_tags(self, value):
        """Every Live Data tag talks to the shared device address."""
        changed = False
        for cfg in self.tag_configurations.values():
            if cfg.get("device_address") != value:
                cfg["device_address"] = value
                changed = True
        if not changed:
            return
        self.tag_live_values.clear()      # old readings belong to the previous device
        self.tag_errors.clear()
        self._update_tag_card_values()
        self._edit_tag_placeholder_refresh_table()
        self._tag_configs_changed()
        QTimer.singleShot(0, self._poll_live_tag_values)

    def on_read_settings_changed(self, *_):
        if self._loading:
            return
        is_bits = self.data_type_combo.currentText().startswith(("1 :", "2 :"))
        limit = 2000 if is_bits else 125
        if self.length_spin.maximum() != limit:
            self.length_spin.setMaximum(limit)  # also clamps the current value
        self.publish_poll_cfg()
        self.schedule_save()

    def on_read(self):
        if self.read_busy:
            return
        self._commit_spins()
        ok, msg = self.connection_guard()
        if not ok:
            RT.set_link("error", msg)
            RT.set_read_status(msg)
            self.read_notice.show_message(
                "warning", "Connect to the RTU device in Modbus Settings first." if msg == "Not connected" else msg)
            return
        self.read_notice.clear_banner()
        cfg = self.build_poll_cfg()
        POLLER.client = self.client
        self.publish_poll_cfg()
        client = self.client
        self.read_busy = True
        self.read_btn.setEnabled(False)       # no double-click before the next refresh tick

        def job():
            return do_read(client=client, device_id=cfg["device_id"], kind=cfg["kind"],
                           address=cfg["address"], count=cfg["count"], data_format=cfg["data_format"],
                           value_type=cfg["value_type"], status_prefix="Read", merge_existing=False)

        def done(ok_flag, result):
            self.read_busy = False
            if ok_flag:
                success, message, _n = result
            else:
                success, message = False, f"{type(result).__name__}: {result}"
            if success:
                RT.log(f"READ OK unit={cfg['device_id']}, function={cfg['kind']}, "
                       f"address={cfg['address']}, count={cfg['count']}")
            else:
                RT.set_read_status(f"Read failed: {message}")
                RT.log(f"READ ERROR {message}")

        self.runner.run(job, done)

    def on_start_auto(self):
        self._commit_spins()
        ok, msg = self.connection_guard()
        if not ok:
            RT.set_link("error", msg)
            RT.set_read_status(msg)
            self.read_notice.show_message(
                "warning", "Connect to the RTU device in Modbus Settings first." if msg == "Not connected" else msg)
            return
        self.read_notice.clear_banner()
        POLLER.client = self.client
        self.publish_poll_cfg()
        self.auto_poll = True
        RT.log(f"AUTO POLLING STARTED rate={self.scan_spin.value()}ms")
        POLLER.start(wake=True)
        self.save_state_now()

    def on_stop_auto(self):
        self.auto_poll = False
        POLLER.stop()
        RT.log("AUTO POLLING STOPPED")
        self.save_state_now()

    def on_clear_read_table(self):
        RT.clear_data()
        self.save_state_now()

    def _download_read_table(self, fmt):
        """Download the Read Data table as Excel / Word / CSV.

        Columns: Device address, Function code, Address, Value. Device address and
        function code are those of the request that produced the table shown.
        """
        with RT.lock:
            data_rows = sorted(RT.data.items())
            signature = RT.data_signature
        if not data_rows:
            QMessageBox.information(
                self, "Download",
                "The read table is empty. Connect to the device and read data first.")
            return
        if signature is not None:                      # (device, kind, address, count, ...)
            device_id, kind = int(signature[0]), str(signature[1])
        else:                                          # table only holds write read-backs
            device_id = int(self.read_device_spin.value())
            kind = self.data_type_combo.currentText().split(" :")[0]
        function_text = f"FC{int(kind):02d}"
        headers = ["Device address", "Function code", "Address", "Value"]
        rows = [[device_id, function_text, int(address), value] for address, value in data_rows]

        ext, kind_filter = {"csv": (".csv", "CSV file (*.csv)"),
                            "xlsx": (".xlsx", "Excel workbook (*.xlsx)"),
                            "docx": (".docx", "Word document (*.docx)")}[fmt]
        default = str(APP_DIR / f"read_data_{datetime.now():%Y%m%d_%H%M%S}{ext}")
        filename, _f = QFileDialog.getSaveFileName(self, "Download read table", default, kind_filter)
        if not filename:
            return
        if not filename.lower().endswith(ext):
            filename += ext
        try:
            if fmt == "csv":
                with open(filename, "w", newline="", encoding="utf-8-sig") as fh:
                    writer = csv.writer(fh)
                    writer.writerow(headers)
                    writer.writerows(rows)
            elif fmt == "xlsx":
                try:
                    from openpyxl import Workbook
                    from openpyxl.styles import Font
                except ImportError:
                    QMessageBox.information(self, "Excel export",
                                            "Excel export needs openpyxl.\n\nInstall it with:\npip install openpyxl")
                    return
                wb = Workbook()
                ws = wb.active
                ws.title = "Read data"
                ws.append(headers)
                for cell in ws[1]:
                    cell.font = Font(bold=True)
                for row in rows:
                    ws.append(row)
                for col in ws.columns:
                    ws.column_dimensions[col[0].column_letter].width = \
                        max(len(str(c.value or "")) for c in col) + 3
                wb.save(filename)
            else:
                try:
                    from docx import Document
                except ImportError:
                    QMessageBox.information(self, "Word export",
                                            "Word export needs python-docx.\n\nInstall it with:\npip install python-docx")
                    return
                doc = Document()
                doc.add_heading("Read Data", level=1)
                grid = doc.add_table(rows=1, cols=len(headers))
                grid.style = "Table Grid"
                for i, head in enumerate(headers):
                    grid.rows[0].cells[i].text = head
                for row in rows:
                    cells = grid.add_row().cells
                    for i, value in enumerate(row):
                        cells[i].text = str(value)
                doc.save(filename)
        except Exception as exc:  # noqa: BLE001
            QMessageBox.warning(self, "Download", f"Download failed:\n{type(exc).__name__}: {exc}")
            return
        RT.log(f"READ TABLE DOWNLOADED {len(rows)} row(s) to {Path(filename).name}")

    def on_clear_counters(self):
        RT.reset_counters()

    # --------------------------------------------------------
    # Write tab actions
    # --------------------------------------------------------
    def on_mode_changed(self, *_):
        self._apply_mode()
        self.write_errors.clear_banner()
        self.schedule_save()

    def on_multi_range_changed(self, *_):
        if self._loading:
            return
        self.rebuild_multi_table()
        self.schedule_save()

    def on_single_item_changed(self, item):
        if self._loading or item.column() not in (1, 2):
            return
        self.persist_single_table()

    def on_multi_item_changed(self, item):
        if self._loading or item.column() != 1:
            return
        addr_item = self.multi_table.item(item.row(), 0)
        if addr_item is None:
            return
        values = self.saved.setdefault("multi_write_values", {})
        values[addr_item.text()] = item.text().strip()
        self.schedule_save()

    def on_clear_write_table(self):
        if self.mode_multi.isChecked():
            self.saved["multi_write_values"] = {}
            self.rebuild_multi_table()
        else:
            self.single_table.blockSignals(True)
            for r in range(50):
                for col in (1, 2):
                    item = self.single_table.item(r, col)
                    if item is not None:
                        item.setText("")
            self.single_table.blockSignals(False)
            self.saved["single_write_rows"] = {}
        self.write_errors.clear_banner()
        self.save_state_now()

    def on_send_write(self):
        if self.write_busy:
            return
        self._commit_spins()
        self.write_errors.clear_banner()
        ok, msg = self.connection_guard()
        if not ok:
            RT.set_link("error", msg)
            RT.set_write_status("Not connected" if msg == "Not connected" else "Blocked — RS settings changed")
            self.write_errors.show_message(
                "error", "Connect to the RTU device in Modbus Settings first." if msg == "Not connected" else msg)
            return
        if self.mode_multi.isChecked():
            self._send_multi()
        else:
            self._send_single()

    def _begin_write(self):
        """Pause the poller during a write; returns whether to resume it afterwards."""
        resume = bool(self.auto_poll and POLLER.on)
        POLLER.on = False
        self.write_busy = True
        self.send_write_btn.setEnabled(False)  # no double-click before the next refresh tick
        return resume

    def _end_write(self, resume):
        self.write_busy = False
        if resume and self.auto_poll:
            POLLER.on = True
            POLLER.wake.set()

    def _write_finished(self, status, errors):
        RT.set_write_status(status)
        if errors:
            self.write_errors.show_message("error", "\n".join(errors))
        else:
            self.write_errors.clear_banner()
        self.save_state_now()

    def _send_single(self):
        is_coil = self.single_kind_combo.currentText().startswith("Coil")
        entries, errors, seen = [], [], set()
        for r in range(50):
            addr_text = self._cell_text(self.single_table, r, 1)
            val_text = self._cell_text(self.single_table, r, 2)
            row_no = r + 1
            if not addr_text and not val_text:
                continue
            try:
                if not addr_text.isdecimal() or not val_text.isdecimal():
                    raise ValueError
                addr_num, val_num = int(addr_text), int(val_text)
                if not 1 <= addr_num <= 65536:
                    raise ValueError("address")
                if addr_num in seen:
                    errors.append(f"Row {row_no}: duplicate address {addr_num}")
                    continue
                if is_coil and val_num not in (0, 1):
                    errors.append(f"Row {row_no}: coil value must be 0 or 1")
                    continue
                if not is_coil and not 0 <= val_num <= 65535:
                    errors.append(f"Row {row_no}: register value must be 0–65535")
                    continue
                seen.add(addr_num)
                entries.append((addr_num, val_num))
            except ValueError as exc:
                errors.append(f"Row {row_no}: enter valid whole-number address/value" +
                              (" (address 1–65536)" if str(exc) == "address" else ""))
        if not entries and not errors:
            errors.append("Enter at least one address/value pair.")
        if not entries:
            self._write_finished("Write failed — see details", errors)
            return

        client = self.client
        device_id = int(self.write_device_spin.value())
        fmt = self.data_format_combo.currentText()
        resume = self._begin_write()

        def job():
            return perform_single_writes(client, device_id, is_coil, entries, fmt)

        def done(ok_flag, result):
            self._end_write(resume)
            if ok_flag:
                status, write_errors = result
            else:
                status, write_errors = "Write failed — see details", [f"{type(result).__name__}: {result}"]
            self._write_finished(status, errors + write_errors)

        self.runner.run(job, done)

    def _send_multi(self):
        is_coil = self.multi_kind_combo.currentText().startswith("Multiple coils")
        start = int(self.multi_start_spin.value())
        end = int(self.multi_end_spin.value())
        expected_count = end - start + 1
        entries, errors = [], []
        if not (1 <= start <= 65536) or not (1 <= end <= 65536):
            errors.append("Starting and ending addresses must be between 1 and 65536.")
        elif end < start:
            errors.append("Ending address must be greater than or equal to Starting address.")
        elif expected_count > 50:
            errors.append("The address range cannot exceed 50 entries.")
        else:
            for offset in range(expected_count):
                raw_value = self._cell_text(self.multi_table, offset, 1)
                if not raw_value:
                    errors.append(f"Row {offset + 1}: enter a write value.")
                    continue
                if not raw_value.isdecimal():
                    errors.append(f"Row {offset + 1}: value must be a whole number.")
                    continue
                value_num = int(raw_value)
                if is_coil and value_num not in (0, 1):
                    errors.append(f"Row {offset + 1}: coil value must be 0 or 1.")
                    continue
                if not is_coil and not 0 <= value_num <= 65535:
                    errors.append(f"Row {offset + 1}: register value must be 0–65535.")
                    continue
                entries.append((start + offset, value_num))

        if errors or len(entries) != expected_count:
            self._write_finished("Write validation failed — see details", errors)
            return

        client = self.client
        device_id = int(self.write_device_spin.value())
        fmt = self.data_format_combo.currentText()
        resume = self._begin_write()

        def job():
            return perform_multi_write(client, device_id, is_coil, start, end, entries, fmt)

        def done(ok_flag, result):
            self._end_write(resume)
            if ok_flag:
                status, write_errors = result
            else:
                status, write_errors = "Write failed — see details", [f"{type(result).__name__}: {result}"]
            self._write_finished(status, write_errors)

        self.runner.run(job, done)

    # --------------------------------------------------------
    # Log / spy actions
    # --------------------------------------------------------
    def on_clear_log(self):
        RT.clear_log()

    def on_clear_spy(self):
        RT.clear_raw()

    # --------------------------------------------------------
    # Periodic refresh (reads the shared store; never blocks)
    # --------------------------------------------------------
    def _set_html(self, label, html_text, tooltip=""):
        key = id(label)
        if self._cache.get(key) != (html_text, tooltip):
            self._cache[key] = (html_text, tooltip)
            label.setText(html_text)
            label.setToolTip(tooltip)

    def connection_badge(self):
        client = self.client
        if not self.connected or client is None:
            return badge("error", "Not connected")
        try:
            if not getattr(client, "connected", True):
                return badge("error", "Serial port closed — press Disconnect, then Connect")
        except Exception:
            pass
        key = self.client_key
        desc = f"{key[0]} · {key[1]} baud · {key[2]}{key[3]}{key[4]}" if key else "serial port open"
        ok, _msg = self.connection_guard()
        if not ok:
            return badge("warn", f"Connected ({desc}) — settings changed, Disconnect and Connect to apply")
        return badge("ok", f"Connected — {desc}")

    def refresh_top_status(self):
        with RT.lock:
            polls, valid = RT.polls, RT.valid_responses
            read_status, write_status, last_update = RT.read_status, RT.write_status, RT.last_update
            link_level, link_text, link_time = RT.link_level, RT.link_status, RT.link_time
            poll_ms = RT.poll_ms
        esc = lambda t: html.escape(str(t), quote=True)  # noqa: E731
        conn_html = (
            f"<div><b>Modbus Connection:</b> {self.connection_badge()}</div>"
            f"<div style='margin-top:4px;'><b>Last Request / Exception:</b> "
            f"{badge(link_level, clip(link_text, 230))} "
            f"<span style='color:#61748b;font-size:11px;'>({esc(link_time)})</span></div>"
        )
        self._set_html(self.conn_label, conn_html, f"{link_text} ({link_time})")
        scan_text = ""
        if self.auto_poll and poll_ms:
            scan_text = (f" <span style='color:#61748b;font-size:11px;'>"
                         f"· scan {poll_ms} ms / {int(self.scan_spin.value())} ms</span>")
        status_html = (
            f"<div><b>Read Status:</b> {esc(clip(read_status, 140))}</div>"
            f"<div style='margin-top:3px;'><b>Write Status:</b> {esc(clip(write_status, 90))}</div>"
            f"<div style='margin-top:3px;'><b>Last Update:</b> {esc(last_update)}{scan_text}</div>"
        )
        self._set_html(self.status_label, status_html,
                       f"Read: {read_status}\nWrite: {write_status}\nLast update: {last_update}"
                       f"\nLast poll took {poll_ms} ms")
        self.polls_metric.set_value(str(polls))
        self.valid_metric.set_value(str(valid))

    def refresh_connection_widgets(self):
        self.connect_btn.setEnabled(not self.connected and not self.connect_busy)
        self.disconnect_btn.setEnabled(self.connected)
        if self.connect_busy:
            self.conn_banner.show_message("info", f"Opening serial port {self.port_combo.currentText().strip()}...")
            self.conn_caption.setVisible(False)
        elif self.connected:
            ok, msg = self.connection_guard()
            if ok:
                self.conn_banner.show_message("success", "Status: Connected")
            else:
                self.conn_banner.show_message("warning", "Status: Connected with previous settings. " + msg)
            key = self.client_key
            if key:
                text = (f"Connected with: {key[0]}, {key[1]} baud, {key[2]} data bits, "
                        f"parity {key[3]}, {key[4]} stop bit(s), timeout {key[5]} ms")
                if self.conn_caption.text() != text:
                    self.conn_caption.setText(text)
                self.conn_caption.setVisible(True)
        else:
            if self.conn_message:
                self.conn_banner.show_message(*self.conn_message)
            else:
                self.conn_banner.show_message("info", "Status: Not connected")
            self.conn_caption.setVisible(False)

    def refresh_read_tab(self):
        self.read_btn.setEnabled(not self.read_busy)
        self.start_poll_btn.setEnabled(not self.auto_poll)
        self.stop_poll_btn.setEnabled(self.auto_poll)

        with RT.lock:
            status_text = str(RT.read_status)
            version = RT.data_version
            shown_signature = RT.data_signature
            has_rows = bool(RT.data)
            rows = sorted(RT.data.items()) if version != self._data_ver else None
        if rows is not None:
            self._data_ver = version
            self.read_model.set_rows(rows)

        low = status_text.lower()
        if "error" in low or "failed" in low:
            self.read_status_banner.show_message("error", status_text)
        elif "partial" in low or "waiting" in low:
            self.read_status_banner.show_message("warning", status_text)
        else:
            self.read_status_banner.clear_banner()

        if not has_rows:
            self.read_table_banner.show_message(
                "info", "No data read yet. Connect to a device, configure the request, then click Read.")
        elif (not self.auto_poll and shown_signature is not None
              and shown_signature != self.current_read_signature()):
            self.read_table_banner.show_message(
                "warning", "Read settings changed since this table was read. Press Read to refresh it.")
        else:
            self.read_table_banner.clear_banner()

    def refresh_write_tab(self):
        self.send_write_btn.setEnabled(not self.write_busy)

    @staticmethod
    def _set_plain_text_keep_scroll(edit, text):
        bar = edit.verticalScrollBar()
        pos = bar.value()
        edit.setPlainText(text)
        bar.setValue(pos)

    def refresh_logs(self):
        with RT.lock:
            log_ver, raw_ver = RT.log_version, RT.raw_version
            log_lines = list(RT.spy_log[-300:]) if log_ver != self._log_ver else None
            raw_lines = list(RT.raw_log[-300:]) if raw_ver != self._raw_ver else None
        if log_lines is not None:
            self._log_ver = log_ver
            self._set_plain_text_keep_scroll(self.log_view, "\n".join(reversed(log_lines)))
        if raw_lines is not None:
            self._raw_ver = raw_ver
            self._set_plain_text_keep_scroll(self.spy_view, "\n".join(reversed(raw_lines)))

    def refresh_save_error(self):
        text = f"⚠️ Could not save settings file: {self.save_error}" if self.save_error else ""
        if self.save_error_label.text() != text:
            self.save_error_label.setText(text)
            self.save_error_label.setVisible(bool(text))

    def refresh_all(self):
        self.refresh_top_status()
        self.refresh_connection_widgets()
        self.refresh_read_tab()
        self.refresh_write_tab()
        self.refresh_logs()
        self.refresh_save_error()

    # --------------------------------------------------------
    # Shutdown
    # --------------------------------------------------------
    def closeEvent(self, event):
        try:
            self.save_state_now()
            self._save_tag_config(False)
        finally:
            POLLER.shutdown()
            client = self.client
            self.client = None
            if client is not None:
                got = MODBUS_LOCK.acquire(timeout=1.5)
                try:
                    client.close()
                except Exception:
                    pass
                finally:
                    if got:
                        MODBUS_LOCK.release()
        super().closeEvent(event)


# ============================================================
# ENTRY POINT
# ============================================================


def main():
    app = QApplication(sys.argv)
    app.setApplicationName("Modbus Tester")
    app.setStyle("Fusion")
    app.setWindowIcon(QIcon("icon.ico"))
    try:  # Qt 6.8+: keep the light theme even when the OS is in dark mode
        app.styleHints().setColorScheme(Qt.ColorScheme.Light)
    except Exception:
        pass
    apply_light_palette(app)
    app.setStyleSheet(STYLESHEET)
    window = MainWindow()
    window.show()
    sys.exit(app.exec())



if __name__ == "__main__":
    main()
