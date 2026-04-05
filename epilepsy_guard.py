"""
EpilepsyGuard -- Full-screen flash detection and protection

Continuously monitors all screens for rapid luminance changes that may trigger
photosensitive epilepsy, and covers all displays with a dark click-through
overlay when flashing is detected.

Uses DXGI Desktop Duplication (via dxcam) for screen capture — captures
hardware-accelerated video (Chrome, Edge, games) that GDI/mss cannot see.

Uses a pure Win32 layered overlay for dimming and the Windows Magnification API
for system-wide colour desaturation — both effects fade in/out smoothly.

Additional colour correction features:
  - Ambient saturation adjustment (greyscale ↔ vivid)
  - Lighten darks (raises black point to reduce harsh contrasts)
  - Dim lights (lowers white point to reduce glare)
  - Detection grid overlay (shows the configurable NxN flash-detection blocks live)

Based on WCAG 2.3.1: content should not flash more than 3 times per second.

Usage:
    python epilepsy_guard.py

Requirements:
    pip install dxcam numpy pystray Pillow
"""

import base64
import io
import json
import os
import pathlib
import sys
import time
import threading
import collections
import ctypes
import ctypes.wintypes
import tkinter as tk
from tkinter import font as tkfont
import numpy as np
import dxcam
import atexit
import pystray
from PIL import Image, ImageDraw


# ── Settings ───────────────────────────────────────────────────────────────────

_DEFAULTS: dict = {
    "overlay_alpha":           220,    # Overlay opacity when protecting (0–255)
    "fade_in_duration":        0.15,   # Seconds to fade overlay IN on trigger
    "fade_duration":           0.60,   # Seconds to fade overlay OUT after flashing stops
    "desaturate_level":        0.85,   # Colour mute depth: 0 = none, 1 = full greyscale
    "filter_always_on":        False,  # Apply colour mute at all times (not just during protection)
    "overlay_always_on":       False,  # Keep dark overlay visible at all times
    "flash_threshold_pct":     10.0,   # Min luminance change (%) to count as a transition
    "min_flash_blocks":        8,      # Blocks that must reverse simultaneously per frame
    "cooldown_sec":            1.5,    # Overlay stays up this many seconds after last flash
    "ambient_saturation":      0.0,    # −1=greyscale, 0=normal, +1=vivid
    "lighten_darks":           0.0,    # 0–0.10, raises black point
    "dim_lights":              0.0,    # 0–0.5, lowers white point
    "show_grid":               False,  # Show detection block grid overlay
    "block_grid":              10,     # Grid dimension N (NxN blocks); 4–20
    "color_flash_sensitivity": 0.0,    # 0=disabled; 5–30% threshold for colour-channel reversals
    "capture_fps":             30,     # Max frames analysed per second (lower = less CPU)
    "tint_red":                1.0,    # Red channel multiplier   (1=normal, 0=fully removed)
    "tint_green":              1.0,    # Green channel multiplier
    "tint_blue":               1.0,    # Blue channel multiplier
    "enabled_monitors":        [0],    # list of _MONITOR_LIST indices to detect on
}

cfg: dict = dict(_DEFAULTS)

# Exe/script directory — used as fallback data directory if the system-drive
# folder can't be created.
_BASE_DIR = pathlib.Path(sys.executable if getattr(sys, "frozen", False) else __file__).parent

# Settings and presets live in a fixed folder on the system drive so they are
# easy for users to find, edit, and back up — regardless of where the exe is.
# Falls back to the exe directory if the system drive folder can't be created
# (e.g. running without write permission to the root).
_system_drive  = os.environ.get("SystemDrive", "C:")          # e.g. "C:"
_DATA_DIR      = pathlib.Path(_system_drive + "\\") / "EpilepsyGuard"
try:
    _DATA_DIR.mkdir(parents=True, exist_ok=True)
except OSError:
    _DATA_DIR  = _BASE_DIR   # fallback: next to the exe
_SETTINGS_FILE = _DATA_DIR / "epilepsy_guard_settings.json"
_PRESETS_FILE  = _DATA_DIR / "epilepsy_guard_presets.json"


# Icon embedded as base64 ICO (16/32/48/64/128/256 px sizes).
# Baked in at build time via: python epilepsy_guard.py --embed-icon myicon.png
# The embedded constant is always used — no file-based override.
_ICON_B64 = (
    "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"
)


def _load_or_create_icon(size: int = 64) -> Image.Image:
    """Return the app icon as a PIL Image decoded from the embedded constant."""
    ico_data = base64.b64decode(_ICON_B64.replace(" ", "").replace("\n", ""))
    return Image.open(io.BytesIO(ico_data)).resize((size, size), Image.LANCZOS).convert("RGBA")


def _icon_to_photoimage(img: Image.Image, size: int = 32) -> tk.PhotoImage:
    """Convert a PIL Image to a tk.PhotoImage (no ImageTk needed)."""
    buf = io.BytesIO()
    img.resize((size, size), Image.LANCZOS).save(buf, format="PNG")
    return tk.PhotoImage(data=base64.b64encode(buf.getvalue()).decode())


def _load_settings() -> None:
    try:
        data = json.loads(_SETTINGS_FILE.read_text())
        for k, v in data.items():
            if k in cfg:
                cfg[k] = type(_DEFAULTS[k])(v)
    except Exception:
        pass


def _save_settings() -> None:
    _SETTINGS_FILE.write_text(json.dumps(cfg, indent=2))


# ── Fixed constants (not exposed in settings) ──────────────────────────────────

MAX_FLASHES_PER_SEC = 3    # WCAG 2.3.1 threshold — do not change
DOWNSAMPLE          = 16   # Pixel stride when sampling frames


def _enum_monitors() -> list:
    """
    Enumerate all DXGI outputs as (device_idx, output_idx, label) tuples.
    Called once in main() to populate _MONITOR_LIST.
    Returns at least [(0, 0, 'Monitor 1 (primary)')] so the rest of the code
    always has a usable entry even when DXGI is temporarily blocked.
    """
    results = []
    n_dev = 1
    try:
        n_dev = max(1, len(dxcam.device_info()))
    except Exception:
        pass
    mon_num = 0
    for d in range(n_dev):
        for o in range(16):
            try:
                cam = dxcam.create(device_idx=d, output_idx=o,
                                   processor_backend="numpy")
                del cam
                suffix = " (primary)" if mon_num == 0 else ""
                results.append((d, o, f"Monitor {mon_num + 1}{suffix}"))
                mon_num += 1
            except Exception:
                break   # no more outputs on this device
    if not results:
        results = [(0, 0, "Monitor 1 (primary)")]
    return results


_MONITOR_LIST: list = []   # populated in main() via _enum_monitors()


# ── Win32 helpers ──────────────────────────────────────────────────────────────

_user32   = ctypes.windll.user32
_kernel32 = ctypes.windll.kernel32
_gdi32    = ctypes.windll.gdi32

_WNDPROC = ctypes.WINFUNCTYPE(
    ctypes.c_ssize_t,
    ctypes.wintypes.HWND,
    ctypes.c_uint,
    ctypes.c_size_t,
    ctypes.c_ssize_t,
)
_user32.DefWindowProcW.restype  = ctypes.c_ssize_t
_user32.DefWindowProcW.argtypes = [
    ctypes.wintypes.HWND, ctypes.c_uint, ctypes.c_size_t, ctypes.c_ssize_t,
]

_user32.GetWindowLongPtrW.restype  = ctypes.c_ssize_t
_user32.GetWindowLongPtrW.argtypes = [ctypes.wintypes.HWND, ctypes.c_int]

_user32.SetWindowLongPtrW.restype  = ctypes.c_ssize_t
_user32.SetWindowLongPtrW.argtypes = [ctypes.wintypes.HWND, ctypes.c_int, ctypes.c_ssize_t]

_user32.SetWindowPos.restype  = ctypes.wintypes.BOOL
_user32.SetWindowPos.argtypes = [
    ctypes.wintypes.HWND, ctypes.c_ssize_t,   # c_ssize_t allows HWND_TOPMOST (-1)
    ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
    ctypes.c_uint,
]

_user32.InvalidateRect.restype  = ctypes.wintypes.BOOL
_user32.InvalidateRect.argtypes = [ctypes.wintypes.HWND, ctypes.c_void_p, ctypes.wintypes.BOOL]

_user32.BeginPaint.restype  = ctypes.wintypes.HDC
_user32.EndPaint.restype    = ctypes.wintypes.BOOL
_user32.FillRect.restype    = ctypes.c_int

_gdi32.CreateSolidBrush.restype = ctypes.wintypes.HANDLE
_gdi32.CreateSolidBrush.argtypes = [ctypes.wintypes.DWORD]
_gdi32.CreatePen.restype    = ctypes.wintypes.HANDLE
_gdi32.CreatePen.argtypes   = [ctypes.c_int, ctypes.c_int, ctypes.wintypes.DWORD]
_gdi32.SelectObject.restype = ctypes.wintypes.HANDLE
_gdi32.SelectObject.argtypes = [ctypes.wintypes.HDC, ctypes.wintypes.HANDLE]
_gdi32.DeleteObject.restype = ctypes.wintypes.BOOL
_gdi32.DeleteObject.argtypes = [ctypes.wintypes.HANDLE]
_gdi32.Rectangle.restype    = ctypes.wintypes.BOOL
_gdi32.Rectangle.argtypes   = [ctypes.wintypes.HDC,
                                ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int]

class _PAINTSTRUCT(ctypes.Structure):
    _fields_ = [
        ("hdc",         ctypes.wintypes.HDC),
        ("fErase",      ctypes.wintypes.BOOL),
        ("rcPaint",     ctypes.wintypes.RECT),
        ("fRestore",    ctypes.wintypes.BOOL),
        ("fIncUpdate",  ctypes.wintypes.BOOL),
        ("rgbReserved", ctypes.c_byte * 32),
    ]

_user32.BeginPaint.argtypes  = [ctypes.wintypes.HWND, ctypes.POINTER(_PAINTSTRUCT)]
_user32.EndPaint.argtypes    = [ctypes.wintypes.HWND, ctypes.POINTER(_PAINTSTRUCT)]
_user32.FillRect.argtypes    = [ctypes.wintypes.HDC,
                                 ctypes.POINTER(ctypes.wintypes.RECT), ctypes.wintypes.HANDLE]


class _WNDCLASSEXW(ctypes.Structure):
    _fields_ = [
        ("cbSize",        ctypes.c_uint),
        ("style",         ctypes.c_uint),
        ("lpfnWndProc",   _WNDPROC),
        ("cbClsExtra",    ctypes.c_int),
        ("cbWndExtra",    ctypes.c_int),
        ("hInstance",     ctypes.wintypes.HANDLE),
        ("hIcon",         ctypes.wintypes.HANDLE),
        ("hCursor",       ctypes.wintypes.HANDLE),
        ("hbrBackground", ctypes.wintypes.HANDLE),
        ("lpszMenuName",  ctypes.wintypes.LPCWSTR),
        ("lpszClassName", ctypes.wintypes.LPCWSTR),
        ("hIconSm",       ctypes.wintypes.HANDLE),
    ]

class _MSG(ctypes.Structure):
    _fields_ = [
        ("hwnd",    ctypes.wintypes.HWND),
        ("message", ctypes.c_uint),
        ("wParam",  ctypes.wintypes.WPARAM),
        ("lParam",  ctypes.wintypes.LPARAM),
        ("time",    ctypes.c_uint),
        ("pt",      ctypes.wintypes.POINT),
    ]


# ── Colour filter (Magnification API) ─────────────────────────────────────────

class _MAGCOLOREFFECT(ctypes.Structure):
    _fields_ = [("transform", ctypes.c_float * 25)]


def _build_full_matrix(
    desat: float,
    ambient_sat: float,
    lighten_darks: float,
    dim_lights: float,
    tint_r: float = 1.0,
    tint_g: float = 1.0,
    tint_b: float = 1.0,
) -> _MAGCOLOREFFECT:
    """
    Build a 5×5 Magnification colour effect matrix combining:
      - desaturation (desat) and ambient saturation boost/cut (ambient_sat)
      - brightness scaling via dim_lights (lowers white point)
      - black-point raising via lighten_darks
      - per-channel tint (tint_r/g/b): 1.0 = normal, 0.0 = channel fully removed

    The matrix is column-major: column k = how input channel k contributes to
    each output channel.  Row 0 → R output, row 1 → G output, row 2 → B output.
    Multiplying every element of an output row by its tint factor scales that
    channel uniformly without disturbing the saturation or brightness maths.
    """
    t  = max(-2.0, min(2.0, desat - ambient_sat * (1.0 - desat)))
    s  = max(0.0, 1.0 - dim_lights)
    cr = max(0.0, min(1.0, tint_r))
    cg = max(0.0, min(1.0, tint_g))
    cb = max(0.0, min(1.0, tint_b))

    e = _MAGCOLOREFFECT()
    m = e.transform

    # Saturation formula × brightness scale × channel tint
    # Row 0 (R output) — multiply every coefficient by cr
    m[0]  = (1.0 - 0.701 * t) * s * cr
    m[5]  = 0.587 * t * s * cr
    m[10] = 0.114 * t * s * cr
    # Row 1 (G output) — multiply every coefficient by cg
    m[1]  = 0.299 * t * s * cg
    m[6]  = (1.0 - 0.413 * t) * s * cg
    m[11] = 0.114 * t * s * cg
    # Row 2 (B output) — multiply every coefficient by cb
    m[2]  = 0.299 * t * s * cb
    m[7]  = 0.587 * t * s * cb
    m[12] = (1.0 - 0.886 * t) * s * cb

    # Alpha passthrough
    m[18] = 1.0
    m[24] = 1.0

    # Brightness offset (lighten darks) — also tinted per channel
    m[20] = lighten_darks * cr
    m[21] = lighten_darks * cg
    m[22] = lighten_darks * cb

    return e


def _clear_color_filter() -> None:
    """Write identity 5×5 matrix to reset the colour filter on exit."""
    if _mag_ok:
        e = _MAGCOLOREFFECT()
        m = e.transform
        m[0]  = 1.0
        m[6]  = 1.0
        m[12] = 1.0
        m[18] = 1.0
        m[24] = 1.0
        _mag.MagSetFullscreenColorEffect(ctypes.byref(e))


_mag_ok = False
try:
    _mag = ctypes.windll.magnification
    if _mag.MagInitialize():
        _mag.MagSetFullscreenColorEffect.argtypes = [ctypes.POINTER(_MAGCOLOREFFECT)]
        _mag.MagSetFullscreenColorEffect.restype  = ctypes.c_bool
        _mag_ok = True
    else:
        print("[info] MagInitialize failed — colour filter disabled")
except Exception as exc:
    _mag = None
    print(f"[info] Magnification API unavailable ({exc}) — colour filter disabled")


def apply_color_filter(protection_level: float = 0.0) -> None:
    """
    Apply the combined colour matrix system-wide.

    protection_level is the current desaturation amount (0=identity, 1=greyscale)
    driven by the dimmer fade.  Ambient saturation, lighten_darks, and dim_lights
    are read directly from cfg.
    """
    if _mag_ok:
        effect = _build_full_matrix(
            desat=protection_level,
            ambient_sat=cfg["ambient_saturation"],
            lighten_darks=cfg["lighten_darks"],
            dim_lights=cfg["dim_lights"],
            tint_r=cfg["tint_red"],
            tint_g=cfg["tint_green"],
            tint_b=cfg["tint_blue"],
        )
        _mag.MagSetFullscreenColorEffect(ctypes.byref(effect))


# ── Grid Overlay ───────────────────────────────────────────────────────────────

class GridOverlay:
    """
    Pure Win32 click-through window that draws the configurable NxN detection block grid.
    Created with WS_EX_TRANSPARENT at CreateWindowExW time (same as OverlayDimmer)
    so input passes through immediately — no Tkinter involvement.
    GDI paints the blocks; InvalidateRect triggers redraws from any thread.
    """

    _CLASS            = "EpilepsyGuardGrid"
    _WS_POPUP         = 0x80000000
    _WS_EX_LAYERED    = 0x00080000
    _WS_EX_TRANSPARENT= 0x00000020
    _WS_EX_NOACTIVATE = 0x08000000
    _WS_EX_TOPMOST    = 0x00000008
    _WS_EX_TOOLWINDOW = 0x00000080
    _LWA_COLORKEY     = 0x00000001
    _SW_SHOW          = 5
    _SW_HIDE          = 0
    _WM_DESTROY       = 2
    _WM_PAINT         = 0x000F

    # COLORREF = 0x00BBGGRR
    _KEY_COLOR      = 0x0000FF00   # transparent green (R=0, G=255, B=0)
    _COLOR_REVERSAL = 0x000022CC   # #CC2200 red-orange  (R=204, G=34,  B=0)
    _COLOR_ACTIVE   = 0x000088FF   # #FF8800 orange      (R=255, G=136, B=0)
    _COLOR_OUTLINE  = 0x00888888   # grey

    def __init__(self):
        g = cfg["block_grid"]
        n = g * g
        self._lock        = threading.Lock()
        self._significant = np.zeros(n, dtype=bool)
        self._reversals   = np.zeros(n, dtype=bool)
        self._grid_size   = g
        self._hwnd      = None
        self._visible   = False
        self._pw        = 0
        self._ph        = 0
        # Pre-created GDI objects (created in _run on the Win32 thread)
        self._brush_key      = None
        self._brush_reversal = None
        self._brush_active   = None
        self._pen_outline    = None
        self._brush_null     = None
        self._ready  = threading.Event()
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()
        self._ready.wait(timeout=5)

    def _wnd_proc(self, hwnd, msg, wparam, lparam):
        if msg == self._WM_PAINT:
            self._paint(hwnd)
            return 0
        if msg == self._WM_DESTROY:
            _user32.PostQuitMessage(0)
            return 0
        return _user32.DefWindowProcW(hwnd, msg, wparam, lparam)

    def _paint(self, hwnd):
        ps  = _PAINTSTRUCT()
        hdc = _user32.BeginPaint(hwnd, ctypes.byref(ps))

        # Snapshot block state and current grid size under lock
        with self._lock:
            grid        = self._grid_size
            significant = self._significant.copy()
            reversals   = self._reversals.copy()

        bw = self._pw // grid
        bh = self._ph // grid

        # Clear background to key colour (transparent)
        rc = ctypes.wintypes.RECT(0, 0, self._pw, self._ph)
        _user32.FillRect(hdc, ctypes.byref(rc), self._brush_key)

        # Single-pass: draw each block's fill + outline together.
        # SelectObject is only called when the brush actually changes between
        # consecutive blocks, minimising GDI round-trips.
        old_pen   = _gdi32.SelectObject(hdc, self._pen_outline)
        old_brush = _gdi32.SelectObject(hdc, self._brush_null)
        cur_brush = self._brush_null

        for row in range(grid):
            y0 = row * bh
            y1 = y0 + bh
            for col in range(grid):
                idx = row * grid + col
                if reversals[idx]:
                    b = self._brush_reversal
                elif significant[idx]:
                    b = self._brush_active
                else:
                    b = self._brush_null
                if b is not cur_brush:
                    _gdi32.SelectObject(hdc, b)
                    cur_brush = b
                _gdi32.Rectangle(hdc, col * bw, y0, col * bw + bw, y1)

        _gdi32.SelectObject(hdc, old_brush)
        _gdi32.SelectObject(hdc, old_pen)
        _user32.EndPaint(hwnd, ctypes.byref(ps))

    def _run(self):
        hinstance  = _kernel32.GetModuleHandleW(None)
        self._proc = _WNDPROC(self._wnd_proc)

        wc = _WNDCLASSEXW()
        wc.cbSize        = ctypes.sizeof(_WNDCLASSEXW)
        wc.lpfnWndProc   = self._proc
        wc.hInstance     = hinstance
        wc.hbrBackground = 0   # we paint manually in WM_PAINT
        wc.lpszClassName = self._CLASS
        _user32.RegisterClassExW(ctypes.byref(wc))

        # Span the full virtual desktop so the grid covers all monitors
        _vx = _user32.GetSystemMetrics(76)
        _vy = _user32.GetSystemMetrics(77)
        self._pw = _user32.GetSystemMetrics(78)
        self._ph = _user32.GetSystemMetrics(79)

        hwnd = _user32.CreateWindowExW(
            self._WS_EX_LAYERED | self._WS_EX_TRANSPARENT
            | self._WS_EX_NOACTIVATE | self._WS_EX_TOPMOST | self._WS_EX_TOOLWINDOW,
            self._CLASS, None, self._WS_POPUP,
            _vx, _vy, self._pw, self._ph,
            None, None, hinstance, None,
        )
        _user32.SetLayeredWindowAttributes(hwnd, self._KEY_COLOR, 0, self._LWA_COLORKEY)

        # Pre-create GDI objects once on this thread
        self._brush_key      = _gdi32.CreateSolidBrush(self._KEY_COLOR)
        self._brush_reversal = _gdi32.CreateSolidBrush(self._COLOR_REVERSAL)
        self._brush_active   = _gdi32.CreateSolidBrush(self._COLOR_ACTIVE)
        self._pen_outline    = _gdi32.CreatePen(0, 1, self._COLOR_OUTLINE)
        self._brush_null     = _gdi32.GetStockObject(5)   # NULL_BRUSH

        self._hwnd = hwnd
        self._ready.set()

        msg = _MSG()
        while _user32.GetMessageW(ctypes.byref(msg), None, 0, 0) != 0:
            _user32.TranslateMessage(ctypes.byref(msg))
            _user32.DispatchMessageW(ctypes.byref(msg))

        _gdi32.DeleteObject(self._brush_key)
        _gdi32.DeleteObject(self._brush_reversal)
        _gdi32.DeleteObject(self._brush_active)
        _gdi32.DeleteObject(self._pen_outline)

    def show(self):
        if self._hwnd:
            _user32.ShowWindow(self._hwnd, self._SW_SHOW)
            self._visible = True

    def hide(self):
        if self._hwnd:
            _user32.ShowWindow(self._hwnd, self._SW_HIDE)
            self._visible = False

    def update_blocks(self, significant: np.ndarray, reversals: np.ndarray) -> None:
        """Update block state and post a repaint (thread-safe, non-blocking)."""
        n = len(significant)
        with self._lock:
            if len(self._significant) != n:
                self._significant = np.zeros(n, dtype=bool)
                self._reversals   = np.zeros(n, dtype=bool)
                self._grid_size   = cfg["block_grid"]
            np.copyto(self._significant, significant)
            np.copyto(self._reversals, reversals)
        if self._hwnd and self._visible:
            _user32.InvalidateRect(self._hwnd, None, False)


# ── Overlay Dimmer ─────────────────────────────────────────────────────────────

class OverlayDimmer:
    """
    Full-screen click-through black overlay (Win32 native window) combined with
    a Magnification API colour desaturation filter.  Both effects fade in/out
    in sync.  All styles are set at CreateWindowEx time so Tkinter never
    steals focus or intercepts input.
    """

    _CLASS            = "EpilepsyGuardOverlay"
    _WS_POPUP         = 0x80000000
    _WS_EX_LAYERED    = 0x00080000
    _WS_EX_TRANSPARENT= 0x00000020
    _WS_EX_NOACTIVATE = 0x08000000
    _WS_EX_TOPMOST    = 0x00000008
    _WS_EX_TOOLWINDOW = 0x00000080
    _LWA_ALPHA        = 0x00000002
    _BLACK_BRUSH      = 4
    _SW_SHOW          = 5
    _SW_HIDE          = 0
    _WM_DESTROY       = 2

    def __init__(self):
        self.active         = False
        self._hwnd          = None
        self._fade_state    = None   # None | "in" | "out"
        self.current_alpha  = 0
        self._current_desat = 0.0
        self._ready         = threading.Event()
        self._thread        = threading.Thread(target=self._run, daemon=True)
        self._thread.start()
        self._ready.wait(timeout=5)
        atexit.register(self.reset_instantly)

    def _wnd_proc(self, hwnd, msg, wparam: int, lparam: int):
        if msg == self._WM_DESTROY:
            _user32.PostQuitMessage(0)
            return 0
        return _user32.DefWindowProcW(hwnd, msg, wparam, lparam)

    def _run(self):
        hinstance  = _kernel32.GetModuleHandleW(None)
        self._proc = _WNDPROC(self._wnd_proc)

        wc = _WNDCLASSEXW()
        wc.cbSize        = ctypes.sizeof(_WNDCLASSEXW)
        wc.lpfnWndProc   = self._proc
        wc.hInstance     = hinstance
        wc.hbrBackground = _gdi32.GetStockObject(self._BLACK_BRUSH)
        wc.lpszClassName = self._CLASS
        _user32.RegisterClassExW(ctypes.byref(wc))

        vx = _user32.GetSystemMetrics(76)
        vy = _user32.GetSystemMetrics(77)
        vw = _user32.GetSystemMetrics(78)
        vh = _user32.GetSystemMetrics(79)

        hwnd = _user32.CreateWindowExW(
            self._WS_EX_LAYERED | self._WS_EX_TRANSPARENT
            | self._WS_EX_NOACTIVATE | self._WS_EX_TOPMOST | self._WS_EX_TOOLWINDOW,
            self._CLASS, None, self._WS_POPUP,
            vx, vy, vw, vh,
            None, None, hinstance, None,
        )
        _user32.SetLayeredWindowAttributes(hwnd, 0, cfg["overlay_alpha"], self._LWA_ALPHA)
        self._hwnd = hwnd
        self._ready.set()

        msg = _MSG()
        while _user32.GetMessageW(ctypes.byref(msg), None, 0, 0) != 0:
            _user32.TranslateMessage(ctypes.byref(msg))
            _user32.DispatchMessageW(ctypes.byref(msg))

    # ── public interface ────────────────────────────────────────────────────────

    def dim(self):
        self.active = True
        if self._fade_state == "out":
            # Flash re-triggered during fade-out — cancel the fade and snap
            # immediately back to full protection so the user never sees a dip.
            # Setting _fade_state != "out" causes the _fade_out thread to exit
            # on its next iteration check; the two Win32 calls here win the race
            # because SetLayeredWindowAttributes is virtually instant.
            self._fade_state    = None
            self.current_alpha  = cfg["overlay_alpha"]
            self._current_desat = cfg["desaturate_level"]
            _user32.SetLayeredWindowAttributes(
                self._hwnd, 0, cfg["overlay_alpha"], self._LWA_ALPHA
            )
            apply_color_filter(cfg["desaturate_level"])
        else:
            self._fade_state = "in"
            threading.Thread(target=self._fade_in, daemon=True).start()

    def restore(self):
        self.active      = False
        self._fade_state = "out"
        threading.Thread(target=self._fade_out, daemon=True).start()

    def desaturate_only(self):
        """
        Instantly apply full desaturation + show a half-brightness overlay for
        colour-only flashes.  Desaturation collapses hue cycling to grey;
        the overlay gives visible feedback and acts as a fallback if the
        Magnification API is unavailable (e.g. exclusive-fullscreen games).
        restore() / _fade_out handles the fade-out for both effects.
        """
        self.active         = True
        self._fade_state    = None
        self._current_desat = cfg["desaturate_level"]
        self.current_alpha  = max(30, cfg["overlay_alpha"] // 2)
        apply_color_filter(self._current_desat)
        _user32.SetLayeredWindowAttributes(
            self._hwnd, 0, self.current_alpha, self._LWA_ALPHA
        )
        _user32.ShowWindow(self._hwnd, self._SW_SHOW)

    def reset_instantly(self):
        """Immediately hide overlay and reset colour filter — used on quit/pause."""
        self._fade_state    = None
        self.current_alpha  = 0
        self._current_desat = 0.0
        if self._hwnd:
            _user32.ShowWindow(self._hwnd, self._SW_HIDE)
        target = cfg["desaturate_level"] if cfg["filter_always_on"] else 0.0
        apply_color_filter(target)

    # ── fades ───────────────────────────────────────────────────────────────────

    def _fade_in(self):
        steps      = 20
        step_time  = cfg["fade_in_duration"] / steps
        alpha      = float(self.current_alpha)
        # When filter_always_on is active the Mag API is already at desaturate_level
        # even though _current_desat may still be 0 (no fade has run yet this session).
        # Start from whichever is higher so we never momentarily drop the colour filter.
        always_on  = cfg["desaturate_level"] if cfg["filter_always_on"] else 0.0
        desat      = max(self._current_desat, always_on)
        alpha_step = cfg["overlay_alpha"] / steps
        desat_step = cfg["desaturate_level"] / steps

        _user32.ShowWindow(self._hwnd, self._SW_SHOW)

        for _ in range(steps):
            if self._fade_state != "in":
                return
            alpha = min(float(cfg["overlay_alpha"]), alpha + alpha_step)
            desat = min(cfg["desaturate_level"],      desat + desat_step)
            self.current_alpha   = int(alpha)
            self._current_desat  = desat
            _user32.SetLayeredWindowAttributes(self._hwnd, 0, int(alpha), self._LWA_ALPHA)
            apply_color_filter(desat)
            time.sleep(step_time)

        if self._fade_state == "in":
            self.current_alpha  = cfg["overlay_alpha"]
            self._current_desat = cfg["desaturate_level"]
            self._fade_state    = None

    def show_always_on(self):
        """Show overlay at full protection alpha for always-on mode."""
        _user32.SetLayeredWindowAttributes(self._hwnd, 0, cfg["overlay_alpha"], self._LWA_ALPHA)
        self.current_alpha = cfg["overlay_alpha"]
        _user32.ShowWindow(self._hwnd, self._SW_SHOW)

    def hide_always_on(self):
        """Hide overlay — called when overlay_always_on is toggled off and not protecting."""
        if not self.active:
            _user32.ShowWindow(self._hwnd, self._SW_HIDE)
            self.current_alpha = 0

    def _fade_out(self):
        steps      = 40
        step_time  = cfg["fade_duration"] / steps
        alpha      = float(self.current_alpha)
        desat      = self._current_desat
        alpha_step = cfg["overlay_alpha"] / steps
        desat_step = cfg["desaturate_level"] / steps

        for _ in range(steps):
            if self._fade_state != "out":
                return
            if not cfg["overlay_always_on"]:
                alpha = max(0.0, alpha - alpha_step)
                self.current_alpha = int(alpha)
                _user32.SetLayeredWindowAttributes(self._hwnd, 0, int(alpha), self._LWA_ALPHA)
            desat = max(0.0, desat - desat_step)
            self._current_desat = desat
            apply_color_filter(desat)
            time.sleep(step_time)

        if self._fade_state == "out":
            if cfg["overlay_always_on"]:
                # Keep overlay visible at full alpha; only desaturation was faded out.
                self.current_alpha = cfg["overlay_alpha"]
                _user32.SetLayeredWindowAttributes(
                    self._hwnd, 0, cfg["overlay_alpha"], self._LWA_ALPHA
                )
            else:
                _user32.ShowWindow(self._hwnd, self._SW_HIDE)
                self.current_alpha = 0
                _user32.SetLayeredWindowAttributes(
                    self._hwnd, 0, cfg["overlay_alpha"], self._LWA_ALPHA
                )
            # Restore to always-on level if enabled, otherwise clear
            target_desat = cfg["desaturate_level"] if cfg["filter_always_on"] else 0.0
            apply_color_filter(target_desat)
            # Keep _current_desat in sync so _fade_in starts from the right level
            # if protection re-triggers immediately after this fade completes.
            self._current_desat = target_desat
            self._fade_state = None


# ── Flash Detector ─────────────────────────────────────────────────────────────

class FlashDetector:
    """
    Detects rapid luminance (and optionally colour) flashes using a configurable NxN block grid.

    A flash event is recorded per frame only when cfg["min_flash_blocks"] or
    more blocks reverse luminance direction simultaneously — filters out
    single-window drags while catching large-area strobes.

    Early trigger: if two consecutive frame-level flashes occur within
    1/MAX_FLASHES_PER_SEC seconds, triggers immediately.
    """

    _LUMA = np.array([0.299, 0.587, 0.114], dtype=np.float32)

    def __init__(self):
        g = cfg["block_grid"]
        n = g * g
        self._prev_blocks:     np.ndarray | None = None
        self._prev_rb:         np.ndarray | None = None
        self._prev_gm:         np.ndarray | None = None
        self._block_dirs       = np.zeros(n, dtype=np.int8)
        self._rb_dirs          = np.zeros(n, dtype=np.int8)
        self._gm_dirs          = np.zeros(n, dtype=np.int8)
        self._decay_count      = np.zeros(n, dtype=np.uint8)
        self._last_reversals   = np.zeros(n, dtype=bool)
        self._last_significant = np.zeros(n, dtype=bool)
        self._flash_times:          collections.deque = collections.deque()
        self._last_frame_flash_time: float = 0.0
        self._last_flash_color_only: bool  = False
        # Persistent per-frame buffers (allocated on first frame, reused every frame)
        self._small_buf: np.ndarray | None = None   # (sh, sw, 3) float32 — only used when color detection is on
        self._luma_buf:  np.ndarray | None = None   # (sh, sw) float32
        self._chan_buf:  np.ndarray | None = None   # (sh, sw) float32 — scratch for luma-only fast path
        # Cached overlay correction factor — avoids a float division every frame
        self._overlay_alpha_last: int   = -1
        self._overlay_scale:      float = 1.0
        # Grid-aligned geometry cache
        self._h  = 0;  self._w  = 0
        self._bh = 0;  self._bw = 0
        # Cached config values — avoid dict lookups every frame
        self._threshold_px   = cfg["flash_threshold_pct"] * 2.55
        self._min_blocks     = int(cfg["min_flash_blocks"])
        self._color_sens_val = cfg["color_flash_sensitivity"]
        # Scale / offset factors to undo the Magnification API transform.
        # _filter_off is used only in the transition-skip check (false_delta),
        # NOT in _to_blocks() — the offset cancels in consecutive-frame deltas,
        # so no per-frame subtraction is needed once the filter has settled.
        _s = max(1e-4, 1.0 - cfg["dim_lights"])
        _t = max(-2.0, min(2.0, -cfg["ambient_saturation"]))
        self._filter_s   = _s
        self._filter_st  = _s * max(1e-4, 1.0 - _t)
        self._filter_off = cfg["lighten_darks"] * 255.0
        # Snapshot of filter params at last sync; used to detect mid-run changes.
        # Initialised to identity (all zeros) so the very first frame fires the
        # change-detection path and the false_delta skip can handle any startup
        # race between apply_color_filter() and the first dxcam grab.
        self._filter_params: tuple = (0.0, 0.0, 0.0, 0.0)
        # Two-frame skip: after a filter change is detected, skip one extra frame so
        # the "store as prev" frame also has settled correction factors.
        self._skip_next: bool = False

    def reset(self):
        self._skip_next            = False
        self._prev_blocks          = None
        self._prev_rb              = None
        self._prev_gm              = None
        self._block_dirs[:]        = 0
        self._rb_dirs[:]           = 0
        self._gm_dirs[:]           = 0
        self._decay_count[:]       = 0
        self._last_reversals[:]    = False
        self._last_significant[:]  = False
        self._flash_times.clear()
        self._last_frame_flash_time = 0.0

    def soft_reset(self):
        """Clear history but keep direction state for faster re-arm after restore."""
        self._flash_times.clear()
        self._last_frame_flash_time = 0.0
        self._decay_count[:] = 0

    def sync_config(self) -> None:
        """Re-cache config values that are read every frame. Call when settings change."""
        self._threshold_px   = cfg["flash_threshold_pct"] * 2.55
        self._min_blocks     = int(cfg["min_flash_blocks"])
        self._color_sens_val = cfg["color_flash_sensitivity"]
        _s = max(1e-4, 1.0 - cfg["dim_lights"])
        _t = max(-2.0, min(2.0, -cfg["ambient_saturation"]))
        self._filter_s   = _s
        self._filter_st  = _s * max(1e-4, 1.0 - _t)
        self._filter_off = cfg["lighten_darks"] * 255.0
        # NOTE: _filter_params is intentionally NOT updated here.
        # It is only updated inside process() on the loop thread, so that
        # the change-detection check (cur_fp != _filter_params) always fires
        # even when sync_config() is called first from the Tkinter thread.

    def _to_blocks(self, frame: np.ndarray, grid: int, overlay_alpha: int = 0):
        """Return (luma_blocks, rb_blocks, gm_blocks); reuses pre-allocated buffers."""
        raw = frame[::DOWNSAMPLE, ::DOWNSAMPLE]   # (sh, sw, 4) uint8 view — no copy
        sh, sw = raw.shape[:2]

        if self._color_sens_val == 0.0:
            # Luma-only fast path: skip the (sh,sw,3) float32 buffer entirely.
            # Compute luma channel-by-channel directly into pre-allocated buffers,
            # avoiding a full 3-channel copy + matmul.
            if self._luma_buf is None or self._luma_buf.shape[0] != sh:
                self._luma_buf  = np.empty((sh, sw), dtype=np.float32)
                self._chan_buf  = np.empty((sh, sw), dtype=np.float32)
                self._small_buf = None   # release if previously held
                self._h = self._w = self._bh = self._bw = 0
            np.multiply(raw[:, :, 0], self._LUMA[0], out=self._luma_buf)
            np.multiply(raw[:, :, 1], self._LUMA[1], out=self._chan_buf)
            np.add(self._luma_buf, self._chan_buf,    out=self._luma_buf)
            np.multiply(raw[:, :, 2], self._LUMA[2], out=self._chan_buf)
            np.add(self._luma_buf, self._chan_buf,    out=self._luma_buf)
            rb_b = gm_b = None
        else:
            # Full 3-channel path required for colour flash detection.
            if self._small_buf is None or self._small_buf.shape[0] != sh:
                self._small_buf = np.empty((sh, sw, 3), dtype=np.float32)
                self._luma_buf  = np.empty((sh, sw),    dtype=np.float32)
                self._h = self._w = self._bh = self._bw = 0
            self._small_buf[:] = raw[:, :, :3]
            np.matmul(self._small_buf, self._LUMA, out=self._luma_buf)
            rb_b = gm_b = None   # may be overwritten below

        if overlay_alpha > 10:
            # The Mag API applies its colour matrix (including the lighten_darks
            # bias) to the already-composited image — AFTER the overlay has been
            # blended in.  The overlay scale-up (×255/(255-alpha)) then amplifies
            # that bias: a dark frame that should read as 0 reads as ~200 after
            # correction with lighten_darks=0.11, collapsing the detection range.
            # Subtracting the bias BEFORE the scale restores the correct range
            # (dark→0, bright→255) without affecting the no-overlay path.
            if self._filter_off > 0.0:
                np.subtract(self._luma_buf, self._filter_off, out=self._luma_buf)
                np.clip(self._luma_buf, 0.0, 255.0, out=self._luma_buf)
            if overlay_alpha != self._overlay_alpha_last:
                self._overlay_alpha_last = overlay_alpha
                self._overlay_scale      = 255.0 / max(1, 255 - overlay_alpha)
            np.multiply(self._luma_buf, self._overlay_scale, out=self._luma_buf)
            np.clip(self._luma_buf, 0.0, 255.0, out=self._luma_buf)

        # Cache block geometry (recalculated after grid or screen-size change)
        if self._h == 0:
            self._h  = (sh // grid) * grid
            self._w  = (sw // grid) * grid
            self._bh = self._h // grid
            self._bw = self._w // grid

        h, w, bh, bw = self._h, self._w, self._bh, self._bw

        # ascontiguousarray is a no-op when w==sw (the common case for standard
        # resolutions); only copies when w < sw to make the reshape safe.
        luma_crop = np.ascontiguousarray(self._luma_buf[:h, :w])
        luma_b = luma_crop.reshape(grid, bh, grid, bw).mean(axis=(1, 3)).ravel()

        # Undo dim_lights scale so detection thresholds stay relative to
        # the original signal amplitude.  lighten_darks is intentionally not
        # corrected: its offset cancels in consecutive-frame deltas (A+off −
        # B+off = A−B) and cannot be inverted for bright values clipped at 255.
        if self._filter_s != 1.0:
            luma_b = luma_b / self._filter_s

        if self._color_sens_val > 0.0 and self._small_buf is not None:
            px = self._small_buf[:h, :w]
            # Subtraction creates a fresh contiguous array, safe to reshape directly
            rb_b = (px[:, :, 0] - px[:, :, 2]).reshape(grid, bh, grid, bw).mean(axis=(1, 3)).ravel()
            gm_b = (px[:, :, 1] - (px[:, :, 0] + px[:, :, 2]) * 0.5).reshape(grid, bh, grid, bw).mean(axis=(1, 3)).ravel()
            # Color axes scale by s*(1−t) under the Magnification API; undo it
            if self._filter_st != 1.0:
                rb_b = rb_b / self._filter_st
                gm_b = gm_b / self._filter_st

        return luma_b, rb_b, gm_b

    def process(self, frame: np.ndarray, overlay_alpha: int = 0) -> int:
        now  = time.monotonic()
        grid = cfg["block_grid"]
        n    = grid * grid

        # Resize all arrays when grid size changes; also re-sync config cache
        if len(self._block_dirs) != n:
            self._block_dirs       = np.zeros(n, dtype=np.int8)
            self._rb_dirs          = np.zeros(n, dtype=np.int8)
            self._gm_dirs          = np.zeros(n, dtype=np.int8)
            self._decay_count      = np.zeros(n, dtype=np.uint8)
            self._last_reversals   = np.zeros(n, dtype=bool)
            self._last_significant = np.zeros(n, dtype=bool)
            self._prev_blocks = None
            self._prev_rb     = None
            self._prev_gm     = None
            self._h = self._w = self._bh = self._bw = 0
            self.sync_config()

        # Two-frame skip recovery: after a large filter change, skip the "store as
        # prev" frame so the first real comparison uses clean data on both sides.
        if self._skip_next:
            self._skip_next   = False
            self._prev_blocks = None
            self._prev_rb     = None
            self._prev_gm     = None
            return 0

        # Detect ambient-filter parameter changes mid-run.
        # _filter_params starts at identity (0,0,0,0) so this fires on the very
        # first frame and sets up correct correction factors.
        # Worst-case luma artifact when _prev_blocks was captured under the OLD
        # filter but luma_b is captured under the NEW filter:
        #   Δ = (|Δs|×255 + |Δoff|) / new_s
        # A slider step of 0.01 gives Δ ≈ 2.55 (< 25.5 threshold) — no skip.
        # A cold-start or config-load jump of e.g. 0→0.11 gives Δ = 28 → skip.
        cur_fp = (
            cfg["dim_lights"], cfg["lighten_darks"], cfg["ambient_saturation"],
            cfg["desaturate_level"] if cfg["filter_always_on"] else 0.0,
        )
        if cur_fp != self._filter_params:
            old_s   = max(1e-4, 1.0 - self._filter_params[0])
            old_off = self._filter_params[1] * 255.0
            self._filter_params = cur_fp
            self.sync_config()   # updates _filter_s, _filter_off, _filter_st
            false_delta = (abs(old_s - self._filter_s) * 255.0 +
                           abs(self._filter_off - old_off)) / self._filter_s
            if false_delta >= self._threshold_px:
                # Large change — clear history and do the 2-frame skip.
                self._skip_next   = True
                self._prev_blocks = None
                self._prev_rb     = None
                self._prev_gm     = None
                return 0
            # Small change — correction factors updated; fall through and keep
            # detecting.  The tiny delta artifact cancels between consecutive frames.

        luma_b, rb_b, gm_b = self._to_blocks(frame, grid, overlay_alpha)

        any_flash_this_frame = False
        if self._prev_blocks is not None:
            # Use cached config values — no dict lookup in the hot path
            threshold_px = self._threshold_px
            min_blocks   = self._min_blocks
            color_sens   = self._color_sens_val

            deltas      = luma_b - self._prev_blocks
            significant = np.abs(deltas) >= threshold_px
            directions  = np.sign(deltas).astype(np.int8)

            # Reversal must be computed BEFORE block_dirs is updated in-place,
            # because prev_dirs is an alias (reference) not a copy.
            luma_rev = significant & (self._block_dirs != 0) & (directions != self._block_dirs)

            # Direction decay: blocks that haven't changed in ~8 frames reset to 0
            np.add(self._decay_count, np.uint8(1), out=self._decay_count,
                   where=~significant)
            self._decay_count[significant] = 0
            expired = self._decay_count > 8
            np.copyto(self._block_dirs, directions, where=significant)
            np.copyto(self._block_dirs, np.int8(0), where=expired & ~significant)

            # Colour flash detection (R–B and G–M channel reversals)
            if color_sens > 0.0 and rb_b is not None and self._prev_rb is not None:
                col_thresh = color_sens * 2.55
                rb_delta   = rb_b - self._prev_rb
                gm_delta   = gm_b - self._prev_gm
                rb_sig     = np.abs(rb_delta) >= col_thresh
                gm_sig     = np.abs(gm_delta) >= col_thresh
                rb_dirs    = np.sign(rb_delta).astype(np.int8)
                gm_dirs    = np.sign(gm_delta).astype(np.int8)
                rb_rev     = rb_sig & (self._rb_dirs != 0) & (rb_dirs != self._rb_dirs)
                gm_rev     = gm_sig & (self._gm_dirs != 0) & (gm_dirs != self._gm_dirs)
                np.copyto(self._rb_dirs, rb_dirs, where=rb_sig)
                np.copyto(self._gm_dirs, gm_dirs, where=gm_sig)
                reversals  = luma_rev | rb_rev | gm_rev
                self._last_significant = significant | rb_sig | gm_sig
            else:
                reversals  = luma_rev
                self._last_significant = significant

            self._last_reversals = reversals

            if reversals.sum() >= min_blocks:
                self._flash_times.append(now)
                any_flash_this_frame = True
                self._last_flash_color_only = (
                    color_sens > 0.0
                    and luma_rev.sum() < min_blocks
                )
        else:
            self._last_reversals[:] = False

        self._prev_blocks = luma_b
        self._prev_rb     = rb_b
        self._prev_gm     = gm_b

        cutoff = now - 1.0
        while self._flash_times and self._flash_times[0] < cutoff:
            self._flash_times.popleft()

        if any_flash_this_frame:
            if (self._last_frame_flash_time > 0
                    and (now - self._last_frame_flash_time)
                        <= (1.0 / MAX_FLASHES_PER_SEC)):
                self._last_frame_flash_time = now
                return MAX_FLASHES_PER_SEC
            self._last_frame_flash_time = now

        return len(self._flash_times)


# ── Settings Window ────────────────────────────────────────────────────────────

class SettingsWindow:
    """Slider-based settings panel that applies changes live and saves to JSON."""

    # Keys whose sliders get an enable/disable toggle checkbox
    _TOGGLE_KEYS = {"desaturate_level", "ambient_saturation", "lighten_darks", "dim_lights"}

    _SLIDERS = [
        # (label,                       key,                    lo,    hi,    res,   fmt)
        ("Overlay Darkness",            "overlay_alpha",        100,   220,   1,     "{:.0f}"),
        ("Colour Mute Strength",        "desaturate_level",     0.0,   1.0,   0.01,  "{:.2f}"),
        ("Ambient Saturation",          "ambient_saturation",   -1.0,  1.0,   0.05,  "{:.2f}"),
        ("Lighten Darks",               "lighten_darks",        0.0,   0.10,  0.01,  "{:.2f}"),
        ("Dim Lights",                  "dim_lights",           0.0,   0.5,   0.01,  "{:.2f}"),
        ("Fade In Speed (s)",           "fade_in_duration",     0.05,  0.50,  0.01,  "{:.2f}"),
        ("Fade Out Speed (s)",          "fade_duration",        0.20,  2.00,  0.05,  "{:.2f}"),
        ("Flash Sensitivity (%)",       "flash_threshold_pct",      5.0,   30.0,  0.5,   "{:.1f}"),
        ("Min Flash Area (blocks)",     "min_flash_blocks",         1,     25,    1,     "{:.0f}"),
        ("Cooldown (s)",                "cooldown_sec",             0.5,   5.0,   0.1,   "{:.1f}"),
        ("Grid Size (NxN blocks)",      "block_grid",               4,     20,    1,     "{:.0f}"),
        ("Color Flash Detect (%)",      "color_flash_sensitivity",  0.0,   30.0,  0.5,   "{:.1f}"),
        ("Capture FPS (CPU usage)",     "capture_fps",              10,    60,    1,     "{:.0f}"),
    ]

    def __init__(self, root: tk.Tk, dimmer: "OverlayDimmer", grid: "GridOverlay",
                 guard: "EpilepsyGuard"):
        self._root   = root
        self._dimmer = dimmer
        self._grid   = grid
        self._guard  = guard
        self._win: tk.Toplevel | None = None
        # Persists across window open/close so toggling back ON restores the last value
        self._saved_toggle_vals: dict = {}
        # Per-build widget references (recreated each open)
        self._toggle_vars:  dict = {}
        self._scale_widgets: dict = {}
        self._slider_fmts:  dict = {}
        # Presets
        self._presets: dict = {}          # name → cfg snapshot
        self._pending_preset: str | None = None   # restored after window rebuild
        self._load_presets_from_file()

    def open(self):
        if self._win and self._win.winfo_exists():
            self._win.lift()
            return

        win = tk.Toplevel(self._root)
        win.title("Settings")
        win.resizable(False, False)
        win.attributes("-topmost", True)
        win.geometry("+10+80")
        win.protocol("WM_DELETE_WINDOW", self._close_settings)
        self._win = win
        self._build(win)

    def _build(self, win: tk.Toplevel):
        # Reset per-build widget references
        self._toggle_vars   = {}
        self._scale_widgets = {}
        self._slider_fmts   = {}

        tk.Label(win, text="EpilepsyGuard Settings",
                 font=tkfont.Font(weight="bold", size=11)).pack(padx=20, pady=(14, 4))

        # ── Presets ──────────────────────────────────────────────────────────────
        tk.Label(win, text="Presets", anchor="w",
                 font=tkfont.Font(weight="bold", size=9)).pack(fill="x", padx=20, pady=(4, 2))

        row_load = tk.Frame(win)
        row_load.pack(fill="x", padx=16, pady=1)
        self._preset_var = tk.StringVar()
        # OptionMenu uses only core tkinter — ttk.Combobox needs theme files that
        # PyInstaller often fails to bundle, causing a blank/broken widget.
        self._preset_menu = tk.OptionMenu(row_load, self._preset_var, "")
        self._preset_menu.config(width=20, anchor="w")
        self._preset_menu.pack(side="left", padx=(0, 4))
        tk.Button(row_load, text="Load",   width=6, command=self._preset_load  ).pack(side="left", padx=(0, 4))
        tk.Button(row_load, text="Delete", width=6, command=self._preset_delete).pack(side="left")

        row_save = tk.Frame(win)
        row_save.pack(fill="x", padx=16, pady=(1, 6))
        self._preset_name_var = tk.StringVar()
        tk.Entry(row_save, textvariable=self._preset_name_var, width=26).pack(side="left", padx=(0, 4))
        tk.Button(row_save, text="Save preset", command=self._preset_save).pack(side="left")

        self._refresh_preset_list()

        tk.Frame(win, height=1, bg="#cccccc").pack(fill="x", padx=14, pady=(2, 8))

        for label, key, lo, hi, res, fmt in self._SLIDERS:
            self._add_slider(win, label, key, lo, hi, res, fmt)

        # ── Channel Tint ────────────────────────────────────────────────────────
        tk.Frame(win, height=1, bg="#cccccc").pack(fill="x", padx=14, pady=(8, 2))
        tk.Label(win, text="Channel Tint  (1 = normal · 0 = removed)",
                 anchor="w", fg="#555555").pack(fill="x", padx=16, pady=(2, 0))
        for label, key, lo, hi, res, fmt in (
            ("Red",   "tint_red",   0.0, 1.0, 0.01, "{:.2f}"),
            ("Green", "tint_green", 0.0, 1.0, 0.01, "{:.2f}"),
            ("Blue",  "tint_blue",  0.0, 1.0, 0.01, "{:.2f}"),
        ):
            self._add_slider(win, label, key, lo, hi, res, fmt)

        tk.Frame(win, height=1, bg="#cccccc").pack(fill="x", padx=14, pady=10)

        # ── Monitor Detection ───────────────────────────────────────────────
        if len(_MONITOR_LIST) > 1:
            tk.Label(win, text="Monitor Detection",
                     anchor="w", fg="#555555").pack(fill="x", padx=16, pady=(0, 2))
            self._monitor_vars = []
            for _mi, (_md, _mo, _ml) in enumerate(_MONITOR_LIST):
                _var = tk.BooleanVar(value=(_mi in cfg["enabled_monitors"]))

                def _on_mon_toggle(_idx=_mi, _v=_var):
                    enabled = list(cfg["enabled_monitors"])
                    if _v.get():
                        if _idx not in enabled:
                            enabled.append(_idx)
                            cfg["enabled_monitors"] = sorted(enabled)
                    else:
                        enabled = [e for e in enabled if e != _idx]
                        if not enabled:          # keep at least one enabled
                            _v.set(True)
                            return
                        cfg["enabled_monitors"] = enabled

                tk.Checkbutton(win, text=_ml, variable=_var,
                               command=_on_mon_toggle, anchor="w"
                               ).pack(fill="x", padx=20, pady=1)
                self._monitor_vars.append(_var)
            tk.Frame(win, height=1, bg="#cccccc").pack(fill="x", padx=14, pady=(4, 0))

        # Always-on colour filter toggle
        self._always_var = tk.BooleanVar(value=bool(cfg["filter_always_on"]))
        tk.Checkbutton(
            win,
            text="Colour Mute: always on (not just during protection)",
            variable=self._always_var,
            command=self._toggle_always_on,
            anchor="w",
        ).pack(fill="x", padx=20, pady=2)

        # Show detection grid overlay toggle
        self._grid_var = tk.BooleanVar(value=bool(cfg["show_grid"]))
        tk.Checkbutton(
            win,
            text="Show detection grid overlay",
            variable=self._grid_var,
            command=self._toggle_grid,
            anchor="w",
        ).pack(fill="x", padx=20, pady=2)

        # Overlay darkness always-on toggle
        self._overlay_always_var = tk.BooleanVar(value=bool(cfg["overlay_always_on"]))
        tk.Checkbutton(
            win,
            text="Overlay darkness: always on",
            variable=self._overlay_always_var,
            command=self._toggle_overlay_always_on,
            anchor="w",
        ).pack(fill="x", padx=20, pady=2)

        # Detection active toggle
        self._detection_var = tk.BooleanVar(value=not self._guard._paused)
        tk.Checkbutton(
            win,
            text="Detection active",
            variable=self._detection_var,
            command=self._toggle_detection,
            anchor="w",
        ).pack(fill="x", padx=20, pady=2)

        tk.Frame(win, height=1, bg="#cccccc").pack(fill="x", padx=14, pady=10)

        btn_frame = tk.Frame(win)
        btn_frame.pack(padx=14, pady=(0, 14))
        tk.Button(btn_frame, text="Save",     width=10, command=self._save   ).pack(side="left", padx=(0, 8))
        tk.Button(btn_frame, text="Defaults", width=10, command=self._defaults).pack(side="left")

        self._status = tk.Label(win, text="", fg="#555555")
        self._status.pack(pady=(0, 8))

    def _add_slider(self, win, label, key, lo, hi, res, fmt):
        row = tk.Frame(win)
        row.pack(fill="x", padx=16, pady=2)

        self._slider_fmts[key] = fmt

        if key in self._TOGGLE_KEYS:
            # Clamp saved/loaded value to the slider's valid range
            clamped = type(_DEFAULTS[key])(max(lo, min(hi, float(cfg[key]))))
            if clamped != cfg[key]:
                cfg[key] = clamped
            is_on = (cfg[key] != 0.0)
            var = tk.BooleanVar(value=is_on)
            self._toggle_vars[key] = var
            if is_on:
                self._saved_toggle_vals.setdefault(key, cfg[key])
            tk.Checkbutton(row, variable=var,
                           command=lambda k=key: self._on_toggle(k)).pack(side="left")
            tk.Label(row, text=label, width=23, anchor="w").pack(side="left")
        else:
            tk.Label(row, text=label, width=26, anchor="w").pack(side="left")

        val_lbl = tk.Label(row, text=fmt.format(cfg[key]), width=6, anchor="e")
        val_lbl.pack(side="right")

        def on_change(v, k=key, f=fmt, lbl=val_lbl):
            new_val = type(_DEFAULTS[k])(float(v))
            cfg[k]  = new_val
            lbl.config(text=f.format(float(v)))
            self._apply_live(k)

        # Create without command first so scale.set() doesn't fire on_change during init
        scale = tk.Scale(row, from_=lo, to=hi, resolution=res,
                         orient="horizontal", showvalue=False)
        scale.set(cfg[key])
        scale.config(command=on_change)
        if key in self._TOGGLE_KEYS and not (cfg[key] != 0.0):
            scale.config(state="disabled")
        scale.pack(side="left", fill="x", expand=True, padx=4)
        self._scale_widgets[key] = scale

    def _on_toggle(self, key: str):
        """Enable or disable a colour/saturation slider via its checkbox."""
        if self._toggle_vars[key].get():   # turning ON
            self._scale_widgets[key].config(state="normal")
            # Restore last non-zero value; fall back to non-zero default if available
            saved = self._saved_toggle_vals.get(key, _DEFAULTS.get(key, 0.0))
            if saved == 0.0:
                saved = _DEFAULTS.get(key, 0.0)
            cfg[key] = type(_DEFAULTS[key])(float(saved))
            self._scale_widgets[key].set(saved)
            self._apply_live(key)
        else:                              # turning OFF
            if cfg[key] != 0.0:
                self._saved_toggle_vals[key] = cfg[key]
            cfg[key] = type(_DEFAULTS[key])(0)
            self._scale_widgets[key].set(0.0)
            self._scale_widgets[key].config(state="disabled")
            self._apply_live(key)

    def _apply_live(self, key: str):
        """Push certain settings through immediately for instant feedback."""
        if key in ("tint_red", "tint_green", "tint_blue"):
            # Channel tint: rebuild matrix at current protection level.
            if self._dimmer.active:
                prot = self._dimmer._current_desat
            elif cfg["filter_always_on"]:
                prot = cfg["desaturate_level"]
            else:
                prot = 0.0
            apply_color_filter(prot)
            return
        if key in ("desaturate_level", "ambient_saturation", "lighten_darks", "dim_lights"):
            # Always apply live so the user sees the effect while dragging the slider.
            # Use the current protection level (0 when not protecting) so ambient
            # settings preview correctly without the protection desaturation on top.
            if self._dimmer.active:
                prot = self._dimmer._current_desat
            elif cfg["filter_always_on"]:
                prot = cfg["desaturate_level"]
            else:
                prot = 0.0
            apply_color_filter(prot)
            # Update inverse-correction factors so detection stays accurate at the new values.
            self._guard.signal_filter_changed()
        elif key == "overlay_alpha":
            if (self._dimmer.active or cfg["overlay_always_on"]) and self._dimmer._fade_state is None:
                _user32.SetLayeredWindowAttributes(
                    self._dimmer._hwnd, 0, cfg["overlay_alpha"], OverlayDimmer._LWA_ALPHA
                )
                self._dimmer.current_alpha = cfg["overlay_alpha"]
        elif key in ("flash_threshold_pct", "min_flash_blocks", "color_flash_sensitivity"):
            # Detection-threshold settings: sync the detector's config cache.
            self._guard.signal_settings_changed()

    def _close_settings(self):
        """Restore filter to its proper non-preview state when the settings window closes."""
        if not cfg["filter_always_on"] and not self._dimmer.active:
            apply_color_filter(0.0)
        self._win.destroy()

    def _toggle_always_on(self):
        cfg["filter_always_on"] = self._always_var.get()
        if cfg["filter_always_on"]:
            apply_color_filter(cfg["desaturate_level"])
        elif not self._dimmer.active:
            apply_color_filter(0.0)
        self._guard.signal_filter_changed()

    def _toggle_grid(self):
        cfg["show_grid"] = self._grid_var.get()
        if cfg["show_grid"]:
            self._grid.show()
        else:
            self._grid.hide()

    def _toggle_overlay_always_on(self):
        cfg["overlay_always_on"] = self._overlay_always_var.get()
        if cfg["overlay_always_on"]:
            self._dimmer.show_always_on()
        else:
            self._dimmer.hide_always_on()

    def _toggle_detection(self):
        active = self._detection_var.get()
        self._guard.panel.set_paused(not active)

    # ── Preset helpers ───────────────────────────────────────────────────────────

    def _load_presets_from_file(self):
        try:
            data = json.loads(_PRESETS_FILE.read_text())
            if isinstance(data, dict):
                self._presets = data
        except Exception:
            self._presets = {}

    def _save_presets_to_file(self):
        _PRESETS_FILE.write_text(json.dumps(self._presets, indent=2))

    def _refresh_preset_list(self):
        names = sorted(self._presets.keys())
        menu = self._preset_menu["menu"]
        menu.delete(0, "end")
        for name in names:
            menu.add_command(label=name, command=lambda v=name: self._preset_var.set(v))
        if self._pending_preset and self._pending_preset in names:
            self._preset_var.set(self._pending_preset)
            self._pending_preset = None
        elif names:
            self._preset_var.set(names[0])
        else:
            self._preset_var.set("")

    def _preset_save(self):
        name = self._preset_name_var.get().strip()
        if not name:
            return
        self._presets[name] = dict(cfg)
        self._save_presets_to_file()
        self._pending_preset = name
        self._refresh_preset_list()
        self._status.config(text=f"Preset '{name}' saved.", fg="#228822")
        if self._win:
            self._win.after(2000, lambda: self._status.config(text=""))

    def _preset_load(self):
        name = self._preset_var.get()
        if not name or name not in self._presets:
            return
        was_overlay_always_on = cfg["overlay_always_on"]
        snapshot = self._presets[name]
        for k, v in snapshot.items():
            if k in _DEFAULTS:
                try:
                    cfg[k] = type(_DEFAULTS[k])(v)
                except (ValueError, TypeError):
                    pass
        self._pending_preset = name
        if self._win:
            self._win.destroy()
        self.open()
        # Apply all live effects for the loaded preset
        if not self._dimmer.active:
            apply_color_filter(cfg["desaturate_level"] if cfg["filter_always_on"] else 0.0)
        self._guard.signal_filter_changed()
        if cfg["overlay_always_on"]:
            self._dimmer.show_always_on()
        elif was_overlay_always_on:
            self._dimmer.hide_always_on()
        if cfg["show_grid"]:
            self._grid.show()
        else:
            self._grid.hide()

    def _preset_delete(self):
        name = self._preset_var.get()
        if not name or name not in self._presets:
            return
        del self._presets[name]
        self._save_presets_to_file()
        self._refresh_preset_list()
        self._status.config(text=f"Preset '{name}' deleted.", fg="#888888")
        if self._win:
            self._win.after(2000, lambda: self._status.config(text=""))

    def _save(self):
        _save_settings()
        self._status.config(text="Saved.", fg="#228822")
        if self._win:
            self._win.after(2000, lambda: self._status.config(text=""))

    def _defaults(self):
        was_overlay_always_on = cfg["overlay_always_on"]
        self._saved_toggle_vals.clear()
        for k, v in _DEFAULTS.items():
            cfg[k] = v
        # Rebuild sliders with reset values
        if self._win:
            self._win.destroy()
        self.open()
        # Reset live effects
        if not self._dimmer.active:
            apply_color_filter(cfg["desaturate_level"] if cfg["filter_always_on"] else 0.0)
        # Hide overlay if always-on was active but is now off after reset
        if was_overlay_always_on and not cfg["overlay_always_on"]:
            self._dimmer.hide_always_on()


# ── Control Panel ──────────────────────────────────────────────────────────────

class ControlPanel:
    def __init__(self, root: tk.Tk, guard: "EpilepsyGuard", settings_win: SettingsWindow):
        self._root        = root
        self._guard       = guard
        self._settings_win = settings_win
        self._paused      = False
        self._status      = tk.StringVar(value="Monitoring...")
        self._count       = 0
        self._tray = None   # pystray.Icon, set in _setup_tray
        self._build()
        self._setup_tray()

    def _build(self):
        r = self._root
        r.title("EpilepsyGuard")
        r.resizable(False, False)
        r.attributes("-topmost", True)
        r.geometry("+10+10")
        r.protocol("WM_DELETE_WINDOW", self._on_close)

        bold = tkfont.Font(weight="bold", size=12)
        tk.Label(r, text="EpilepsyGuard", font=bold).pack(padx=20, pady=(14, 2))

        self._status_label = tk.Label(r, textvariable=self._status,
                                      fg="#555555", wraplength=200)
        self._status_label.pack(padx=20)

        self._count_label = tk.Label(r, text="Flashes blocked: 0", fg="#888888")
        self._count_label.pack(padx=20, pady=(2, 0))

        tk.Frame(r, height=1, bg="#cccccc").pack(fill="x", padx=14, pady=10)

        btn_frame = tk.Frame(r)
        btn_frame.pack(padx=14, pady=(0, 14))

        self._toggle_btn = tk.Button(btn_frame, text="Pause",    width=8, command=self._toggle)
        self._toggle_btn.pack(side="left", padx=(0, 6))
        tk.Button(btn_frame, text="Settings", width=8,
                  command=self._settings_win.open).pack(side="left", padx=(0, 6))
        tk.Button(btn_frame, text="Quit",     width=8,
                  command=self._quit).pack(side="left")

    def _toggle(self):
        self.set_paused(not self._paused)

    def set_paused(self, paused: bool):
        """Set detection paused state — called from settings window or toggle button."""
        self._paused = paused
        if self._paused:
            self._guard.pause()
            self._toggle_btn.configure(text="Resume")
            self._set_status("Paused", "#e08800")
        else:
            self._guard.resume()
            self._toggle_btn.configure(text="Pause")
            self._set_status("Monitoring...", "#555555")

    def _setup_tray(self):
        icon_img = _load_or_create_icon()

        # Set the window / taskbar icon
        self._icon_photo = _icon_to_photoimage(icon_img, 32)   # keep reference
        self._root.iconphoto(True, self._icon_photo)

        # Build the system-tray icon (always visible while the app is running)
        menu = pystray.Menu(
            pystray.MenuItem("Show EpilepsyGuard", self._show_from_tray, default=True),
            pystray.Menu.SEPARATOR,
            pystray.MenuItem("Quit", lambda: self._root.after(0, self._quit)),
        )
        self._tray = pystray.Icon("EpilepsyGuard", icon_img, "EpilepsyGuard", menu)
        threading.Thread(target=self._tray.run, daemon=True).start()

    def _show_from_tray(self):
        self._root.after(0, self._root.deiconify)

    def _on_close(self):
        """X button — hide the window to the system tray."""
        self._root.withdraw()

    def _quit(self):
        """Fully exit the application."""
        if self._tray:
            self._tray.stop()
        self._guard.stop()
        self._root.destroy()

    def _set_status(self, text: str, color: str = "#555555"):
        self._status.set(text)
        self._status_label.configure(fg=color)

    def notify_flash(self):
        self._count += 1
        self._count_label.configure(text=f"Flashes blocked: {self._count}")
        self._set_status("Flash detected! Protecting...", "#cc0000")
        self._root.after(2000, lambda: self._set_status("Monitoring...", "#555555"))

    def notify_restored(self):
        self._set_status("Monitoring...", "#555555")

    def notify_camera_error(self, detail: str):
        self._set_status(f"Screen capture failed: {detail}", "#cc0000")


# ── Monitor capture state ────────────────────────────────────────────────────

class _MonitorState:
    """Per-monitor capture + detector state for EpilepsyGuard._loop()."""
    __slots__ = ('device_idx', 'output_idx', 'label', 'camera',
                 'detector', 'null_streak', 'retry_at')

    def __init__(self, device_idx: int, output_idx: int, label: str):
        self.device_idx  = device_idx
        self.output_idx  = output_idx
        self.label       = label
        self.camera      = None
        self.detector    = FlashDetector()
        self.null_streak = 0
        self.retry_at    = 0.0

    def acquire(self):
        """Try to open the dxcam capture for this output."""
        try:
            self.camera = dxcam.create(
                device_idx=self.device_idx,
                output_idx=self.output_idx,
                processor_backend="numpy",
            )
            self.null_streak = 0
        except Exception:
            self.camera = None


# ── Main Guard ─────────────────────────────────────────────────────────────────

class EpilepsyGuard:
    def __init__(self):
        self._running = False
        self._paused  = False
        self._thread: threading.Thread | None = None
        self._root: tk.Tk | None = None
        self.dimmer: OverlayDimmer | None = None
        self.panel:  ControlPanel  | None = None
        self.grid:   GridOverlay   | None = None
        self._resume_event    = threading.Event()
        self._resume_event.set()                # starts unpaused
        self._detector: "FlashDetector | None" = None
    def signal_filter_changed(self):
        """Any filter or detection setting changed — sync the detector's config cache."""
        if self._detector is not None:
            self._detector.sync_config()

    # Alias kept so existing call-sites that used the old name still work
    signal_settings_changed = signal_filter_changed

    def start(self, root: tk.Tk):
        self._root    = root
        self._running = True
        self._thread  = threading.Thread(target=self._loop, daemon=True)
        self._thread.start()

    def pause(self):
        self._paused = True
        self._resume_event.clear()
        self.dimmer.reset_instantly()

    def resume(self):
        self._paused = False
        self._resume_event.set()
        if cfg["overlay_always_on"]:
            self.dimmer.show_always_on()

    def stop(self):
        self._running = False
        self._resume_event.set()   # unblock if currently paused
        self.dimmer.reset_instantly()

    def _loop(self):
        # Normal thread priority — ABOVE_NORMAL caused visible CPU spikes.
        _kernel32.SetThreadPriority(_kernel32.GetCurrentThread(), 0)  # NORMAL

        last_flash_time   = 0.0
        last_grid_update  = 0.0
        protected         = False
        skip_until        = 0.0
        restore_pending   = 0.0

        try:
            n_devices = max(1, len(dxcam.device_info()))
        except Exception:
            n_devices = 1

        # ── per-monitor state ──────────────────────────────────────────────────
        _mons: list = []       # list[_MonitorState]
        _last_enabled: list = []

        def _build_monitors():
            nonlocal _mons, _last_enabled
            # Release old cameras cleanly
            for m in _mons:
                if m.camera is not None:
                    try:
                        del m.camera
                    except Exception:
                        pass
            _mons.clear()
            enabled = list(cfg["enabled_monitors"])
            _last_enabled = list(enabled)
            for mi in enabled:
                if mi >= len(_MONITOR_LIST):
                    continue
                d, o, label = _MONITOR_LIST[mi]
                mon = _MonitorState(d, o, label)
                mon.acquire()
                _mons.append(mon)
            # Always keep at least the primary monitor
            if not _mons:
                entry = _MONITOR_LIST[0] if _MONITOR_LIST else (0, 0, "Monitor 1 (primary)")
                mon = _MonitorState(*entry)
                mon.acquire()
                _mons.append(mon)

        _build_monitors()

        # Primary camera GPU-cycling recovery (handles Discord DXGI conflict)
        def _recover_primary():
            """Try every DXGI device for the primary output_idx."""
            if not _mons:
                return None, 0
            o_primary = _mons[0].output_idx
            for d in range(n_devices):
                try:
                    cam = dxcam.create(device_idx=d, output_idx=o_primary,
                                       processor_backend="numpy")
                    return cam, d
                except Exception:
                    continue
            return None, _mons[0].device_idx

        if _mons and _mons[0].camera is None:
            self._root.after(0, lambda: self.panel.notify_camera_error(
                "capture blocked — retrying (close screenshare?)"))

        _NULL_LIMIT     = 30
        _next_grab      = time.monotonic()
        _frame_interval = 1.0 / max(10, min(60, cfg["capture_fps"]))
        _idle_interval  = max(_frame_interval, 1.0 / 15.0)  # ≤15 fps when quiet
        _last_fps_cfg   = cfg["capture_fps"]

        try:
            while self._running:
                # ── pause handling ─────────────────────────────────────────────
                if self._paused:
                    self._resume_event.wait(timeout=0.1)
                    for m in _mons:
                        m.null_streak = 0
                    _next_grab = time.monotonic()
                    continue

                # ── rebuild cameras if enabled monitors changed ─────────────────
                if cfg["enabled_monitors"] != _last_enabled:
                    _build_monitors()

                # ── primary camera blocked (e.g. Discord screenshare) ──────────
                if _mons and _mons[0].camera is None:
                    time.sleep(2.0)
                    cam, new_d = _recover_primary()
                    _mons[0].camera     = cam
                    _mons[0].device_idx = new_d
                    _mons[0].null_streak = 0
                    if cam is None:
                        self._root.after(0, lambda: self.panel.notify_camera_error(
                            "capture blocked — retrying (close screenshare?)"))
                    _next_grab = time.monotonic()
                    continue

                now = time.monotonic()

                # Recache frame interval only when slider changes
                if cfg["capture_fps"] != _last_fps_cfg:
                    _last_fps_cfg   = cfg["capture_fps"]
                    _frame_interval = 1.0 / max(10, min(60, _last_fps_cfg))
                    _idle_interval  = max(_frame_interval, 1.0 / 15.0)

                # Unified rate limiter: FPS cap + post-restore skip window
                _wait = max(_next_grab, skip_until) - now
                if _wait > 0.0005:
                    time.sleep(_wait)
                    continue

                # Rate selection: 3× slower while overlay is up (fade threads also
                # running; we only need cooldown tracking, not fast detection).
                # 15 fps idle when quiet; full rate only near recent flash activity.
                if protected:
                    _next_grab = now + _frame_interval * 3
                elif (now - last_flash_time) > 2.0:
                    _next_grab = now + _idle_interval
                else:
                    _next_grab = now + _frame_interval

                # ── grab + process all enabled monitors ─────────────────────────
                any_flash       = False
                primary_detector = None

                for mi, mon in enumerate(_mons):
                    if mon.camera is None:
                        # Secondary monitor: retry on a timer
                        if now >= mon.retry_at:
                            mon.acquire()
                            if mon.camera is None:
                                mon.retry_at = now + 5.0
                        continue

                    frame = mon.camera.grab()

                    if frame is None:
                        mon.null_streak += 1
                        if mon.null_streak >= _NULL_LIMIT:
                            mon.null_streak = 0
                            del mon.camera
                            mon.camera = None
                            if mi == 0:
                                # Primary: cycle GPUs immediately
                                cam, new_d = _recover_primary()
                                mon.camera     = cam
                                mon.device_idx = new_d
                                if cam is None:
                                    self._root.after(0, lambda: self.panel.notify_camera_error(
                                        "capture blocked — retrying (close screenshare?)"))
                            else:
                                mon.retry_at = now + 5.0
                            _next_grab = time.monotonic()
                        continue

                    mon.null_streak = 0

                    flashes = mon.detector.process(
                        frame, overlay_alpha=self.dimmer.current_alpha
                    )
                    if flashes >= MAX_FLASHES_PER_SEC:
                        any_flash = True

                    if mi == 0 or primary_detector is None:
                        primary_detector = mon.detector

                if primary_detector is None and _mons:
                    primary_detector = _mons[0].detector

                if any_flash:
                    last_flash_time = now

                should_protect = (now - last_flash_time) < cfg["cooldown_sec"]

                if should_protect and not protected:
                    restore_pending = 0.0
                    protected = True
                    self.dimmer.dim()
                    skip_until = now + cfg["fade_in_duration"]
                    self._root.after(0, self.panel.notify_flash)

                elif should_protect and protected:
                    restore_pending = 0.0

                elif not should_protect and protected:
                    if restore_pending == 0.0:
                        restore_pending = now
                    elif now - restore_pending >= 0.15:
                        restore_pending = 0.0
                        protected = False
                        self.dimmer.restore()
                        for mon in _mons:
                            mon.detector.soft_reset()
                        skip_until = now + 0.05
                        self._root.after(0, self.panel.notify_restored)

                # Grid overlay update at ~15 fps (uses primary monitor's detector)
                if (cfg["show_grid"] and self.grid is not None
                        and primary_detector is not None
                        and (now - last_grid_update) > 0.067):
                    last_grid_update = now
                    self.grid.update_blocks(primary_detector._last_significant,
                                            primary_detector._last_reversals)

        finally:
            for mon in _mons:
                if mon.camera is not None:
                    del mon.camera

# ── Entry Point ────────────────────────────────────────────────────────────────

def main():
    _load_settings()

    # Enumerate connected monitors; populates _MONITOR_LIST used by the loop
    # and the settings window.  Must happen before guard.start().
    global _MONITOR_LIST
    _MONITOR_LIST = _enum_monitors()

    root         = tk.Tk()
    guard        = EpilepsyGuard()
    dimmer       = OverlayDimmer()
    grid_overlay = GridOverlay()
    settings_win = SettingsWindow(root, dimmer, grid_overlay, guard)
    panel        = ControlPanel(root, guard, settings_win)

    guard.dimmer = dimmer
    guard.panel  = panel
    guard.grid   = grid_overlay

    atexit.register(_clear_color_filter)

    # Apply colour filter at startup.
    # Always-on: include the desaturation level.
    # Ambient-only (filter_always_on=False): still apply lighten_darks/dim_lights/
    # ambient_sat so the Mag API state matches the detector's correction factors
    # from frame 1 and to show the user their saved visual settings immediately.
    if cfg["filter_always_on"]:
        apply_color_filter(cfg["desaturate_level"])
    elif (cfg["lighten_darks"] != 0.0 or cfg["dim_lights"] != 0.0
          or cfg["ambient_saturation"] != 0.0
          or cfg["tint_red"] != 1.0 or cfg["tint_green"] != 1.0 or cfg["tint_blue"] != 1.0):
        apply_color_filter(0.0)

    # Show grid overlay if it was enabled in saved settings
    if cfg["show_grid"]:
        grid_overlay.show()

    # Show dark overlay at startup if always-on mode was saved
    if cfg["overlay_always_on"]:
        dimmer.show_always_on()

    guard.start(root)
    root.mainloop()


if __name__ == "__main__":
    # --embed-icon FILEPATH: bake a custom icon into _ICON_B64 in this source file,
    # then exit.  Run this before building the exe so the icon is permanently embedded.
    # Usage:  python epilepsy_guard.py --embed-icon myicon.png
    import sys as _sys
    if len(_sys.argv) == 3 and _sys.argv[1] == "--embed-icon":
        _icon_path = _sys.argv[2]
        try:
            _img = Image.open(_icon_path).convert("RGBA")
        except Exception as e:
            print(f"Cannot open icon: {e}")
            _sys.exit(1)
        _buf = io.BytesIO()
        _img.save(_buf, format="ICO",
                  sizes=[(16,16),(32,32),(48,48),(64,64),(128,128),(256,256)])
        _b64 = base64.b64encode(_buf.getvalue()).decode()
        _lines = "\n".join(f'    "{_b64[i:i+76]}"' for i in range(0, len(_b64), 76))
        _new_const = f"_ICON_B64 = (\n{_lines}\n)"
        import re as _re, pathlib as _pl
        _me = _pl.Path(__file__).read_text(encoding="utf-8")
        _me2 = _re.sub(r'_ICON_B64 = \(\n(?:    ".*"\n)*\)', _new_const, _me)
        if _me2 == _me:
            print("ERROR: could not locate _ICON_B64 block to replace.")
            _sys.exit(1)
        _pl.Path(__file__).write_text(_me2, encoding="utf-8")
        print(f"Embedded {_icon_path} into _ICON_B64 ({len(_b64)} chars). Rebuild the exe to apply.")
        _sys.exit(0)
    main()
