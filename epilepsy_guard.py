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
    "AElFTkSuQmCC"
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
