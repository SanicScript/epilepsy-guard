# EpilepsyGuard

A Windows background tool that monitors your screen in real time and automatically covers it with a dark overlay the moment rapid flashing is detected — helping protect users with photosensitive epilepsy.

## What it does

- Captures all connected monitors using DXGI (sees hardware-accelerated video — games, browsers, everything)
- Detects rapid luminance changes that meet the WCAG 2.3.1 threshold (3+ flashes per second)
- Fades in a dark overlay and applies system-wide colour desaturation instantly when flashing is detected
- Fades the overlay back out after flashing stops
- Multi-monitor support with per-monitor on/off toggles
- Colour correction tools: ambient saturation, lighten darks, dim lights, per-channel tint
- Detection grid overlay to see exactly which screen regions are triggering
- Colour flash detection (red-blue and green-magenta channel reversals)
- Lives in the system tray — minimal footprint, no taskbar presence
- Settings and presets auto-saved to `C:\EpilepsyGuard\`

## Requirements

- Windows 10 or 11 (64-bit)
- Python 3.10+ (if running from source)
- A DirectX-capable GPU (required by dxcam)

## Running from source

```powershell
pip install dxcam numpy pystray Pillow
python epilepsy_guard.py
```

> **Note:** `opencv-python` in `requirements.txt` is a dxcam dependency — you do not need to import it yourself.

## Building the exe

### 1. Install PyInstaller

```powershell
pip install pyinstaller
```

### 2. (Optional) Embed a custom icon

If you want to change the app icon, run this once before building. It bakes the icon directly into the source so it appears on every machine without needing any extra files.

```powershell
python epilepsy_guard.py --embed-icon YourIcon.ico
```

### 3. Build

```powershell
python -m PyInstaller --onefile --noconsole --collect-all dxcam --collect-all pystray --collect-all PIL --icon=YourIcon.ico --name EpilepsyGuard epilepsy_guard.py
```

The finished exe will be in the `dist\` folder.

## Settings

Settings and presets are stored in `C:\EpilepsyGuard\` and are created automatically on first run. You can edit them by hand or use the Settings window in the tray menu.

| Setting | Default | Description |
|---|---|---|
| Overlay opacity | 220 | How dark the protection overlay is (0–255) |
| Fade in | 0.15 s | Time for overlay to appear |
| Fade out | 0.60 s | Time for overlay to disappear |
| Cooldown | 1.5 s | How long overlay stays up after flashing stops |
| Capture FPS | 30 | Frames analysed per second — lower = less CPU |
| Flash threshold | 10% | Minimum luminance change to count as a flash |
| Min flash blocks | 8 | How many screen regions must flash simultaneously |
| Detection grid | 10×10 | Grid resolution for block-based detection |
| Colour flash sensitivity | Off | Detects red-blue / green-magenta colour cycling |
| Ambient saturation | 0 | Permanent colour adjustment (-1 greyscale → +1 vivid) |
| Lighten darks | 0 | Raises black point to soften harsh contrasts |
| Dim lights | 0 | Lowers white point to reduce glare |
| Tint | 1.0 each | Per-channel (R/G/B) multiplier |

## Tray menu

Right-click the tray icon to access:

- **Pause / Resume** — temporarily disable detection
- **Settings** — open the live settings panel
- **Save / Load Preset** — store and recall setting profiles
- **Quit**

## Limitations

- Screen capture requires a DirectX-capable GPU. If another app holds an exclusive DXGI lock (e.g. some screen-sharing software), capture will retry automatically.
- True exclusive-fullscreen D3D games (with Windows Fullscreen Optimizations disabled) bypass the DWM compositor — the overlay cannot appear above them. Running games in borderless windowed mode resolves this.

## License

MIT — see [LICENSE](LICENSE) if present, otherwise use freely.
