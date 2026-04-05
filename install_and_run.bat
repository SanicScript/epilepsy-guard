@echo off
echo Installing dependencies...
pip install -r requirements.txt
echo.
echo Starting EpilepsyGuard...
python epilepsy_guard.py
pause
