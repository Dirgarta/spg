@echo off
chcp 65001 >nul
cd /d "%~dp0"
set SPG_DEV=1
python -m pip install -r requirements.txt
python app_spg.py
pause
