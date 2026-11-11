@echo off
cd /d %~dp0

echo Starting Seongbuk SafePass (team3_project)...
echo.

if exist "C:\김경민\h_claude\세이프패스_v1\python\python.exe" (
  "C:\김경민\h_claude\세이프패스_v1\python\python.exe" tools\로컬서버.py
) else (
  py tools\로컬서버.py 2>nul || python tools\로컬서버.py
)

echo.
echo Server stopped. You can close this window.
pause >nul
