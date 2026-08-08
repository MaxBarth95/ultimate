@echo off
setlocal
set "DIR=%~dp0"
set "ULTIMATE_DIR=%DIR%..\..\releaseScripts\default\UAutomizer-win32"
set "PYTHON=C:\Users\maxba\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe"
set "JAVA_HOME=C:\Program Files\Eclipse Adoptium\jdk-21.0.11.10-hotspot"
set "PATH=%JAVA_HOME%\bin;%PATH%"

if "%~1"=="" (
	echo Usage: run-coordinator.cmd ^<program.c^> [run-directory]
	exit /b 2
)
set "PROGRAM=%~f1"
if "%~2"=="" (set "RUN=%DIR%runtime") else (set "RUN=%~f2")

if not exist "%RUN%\exchange\worker-0" mkdir "%RUN%\exchange\worker-0"
if not exist "%RUN%\coordinator-data" mkdir "%RUN%\coordinator-data"
if not exist "%RUN%\logs\coordinator" mkdir "%RUN%\logs\coordinator"

cd /d "%RUN%\logs\coordinator"
"%PYTHON%" "%ULTIMATE_DIR%\Ultimate.py" ^
	--file "%PROGRAM%" ^
	--spec "%DIR%examples\reach.prp" ^
	--architecture 32bit ^
	--data "%RUN%\coordinator-data" ^
	--traceabstraction.multi.process.component COORDINATOR ^
	--traceabstraction.multi.process.exchange.root "%RUN%\exchange\worker-0" ^
	--traceabstraction.multi.process.worker.count 1

