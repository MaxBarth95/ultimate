#!/usr/bin/env bash
set -Eeuo pipefail

usage() {
	cat <<'EOF'
Usage: run-multiprocess.sh --file PROGRAM.c --spec PROPERTY.prp [options]

Creates an isolated run directory, starts persistent workers, runs the
coordinator, waits for clean shutdown, and verifies the exchange artifacts.

Options:
  --file PATH             C program to analyze (required)
  --spec PATH             property file (required)
  --ultimate-dir PATH     Automizer distribution containing Ultimate.py
                          (default: $ULTIMATE_DIR)
  --workers N             number of worker processes (default: 8)
  --architecture BITS     32bit or 64bit (default: 32bit)
  --run-root PATH         directory in which the run folder is created
                          (default: current directory)
  --name NAME             run folder name (default: program-timestamp)
  --timeout SECONDS       maximum lifetime per process (default: 900)
  --job-timeout SECONDS   coordinator timeout for a worker job (default: 300)
  -h, --help              show this help

Example:
  ./run-multiprocess.sh \
    --ultimate-dir /c/tools/UAutomizer-win32 \
    --file examples/Problem18_label42.c \
    --spec examples/reach.prp --workers 8
EOF
}

die() {
	echo "error: $*" >&2
	exit 2
}

file=""
spec=""
ultimate_dir="${ULTIMATE_DIR:-}"
workers=8
architecture=32bit
run_root="$PWD"
run_name=""
process_timeout=900
job_timeout=300

while (( $# )); do
	case "$1" in
		--file) file="${2:-}"; shift 2 ;;
		--spec) spec="${2:-}"; shift 2 ;;
		--ultimate-dir) ultimate_dir="${2:-}"; shift 2 ;;
		--workers) workers="${2:-}"; shift 2 ;;
		--architecture) architecture="${2:-}"; shift 2 ;;
		--run-root) run_root="${2:-}"; shift 2 ;;
		--name) run_name="${2:-}"; shift 2 ;;
		--timeout) process_timeout="${2:-}"; shift 2 ;;
		--job-timeout) job_timeout="${2:-}"; shift 2 ;;
		-h|--help) usage; exit 0 ;;
		*) die "unknown argument: $1" ;;
	esac
done

[[ -n "$file" ]] || die "--file is required"
[[ -f "$file" ]] || die "program does not exist: $file"
[[ -n "$spec" ]] || die "--spec is required"
[[ -f "$spec" ]] || die "property does not exist: $spec"
[[ -n "$ultimate_dir" ]] || die "use --ultimate-dir or set ULTIMATE_DIR"
[[ -f "$ultimate_dir/Ultimate.py" ]] || die "Ultimate.py not found in: $ultimate_dir"
[[ "$workers" =~ ^[1-9][0-9]*$ ]] || die "--workers must be positive"
[[ "$process_timeout" =~ ^[1-9][0-9]*$ ]] || die "--timeout must be positive"
[[ "$job_timeout" =~ ^[1-9][0-9]*$ ]] || die "--job-timeout must be positive"
[[ "$architecture" == 32bit || "$architecture" == 64bit ]] || die "invalid architecture"
command -v timeout >/dev/null || die "GNU timeout is required"
command -v python3 >/dev/null || die "python3 is required for the multiprocessing monitor"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

file="$(cd "$(dirname "$file")" && pwd)/$(basename "$file")"
spec="$(cd "$(dirname "$spec")" && pwd)/$(basename "$spec")"
ultimate_dir="$(cd "$ultimate_dir" && pwd)"
mkdir -p "$run_root"
run_root="$(cd "$run_root" && pwd)"
if [[ -z "$run_name" ]]; then
	run_name="$(basename "${file%.*}")-$(date +%Y%m%d-%H%M%S)"
fi
run="$run_root/$run_name"
[[ ! -e "$run" ]] || die "run directory already exists: $run"

inbox="$run/exchange/worker-0"
logs="$run/logs"
mkdir -p "$inbox" "$logs" "$run/coordinator-data"
for ((i=0; i<workers; i++)); do
	mkdir -p "$run/worker-$i/data"
done

worker_pids=()
monitor_pid=""
shutdown_grace="${MULTIPROCESS_SHUTDOWN_GRACE_SECONDS:-15}"
kill_grace="${MULTIPROCESS_KILL_GRACE_SECONDS:-15}"
wait_until_stopped() {
	local pid="$1"
	local seconds="$2"
	local deadline=$((SECONDS + seconds))
	while kill -0 "$pid" 2>/dev/null; do
		if (( SECONDS >= deadline )); then
			return 1
		fi
		sleep 0.1
	done
	return 0
}
kill_process_tree() {
	local pid="$1"
	if ! kill -0 "$pid" 2>/dev/null; then
		return
	fi
	if command -v taskkill.exe >/dev/null 2>&1; then
		timeout --signal=KILL "$kill_grace" taskkill.exe //PID "$pid" //T //F >/dev/null 2>&1 || true
		if kill -0 "$pid" 2>/dev/null; then
			kill -KILL "$pid" 2>/dev/null || true
		fi
		return
	fi
	local child
	while read -r child; do
		[[ -n "$child" ]] && kill_process_tree "$child"
	done < <(pgrep -P "$pid" 2>/dev/null || true)
	kill "$pid" 2>/dev/null || true
}
cleanup() {
	local pid
	if [[ -n "$monitor_pid" ]] && kill -0 "$monitor_pid" 2>/dev/null; then
		kill_process_tree "$monitor_pid"
		wait_until_stopped "$monitor_pid" "$kill_grace" || true
		if ! kill -0 "$monitor_pid" 2>/dev/null; then
			wait "$monitor_pid" 2>/dev/null || true
		fi
	fi
	for pid in "${worker_pids[@]:-}"; do
		kill_process_tree "$pid"
	done
	for pid in "${worker_pids[@]:-}"; do
		wait_until_stopped "$pid" "$kill_grace" || true
		if ! kill -0 "$pid" 2>/dev/null; then
			wait "$pid" 2>/dev/null || true
		fi
	done
}
trap cleanup INT TERM EXIT

echo "Run directory: $run"
echo "Starting multiprocessing monitor..."
python3 "$script_dir/multiprocess_monitor.py" --exchange "$inbox" --log "$logs/monitor.log" &
monitor_pid="$!"
echo "Starting $workers workers..."
for ((i=0; i<workers; i++)); do
	(
		cd "$ultimate_dir"
		timeout --signal=TERM "$process_timeout" ./Ultimate.py \
			--full-output \
			--file "$file" --spec "$spec" --architecture "$architecture" \
			--data "$run/worker-$i/data" \
			--traceabstraction.multi.process.component WORKER \
			--traceabstraction.multi.process.exchange.root "$inbox" \
			--traceabstraction.multi.process.worker.id "worker-$i" \
			--traceabstraction.multi.process.job.timeout.in.seconds "$job_timeout"
	) >"$logs/worker-$i.log" 2>&1 &
	worker_pids+=("$!")
done

echo "Starting coordinator..."
coordinator_status=0
(
	cd "$ultimate_dir"
	timeout --signal=TERM "$process_timeout" ./Ultimate.py \
		--full-output \
		--file "$file" --spec "$spec" --architecture "$architecture" \
		--data "$run/coordinator-data" \
		--traceabstraction.multi.process.component COORDINATOR \
		--traceabstraction.multi.process.exchange.root "$inbox" \
		--traceabstraction.multi.process.worker.count "$workers" \
		--traceabstraction.multi.process.job.timeout.in.seconds "$job_timeout"
) 2>&1 | tee "$logs/coordinator.log" || coordinator_status=${PIPESTATUS[0]}

echo "Coordinator terminated; stopping worker and monitor process trees..."
worker_status=0
for i in "${!worker_pids[@]}"; do
	was_running=0
	if kill -0 "${worker_pids[$i]}" 2>/dev/null; then
		was_running=1
	fi
	if (( was_running )) && ! wait_until_stopped "${worker_pids[$i]}" "$shutdown_grace"; then
		echo "worker-$i did not exit within ${shutdown_grace}s of coordinator shutdown; terminating its process tree" >&2
		kill_process_tree "${worker_pids[$i]}"
	fi
	if ! wait_until_stopped "${worker_pids[$i]}" "$kill_grace"; then
		echo "worker-$i process tree survived forced termination" >&2
		worker_status=1
		continue
	fi
	status=0
	wait "${worker_pids[$i]}" || status=$?
	if (( !was_running && status != 0 )); then
		echo "worker-$i failed or timed out (status $status)" >&2
		worker_status=1
	fi
done
worker_pids=()
monitor_status=0
if kill -0 "$monitor_pid" 2>/dev/null; then
	kill_process_tree "$monitor_pid"
fi
if wait_until_stopped "$monitor_pid" "$kill_grace"; then
	wait "$monitor_pid" || monitor_status=$?
else
	echo "multiprocessing monitor survived forced termination" >&2
	monitor_status=1
fi
monitor_pid=""
trap - INT TERM EXIT

request_count=$(find "$inbox" -maxdepth 1 -type f -name 'request-*.json' | wc -l)
claim_count=$(find "$inbox" -maxdepth 1 -type f -name 'request-*.json.claim' | wc -l)
result_count=$(find "$inbox" -maxdepth 1 -type f -name 'result-*.json' | wc -l)
cancel_count=$(find "$inbox" -maxdepth 1 -type f -name 'cancel-*.json' | wc -l)
terminal_count=$(find "$inbox" -maxdepth 1 -type f \( -name 'result-*.json' -o -name 'cancel-*.json' \) \
	-printf '%f\n' | sed -E 's/^(result|cancel)-//' | sort -u | wc -l)
claimed_terminal_count=$(comm -12 \
	<(find "$inbox" -maxdepth 1 -type f -name 'request-*.json.claim' -printf '%f\n' \
		| sed -E 's/^request-|\.json\.claim$//g' | sort -u) \
	<(find "$inbox" -maxdepth 1 -type f \( -name 'result-*.json' -o -name 'cancel-*.json' \) -printf '%f\n' \
		| sed -E 's/^(result|cancel)-|\.json$//g' | sort -u) | wc -l)
claimant_count=$(find "$inbox" -maxdepth 1 -type f -name 'request-*.json.claim' \
	-exec cat {} + 2>/dev/null | sed '/^[[:space:]]*$/d' | sort -u | wc -l)

echo "---- Multiprocess verification ----"
printf 'requests=%s claims=%s results=%s cancellations=%s terminals=%s distinct-claimants=%s\n' \
	"$request_count" "$claim_count" "$result_count" "$cancel_count" "$terminal_count" "$claimant_count"

verification_status=0
[[ "$coordinator_status" -eq 0 ]] || { echo "coordinator failed (status $coordinator_status)" >&2; verification_status=1; }
[[ "$worker_status" -eq 0 ]] || verification_status=1
[[ "$monitor_status" -eq 0 ]] || { echo "multiprocessing monitor failed (status $monitor_status)" >&2; verification_status=1; }
[[ -f "$inbox/shutdown" ]] || { echo "missing shutdown marker" >&2; verification_status=1; }
[[ -f "$inbox/coordinator-status.json" ]] || { echo "missing coordinator status" >&2; verification_status=1; }
worker_status_count=$(find "$inbox" -maxdepth 1 -type f -name 'worker-status-*.json' | wc -l)
[[ "$worker_status_count" -eq "$workers" ]] || {
	echo "expected $workers worker status files, found $worker_status_count" >&2
	verification_status=1
}
[[ -f "$logs/monitor.log" ]] || { echo "missing monitor log" >&2; verification_status=1; }
[[ "$claim_count" -eq "$claimed_terminal_count" ]] || {
	echo "claim/terminal counts differ" >&2
	verification_status=1
}
if (( request_count >= workers && claimant_count != workers )); then
	echo "expected $workers distinct claiming workers, found $claimant_count" >&2
	verification_status=1
fi

if (( verification_status == 0 )); then
	echo "PASS: coordinator and all workers terminated cleanly"
	echo "Logs and exchange artifacts: $run"
else
	echo "FAIL: inspect $logs and $inbox" >&2
fi
exit "$verification_status"
