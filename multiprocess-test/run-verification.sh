#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ULTIMATE_DIR="${ULTIMATE_DIR:?Set ULTIMATE_DIR to the extracted Automizer distribution}"
RUN_ROOT="${RUN_ROOT:-$DIR/runtime}"

mkdir -p "$RUN_ROOT"

worker_pid=""
stop_worker() {
	if [[ -n "$worker_pid" ]] && kill -0 "$worker_pid" 2>/dev/null; then
		kill "$worker_pid" 2>/dev/null || true
		wait "$worker_pid" 2>/dev/null || true
	fi
	worker_pid=""
}
trap stop_worker EXIT INT TERM

echo "---- Verification ----"
for file in "$DIR"/examples/*.c; do
	name="$(basename "$file" .c)"
	run="$RUN_ROOT/$name"
	inbox="$run/exchange/worker-0"
	mkdir -p "$inbox" "$run/worker-data" "$run/coordinator-data" "$run/logs"

	"$ULTIMATE_DIR"/Ultimate.py --file "$file" --spec "$DIR/examples/reach.prp" --architecture 32bit \
		--data "$run/worker-data" \
		--traceabstraction.multi.process.component WORKER \
		--traceabstraction.multi.process.exchange.root "$inbox" \
		>"$run/logs/worker.log" 2>&1 &
	worker_pid=$!

	for spec in "$DIR"/examples/*.prp; do
		"$ULTIMATE_DIR"/Ultimate.py --file "$file" --spec "$spec" --architecture 32bit \
			--data "$run/coordinator-data" \
			--traceabstraction.multi.process.component COORDINATOR \
			--traceabstraction.multi.process.exchange.root "$inbox" \
			--traceabstraction.multi.process.worker.count 1
	done

	# Give the worker a bounded grace period to atomically publish the final result before shutdown.
	sleep 2
	stop_worker
done
