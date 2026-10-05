#!/usr/bin/env python3
"""Run the complete Nanoda check without letting resource pressure kill the runner.

This wrapper only manages the process and records evidence. It never changes
the export, Nanoda configuration, declaration selection or checker rules.
"""
import argparse
import json
import os
import re
import signal
import subprocess
import time
from pathlib import Path

GIB = 1024**3


def read_memory():
    values = {}
    for line in Path('/proc/meminfo').read_text().splitlines():
        key, value = line.split(':', 1)
        if key in ('MemTotal', 'MemAvailable', 'SwapTotal', 'SwapFree'):
            values[key] = int(value.split()[0]) * 1024
    if len(values) != 4:
        raise RuntimeError('Linux memory telemetry is unavailable')
    return values


def read_rss(pid):
    try:
        for line in Path(f'/proc/{pid}/status').read_text().splitlines():
            if line.startswith('VmRSS:'):
                return int(line.split()[1]) * 1024
    except FileNotFoundError:
        pass
    return 0


def last_trace_entries(out):
    entries = []
    for path in sorted(out.glob('*.trace')):
        with path.open('rb') as stream:
            stream.seek(max(0, path.stat().st_size - 4096))
            lines = stream.read().decode('utf-8', errors='replace').splitlines()
        if lines:
            entries.append(lines[-1])
    return entries


def stop_checker(process):
    # The process group belongs only to this checker and its worker threads.
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        return process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        return process.wait()


def run_checked(binary, directory, poll_seconds=1, heartbeat_seconds=60,
                max_seconds=19800):
    out = directory.resolve()
    command = [str(binary.resolve()), str(out / 'nanoda-config.json')]
    record = {
        'workflow_commit': os.environ.get('GITHUB_SHA'),
        'run_id': os.environ.get('GITHUB_RUN_ID'),
        'command': command,
        'status': 'running',
        'checker_exit_code': None,
        'accepted': False,
        'memory_reserve_bytes': GIB,
        'max_seconds': max_seconds,
    }
    result_path = out / 'nanoda-result.json'

    def save():
        result_path.write_text(json.dumps(record, indent=2) + '\n')

    # Check telemetry before starting any expensive work.
    read_memory()
    save()
    start = time.monotonic()
    next_heartbeat = start
    peak_rss = 0
    reason = None
    with (out / 'solution.ndjson').open('rb') as source, \
            (out / 'nanoda.log').open('w') as log, \
            (out / 'memory-monitor.jsonl').open('w') as monitor:
        process = subprocess.Popen(command, stdin=source, stdout=log,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while process.poll() is None:
                now = time.monotonic()
                memory = read_memory()
                rss = read_rss(process.pid)
                peak_rss = max(peak_rss, rss)
                exhausted = (memory['MemAvailable'] < GIB and
                             memory['SwapFree'] < GIB)
                if now - start >= max_seconds:
                    reason = 'time_limit'
                elif exhausted:
                    reason = 'memory_pressure'
                if now >= next_heartbeat or reason:
                    sample = {'elapsed_seconds': round(now - start, 2),
                              'rss_bytes': rss, **memory,
                              'last_declarations': last_trace_entries(out)}
                    monitor.write(json.dumps(sample) + '\n')
                    monitor.flush()
                    print(json.dumps(sample), flush=True)
                    next_heartbeat = now + heartbeat_seconds
                if reason:
                    print(f'::error::Nanoda stopped: {reason}; full acceptance was not obtained.',
                          flush=True)
                    stop_checker(process)
                    break
                time.sleep(poll_seconds)
        finally:
            if process.poll() is None:
                stop_checker(process)
        record['checker_exit_code'] = process.returncode

    with (out / 'nanoda.log').open('rb') as stream:
        stream.seek(max(0, (out / 'nanoda.log').stat().st_size - 8192))
        text = stream.read().decode('utf-8', errors='replace')
    print(text, flush=True)
    receipt = re.search(r'^Checked ([0-9]+) declarations with no errors$', text, re.M)
    targets = out / 'checked-targets.txt'
    resolved = targets.is_file() and targets.stat().st_size > 0
    record.update({
        'elapsed_seconds': round(time.monotonic() - start, 2),
        'peak_sampled_rss_bytes': peak_rss,
        'checked_declarations': int(receipt[1]) if receipt else None,
        'registered_targets_resolved': resolved,
        'accepted': reason is None and process.returncode == 0 and
                    receipt is not None and resolved,
    })
    record['status'] = ('passed' if record['accepted'] else reason or
                        ('checker_failed' if process.returncode else 'incomplete_receipt'))
    save()
    if record['accepted']:
        return 0
    return 75 if reason else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', required=True, type=Path)
    parser.add_argument('--directory', default='external-check', type=Path)
    args = parser.parse_args()
    return run_checked(args.binary, args.directory)


if __name__ == '__main__':
    raise SystemExit(main())
