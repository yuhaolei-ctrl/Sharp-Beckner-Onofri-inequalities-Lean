"""Process-level regression checks for evidence and resource-failure handling."""
import importlib.util
import io
import json
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('nanoda_runner', ROOT / 'scripts/run_nanoda.py')
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)
AMPLE = {'MemTotal': 16 * RUNNER.GIB, 'MemAvailable': 8 * RUNNER.GIB,
         'SwapTotal': 8 * RUNNER.GIB, 'SwapFree': 8 * RUNNER.GIB}


class RunnerTests(unittest.TestCase):
    def run_fake(self, body, memory=AMPLE, resolved=True, max_seconds=3):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            binary = out / 'fake-checker'
            binary.write_text('#!/usr/bin/env python3\n' + body)
            binary.chmod(0o755)
            (out / 'nanoda-config.json').write_text('{}')
            (out / 'solution.ndjson').write_text('fixture input\n')
            (out / 'checked-targets.txt').write_text('target\n' if resolved else '')
            # Expected failures must not emit real GitHub Actions annotations.
            with patch.object(RUNNER, 'read_memory', return_value=memory), redirect_stdout(io.StringIO()):
                code = RUNNER.run_checked(binary, out, poll_seconds=0.01,
                                          heartbeat_seconds=60, max_seconds=max_seconds)
            result = json.loads((out / 'nanoda-result.json').read_text())
            self.assertTrue((out / 'nanoda.log').is_file())
            self.assertTrue((out / 'memory-monitor.jsonl').is_file())
            return code, result

    def test_accepts_complete_success_receipt(self):
        code, result = self.run_fake("print('Checked 5 declarations with no errors')\n")
        self.assertEqual(code, 0)
        self.assertTrue(result['accepted'])
        self.assertEqual(result['checked_declarations'], 5)

    def test_checker_failure_cannot_be_hidden_by_success_text(self):
        code, result = self.run_fake("print('Checked 5 declarations with no errors')\nraise SystemExit(1)\n")
        self.assertEqual(code, 1)
        self.assertEqual(result['status'], 'checker_failed')
        self.assertFalse(result['accepted'])

    def test_zero_exit_without_receipt_is_not_acceptance(self):
        code, result = self.run_fake("print('incomplete output')\n")
        self.assertEqual(code, 1)
        self.assertEqual(result['status'], 'incomplete_receipt')

    def test_targets_must_be_resolved(self):
        code, result = self.run_fake("print('Checked 5 declarations with no errors')\n", resolved=False)
        self.assertEqual(code, 1)
        self.assertFalse(result['accepted'])

    def test_memory_pressure_stops_checker_and_preserves_failure_record(self):
        memory = {**AMPLE, 'MemAvailable': 0, 'SwapFree': 0}
        code, result = self.run_fake('import time\ntime.sleep(30)\n', memory=memory)
        self.assertEqual(code, 75)
        self.assertEqual(result['status'], 'memory_pressure')
        self.assertIsNotNone(result['checker_exit_code'])
        self.assertFalse(result['accepted'])

    def test_swap_can_cover_low_physical_memory(self):
        memory = {**AMPLE, 'MemAvailable': 0}
        code, result = self.run_fake("print('Checked 5 declarations with no errors')\n", memory=memory)
        self.assertEqual(code, 0)
        self.assertTrue(result['accepted'])

    def test_deadline_preserves_failure_record(self):
        code, result = self.run_fake('import time\ntime.sleep(30)\n', max_seconds=0)
        self.assertEqual(code, 75)
        self.assertEqual(result['status'], 'time_limit')
        self.assertFalse(result['accepted'])


if __name__ == '__main__':
    unittest.main()
