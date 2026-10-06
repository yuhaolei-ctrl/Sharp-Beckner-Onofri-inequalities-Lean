#!/usr/bin/env python3
"""Check that Challenge.lean and BecknerOnofri/Statement.lean share their vocabulary.

Comparator requires every definition reached by a compared statement to be the
same constant in the challenge and in the solution environment. The solution
obtains these definitions from `BecknerOnofri.Statement`. This check makes the
identity hold by construction: both files must have the same `public import`
lines and a byte-identical block between the `BEGIN VOCABULARY` and
`END VOCABULARY` markers.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BEGIN, END = "-- BEGIN VOCABULARY\n", "-- END VOCABULARY\n"


def parts(path: Path) -> tuple[list[str], str]:
    text = path.read_text(encoding="utf-8")
    imports = re.findall(r"^public import .*$", text, re.M)
    try:
        start = text.index(BEGIN)
        stop = text.index(END, start)
    except ValueError:
        sys.exit(f"{path.relative_to(ROOT)}: missing vocabulary markers")
    return imports, text[start:stop + len(END)]


def main() -> int:
    challenge = parts(ROOT / "Challenge.lean")
    statement = parts(ROOT / "BecknerOnofri" / "Statement.lean")
    failed = False
    if challenge[0] != statement[0]:
        print("Challenge.lean and BecknerOnofri/Statement.lean import different modules")
        failed = True
    if challenge[1] != statement[1]:
        print("Challenge.lean and BecknerOnofri/Statement.lean have different vocabulary blocks")
        failed = True
    if not failed:
        print("vocabulary blocks are identical")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
