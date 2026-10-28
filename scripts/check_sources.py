#!/usr/bin/env python3
"""Check this repository's module headers, file limits, and proof-hole policy.

This local preflight does not replace Lean, Comparator, or Palomar's scanner.
"""
from pathlib import Path
import os
import re

ROOT = Path(__file__).resolve().parents[1]
errors = []
count = 0
for directory, subdirs, names in os.walk(ROOT, followlinks=False):
    subdirs[:] = [name for name in subdirs if name not in {".git", ".lake", "__pycache__"}]
    for name in names:
        if not name.endswith(".lean"):
            continue
        path = Path(directory) / name
        relative = path.relative_to(ROOT)
        count += 1
        if path.is_symlink():
            errors.append(f"{relative}: Lean symlinks are not permitted")
            continue
        text = path.read_text()
        if len(text.splitlines()) > 10000:
            errors.append(f"{relative}: more than 10000 lines")
        if name != "lakefile.lean" and not re.match(r"\Amodule(?:\s|$)", text):
            errors.append(f"{relative}: expected initial module header")
        if relative == Path("lean/Challenge.lean"):
            if len(text.splitlines()) > 1000 or len(text.encode()) > 100 * 1024:
                errors.append(f"{relative}: Challenge exceeds Palomar's size limits")
        else:
            # A conservative check of executable proof-hole lines; comments may
            # explain forbidden mechanisms without invoking them.
            for number, line in enumerate(text.splitlines(), 1):
                if re.search(r"(?:\bby\s+|^\s*)(?:sorry|admit|axiom|native_decide)\b", line):
                    errors.append(f"{relative}:{number}: proof hole or nonstandard assumption")
if errors:
    raise SystemExit("\n".join(errors))
print(f"PASS: {count} Lean files; module headers, size limits, and proof-hole preflight.")
