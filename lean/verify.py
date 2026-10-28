#!/usr/bin/env python3
"""Recheck every local dependency, sequentially, and print the axiom audit.

Run from the project with:
    lake update
    lake exe cache get
    lake env python3 verify.py

The sequential schedule keeps memory use below a parallel whole-project build.
No precompiled local proof files are needed or trusted as a substitute for
checking the source: each local module is rebuilt in dependency order.
"""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / ".lake" / "build" / "lib" / "lean"
LEAN = shutil.which("lean")
if LEAN is None:
    raise SystemExit("Lean was not found. Run this script with `lake env python3 verify.py`.")

ordered: list[tuple[str, Path]] = []
seen: set[str] = set()


def visit(module: str) -> None:
    if module in seen:
        return
    seen.add(module)
    source = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
    if not source.is_file():
        return  # A pinned external dependency, supplied by Mathlib/Lake.
    text = source.read_text(encoding="utf-8")
    for line in text.splitlines():
        match = re.match(r"^(?:public\s+)?import\s+(.*)$", line)
        if match:
            for dependency in match.group(1).split():
                visit(dependency)
    ordered.append((module, source))


visit("Audit")
OUTPUT.mkdir(parents=True, exist_ok=True)
environment = os.environ.copy()
environment["LEAN_PATH"] = str(OUTPUT) + os.pathsep + environment.get("LEAN_PATH", "")
log: list[str] = []


def record(text: str) -> None:
    print(text, flush=True)
    log.append(text)


version = subprocess.run([LEAN, "--version"], text=True, capture_output=True, check=True)
record(version.stdout.strip())
record(f"Rechecking {len(ordered)} local modules sequentially.")

for index, (module, source) in enumerate(ordered, start=1):
    target = OUTPUT.joinpath(*module.split(".")).with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    record(f"[{index}/{len(ordered)}] {module}")
    result = subprocess.run(
        [LEAN, "-j", "1", "-o", str(target), str(source.relative_to(ROOT))],
        cwd=ROOT,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.stdout.strip():
        record(result.stdout.rstrip())
    if result.returncode or "sorryAx" in result.stdout or "uses 'sorry'" in result.stdout:
        record(f"FAILED: {module}")
        (ROOT / "verification.log").write_text("\n".join(log) + "\n", encoding="utf-8")
        raise SystemExit(result.returncode or 1)
    if module == "Audit":
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        audited = re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout)
        if not audited:
            raise SystemExit("The expected axiom-audit output was not found.")
        for group in audited:
            names = {name.strip() for name in group.split(",") if name.strip()}
            if names - allowed:
                raise SystemExit(f"Unexpected axioms: {sorted(names - allowed)}")

record("SUCCESS: every local dependency and the final theorem passed Lean checking.")
(ROOT / "verification.log").write_text("\n".join(log) + "\n", encoding="utf-8")
