#!/usr/bin/env python3
"""Run the Lean audit and reject any axiom outside the standard three."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
result = subprocess.run(
    ["lake", "env", "lean", "Audit.lean"], cwd=ROOT / "lean", text=True,
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
)
print(result.stdout, end="")
(ROOT / "verification" / "axiom-audit.log").write_text(result.stdout)
if result.returncode:
    raise SystemExit(result.returncode)
audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout)
required = {"Lorentz.Construction.lorentz_counterexample",
            "LorentzSubmission.common_origin_counterexample"}
if not required.issubset({name for name, _ in audits}):
    raise SystemExit("Missing required endpoint audit output")
allowed = {"propext", "Quot.sound", "Classical.choice"}
for theorem, group in audits:
    unexpected = {name.strip() for name in group.split(",") if name.strip()} - allowed
    if unexpected:
        raise SystemExit(f"{theorem}: unexpected axioms {sorted(unexpected)}")
if "uses 'sorry'" in result.stdout:
    raise SystemExit("Unexpected proof hole in the audit dependencies")
print(f"PASS: {len(audits)} audited declarations use only permitted axioms.")
