#!/usr/bin/env python3
"""Account for the old inventory and preserve incoming archive bytes."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
inventory = json.loads((ROOT / "verification/reorganization/before.json").read_text())
lean_roots = {"verify.py", "README.md", "PROOF_MANIFEST.json", "lean-toolchain",
              "Audit.lean", "lakefile.toml", "lake-manifest.json", "Lorentz.lean"}
rows = []
for item in inventory:
    old = item["path"]
    if old.startswith("Lorentz/") or old in lean_roots:
        new = "lean/" + old
    elif old == "audit.log":
        new = "verification/optimized-axiom-audit.log"
    elif old.startswith("lorentz_plateau_constructions/"):
        new = "archive/plateau-input/" + old.split("/", 1)[1]
    elif old == "lorentz_plateau_counterexamples.pdf":
        new = "archive/plateau-counterexamples-copy.pdf"
    elif old.startswith("lorentz_self_similar"):
        new = "archive/origin/" + old
    else:
        new = old
    path = ROOT / new
    if not path.is_file():
        raise SystemExit(f"Missing relocated file: {old} -> {new}")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if new.startswith("archive/") and digest != item["sha256"]:
        raise SystemExit(f"Archived input changed: {new}")
    rows.append({"old_path": old, "new_path": new, "old_sha256": item["sha256"],
                 "current_sha256": digest, "unchanged": digest == item["sha256"]})
report = ROOT / "verification/reorganization"
(report / "file_moves.json").write_text(json.dumps(rows, indent=2) + "\n")
(report / "file_moves.tsv").write_text(
    "old_path\tnew_path\tstatus\n" + "".join(
        f"{r['old_path']}\t{r['new_path']}\t{'unchanged' if r['unchanged'] else 'updated'}\n"
        for r in rows))
print(f"PASS: {len(rows)} original files accounted for; archived inputs are byte-identical.")
