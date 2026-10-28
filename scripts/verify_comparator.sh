#!/usr/bin/env bash
set -euo pipefail
lorentz_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$lorentz_root/lean"
lorentz_prefix=$(lean --print-prefix)
lorentz_config=$(mktemp "${TMPDIR:-/tmp}/lorentz-comparator.XXXXXX.json")
trap 'rm -f "$lorentz_config"' EXIT
python3 - "$lorentz_prefix" "$lorentz_config" <<'PY'
import json
from pathlib import Path
import sys

prefix, destination = sys.argv[1:]
config = json.loads(Path("comparator.json").read_text())
if "external_kernels" in config:
    raise SystemExit("Palomar refuses external_kernels in the committed configuration")
config.pop("enable_nanoda", None)
config["external_kernels"] = {}
for name, executable in (("nanoda", "nanoda_bin"), ("con-ron", "con-ron")):
    path = Path(prefix) / "bin" / executable
    if not path.is_file():
        raise SystemExit(f"Missing bundled checker: {path}")
    # Con-ron otherwise starts up to 16 workers, multiplying the memory used
    # by the large exact-rational certificate reductions. One worker checks
    # the identical declaration stream in the same verified mode.
    config["external_kernels"][name] = [str(path)] + (["--jobs=1"] if name == "con-ron" else [])
Path(destination).write_text(json.dumps(config, indent=2) + "\n")
PY
lake comparator --config "$lorentz_config" "$@"
