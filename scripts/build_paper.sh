#!/usr/bin/env bash
set -euo pipefail
lorentz_root=$(cd "$(dirname "$0")/.." && pwd)
lorentz_build=$(mktemp -d "${TMPDIR:-/tmp}/lorentz-paper.XXXXXX")
trap 'rm -rf "$lorentz_build"' EXIT
cd "$lorentz_root"
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir="$lorentz_build" paper/lorentz_counterexamples.tex
cp "$lorentz_build/lorentz_counterexamples.pdf" paper/lorentz_counterexamples.pdf
cp "$lorentz_build/lorentz_counterexamples.log" verification/paper-build.log
