# Verification records

Current source hashes, exact toolchain pin, and proof scope are recorded in
[`../lean/PROOF_MANIFEST.json`](../lean/PROOF_MANIFEST.json).

| Record | Meaning |
|---|---|
| `palomar-build.log` | Successful build on Lean/Mathlib 4.35.0-rc2 |
| `axiom-audit.log` | Endpoint and central lemma axioms; generated and checked by `scripts/check_axioms.py` |
| `comparator-local.log` | Matching independent statement and proved solution, accepted by Lean, NanoDa, and con-ron; local sandbox disabled |
| `comparator-sandbox.log` | Local host limitation: Bubblewrap cannot establish its user namespace |
| `paper-build.log` | Final LaTeX build log |
| `plateau/*-certificate-audit.log` | Exact Python audits of the supplied odd/even plateau certificates |
| `reorganization/before.json` | Source inventory immediately before the reorganization |
| `reorganization/file_moves.json` / `.tsv` | Mapping of every earlier file to its new location |
| `original-build.log` | Historical original Lean 4.24 build |
| `optimized-build.log` / `optimized-axiom-audit.log` | Historical optimized Lean 4.24 build and audit |
| `performance.json` | Historical optimization observations; not a controlled benchmark |
| `original-sources.tar.gz` | Historical original source snapshot |

The local Comparator check used `--inadvisably-no-sandbox` on this trusted
development because the host denies Bubblewrap's user namespace. The CI
workflow uses the default sandbox and the same pinned independent checkers.
Local success and CI success are separate records.

The exact Python certificate checks supplement the mathematics; they are not
assumptions of a Lean theorem. In particular, a passing external audit of a
plateau certificate does not complete the missing Lean endpoint proof.
