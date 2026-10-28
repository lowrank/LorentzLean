# Lorentz counterexamples

Three constructions in uniform polynomial approximation, with a combined
manuscript, exact arithmetic certificates, and a Lean development.

- **Read the mathematics:** [combined PDF](paper/lorentz_counterexamples.pdf)
  and [standalone LaTeX source](paper/lorentz_counterexamples.tex).
- **Read the formal theorem:** [independent statement](lean/Challenge.lean),
  [proved solution](lean/Solution.lean), and [Lean project guide](lean/README.md).
- **Prepare a registry submission:** [Palomar preparation notes](submission/README.md).

| Result | Mathematical proof | Lean status |
|---|---|---|
| Nonodd function whose best approximants all vanish at zero | Part I; exact finite certificate checked | Full unconditional existence theorem; sufficiently small positive perturbation |
| Nonodd function with equal approximants in degrees `(2k+1, 2k+2)` | Part II; supplied exact audit passes | In progress; degree propagation, series tools, and baseline estimates proved |
| Noneven function with equal approximants in degrees `(2k, 2k+1)` | Part II; supplied exact audit passes | In progress; degree propagation, series tools, and baseline estimates proved |

The written proofs include explicit perturbation sizes. The current Lean
endpoint for Part I proves existence of a sufficiently small positive size;
it does not assert the numerical choice. The Palomar statement currently
covers Part I only.

## Directory layout

| Directory | Contents |
|---|---|
| `paper/` | One current manuscript, as `.tex` and `.pdf` |
| `lean/` | Pinned Lake project, mathematical modules, statement, solution, and Comparator configuration |
| `certificates/plateau/` | Exact JSON data, independent audits, and original generators for the two plateau constructions |
| `scripts/` | Root-level build and verification entry points |
| `submission/` | Submission instructions and remaining metadata requirements |
| `verification/` | Build/audit records, source manifest, performance records, and relocation inventory |
| `archive/` | Preserved incoming PDFs, LaTeX sources, and the complete plateau input package |

## Reproduce

From this directory:

```sh
python3 scripts/check_sources.py
python3 scripts/check_certificate.py
python3 certificates/plateau/audit_odd.py
python3 certificates/plateau/audit_even.py
./scripts/build_paper.sh
```

With `elan` installed:

```sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

For a complete sequential recheck of all local proof modules, use
`lake env python3 verify.py` from `lean/`. For the registry's statement and
independent-kernel checks, run `./scripts/verify_comparator.sh` from the
repository root. See the submission notes for host requirements.

The original source archive and historical Lean 4.24 timings are retained in
`verification/`; they are distinguished from the current toolchain checks.
