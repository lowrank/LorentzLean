# Palomar preparation

This package follows the [current submission instructions](https://palomar-registry.org/how-to-submit).
The source repository contains the substantive formalization. Its selected
Lake project is the nested directory `lean`.

## Exact scope

The compared theorems in `LorentzSubmission` are:

- `common_origin_counterexample`: a normalized nonodd continuous function
  whose best approximants of every degree all vanish at zero.
- `odd_plateau_counterexample`: a normalized nonodd continuous function with
  equal best approximants at every pair `(2k+1, 2k+2)`.
- `even_plateau_counterexample`: a noneven continuous function with equal
  best approximants at every pair `(2k, 2k+1)`.

All symmetry witnesses lie inside `[-1,1]`. The minimax definition compares
against every polynomial of the relevant degree; existence and the required
uniqueness are proved without assuming a best-approximation operator.

`Challenge.lean` imports only Mathlib and states these results independently.
Its three deliberate holes belong to the advertised statements, as permitted
by the protocol. `Solution.lean` proves all three matching statements with
no proof holes or custom axioms. The Lean constructions prove existence of
sufficiently small positive perturbations. The manuscript also establishes
explicit numerical choices, which are not claimed by these endpoints.

## Verification

The project pins `leanprover/lean4:v4.35.0-rc2` and the matching Mathlib release.
`lake-manifest.json` fixes the transitive Git revisions. All live Lean source
files use the module system and are below Palomar's line limits.

Run from the repository root:

```sh
python3 scripts/check_sources.py
./scripts/verify_comparator.sh
```

The script uses the pinned toolchain's Comparator and explicitly registers
its bundled NanoDa and con-ron checkers in a temporary configuration. The
committed `comparator.json` contains no forbidden `external_kernels` field.
The default run requires working Bubblewrap user namespaces. The CI workflow
uses this default and has [passed on the private repository](https://github.com/lowrank/LorentzLean/actions/runs/40778650615).
The wrapper limits con-ron to one worker, preserving its verified mode while
controlling the memory needed for exact certificate reductions.
A local run with `--inadvisably-no-sandbox` is useful only
for trusted source on a host that cannot create those namespaces; record that
limitation and do not describe it as the registry's sandboxed verification.

## Submission metadata and snapshot

The author and responsible maintainer are **Yimin Zhong**, as confirmed by
the owner. The repository uses **Apache-2.0**, with the full license at
[`LICENSE`](../LICENSE) and the attribution at [`NOTICE`](../NOTICE).
[`formalization.yaml`](../lean/formalization.yaml) records all three results,
AI assistance, review status, the original source artifacts, and the remaining
difference between existential and explicit perturbation sizes.

The source repository is [lowrank/LorentzLean](https://github.com/lowrank/LorentzLean).
The owner authorized making it public after verification. No Palomar submission
or registration has been sent. Use the full 40-character SHA of the final
pushed, checked snapshot; `git rev-parse HEAD` prints it.

| Form field | Value |
|---|---|
| Repository | `https://github.com/lowrank/LorentzLean` |
| Commit | Full SHA of the final checked snapshot |
| Project path | `lean` |
| Comparator configuration | Leave blank; uses `lean/comparator.json` |
| Formalization metadata | Leave blank; uses `lean/formalization.yaml` |
| Relationship | Responsible author/maintainer of the substantive formalization |

Suggested review note:

> Three existential counterexamples in uniform polynomial approximation.
> Exact algebraic tables, analytic contact persistence, alternation, and
> cubic self-similarity are formalized. The manuscript also gives explicit
> perturbation sizes, which are not claimed by the Lean endpoints. The
> development was audited and extended with AI assistance; independent
> human mathematical review is not recorded.

The [submission form](https://submit.palomar-registry.org/) requires GitHub
sign-in to confirm write access. Agents should instead follow Palomar's
[documented protocol](https://palomar-registry.org/llms.txt), if instructed
to submit. Registration is a subsequent explicit action after review.
