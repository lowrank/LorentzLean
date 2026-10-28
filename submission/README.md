# Palomar preparation

This package follows the [current submission instructions](https://palomar-registry.org/how-to-submit).
The source repository contains the substantive formalization. Its selected
Lake project is the nested directory `lean`.

## Exact scope

The compared theorem is
`LorentzSubmission.common_origin_counterexample`. It asserts the existence of
a continuous function on `[-1,1]` that vanishes at zero, fails oddness at a point
in that interval, and has best uniform approximants of every degree, all of
which vanish at zero. The definition compares with every polynomial of degree
at most `n`, without a pre-assumed best-approximation operator.

`Challenge.lean` imports only Mathlib and states the result independently.
`Solution.lean` proves the same statement from the full development. The
Challenge contains one deliberate `sorry`, as the protocol permits. The
Solution and its proof dependencies contain no proof holes or custom axioms.

The manuscript's two plateau counterexamples are additional mathematics;
their complete Lean endpoints are still in development and are excluded from
this Comparator claim. The original Lean result is existential in the
perturbation size, whereas the manuscript also proves an explicit range.

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
A local run with `--inadvisably-no-sandbox` is useful only
for trusted source on a host that cannot create those namespaces; record that
limitation and do not describe it as the registry's sandboxed verification.

## Fields to finish before submission

The metadata draft is [formalization.yaml](../lean/formalization.yaml).
The author, responsible maintainer, and repository license require the
owner's information. Their explicit `TEMPLATE:` values must be replaced,
and the chosen license must be placed at repository root as `LICENSE`.
No authorship or licensing decision has been inferred.

The working repository is [lowrank/LorentzLean](https://github.com/lowrank/LorentzLean),
and is private at the owner's request. CI can verify this private repository.
Palomar intake requires a public snapshot, so registry submission remains
pending a later explicit decision about publication as well as the metadata.
After those fields and all checks are complete, an authorized public snapshot
would need a full pushed 40-character commit.
The submission form values are:

| Field | Value |
|---|---|
| Repository | `lowrank/LorentzLean`, currently private and ineligible for intake |
| Commit | Full SHA of the eventual authorized public snapshot |
| Project path | `lean` |
| Comparator configuration | Leave blank: default inside `lean` |
| Formalization metadata | Leave blank: default inside `lean` |

The owner can submit at <https://submit.palomar-registry.org/>. Preparing these
files has not submitted, published, or registered the result.
