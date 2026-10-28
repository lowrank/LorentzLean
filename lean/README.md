# A Lean formalization of the self-similar Lorentz construction

## Verification status

The original common-origin theorem has a complete proof. The project is now
pinned to Lean and Mathlib `v4.35.0-rc2` for Palomar compatibility. Current
build and axiom records are under [`../verification/`](../verification/).
Local Comparator accepted the statement with Lean, NanoDa, and con-ron;
that local run disabled its sandbox because this host denies user namespaces.
The private repository's CI runs the sandboxed configuration.
The old Lean 4.24 records are retained separately as historical evidence.

The two plateau counterexamples in the combined manuscript are still being
formalized. `Plateau/Reduction.lean` proves the parity-preserving induction
from finitely many plateau certificates; `Plateau/SeriesTools.lean` proves
contraction uniqueness and the polynomial subtraction identity.
`Plateau/Baseline.lean` proves the new baseline's resolvent identity, exact
extrema, strictness, and a lower bound from an even orbit term. These are
infrastructure results, not complete plateau endpoint theorems.

[`Challenge.lean`](Challenge.lean) independently states the completed origin
result using only Mathlib imports. [`Solution.lean`](Solution.lean) proves the
same statement. The one intentional Challenge hole is excluded from the
proof development and its axiom audit. The Palomar claim currently covers
only the origin result.

## What the theorem says

The endpoint is `Lorentz.Construction.lorentz_counterexample` in
`Lorentz/Counterexample.lean`:

```lean
∃ f : ℝ → ℝ,
  ContinuousOn f interval ∧ f 0 = 0 ∧
  (∃ x ∈ interval, f (-x) ≠ -f x) ∧
  ∀ n : ℕ, (∃ p : ℝ[X], IsBest f n p) ∧
    ∀ p : ℝ[X], IsBest f n p → p.eval 0 = 0
```

Here `interval` is `Set.Icc (-1 : ℝ) 1`. The nonoddness witness is inside the
approximation interval. Existence of a best polynomial at every degree is
included, in addition to the assertion about every best polynomial.

The approximation definitions in `Lorentz/Minimax.lean` are:

```lean
def HasErrorBound (f : ℝ → ℝ) (p : ℝ[X]) (E : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x - p.eval x| ≤ E

def IsBest (f : ℝ → ℝ) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧
  ∀ q : ℝ[X], q.natDegree ≤ n → ∀ E : ℝ,
    HasErrorBound f q E → HasErrorBound f p E
```

This is the usual best uniform approximation condition written with upper
bounds: every uniform error bound achieved by a competing polynomial is also
achieved by `p`. For continuous functions on the compact interval it is
equivalent to minimizing the uniform norm. It introduces no assumed best
approximation operator. Alternation proves both bestness and uniqueness in
this project.

## Mathematical construction

Write `T₃(x) = 4x³ - 3x` and `a = √2/2`. The series used in the proof are

\[
G(x)=\sum_{j\ge0}(-1/3)^j T_3^{\circ j}(x),\qquad
H_\beta(x)=\sum_{j\ge0}(-1/3)^j h_\beta(T_3^{\circ j}(x)),
\]

where

\[
h_\beta=T_4-1-2T_5+\beta T_7.
\]

The candidate is

\[
f_\varepsilon(x)=G(T_3(x))+\varepsilon H_\beta(x).
\]

`candidateFunction_eq_orbitSeries` also identifies it, on the approximation
interval, with the single series having polynomial forcing
`qε = T₃ + ε hβ`. It satisfies

\[
f_\varepsilon(x)=q_\varepsilon(x)
  -\tfrac13 f_\varepsilon(T_3(x)).
\]

The parameter `β` is determined by the exact rational coefficient data in
`CertificateData.lean`. Its real algebraic argument `z` is supplied by the
intermediate value theorem as a root of

\[
z^{12}-12z^{10}+54z^8-112z^6+105z^4-36z^2+1=0
\]

in the rational interval `[199238939/100000000, 199238940/100000000]`.
The proof does not need a separate identification of this algebraic root
with a trigonometric expression.

The finite certificate verifies degrees `0` through `6`. Cubic pullback
provides `3m+4` alternating contacts from a degree-`m` certificate. Combining
that fact with the degree-seven functional equation and strong induction on
`n`, using `m = n/3`, supplies certificates for every degree.

Nonoddness is explicit:

\[
f_\varepsilon(a)+f_\varepsilon(-a)=-3\varepsilon\ne0.
\]

## Scope of the perturbation parameter

This formalization proves the existence of a **sufficiently small positive
real `ε`**. The seven thresholds are obtained by local cusp and Lipschitz
estimates, compactness, and a positive finite minimum. All of those steps
are part of the Lean development.

The final Lean theorem does **not** assert that the particular numerical choice
`ε = 10⁻¹⁰` works. The revised written proof establishes the stronger sufficient
range `0 < ε ≤ 4 × 10⁻⁸`. A quantitative Lean corollary is still separate work;
the generic signed persistence lemma is formalized, while the final theorem
continues to use its fully proved existential thresholds.

## Audited and optimized written proof

- [Combined manuscript](../paper/lorentz_counterexamples.pdf), with
  [standalone LaTeX source](../paper/lorentz_counterexamples.tex).
- [Earlier optimized proof](../archive/origin/lorentz_self_similar_optimized.pdf)
  and [original proof](../archive/origin/lorentz_self_similar.pdf), preserved for comparison.
- [Independent exact certificate checker](../scripts/check_certificate.py):
  `python3 ../scripts/check_certificate.py` passes 400 checks using only Python's
  standard library and exact fractions. It reads the Lean coefficient tables,
  reconstructs the trigonometric grid, and checks identities, strict signs,
  defining-system determinants, alternation, and coefficient bounds.

The original PDF's equation (25) needs `≤` in its Lipschitz estimate: strict
inequality fails when the two points coincide. The revised proof corrects this.
The original PDF also refers to `verify_lorentz.py` and `certificate.json`, which
were absent from this folder; the new checker supplies a reproducible finite
audit without either file.

The main simplification separates the positive and negative contact sets
`Sₙ,ₛ`. A signed cusp and a bound relative to each contact give, with
`d = |x - ξ|` for a nearest contact of the prescribed sign,

\[
s(b_n(x)+\varepsilon r_n(x))
\le E_n+\varepsilon\lambda_n-(1/250-10^5\varepsilon)d.
\]

Apply both signs. The single condition `ε · 10⁵ ≤ 1/250` replaces the
near/far persistence split and its separate sign-preservation condition.
The new `Stability.signed_contact_persistence_bound` checks the generic
algebraic step in Lean.

## Compilation improvements

Historical module build times on this machine under Lean/Mathlib 4.24,
with the Mathlib cache:

| Module | Original audit build | Optimized build |
|---|---:|---:|
| `CertificateIdentities` | 788 s | 112 s |
| `CertificatePerturbation` | 211 s | 40 s |
| `Series` | 210 s | 2.3 s |

These are observed compiler timings, not a controlled performance benchmark;
machine load and parallel scheduling affect them. The shared coefficient
checker adds a module that took 4.4 s to build. The final rebuild of changed
modules and their dependents took 149 s; that is not a clean-build timing.

`PolynomialCertificate.lean` proves the soundness of rational coefficient-list
arithmetic once. The 66 slack identities and 18 grid recurrences now check exact
coefficient certificates with `decide +kernel`, replacing repeated large real
polynomial expansions. In `Series.lean`, explicitly supplying the summand to
the even/odd series rewrite removes expensive inference; its imports are also
narrower. All 131 existing theorem/lemma statements in the edited mathematical
modules were preserved, as were their existing docstrings.

## Proof organization

| Modules | Role |
|---|---|
| `Minimax` | Weak alternation, bestness, uniqueness, and the origin condition |
| `Composition`, `AllDegrees` | Cubic alternation lifting and the seven-to-all-degrees induction |
| `Series`, `Trigonometry`, `QuarterSeries` | Uniform convergence, continuity, functional equation, pairing, and phase identities |
| `PolynomialBounds`, `SeriesEstimates`, `AngularSeries`, `LocalComposition` | Polynomial stationarity, the exit-scale estimates, angular-to-spatial transfer, and local pullback |
| `Baseline`, `BaselineLocal` | The actual unperturbed series, its exact extrema, strictness, and local linear cusps |
| `ForcingPolynomials`, `Perturbation` | The actual perturbation series, stationarity, local Lipschitz bounds, and its nonzero even part |
| `Stability`, `CompactStability` | Preservation of finite signed contact bounds for a positive perturbation threshold |
| `CertificateBounds`, `CertificateRoot`, `CertificateData`, `CertificateSigns` | Sound rational interval evaluation, root existence, and exact coefficient/sign data |
| `CertificateGrid`, `CertificateOrder`, `CertificateGeometry`, `CertificateCompleteness` | Contact nodes, ordering, cubic maps, and completeness of the contact sets |
| `CertificateIdentities`, `CertificateFinite`, `CertificatePolynomials`, `CertificateAlternation` | Exact finite minimax identities and usable polynomial/alternation certificates |
| `PolynomialCertificate` | Shared soundness theorem for exact rational coefficient identities |
| `CertificatePerturbation` | Identification of the actual infinite-series values on the finite invariant grid |
| `ContactGeometry`, `PerturbationContacts`, `BaseCertificates` | The seven perturbed minimax certificates with a common positive parameter |
| `Counterexample` | The final unconditional existence theorem |
| `CertificateNorms` | Additional exact coefficient bounds, also included in the checked project |
| `Audit` | The final theorem statement and its logical-axiom dependency report |

The certificate data use exact rational arithmetic. Finite sign checks and the
optimized coefficient identities use `decide +kernel`; the other algebraic
proofs use proof-producing arithmetic tactics. External Python calculations
are not accepted as proof assumptions.

## Versions and rebuilding

- Lean: `leanprover/lean4:v4.35.0-rc2`.
- Mathlib: `v4.35.0-rc2`, locked by `lake-manifest.json` to commit
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

With Lean's `elan` toolchain manager installed, run from this directory:

```sh
lake exe cache get
lake env python3 verify.py
```

The script rechecks every local dependency in order, with one Lean worker
and one local module at a time. It then checks `Audit.lean`, rejects
`sorryAx` and any unexpected axiom in the audit, and writes
`verification.log`. It needs Python 3.9 or newer.

The ordinary project target is also available:

```sh
lake build
lake env lean Audit.lean
```

On a memory-constrained machine, prefer `verify.py` over a parallel build.
The source archive
excludes `.lake`, generated object files, and downloaded dependencies.

## Assumption audit

`Audit.lean` prints the axioms of the final theorem and several central
intermediate results. The recorded output for the final theorem is:

```text
'Lorentz.Construction.lorentz_counterexample' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard logical axioms. No new mathematical axiom,
`sorry`, `admit`, or `native_decide` is used by the proved source development.
The only deliberate hole is in the independent `Challenge.lean` statement.
