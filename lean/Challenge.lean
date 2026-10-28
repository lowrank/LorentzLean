module

public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# A nonodd function whose best approximants all vanish at zero

This independent statement imports only Mathlib. `IsBest` compares uniform
error bounds over every real polynomial of degree at most `n`; it is the
usual minimax condition on the compact interval. Existence is part of the
conclusion, and nonoddness has a witness inside that interval.

The deliberate hole belongs only to this advertised statement. The matching
declaration in `Solution.lean` is proved from the full development.
The two additional degree-plateau constructions in the manuscript are not
claims of this submission.
-/

namespace LorentzSubmission

open Polynomial Set

/-- Uniform approximation error at most `E` on `[-1,1]`. -/
def HasErrorBound (f : ℝ → ℝ) (p : ℝ[X]) (E : ℝ) : Prop :=
  ∀ x ∈ Icc (-1 : ℝ) 1, |f x - p.eval x| ≤ E

/-- Every error bound attained by a competing polynomial is also attained by `p`. -/
def IsBest (f : ℝ → ℝ) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧
    ∀ q : ℝ[X], q.natDegree ≤ n → ∀ E : ℝ,
      HasErrorBound f q E → HasErrorBound f p E

/-- A continuous nonodd function, normalized at zero, with best approximants
of every degree, all of which vanish at zero. -/
theorem common_origin_counterexample :
    ∃ f : ℝ → ℝ,
      ContinuousOn f (Icc (-1 : ℝ) 1) ∧ f 0 = 0 ∧
      (∃ x ∈ Icc (-1 : ℝ) 1, f (-x) ≠ -f x) ∧
      ∀ n : ℕ, (∃ p : ℝ[X], IsBest f n p) ∧
        ∀ p : ℝ[X], IsBest f n p → p.eval 0 = 0 := by
  sorry

end LorentzSubmission
