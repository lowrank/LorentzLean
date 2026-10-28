module

public import Lorentz.Counterexample

@[expose] public section

/-! The proved counterpart of the independent Palomar statement. -/

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
  exact Lorentz.Construction.lorentz_counterexample

end LorentzSubmission
