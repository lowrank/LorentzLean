module

public import Lorentz.Counterexample
public import Lorentz.Plateau.OddCounterexample
public import Lorentz.Plateau.EvenCounterexample

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

/-- A nonodd function with identical best approximants at every odd/even pair. -/
theorem odd_plateau_counterexample :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) ∧ f 0 = 0 ∧
      (∃ x ∈ Icc (-1 : ℝ) 1, f (-x) ≠ -f x) ∧
      ∀ k : ℕ, ∃ p : ℝ[X], IsBest f (2 * k + 1) p ∧ IsBest f (2 * k + 2) p ∧
        ∀ q r : ℝ[X], IsBest f (2 * k + 1) q → IsBest f (2 * k + 2) r → q = r := by
  exact Lorentz.Plateau.odd_plateau_counterexample

/-- A noneven function with identical best approximants at every even/odd pair. -/
theorem even_plateau_counterexample :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) ∧
      (∃ x ∈ Icc (-1 : ℝ) 1, f (-x) ≠ f x) ∧
      ∀ k : ℕ, ∃ p : ℝ[X], IsBest f (2 * k) p ∧ IsBest f (2 * k + 1) p ∧
        ∀ q r : ℝ[X], IsBest f (2 * k) q → IsBest f (2 * k + 1) r → q = r := by
  exact Lorentz.Plateau.even_plateau_counterexample

end LorentzSubmission
