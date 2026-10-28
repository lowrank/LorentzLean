module

public import Mathlib

@[expose] public section

/-! A rational interval evaluator.  Its soundness is proved over the reals;
    numerical uses below are discharged by kernel-checked arithmetic. -/
namespace Lorentz.Certificate

/-- Coefficients are in increasing order of degree. -/
def eval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, z => (c : ℝ) + z * eval cs z

/-- A lower Horner bound, valid when the argument is nonnegative. -/
def lower : List ℚ → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | c :: cs, l, u =>
      let b := lower cs l u
      c + (if b < 0 then u else l) * b

/-- An upper Horner bound, valid when the argument is nonnegative. -/
def upper : List ℚ → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | c :: cs, l, u =>
      let b := upper cs l u
      c + (if b < 0 then l else u) * b

 theorem eval_bounds (cs : List ℚ) (z : ℝ) (l u : ℚ)
    (hl : (l : ℝ) ≤ z) (hu : z ≤ (u : ℝ)) (hz : 0 ≤ z) :
    (lower cs l u : ℝ) ≤ eval cs z ∧ eval cs z ≤ (upper cs l u : ℝ) := by
  induction cs with
  | nil => simp [eval, lower, upper]
  | cons c cs ih =>
      constructor
      · simp only [eval, lower, Rat.cast_add, Rat.cast_mul]
        apply add_le_add_right
        apply le_trans _ (mul_le_mul_of_nonneg_left ih.1 hz)
        split_ifs with h
        · exact mul_le_mul_of_nonpos_right hu (le_of_lt (by exact_mod_cast h))
        · exact mul_le_mul_of_nonneg_right hl (by exact_mod_cast (le_of_not_gt h))
      · simp only [eval, upper, Rat.cast_add, Rat.cast_mul]
        apply add_le_add_right
        apply le_trans (mul_le_mul_of_nonneg_left ih.2 hz)
        split_ifs with h
        · exact mul_le_mul_of_nonpos_right hl (le_of_lt (by exact_mod_cast h))
        · exact mul_le_mul_of_nonneg_right hu (by exact_mod_cast (le_of_not_gt h))

 theorem eval_nonneg (cs : List ℚ) (z : ℝ) (l u : ℚ)
    (hl : (l : ℝ) ≤ z) (hu : z ≤ (u : ℝ)) (hz : 0 ≤ z)
    (hc : 0 ≤ lower cs l u) : 0 ≤ eval cs z := by
  exact le_trans (by exact_mod_cast hc) (eval_bounds cs z l u hl hu hz).1

 theorem eval_pos (cs : List ℚ) (z : ℝ) (l u : ℚ)
    (hl : (l : ℝ) ≤ z) (hu : z ≤ (u : ℝ)) (hz : 0 ≤ z)
    (hc : 0 < lower cs l u) : 0 < eval cs z := by
  exact lt_of_lt_of_le (by exact_mod_cast hc) (eval_bounds cs z l u hl hu hz).1

 theorem eval_lt (cs : List ℚ) (z : ℝ) (l u b : ℚ)
    (hl : (l : ℝ) ≤ z) (hu : z ≤ (u : ℝ)) (hz : 0 ≤ z)
    (hc : upper cs l u < b) : eval cs z < (b : ℝ) := by
  exact lt_of_le_of_lt (eval_bounds cs z l u hl hu hz).2 (by exact_mod_cast hc)

end Lorentz.Certificate
