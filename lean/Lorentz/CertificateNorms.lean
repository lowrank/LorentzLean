module

public import Lorentz.CertificateGrid

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Lorentz.Certificate

def absoluteUpper (cs : List ℚ) : ℚ :=
  max |lower cs rootLower rootUpper| |upper cs rootLower rootUpper|

 theorem absolute_eval_bound (cs : List ℚ) (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    |eval cs z| ≤ (absoluteUpper cs : ℝ) := by
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  have h := eval_bounds cs z rootLower rootUpper hl hu hz
  simpa only [absoluteUpper, Rat.cast_max, Rat.cast_abs] using abs_le_max_abs_abs h.1 h.2

def coefficientNorm (cs : List (List ℚ)) (z : ℝ) : ℝ := (cs.map fun p => |eval p z|).sum

def coefficientNormBound (cs : List (List ℚ)) : ℚ := (cs.map absoluteUpper).sum

 theorem coefficient_norm_bound (cs : List (List ℚ)) (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    coefficientNorm cs z ≤ (coefficientNormBound cs : ℝ) := by
  induction cs with
  | nil => simp [coefficientNorm, coefficientNormBound]
  | cons p ps ih =>
      simpa only [coefficientNorm, coefficientNormBound, List.map_cons, List.sum_cons,
        Rat.cast_add] using add_le_add (absolute_eval_bound p z hl hu) ih

def derivativeMass : List (List ℚ) → ℝ → ℕ → ℝ
  | [], _, _ => 0
  | p :: ps, z, k => |eval p z| * (k : ℝ) ^ 2 + derivativeMass ps z (k + 1)

def derivativeMassBound : List (List ℚ) → ℕ → ℚ
  | [], _ => 0
  | p :: ps, k => absoluteUpper p * (k : ℚ) ^ 2 + derivativeMassBound ps (k + 1)

 theorem derivative_mass_bound (cs : List (List ℚ)) (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) (k : ℕ) :
    derivativeMass cs z k ≤ (derivativeMassBound cs k : ℝ) := by
  induction cs generalizing k with
  | nil => simp [derivativeMass, derivativeMassBound]
  | cons p ps ih =>
      have hp := mul_le_mul_of_nonneg_right (absolute_eval_bound p z hl hu) (sq_nonneg (k : ℝ))
      simpa only [derivativeMass, derivativeMassBound, Rat.cast_add, Rat.cast_mul,
        Rat.cast_pow, Rat.cast_natCast] using add_le_add hp (ih (k + 1))

private theorem rational_norm_bounds : ∀ n : Fin 7,
    coefficientNormBound (chebyshevRows.getD n []) < 6 ∧
    derivativeMassBound (chebyshevRows.getD n []) 0 < 216 := by
  decide +kernel

 theorem correction_coefficient_bounds (n : Fin 7) (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    coefficientNorm (chebyshevRows.getD n []) z < 6 ∧
    derivativeMass (chebyshevRows.getD n []) z 0 < 216 := by
  have h := rational_norm_bounds n
  constructor
  · exact lt_of_le_of_lt (coefficient_norm_bound _ z hl hu) (by exact_mod_cast h.1)
  · exact lt_of_le_of_lt (derivative_mass_bound _ z hl hu 0) (by exact_mod_cast h.2)

end Lorentz.Certificate
