module

public import Lorentz.CertificateData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Lorentz.Certificate

private theorem rational_slacks_nonnegative :
    (slackRows.flatten.all fun p => decide (0 ≤ lower p rootLower rootUpper)) = true := by
  decide +kernel

 theorem slacks_nonnegative (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    ∀ p ∈ slackRows.flatten, 0 ≤ eval p z := by
  intro p hp
  apply eval_nonneg p z rootLower rootUpper hl hu
  · have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  · exact of_decide_eq_true (List.all_eq_true.mp rational_slacks_nonnegative p hp)

 theorem beta_bounds (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (419 : ℝ) / 1000 < beta z ∧ beta z < (420 : ℝ) / 1000 := by
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  have h := eval_bounds betaCoeffs z rootLower rootUpper hl hu hz
  have hlo : (419 : ℚ) / 1000 < lower betaCoeffs rootLower rootUpper := by decide +kernel
  have hhi : upper betaCoeffs rootLower rootUpper < (420 : ℚ) / 1000 := by decide +kernel
  constructor
  · have hloReal : (((419 : ℚ) / 1000 : ℚ) : ℝ) < (lower betaCoeffs rootLower rootUpper : ℝ) := Rat.cast_lt.mpr hlo
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hloReal
    exact lt_of_lt_of_le hloReal h.1
  · have hhiReal : (upper betaCoeffs rootLower rootUpper : ℝ) < (((420 : ℚ) / 1000 : ℚ) : ℝ) := Rat.cast_lt.mpr hhi
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hhiReal
    convert lt_of_le_of_lt h.2 hhiReal using 1 <;> norm_num [beta]

 theorem t0_bounds (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    0 < t0 z ∧ t0 z < 2 := by
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  constructor
  · exact eval_pos t0Coeffs z rootLower rootUpper hl hu hz (by decide +kernel)
  · exact eval_lt t0Coeffs z rootLower rootUpper 2 hl hu hz (by decide +kernel)

 theorem t1_bounds (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    0 < t1 z ∧ t1 z < 2 := by
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  constructor
  · exact eval_pos t1Coeffs z rootLower rootUpper hl hu hz (by decide +kernel)
  · exact eval_lt t1Coeffs z rootLower rootUpper 2 hl hu hz (by decide +kernel)

 theorem t3_bounds (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    0 < t3 z ∧ t3 z < 2 := by
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  constructor
  · exact eval_pos t3Coeffs z rootLower rootUpper hl hu hz (by decide +kernel)
  · exact eval_lt t3Coeffs z rootLower rootUpper 2 hl hu hz (by decide +kernel)

 theorem t4_bounds (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    0 < t4 z ∧ t4 z < 2 := by
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  constructor
  · exact eval_pos t4Coeffs z rootLower rootUpper hl hu hz (by decide +kernel)
  · exact eval_lt t4Coeffs z rootLower rootUpper 2 hl hu hz (by decide +kernel)

 theorem t5_bounds (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    0 < t5 z ∧ t5 z < 2 := by
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  constructor
  · exact eval_pos t5Coeffs z rootLower rootUpper hl hu hz (by decide +kernel)
  · exact eval_lt t5Coeffs z rootLower rootUpper 2 hl hu hz (by decide +kernel)

end Lorentz.Certificate
