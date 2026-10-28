module

public import Lorentz.Plateau.Certificates.OddData
public import Lorentz.Plateau.Certificates.Checker
public import Lorentz.Plateau.Certificates.OddBounds
public import Lorentz.Plateau.Certificates.OddCubicGrid
public import Lorentz.Plateau.Families

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Odd

open Certificate.PolynomialCertificate

def aCoeffs : List ℚ := [0, (9 / 2), 0, -15, 0, (27 / 2), 0, (-9 / 2), 0, (1 / 2)]

def aSquareQuotient : List ℚ := [(-1 / 2), 0, (9 / 4), 0, (-3 / 2), 0, (1 / 4)]

theorem algebraic_a (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    Certificate.eval aCoeffs z = PolynomialBounds.a := by
  have hs := FiniteTools.eq_of_modulus_certificate (power aCoeffs 2) [1 / 2]
    aSquareQuotient modulusCoeffs z hm (by decide +kernel)
  have hp := Certificate.eval_pos aCoeffs z rootLower rootUpper hl hu (root_nonneg z hl)
    (by decide +kernel)
  have ha := PolynomialBounds.a_pos
  have ha2 := PolynomialBounds.a_sq
  norm_num only [eval_power, Certificate.eval, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, mul_zero, add_zero] at hs
  nlinarith

def contactQuotient0_0 : List ℚ := []

theorem contact_0_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false false).eval (node z 1) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (nodeRows.getD 4 []) (scale (-1) aCoeffs)
    contactQuotient0_0 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_1 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient0_1 : List ℚ := []

theorem contact_0_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false false).eval (node z 4) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (nodeRows.getD 13 []) (scale (1) aCoeffs)
    contactQuotient0_1 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_4 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient0_2 : List ℚ := []

theorem contact_0_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false false).eval (node z 7) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (nodeRows.getD 13 []) (scale (1) aCoeffs)
    contactQuotient0_2 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_7 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient0_3 : List ℚ := []

theorem contact_0_3 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false false).eval (node z 10) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (nodeRows.getD 4 []) (scale (-1) aCoeffs)
    contactQuotient0_3 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_10 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient0_4 : List ℚ := []

theorem contact_0_4 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false false).eval (node z 13) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (nodeRows.getD 4 []) (scale (-1) aCoeffs)
    contactQuotient0_4 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_13 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient0_5 : List ℚ := []

theorem contact_0_5 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false false).eval (node z 16) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (nodeRows.getD 13 []) (scale (1) aCoeffs)
    contactQuotient0_5 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_16 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

theorem contacts_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))
    (j : Fin 6) : (pullback false false).eval (node z (gridIndex 0 j)) =
      (gridSign 0 j : ℝ) * PolynomialBounds.a := by
  fin_cases j
  · simpa [gridIndex, gridSign] using contact_0_0 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_0_1 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_0_2 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_0_3 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_0_4 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_0_5 z hm hl hu

def contactQuotient1_0 : List ℚ := []

theorem contact_1_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 0) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient1_0 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_0 z hm]
  rw [cubic_at_1 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_1 : List ℚ := []

theorem contact_1_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 1) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient1_1 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_1 z hm]
  rw [cubic_at_4 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_2 : List ℚ := []

theorem contact_1_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 2) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient1_2 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_2 z hm]
  rw [cubic_at_7 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_3 : List ℚ := []

theorem contact_1_3 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 3) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient1_3 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_3 z hm]
  rw [cubic_at_10 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_4 : List ℚ := []

theorem contact_1_4 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 4) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient1_4 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_4 z hm]
  rw [cubic_at_13 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_5 : List ℚ := []

theorem contact_1_5 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 5) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient1_5 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_5 z hm]
  rw [cubic_at_16 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_6 : List ℚ := []

theorem contact_1_6 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 6) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient1_6 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_6 z hm]
  rw [cubic_at_16 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_7 : List ℚ := []

theorem contact_1_7 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 7) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient1_7 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_7 z hm]
  rw [cubic_at_13 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_8 : List ℚ := []

theorem contact_1_8 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 8) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient1_8 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_8 z hm]
  rw [cubic_at_10 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_9 : List ℚ := []

theorem contact_1_9 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 9) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient1_9 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_9 z hm]
  rw [cubic_at_7 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_10 : List ℚ := []

theorem contact_1_10 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 10) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient1_10 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_10 z hm]
  rw [cubic_at_4 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_11 : List ℚ := []

theorem contact_1_11 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 11) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient1_11 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_11 z hm]
  rw [cubic_at_1 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_12 : List ℚ := []

theorem contact_1_12 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 12) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient1_12 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_12 z hm]
  rw [cubic_at_1 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_13 : List ℚ := []

theorem contact_1_13 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 13) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient1_13 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_13 z hm]
  rw [cubic_at_4 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_14 : List ℚ := []

theorem contact_1_14 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 14) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient1_14 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_14 z hm]
  rw [cubic_at_7 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_15 : List ℚ := []

theorem contact_1_15 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 15) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient1_15 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_15 z hm]
  rw [cubic_at_10 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_16 : List ℚ := []

theorem contact_1_16 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 16) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient1_16 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_16 z hm]
  rw [cubic_at_13 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient1_17 : List ℚ := []

theorem contact_1_17 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 17) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient1_17 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_17 z hm]
  rw [cubic_at_16 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

theorem contacts_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))
    (j : Fin 18) : (pullback false true).eval (node z (gridIndex 1 j)) =
      (gridSign 1 j : ℝ) * PolynomialBounds.a := by
  fin_cases j
  · simpa [gridIndex, gridSign] using contact_1_0 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_1 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_2 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_3 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_4 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_5 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_6 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_7 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_8 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_9 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_10 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_11 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_12 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_13 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_14 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_15 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_16 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_1_17 z hm hl hu

def contactQuotient2_0 : List ℚ := []

theorem contact_2_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 0) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient2_0 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_0 z hm]
  rw [cubic_at_1 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_1 : List ℚ := []

theorem contact_2_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 1) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient2_1 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_1 z hm]
  rw [cubic_at_4 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_2 : List ℚ := []

theorem contact_2_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 2) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient2_2 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_2 z hm]
  rw [cubic_at_7 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_3 : List ℚ := []

theorem contact_2_3 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 3) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient2_3 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_3 z hm]
  rw [cubic_at_10 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_4 : List ℚ := []

theorem contact_2_4 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 4) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient2_4 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_4 z hm]
  rw [cubic_at_13 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_5 : List ℚ := []

theorem contact_2_5 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 5) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient2_5 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_5 z hm]
  rw [cubic_at_16 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_6 : List ℚ := []

theorem contact_2_6 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 6) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient2_6 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_6 z hm]
  rw [cubic_at_16 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_7 : List ℚ := []

theorem contact_2_7 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 7) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient2_7 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_7 z hm]
  rw [cubic_at_13 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_8 : List ℚ := []

theorem contact_2_8 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 8) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient2_8 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_8 z hm]
  rw [cubic_at_10 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_9 : List ℚ := []

theorem contact_2_9 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 9) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient2_9 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_9 z hm]
  rw [cubic_at_7 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_10 : List ℚ := []

theorem contact_2_10 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 10) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient2_10 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_10 z hm]
  rw [cubic_at_4 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_11 : List ℚ := []

theorem contact_2_11 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 11) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient2_11 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_11 z hm]
  rw [cubic_at_1 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_12 : List ℚ := []

theorem contact_2_12 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 12) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient2_12 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_12 z hm]
  rw [cubic_at_1 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_13 : List ℚ := []

theorem contact_2_13 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 13) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient2_13 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_13 z hm]
  rw [cubic_at_4 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_14 : List ℚ := []

theorem contact_2_14 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 14) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient2_14 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_14 z hm]
  rw [cubic_at_7 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_15 : List ℚ := []

theorem contact_2_15 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 15) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient2_15 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_15 z hm]
  rw [cubic_at_10 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_16 : List ℚ := []

theorem contact_2_16 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 16) = (1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 4 [])) (scale (1) aCoeffs)
    contactQuotient2_16 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_16 z hm]
  rw [cubic_at_13 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

def contactQuotient2_17 : List ℚ := []

theorem contact_2_17 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (pullback false true).eval (node z 17) = (-1 : ℝ) * PolynomialBounds.a := by
  have h := FiniteTools.eq_of_modulus_certificate (scale (-1) (nodeRows.getD 13 [])) (scale (-1) aCoeffs)
    contactQuotient2_17 modulusCoeffs z hm (by decide +kernel)
  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]
  rw [cubic_at_17 z hm]
  rw [cubic_at_16 z hm]
  simpa only [node, neg_one_mul, one_mul] using h

theorem contacts_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))
    (j : Fin 18) : (pullback false true).eval (node z (gridIndex 2 j)) =
      (gridSign 2 j : ℝ) * PolynomialBounds.a := by
  fin_cases j
  · simpa [gridIndex, gridSign] using contact_2_0 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_1 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_2 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_3 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_4 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_5 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_6 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_7 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_8 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_9 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_10 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_11 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_12 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_13 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_14 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_15 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_16 z hm hl hu
  · simpa [gridIndex, gridSign] using contact_2_17 z hm hl hu

end Lorentz.Plateau.Certificates.Odd
