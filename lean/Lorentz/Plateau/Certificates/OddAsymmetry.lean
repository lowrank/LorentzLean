module

public import Lorentz.Plateau.Certificates.OddData
public import Lorentz.Plateau.Certificates.Checker
public import Lorentz.Plateau.Certificates.OddBounds

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Odd

open Certificate.PolynomialCertificate

def asymmetryCoeffs : List ℚ := [(88 / 5), 0, (-2276 / 15), 0, (3272 / 15), 0, (-644 / 5), 0, (104 / 3), 0, (-52 / 15)]

def asymmetryQuotient : List ℚ := []

theorem forcing_asymmetry (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    (forcing z).eval 1 + (forcing z).eval (-1) =
      Certificate.eval asymmetryCoeffs z := by
  have h := FiniteTools.eq_of_modulus_certificate
    (add (FiniteTools.substitute forcingCoeffs [1]) (scale (1) (FiniteTools.substitute forcingCoeffs [-1])))
    asymmetryCoeffs asymmetryQuotient modulusCoeffs z hm (by decide +kernel)
  have hp : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  have hn : Certificate.eval [-1] z = (-1 : ℝ) := by simp [Certificate.eval]
  simpa only [eval_add, eval_scale, FiniteTools.eval_substitute, hp, hn, forcing,
    Rat.cast_one, Rat.cast_neg, one_mul, neg_one_mul, sub_eq_add_neg] using h

theorem forcing_asymmetry_ne (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (forcing z).eval 1 + (forcing z).eval (-1) ≠ 0 := by
  rw [forcing_asymmetry z hm]
  simpa only [Rat.cast_zero] using (Certificate.eval_lt asymmetryCoeffs z rootLower rootUpper 0 hl hu
    (root_nonneg z hl) (by decide +kernel)).ne

theorem forcing_zero (z : ℝ) : (forcing z).eval 0 = 0 := by
  change (Polynomial.C (Certificate.eval [] z) + Polynomial.X * _).eval 0 = 0
  simp [Certificate.eval]

end Lorentz.Plateau.Certificates.Odd
