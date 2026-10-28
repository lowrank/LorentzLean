module

public import Lorentz.Plateau.Certificates.EvenData
public import Lorentz.Plateau.Certificates.Checker
public import Lorentz.Plateau.Certificates.EvenBounds

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Even

open Certificate.PolynomialCertificate

def asymmetryCoeffs : List ℚ := [0, (491127671564609290454 / 20845224569152687827), 0,
  (-5883577986227509345682 / 20845224569152687827), 0,
  (24461633833679491599118 / 20845224569152687827), 0,
  (-43621097037643163985892 / 20845224569152687827), 0,
  (30954788398053488054053 / 20845224569152687827), 0,
  (2009749495917039363847 / 6948408189717562609), 0,
  (-25909895088423898476929 / 20845224569152687827), 0,
  (19565705770802107452497 / 20845224569152687827), 0,
  (-7598452222616510252774 / 20845224569152687827), 0,
  (557123060366521853046 / 6948408189717562609), 0,
  (-65952416947973168699 / 6948408189717562609), 0,
  (9820123223367235435 / 20845224569152687827)]

def asymmetryQuotient : List ℚ := []

theorem forcing_asymmetry (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    (forcing z).eval 1 - (forcing z).eval (-1) =
      Certificate.eval asymmetryCoeffs z := by
  have h := FiniteTools.eq_of_modulus_certificate
    (add (FiniteTools.substitute forcingCoeffs [1]) (scale (-1) (FiniteTools.substitute forcingCoeffs [-1])))
    asymmetryCoeffs asymmetryQuotient modulusCoeffs z hm (by decide +kernel)
  have hp : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]
  have hn : Certificate.eval [-1] z = (-1 : ℝ) := by simp [Certificate.eval]
  simpa only [eval_add, eval_scale, FiniteTools.eval_substitute, hp, hn, forcing,
    Rat.cast_one, Rat.cast_neg, one_mul, neg_one_mul, sub_eq_add_neg] using h

theorem forcing_asymmetry_ne (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    (forcing z).eval 1 - (forcing z).eval (-1) ≠ 0 := by
  rw [forcing_asymmetry z hm]
  exact (Certificate.eval_pos asymmetryCoeffs z rootLower rootUpper hl hu
    (root_nonneg z hl) (by decide +kernel)).ne'

end Lorentz.Plateau.Certificates.Even
