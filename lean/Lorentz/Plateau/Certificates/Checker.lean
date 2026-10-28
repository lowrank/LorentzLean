module

public import Lorentz.Plateau.FiniteTools

@[expose] public section

/-! Soundness of finite coefficient certificates for recurrences and contact slacks. -/

namespace Lorentz.Plateau.Certificates.Checker

open Certificate.PolynomialCertificate

theorem recurrence (forcing : List (List ℚ)) (node value nextValue quotient m : List ℚ)
    (ρ : ℚ) (z : ℝ) (hm : Certificate.eval m z = 0)
    (hc : isZero (sub (sub value (add (FiniteTools.substitute forcing node) (scale ρ nextValue)))
      (mul quotient m)) = true) :
    Certificate.eval value z =
      (FiniteTools.fieldPolynomial forcing z).eval (Certificate.eval node z) +
      (ρ : ℝ) * Certificate.eval nextValue z := by
  have h := FiniteTools.eq_of_modulus_certificate value
    (add (FiniteTools.substitute forcing node) (scale ρ nextValue)) quotient m z hm hc
  simpa only [eval_add, eval_scale, FiniteTools.eval_substitute] using h

theorem slack (correction : List (List ℚ))
    (node value slope slackValue quotient m : List ℚ) (s : ℚ) (z : ℝ)
    (hm : Certificate.eval m z = 0)
    (hc : isZero (sub (sub (sub slope (scale s
      (sub value (FiniteTools.substitute correction node)))) slackValue) (mul quotient m)) = true) :
    Certificate.eval slope z - (s : ℝ) * (Certificate.eval value z -
      (FiniteTools.fieldPolynomial correction z).eval (Certificate.eval node z)) =
      Certificate.eval slackValue z := by
  have h := FiniteTools.eq_of_modulus_certificate
    (sub slope (scale s (sub value (FiniteTools.substitute correction node))))
    slackValue quotient m z hm hc
  simpa only [eval_sub, eval_scale, FiniteTools.eval_substitute] using h

theorem cubic_map (node nextNode quotient m : List ℚ) (z : ℝ)
    (hm : Certificate.eval m z = 0)
    (hc : isZero (sub (sub (sub (scale 4 (power node 3)) (scale 3 node)) nextNode)
      (mul quotient m)) = true) :
    cubic (Certificate.eval node z) = Certificate.eval nextNode z := by
  have h := FiniteTools.eq_of_modulus_certificate
    (sub (scale 4 (power node 3)) (scale 3 node)) nextNode quotient m z hm hc
  norm_num only [eval_sub, eval_scale, eval_power, Rat.cast_ofNat] at h
  exact h

end Lorentz.Plateau.Certificates.Checker
