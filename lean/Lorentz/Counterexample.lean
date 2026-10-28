module

public import Lorentz.BaseCertificates

@[expose] public section

/-!
# A continuous counterexample to the origin-vanishing implication

The finite algebraic certificate, the local series estimates, compactness,
and cubic alternation lifting are all imported through `BaseCertificates`.
The perturbation parameter is existentially chosen positive; this theorem
does not claim the additional explicit value `10^(-10)`.
-/

namespace Lorentz.Construction

open Set Polynomial

noncomputable def forcingPolynomial (z ε : ℝ) : ℝ[X] :=
  Lorentz.cubicPoly + C ε * ForcingPolynomials.hPoly (Certificate.beta z)

lemma forcingPolynomial_degree (z ε : ℝ) : (forcingPolynomial z ε).natDegree ≤ 7 := by
  have h3 : Lorentz.cubicPoly.natDegree ≤ 3 := by
    unfold Lorentz.cubicPoly
    compute_degree
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (h3.trans (by decide))
      ((Polynomial.natDegree_C_mul_le _ _).trans (ForcingPolynomials.natDegree_hPoly_le _)))

lemma forcingPolynomial_zero (z ε : ℝ) : (forcingPolynomial z ε).eval 0 = 0 := by
  simp [forcingPolynomial, Lorentz.cubicPoly]

lemma candidateFunction_continuousOn (z ε : ℝ) :
    ContinuousOn (candidateFunction z ε) interval :=
  F_continuousOn.add (continuousOn_const.mul (H_continuousOn _))

lemma candidateFunction_zero (z ε : ℝ) : candidateFunction z ε 0 = 0 := by
  simp [candidateFunction, F, cubic_zero, Baseline.G_zero]

lemma candidateFunction_selfsimilar (z ε : ℝ) {x : ℝ} (hx : x ∈ interval) :
    candidateFunction z ε x = (forcingPolynomial z ε).eval x -
      candidateFunction z ε (Lorentz.cubic x) / 3 := by
  have hF := Baseline.G_equation (cubic_maps_interval hx)
  have hH := H_equation (Certificate.beta z) hx
  simp only [candidateFunction, F, forcingPolynomial, eval_add, eval_mul, eval_C,
    eval_cubicPoly]
  linear_combination hF + ε * hH

lemma candidateFunction_reflected_sum (z ε : ℝ) :
    candidateFunction z ε PolynomialBounds.a +
      candidateFunction z ε (-PolynomialBounds.a) = -3 * ε := by
  have hH := H_reflected_sum_at_a (Certificate.beta z)
  simp only [candidateFunction, F, cubic_neg]
  rw [Baseline.G_odd]
  linear_combination ε * hH

lemma candidateFunction_not_odd (z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    candidateFunction z ε (-PolynomialBounds.a) ≠
      -candidateFunction z ε PolynomialBounds.a := by
  intro h
  have hsum := candidateFunction_reflected_sum z ε
  rw [h] at hsum
  linarith

/-- The constructed function is the proposed polynomial-forcing orbit series
on the entire approximation interval. -/
lemma candidateFunction_eq_orbitSeries (z ε : ℝ) {x : ℝ} (hx : x ∈ interval) :
    candidateFunction z ε x = orbitSeries (forcingPolynomial z ε).eval (-1 / 3) x := by
  have hfun : (forcingPolynomial z ε).eval = fun y =>
      Lorentz.cubic y + ε * (ForcingPolynomials.hPoly (Certificate.beta z)).eval y := by
    funext y
    simp [forcingPolynomial, eval_cubicPoly]
  rw [hfun, orbitSeries_linear' (by norm_num) cubic_continuous
    (ForcingPolynomials.hPoly (Certificate.beta z)).continuous hx]
  have hcomp := orbitSeries_comp_cubic id (-1 / 3) x
  change orbitSeries Lorentz.cubic (-1 / 3) x = Baseline.G (Lorentz.cubic x) at hcomp
  rw [hcomp]
  rfl

/-- A continuous non-odd function whose best uniform polynomial
approximations of every degree exist and all vanish at the origin. -/
theorem lorentz_counterexample :
    ∃ f : ℝ → ℝ,
      ContinuousOn f interval ∧ f 0 = 0 ∧
      (∃ x ∈ interval, f (-x) ≠ -f x) ∧
      ∀ n : ℕ, (∃ p : ℝ[X], IsBest f n p) ∧
        ∀ p : ℝ[X], IsBest f n p → p.eval 0 = 0 := by
  obtain ⟨z, hl, hu, hm⟩ := Certificate.exists_certificate_root
  obtain ⟨ε, hε, hbase⟩ := exists_seven_base_certificates z hm hl hu
  refine ⟨candidateFunction z ε, candidateFunction_continuousOn z ε,
    candidateFunction_zero z ε,
    ⟨PolynomialBounds.a, PolynomialBounds.a_mem, candidateFunction_not_odd z hε⟩, ?_⟩
  intro n
  exact ⟨exists_best_of_selfsimilar (forcingPolynomial_degree z ε)
      (forcingPolynomial_zero z ε) (fun _ hx => candidateFunction_selfsimilar z ε hx) hbase n,
    all_best_vanish_of_selfsimilar (forcingPolynomial_degree z ε)
      (forcingPolynomial_zero z ε) (fun _ hx => candidateFunction_selfsimilar z ε hx) hbase n⟩

end Lorentz.Construction
