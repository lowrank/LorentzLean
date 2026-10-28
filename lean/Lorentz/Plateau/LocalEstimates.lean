module

public import Lorentz.Plateau.Baseline
public import Lorentz.Plateau.SeriesEstimates
public import Lorentz.AngularSeries

@[expose] public section

/-! Baseline deficit and perturbation oscillation at a common angular exit scale. -/

namespace Lorentz.Plateau

open Set Polynomial

/-- A baseline deficit retains a positive multiple of the exit-scale weight. -/
theorem exists_baseline_exit_gap :
    ∃ δ > 0, ∃ c > 0, ∀ (u : ℝ) (n : ℕ),
      (9 : ℝ) ^ n * |u| ≤ δ → δ ≤ (9 : ℝ) ^ (n + 1) * |u| →
      c * (9 / 25 : ℝ) ^ n ≤
        Baseline.B - Baseline.G (Real.cos (Real.pi / 4 + u)) := by
  have hsin : Real.sin (Real.pi / 4) ≠ 0 := by rw [Real.sin_pi_div_four]; positivity
  obtain ⟨δ, hδ, k, hk, hlower⟩ := AngularSeries.exists_cosine_local_lower_bound hsin
  have hc := PolynomialBounds.cubicGapConstant_pos
  refine ⟨δ, hδ, (4 / 9) * PolynomialBounds.cubicGapConstant * (k * δ / 9) ^ 2,
    by positivity, ?_⟩
  intro u n hnear hexit
  have hcos := hlower ((9 : ℝ) ^ n * u) (by
    rwa [abs_mul, abs_of_nonneg (by positivity)] )
  rw [Real.cos_pi_div_four] at hcos
  change k * |(9 : ℝ) ^ n * u| ≤
    |Real.cos (Real.pi / 4 + (9 : ℝ) ^ n * u) - PolynomialBounds.a| at hcos
  rw [abs_mul, abs_of_nonneg (by positivity)] at hcos
  rw [pow_succ] at hexit
  have hscaled := mul_le_mul_of_nonneg_left hexit hk.le
  have hl : k * δ / 9 ≤
      |Real.cos (Real.pi / 4 + (9 : ℝ) ^ n * u) - PolynomialBounds.a| := by nlinarith
  have hsq : (k * δ / 9) ^ 2 ≤
      (Real.cos (Real.pi / 4 + (9 : ℝ) ^ n * u) - PolynomialBounds.a) ^ 2 := by
    have hnonneg : 0 ≤ k * δ / 9 := by positivity
    nlinarith [sq_abs (Real.cos (Real.pi / 4 + (9 : ℝ) ^ n * u) - PolynomialBounds.a)]
  have hq := Baseline.old_quadratic_gap
    (cosine_mem_interval (Real.pi / 4 + (9 : ℝ) ^ n * u))
  have hq' := (mul_le_mul_of_nonneg_left hsq PolynomialBounds.cubicGapConstant_pos.le).trans hq
  have hterm := Baseline.even_orbit_gap (cosine_mem_interval (Real.pi / 4 + u)) n
  rw [cubic_even_iterate_cos] at hterm
  have hphase := cosine_quarter_phase 1 n u
  norm_num only [Nat.cast_one, one_mul] at hphase
  rw [hphase] at hterm
  have hweighted := mul_le_mul_of_nonneg_left hq'
    (show 0 ≤ (4 / 9 : ℝ) * (9 / 25 : ℝ) ^ n by positivity)
  nlinarith

noncomputable def pairedForcing (q : ℝ[X]) : ℝ[X] :=
  q + C (-3 / 5) * q.comp Lorentz.cubicPoly

lemma paired_series_cos (q : ℝ[X]) (θ : ℝ) :
    orbitSeries q.eval (-3 / 5) (Real.cos θ) =
      ∑' j : ℕ, (9 / 25 : ℝ) ^ j *
        (pairedForcing q).eval (Real.cos ((9 : ℝ) ^ j * θ)) := by
  obtain ⟨M, _, hM⟩ := PolynomialBounds.exists_pos_eval_bound q
  rw [orbitSeries_pair (by norm_num : |(-3 : ℝ) / 5| < 1) hM (cosine_mem_interval θ)]
  apply tsum_congr
  intro j
  rw [cubic_even_iterate_cos]
  simp only [pairedForcing, eval_add, eval_mul, eval_C, eval_comp, eval_cubicPoly]
  norm_num

/-- Polynomial forcing gives an oscillation bound at the scale chosen for
any controlling angular displacement. No stationarity hypothesis is needed. -/
theorem exists_polynomial_oscillation (q : ℝ[X]) {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) :
    ∃ C > 0, ∀ (θ φ u : ℝ) (n : ℕ), 0 ≤ u → |θ - φ| ≤ K * u →
      (9 : ℝ) ^ n * u ≤ δ →
      |orbitSeries q.eval (-3 / 5) (Real.cos θ) -
        orbitSeries q.eval (-3 / 5) (Real.cos φ)| ≤ C * (9 / 25 : ℝ) ^ n := by
  obtain ⟨M, hM, hbound⟩ := PolynomialBounds.exists_pos_eval_bound (pairedForcing q)
  obtain ⟨L, hL, hlip⟩ := PolynomialBounds.exists_pos_lipschitz_bound (pairedForcing q)
  refine ⟨2 * (L * K) * δ + 2 * M, by positivity, ?_⟩
  intro θ φ u n hu hdist hscale
  let a : ℕ → ℝ := fun j ↦ (pairedForcing q).eval (Real.cos ((9 : ℝ) ^ j * θ)) -
    (pairedForcing q).eval (Real.cos ((9 : ℝ) ^ j * φ))
  have ha : ∀ j, |a j| ≤ 2 * M := by
    intro j
    exact (abs_sub _ _).trans (by
      have hθ := hbound _ (cosine_mem_interval ((9 : ℝ) ^ j * θ))
      have hφ := hbound _ (cosine_mem_interval ((9 : ℝ) ^ j * φ))
      linarith)
  have haLip : ∀ j ≤ n, |a j| ≤ (L * K) * (9 : ℝ) ^ j * u := by
    intro j _
    have hp := hlip _ (cosine_mem_interval ((9 : ℝ) ^ j * φ))
      _ (cosine_mem_interval ((9 : ℝ) ^ j * θ))
    have hc := PolynomialBounds.abs_cos_sub_cos_le ((9 : ℝ) ^ j * φ) ((9 : ℝ) ^ j * θ)
    rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ (9 : ℝ) ^ j by positivity)] at hc
    have h1 := mul_le_mul_of_nonneg_left hc hL.le
    have h2 := mul_le_mul_of_nonneg_left hdist (show 0 ≤ L * (9 : ℝ) ^ j by positivity)
    dsimp [a]
    nlinarith
  have hsθ := SeriesEstimates.summable_weighted
    (fun j ↦ hbound _ (cosine_mem_interval ((9 : ℝ) ^ j * θ)))
  have hsφ := SeriesEstimates.summable_weighted
    (fun j ↦ hbound _ (cosine_mem_interval ((9 : ℝ) ^ j * φ)))
  rw [paired_series_cos, paired_series_cos, ← hsθ.tsum_sub hsφ]
  have heq : (fun j : ℕ ↦ (9 / 25 : ℝ) ^ j *
      (pairedForcing q).eval (Real.cos ((9 : ℝ) ^ j * θ)) -
      (9 / 25 : ℝ) ^ j * (pairedForcing q).eval (Real.cos ((9 : ℝ) ^ j * φ))) =
      (fun j ↦ (9 / 25 : ℝ) ^ j * a j) := by
    funext j
    dsimp [a]
    ring
  rw [heq]
  exact SeriesEstimates.oscillation_at_scale (mul_nonneg hL.le hK.le)
    (by positivity) hu ha haLip hscale

end Lorentz.Plateau
