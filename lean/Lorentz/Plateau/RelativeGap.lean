module

public import Lorentz.Plateau.LocalEstimates
public import Lorentz.LocalComposition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

@[expose] public section

/-! Local perturbation control by the baseline deficit at a simple contact. -/

namespace Lorentz.Plateau

open Set Polynomial

/-- Near an interior simple preimage of the positive extremum, every
polynomial-forcing orbit series is controlled by the baseline deficit. -/
theorem exists_relative_gap_bound (q : ℝ[X]) {P : ℝ → ℝ} {d ξ : ℝ}
    (hP : HasDerivAt P d ξ) (hd : d ≠ 0) (hξ : ξ ∈ Ioo (-1 : ℝ) 1)
    (hcontact : P ξ = PolynomialBounds.a)
    (hmap : ∀ x ∈ interval, P x ∈ interval) :
    ∃ C > 0, ∃ δ > 0, ∀ x ∈ interval, |x - ξ| ≤ δ →
      |orbitSeries q.eval (-3 / 5) x - orbitSeries q.eval (-3 / 5) ξ| ≤
        C * (Baseline.B - Baseline.G (P x)) := by
  obtain ⟨δg, hδg, c, hc, hgap⟩ := exists_baseline_exit_gap
  obtain ⟨k, hk, δP, hδP, hlower⟩ :=
    LocalComposition.exists_local_lower_of_hasDerivAt hP hd
  have hacos := Real.hasDerivAt_arccos (by linarith [hξ.1] : ξ ≠ -1)
    (by linarith [hξ.2] : ξ ≠ 1)
  obtain ⟨L, hL, δa, hδa, hsource⟩ :=
    LocalComposition.exists_local_lipschitz_of_hasDerivAt hacos
  have hcont : ContinuousAt (fun x ↦ Real.arccos (P x)) ξ :=
    Real.continuous_arccos.continuousAt.comp hP.continuousAt
  obtain ⟨r, hr, hangle⟩ := (Metric.continuousAt_iff.mp hcont) δg hδg
  have hacontact : Real.arccos (P ξ) = Real.pi / 4 := by
    rw [hcontact, PolynomialBounds.a, ← Real.cos_pi_div_four]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  obtain ⟨C, hC, hosc⟩ := exists_polynomial_oscillation q (div_pos hL hk) hδg
  refine ⟨C / c, div_pos hC hc, min (r / 2) (min δP δa),
    lt_min (by positivity) (lt_min hδP hδa), ?_⟩
  intro x hx hnear
  let t : ℝ := Real.arccos (P x) - Real.pi / 4
  have hnearP := hnear.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hneara := hnear.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnearR : dist x ξ < r := by
    rw [Real.dist_eq]
    have h := hnear.trans (min_le_left _ _)
    linarith
  have ht : |t| ≤ δg := by
    have h := hangle hnearR
    rw [Real.dist_eq, hacontact] at h
    exact h.le
  have hcos := PolynomialBounds.abs_cos_sub_cos_le (Real.pi / 4) (Real.arccos (P x))
  rw [Real.cos_arccos (hmap x hx).1 (hmap x hx).2, Real.cos_pi_div_four] at hcos
  have hlower' := hlower x hnearP
  rw [hcontact] at hlower'
  have hkt : k * |x - ξ| ≤ |t| := hlower'.trans hcos
  have hsource' := hsource x hneara
  have hangleDist : |Real.arccos x - Real.arccos ξ| ≤ (L / k) * |t| := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hk).mpr
    have h1 := mul_le_mul_of_nonneg_right hsource' hk.le
    have h2 := mul_le_mul_of_nonneg_left hkt hL.le
    nlinarith
  by_cases ht0 : t = 0
  · have hdist0 : |x - ξ| = 0 := by
      rw [ht0, abs_zero] at hkt
      nlinarith [abs_nonneg (x - ξ)]
    have heq := sub_eq_zero.mp (abs_eq_zero.mp hdist0)
    subst x
    simp [hcontact, Baseline.G_at_a]
  · obtain ⟨n, hn, hn'⟩ := Lorentz.SeriesEstimates.exists_scale_nine (abs_pos.mpr ht0) ht
    have hg := hgap t n hn hn'.le
    have hcosP : Real.cos (Real.pi / 4 + t) = P x := by
      dsimp [t]
      rw [show Real.pi / 4 + (Real.arccos (P x) - Real.pi / 4) =
        Real.arccos (P x) by ring, Real.cos_arccos (hmap x hx).1 (hmap x hx).2]
    rw [hcosP] at hg
    have ho := hosc (Real.arccos x) (Real.arccos ξ) |t| n (abs_nonneg t) hangleDist hn
    rw [Real.cos_arccos hx.1 hx.2, Real.cos_arccos hξ.1.le hξ.2.le] at ho
    calc
      _ ≤ C * (9 / 25 : ℝ) ^ n := ho
      _ = (C / c) * (c * (9 / 25 : ℝ) ^ n) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hc.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (div_pos hC hc).le

end Lorentz.Plateau
