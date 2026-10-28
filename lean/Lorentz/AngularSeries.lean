module

public import Lorentz.SeriesEstimates
public import Lorentz.PolynomialBounds

@[expose] public section

/-!
# Angular specialization of the paired-series estimates

The estimates are stated directly for the angular series.  The separate
Chebyshev composition identities identify these series with the residuals in
the construction.  No differentiability of the infinite series is used.
-/

namespace Lorentz
namespace AngularSeries

open Set Filter Polynomial
open scoped Topology

/-- At a point where sine is nonzero, cosine has a positive local lower
Lipschitz bound.  This is the inverse estimate supplied by its nonzero
derivative, with an unspecified but positive neighborhood radius. -/
theorem exists_cosine_local_lower_bound {θ : ℝ} (hsin : Real.sin θ ≠ 0) :
    ∃ δ > 0, ∃ k > 0, ∀ u : ℝ, |u| ≤ δ →
      k * |u| ≤ |Real.cos (θ + u) - Real.cos θ| := by
  have hderiv : -Real.sin θ ≠ 0 := neg_ne_zero.mpr hsin
  obtain ⟨C, hC, hO⟩ := (((Real.hasDerivAt_cos θ).isTheta_sub hderiv).isBigO_symm.comp_tendsto
    (tendsto_id.prodMk tendsto_const_pure)).exists_pos
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp hO.bound
  refine ⟨r / 2, by positivity, 1 / C, by positivity, ?_⟩
  intro u hu
  have hdist : dist (θ + u) θ < r := by
    rw [Real.dist_eq]
    have hru : |u| < r := by linarith
    simpa using hru
  have h := hbound hdist
  have h' : |u| ≤ C * |Real.cos (θ + u) - Real.cos θ| := by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, add_sub_cancel_left] using h
  have hdiv : |u| / C ≤ |Real.cos (θ + u) - Real.cos θ| :=
    (div_le_iff₀ hC).2 (by nlinarith)
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hdiv

/-- Small displacement in the spatial variable gives any prescribed small
angular displacement about an angle in `[0,π]`. -/
theorem exists_arccos_neighborhood {θ δ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (hδ : 0 < δ) :
    ∃ r > 0, ∀ x : ℝ, |x - Real.cos θ| ≤ r →
      |Real.arccos x - θ| ≤ δ := by
  have hcontAt : ContinuousAt Real.arccos (Real.cos θ) :=
    Real.continuous_arccos.continuousAt
  obtain ⟨r, hr, hcont⟩ :=
    (Metric.continuousAt_iff.mp hcontAt) δ hδ
  refine ⟨r / 2, by positivity, ?_⟩
  intro x hx
  have hdist : dist x (Real.cos θ) < r := by
    rw [Real.dist_eq]
    linarith
  have h := hcont hdist
  rw [Real.dist_eq, Real.arccos_cos hθ₀ hθπ] at h
  exact h.le

/-- A local linear cusp in angular coordinates implies the same cusp
constant in spatial coordinates. -/
theorem angular_cusp_to_spatial
    {F : ℝ → ℝ} {θ δ c E : ℝ}
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (hδ : 0 < δ) (hc : 0 ≤ c)
    (hgap : ∀ u : ℝ, |u| ≤ δ →
      c * |u| ≤ E - F (Real.cos (θ + u))) :
    ∃ r > 0, ∀ x ∈ Icc (-1 : ℝ) 1, |x - Real.cos θ| ≤ r →
      c * |x - Real.cos θ| ≤ E - F x := by
  obtain ⟨r, hr, harccos⟩ := exists_arccos_neighborhood hθ₀ hθπ hδ
  refine ⟨r, hr, ?_⟩
  intro x hx hnear
  have h := hgap (Real.arccos x - θ) (harccos x hnear)
  have hcos : Real.cos (θ + (Real.arccos x - θ)) = x := by
    have harg : θ + (Real.arccos x - θ) = Real.arccos x := by ring
    rw [harg, Real.cos_arccos hx.1 hx.2]
  rw [hcos] at h
  have hdist : |x - Real.cos θ| ≤ |Real.arccos x - θ| := by
    simpa only [Real.cos_arccos hx.1 hx.2] using
      PolynomialBounds.abs_cos_sub_cos_le θ (Real.arccos x)
  exact (mul_le_mul_of_nonneg_left hdist hc).trans h

/-- At a noncritical point of cosine, a pointwise angular Lipschitz bound
transfers to a pointwise spatial Lipschitz bound. -/
theorem angular_lipschitz_to_spatial
    {F : ℝ → ℝ} {θ δ L : ℝ}
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (hsin : Real.sin θ ≠ 0)
    (hδ : 0 < δ) (hL : 0 ≤ L)
    (hlip : ∀ u : ℝ, |u| ≤ δ →
      |F (Real.cos (θ + u)) - F (Real.cos θ)| ≤ L * |u|) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ Icc (-1 : ℝ) 1, |x - Real.cos θ| ≤ r →
      |F x - F (Real.cos θ)| ≤ C * |x - Real.cos θ| := by
  obtain ⟨δ', hδ', k, hk, hlower⟩ := exists_cosine_local_lower_bound hsin
  obtain ⟨r, hr, harccos⟩ :=
    exists_arccos_neighborhood hθ₀ hθπ (lt_min hδ hδ')
  refine ⟨r, hr, (L + 1) / k, div_pos (by linarith) hk, ?_⟩
  intro x hx hnear
  have hu := harccos x hnear
  have hcos : Real.cos (θ + (Real.arccos x - θ)) = x := by
    have harg : θ + (Real.arccos x - θ) = Real.arccos x := by ring
    rw [harg, Real.cos_arccos hx.1 hx.2]
  have hupper := hlip (Real.arccos x - θ) (hu.trans (min_le_left _ _))
  have hlower' := hlower (Real.arccos x - θ) (hu.trans (min_le_right _ _))
  rw [hcos] at hupper hlower'
  have hupperScaled := mul_le_mul_of_nonneg_right hupper hk.le
  have hlowerScaled := mul_le_mul_of_nonneg_left hlower' hL
  have hcalc : |F x - F (Real.cos θ)| * k ≤ (L + 1) * |x - Real.cos θ| := by
    nlinarith [abs_nonneg (x - Real.cos θ)]
  have hfinal := (le_div_iff₀ hk).2 hcalc
  convert hfinal using 1 <;> ring

/-- Polynomial stationarity makes the paired angular difference series
pointwise Lipschitz, despite possible failure of global differentiability. -/
theorem exists_paired_cosine_lipschitz (p : ℝ[X]) (θ : ℝ)
    (hstationary : p.derivative.eval (Real.cos θ) = 0) :
    ∃ L > 0, ∀ u : ℝ, |u| ≤ 1 →
      |∑' k : ℕ, ((1 : ℝ) / 9) ^ k *
        (p.eval (Real.cos (θ + (9 : ℝ) ^ k * u)) - p.eval (Real.cos θ))| ≤ L * |u| := by
  obtain ⟨A, hA, hquad⟩ :=
    PolynomialBounds.exists_pos_cosine_quadratic_bound p θ hstationary
  obtain ⟨M, hM, hbound⟩ := PolynomialBounds.exists_pos_eval_bound p
  refine ⟨9 * (A + 2 * M) / 8, by positivity, ?_⟩
  intro u hu
  have ha : ∀ k : ℕ,
      |p.eval (Real.cos (θ + (9 : ℝ) ^ k * u)) - p.eval (Real.cos θ)| ≤ 2 * M := by
    intro k
    calc
      _ ≤ |p.eval (Real.cos (θ + (9 : ℝ) ^ k * u))| +
          |p.eval (Real.cos θ)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (p.eval (Real.cos (θ + (9 : ℝ) ^ k * u))) (-p.eval (Real.cos θ))
      _ ≤ M + M := add_le_add
        (hbound _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
        (hbound _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
      _ = 2 * M := by ring
  have h := SeriesEstimates.paired_lipschitz
    (a := fun k : ℕ => p.eval (Real.cos (θ + (9 : ℝ) ^ k * u)) - p.eval (Real.cos θ))
    (A := A) (B := 2 * M) (u := |u|) (δ := 1)
    hA.le (by positivity) (abs_nonneg _) (by norm_num) hu ha
    (fun k _ => by
      have hk := hquad ((9 : ℝ) ^ k * u)
      simpa only [mul_pow, sq_abs] using hk)
  convert h using 1 <;> ring

/-- The cubic gap series has a genuine local linear cusp at every angular
representative of the positive extremal point. -/
theorem exists_cubic_angular_cusp {θ : ℝ}
    (hcos : Real.cos θ = PolynomialBounds.a) :
    ∃ δ > 0, ∃ c > 0, ∀ u : ℝ, |u| ≤ δ →
      c * |u| ≤ ∑' k : ℕ, ((1 : ℝ) / 9) ^ k *
        (PolynomialBounds.cubic PolynomialBounds.a -
          PolynomialBounds.cubic (Real.cos (θ + (9 : ℝ) ^ k * u))) := by
  have hsin : Real.sin θ ≠ 0 := by
    intro hzero
    have h := Real.sin_sq_add_cos_sq θ
    rw [hzero, hcos, PolynomialBounds.a_sq] at h
    norm_num at h
  obtain ⟨δ, hδ, k, hk, hlower⟩ := exists_cosine_local_lower_bound hsin
  let A : ℝ := PolynomialBounds.cubicGapConstant * k ^ 2
  have hA : 0 < A := mul_pos PolynomialBounds.cubicGapConstant_pos (sq_pos_of_pos hk)
  refine ⟨δ, hδ, A * δ / 9, by positivity, ?_⟩
  intro u hu
  let d : ℕ → ℝ := fun j => PolynomialBounds.cubic PolynomialBounds.a -
    PolynomialBounds.cubic (Real.cos (θ + (9 : ℝ) ^ j * u))
  have hn : ∀ j, 0 ≤ d j := by
    intro j
    have h := PolynomialBounds.cubic_le_max
      (x := Real.cos (θ + (9 : ℝ) ^ j * u))
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    dsimp [d]
    linarith
  have hb : ∀ j, |d j| ≤ 2 * PolynomialBounds.cubic PolynomialBounds.a := by
    intro j
    have h := PolynomialBounds.abs_cubic_le_max
      (x := Real.cos (θ + (9 : ℝ) ^ j * u))
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    rw [abs_of_nonneg (hn j)]
    dsimp [d]
    have hlo := (abs_le.mp h).1
    linarith
  have hsum := SeriesEstimates.summable_paired_of_bounded hb
  by_cases hu0 : u = 0
  · subst u
    have hnonneg : 0 ≤ ∑' j, ((1 : ℝ) / 9) ^ j * d j :=
      tsum_nonneg (fun j => mul_nonneg (by positivity) (hn j))
    simpa [d] using hnonneg
  · have habs : 0 < |u| := abs_pos.mpr hu0
    have hquad : ∀ j, (9 : ℝ) ^ j * |u| ≤ δ →
        A * ((9 : ℝ) ^ j * |u|) ^ 2 ≤ d j := by
      intro j hj
      have habsprod : |(9 : ℝ) ^ j * u| = (9 : ℝ) ^ j * |u| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
      have hlow := hlower ((9 : ℝ) ^ j * u) (by simpa only [habsprod] using hj)
      rw [habsprod, hcos] at hlow
      have hsq : (k * ((9 : ℝ) ^ j * |u|)) ^ 2 ≤
          (Real.cos (θ + (9 : ℝ) ^ j * u) - PolynomialBounds.a) ^ 2 := by
        apply sq_le_sq.mpr
        simpa only [abs_of_nonneg (by positivity : 0 ≤ k * ((9 : ℝ) ^ j * |u|))]
          using hlow
      have hgap := PolynomialBounds.cubic_quadratic_gap
        (x := Real.cos (θ + (9 : ℝ) ^ j * u))
        ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have hscaled := mul_le_mul_of_nonneg_left hsq PolynomialBounds.cubicGapConstant_pos.le
      dsimp [A, d]
      nlinarith
    have h := SeriesEstimates.paired_cusp hA.le habs hu hsum hn hquad
    convert h using 1 <;> ring

end AngularSeries
end Lorentz
