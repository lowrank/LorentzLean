module

public import Mathlib

@[expose] public section

/-!
# Estimates for the paired self-similar series

This file proves the scalar series estimates used for the cusp and the
pointwise Lipschitz bound.  The expansion factor is nine.  Keeping the
geometric-series argument separate from the Chebyshev identities makes the
analytic mechanism explicit: a quadratic gap becomes linear at the last
iterate before leaving a fixed neighborhood, and quadratic prefix control
together with a bounded tail gives a linear upper bound.
-/

namespace Lorentz
namespace SeriesEstimates

open scoped BigOperators

lemma inverse_power_nine (n : ℕ) :
    ((1 : ℝ) / 9) ^ n * (9 : ℝ) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

lemma weighted_square_nine (n : ℕ) (u : ℝ) :
    ((1 : ℝ) / 9) ^ n * ((9 : ℝ) ^ n * u) ^ 2 = (9 : ℝ) ^ n * u ^ 2 := by
  calc
    ((1 : ℝ) / 9) ^ n * ((9 : ℝ) ^ n * u) ^ 2 =
        (((1 : ℝ) / 9) ^ n * (9 : ℝ) ^ n) * (9 : ℝ) ^ n * u ^ 2 := by ring
    _ = (9 : ℝ) ^ n * u ^ 2 := by rw [inverse_power_nine]; ring

/-- A positive number no greater than `δ` has a last scale before it exceeds
`δ` under repeated multiplication by nine. -/
theorem exists_scale_nine {u δ : ℝ} (hu : 0 < u) (huδ : u ≤ δ) :
    ∃ n : ℕ, (9 : ℝ) ^ n * u ≤ δ ∧ δ < (9 : ℝ) ^ (n + 1) * u := by
  have hratio : 1 ≤ δ / u := (le_div_iff₀ hu).2 (by simpa using huδ)
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 9)
  exact ⟨n, (le_div_iff₀ hu).1 hn, (div_lt_iff₀ hu).1 hn'⟩

/-- Bounded coefficients give an absolutely convergent paired series. -/
theorem summable_paired_of_bounded {a : ℕ → ℝ} {B : ℝ}
    (hbound : ∀ k, |a k| ≤ B) :
    Summable (fun k => ((1 : ℝ) / 9) ^ k * a k) := by
  have hgeo : Summable (fun k : ℕ => ((1 : ℝ) / 9) ^ k * B) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9)
      (by norm_num : (1 : ℝ) / 9 < 1)).mul_right B
  apply hgeo.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ ((1 : ℝ) / 9) ^ k)]
  exact mul_le_mul_of_nonneg_left (hbound k) (by positivity)

/-- A single term at the exit scale gives a linear lower bound for a
nonnegative paired series. -/
theorem paired_cusp_at_scale
    {a : ℕ → ℝ} {A u δ : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hu : 0 ≤ u)
    (hsum : Summable (fun k => ((1 : ℝ) / 9) ^ k * a k))
    (hnonneg : ∀ k, 0 ≤ a k)
    (hquad : A * ((9 : ℝ) ^ n * u) ^ 2 ≤ a n)
    (hscale : δ ≤ (9 : ℝ) ^ (n + 1) * u) :
    A * δ * u / 9 ≤ ∑' k, ((1 : ℝ) / 9) ^ k * a k := by
  have hterm : ((1 : ℝ) / 9) ^ n * a n ≤
      ∑' k, ((1 : ℝ) / 9) ^ k * a k :=
    hsum.le_tsum n (fun k _ => mul_nonneg (by positivity) (hnonneg k))
  have hweighted := mul_le_mul_of_nonneg_left hquad
    (by positivity : (0 : ℝ) ≤ ((1 : ℝ) / 9) ^ n)
  have hidentity : ((1 : ℝ) / 9) ^ n *
      (A * ((9 : ℝ) ^ n * u) ^ 2) = A * (9 : ℝ) ^ n * u ^ 2 := by
    calc
      _ = A * (((1 : ℝ) / 9) ^ n * ((9 : ℝ) ^ n * u) ^ 2) := by ring
      _ = _ := by rw [weighted_square_nine]; ring
  rw [hidentity] at hweighted
  rw [pow_succ] at hscale
  have hscaled := mul_le_mul_of_nonneg_left hscale (mul_nonneg hA hu)
  nlinarith

/-- Quadratic lower bounds at all sufficiently near iterates imply a linear
cusp, with the exit scale chosen automatically. -/
theorem paired_cusp
    {a : ℕ → ℝ} {A u δ : ℝ}
    (hA : 0 ≤ A) (hu : 0 < u) (huδ : u ≤ δ)
    (hsum : Summable (fun k => ((1 : ℝ) / 9) ^ k * a k))
    (hnonneg : ∀ k, 0 ≤ a k)
    (hquad : ∀ k, (9 : ℝ) ^ k * u ≤ δ →
      A * ((9 : ℝ) ^ k * u) ^ 2 ≤ a k) :
    A * δ * u / 9 ≤ ∑' k, ((1 : ℝ) / 9) ^ k * a k := by
  obtain ⟨n, hn, hn'⟩ := exists_scale_nine hu huδ
  exact paired_cusp_at_scale hA hu.le hsum hnonneg (hquad n hn) hn'.le

lemma sum_powers_nine_bound (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (9 : ℝ) ^ k) ≤ (9 : ℝ) ^ (n + 1) / 8 := by
  have h := mul_geom_sum (9 : ℝ) (n + 1)
  nlinarith

/-- The sum of the geometric majorant for a tail after scale `n`. -/
lemma paired_tail_hasSum (B : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ => ((1 : ℝ) / 9) ^ (k + (n + 1)) * B)
      (((1 : ℝ) / 9) ^ n * B / 8) := by
  have h := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 9)
    (by norm_num : (1 : ℝ) / 9 < 1)).mul_right
      (((1 : ℝ) / 9) ^ (n + 1) * B)
  convert h using 1
  · ext k
    rw [pow_add]
    ring
  · rw [pow_succ]
    norm_num
    ring

/-- Quadratic control before the exit scale and a uniform tail bound imply
a linear upper bound.  `A` is half a second-derivative bound and `B` is twice
a uniform forcing bound in the intended application. -/
theorem paired_lipschitz_at_scale
    {a : ℕ → ℝ} {A B u δ : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : 0 ≤ u) (hδ : 0 < δ)
    (hbound : ∀ k, |a k| ≤ B)
    (hquad : ∀ k ≤ n, |a k| ≤ A * ((9 : ℝ) ^ k * u) ^ 2)
    (hscale₁ : (9 : ℝ) ^ n * u ≤ δ)
    (hscale₂ : δ ≤ (9 : ℝ) ^ (n + 1) * u) :
    |∑' k, ((1 : ℝ) / 9) ^ k * a k| ≤
      9 * (A * δ ^ 2 + B) * u / (8 * δ) := by
  have hsum := summable_paired_of_bounded hbound
  have hprefix :
      |∑ k ∈ Finset.range (n + 1), ((1 : ℝ) / 9) ^ k * a k| ≤
        9 * A * δ * u / 8 := by
    have hpoint : ∀ k ∈ Finset.range (n + 1),
        |((1 : ℝ) / 9) ^ k * a k| ≤ A * u ^ 2 * (9 : ℝ) ^ k := by
      intro k hk
      have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      calc
        |((1 : ℝ) / 9) ^ k * a k| = ((1 : ℝ) / 9) ^ k * |a k| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ ((1 : ℝ) / 9) ^ k * (A * ((9 : ℝ) ^ k * u) ^ 2) :=
          mul_le_mul_of_nonneg_left (hquad k hk') (by positivity)
        _ = A * u ^ 2 * (9 : ℝ) ^ k := by
          calc
            _ = A * (((1 : ℝ) / 9) ^ k * ((9 : ℝ) ^ k * u) ^ 2) := by ring
            _ = _ := by rw [weighted_square_nine]; ring
    have hprefix₁ := (Finset.abs_sum_le_sum_abs
      (fun k => ((1 : ℝ) / 9) ^ k * a k) (Finset.range (n + 1))).trans
        (Finset.sum_le_sum hpoint)
    rw [← Finset.mul_sum] at hprefix₁
    have hprefix₂ := mul_le_mul_of_nonneg_left (sum_powers_nine_bound n)
      (mul_nonneg hA (sq_nonneg u))
    have hscale₁' : (9 : ℝ) ^ (n + 1) * u ≤ 9 * δ := by
      rw [pow_succ]
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hscale₁' (mul_nonneg hA hu)
    nlinarith
  have htail :
      |∑' k : ℕ, ((1 : ℝ) / 9) ^ (k + (n + 1)) * a (k + (n + 1))| ≤
        ((1 : ℝ) / 9) ^ n * B / 8 := by
    have h := tsum_of_norm_bounded (paired_tail_hasSum B n)
      (f := fun k : ℕ => ((1 : ℝ) / 9) ^ (k + (n + 1)) * a (k + (n + 1)))
      (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hbound _) (by positivity))
    simpa only [Real.norm_eq_abs] using h
  have hscaled₂ := mul_le_mul_of_nonneg_left hscale₂
    (by positivity : (0 : ℝ) ≤ ((1 : ℝ) / 9) ^ n)
  have hpow : ((1 : ℝ) / 9) ^ n * ((9 : ℝ) ^ (n + 1) * u) = 9 * u := by
    rw [pow_succ]
    calc
      _ = (((1 : ℝ) / 9) ^ n * (9 : ℝ) ^ n) * 9 * u := by ring
      _ = 9 * u := by rw [inverse_power_nine]; ring
  rw [hpow] at hscaled₂
  have htailScaled := mul_le_mul_of_nonneg_left htail hδ.le
  have hscaledB := mul_le_mul_of_nonneg_left hscaled₂ hB
  have hsplit := hsum.sum_add_tsum_nat_add (n + 1)
  have htotal :
      |∑' k, ((1 : ℝ) / 9) ^ k * a k| ≤
      |∑ k ∈ Finset.range (n + 1), ((1 : ℝ) / 9) ^ k * a k| +
      |∑' k : ℕ, ((1 : ℝ) / 9) ^ (k + (n + 1)) * a (k + (n + 1))| := by
    rw [← hsplit]
    exact abs_add_le _ _
  have htotalScaled := mul_le_mul_of_nonneg_left htotal hδ.le
  have hprefixScaled := mul_le_mul_of_nonneg_left hprefix hδ.le
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * δ)).2
  nlinarith

/-- A version of the paired-series upper bound with the exit scale selected
automatically; it includes the zero-distance case. -/
theorem paired_lipschitz
    {a : ℕ → ℝ} {A B u δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : 0 ≤ u) (hδ : 0 < δ)
    (huδ : u ≤ δ)
    (hbound : ∀ k, |a k| ≤ B)
    (hquad : ∀ k, (9 : ℝ) ^ k * u ≤ δ →
      |a k| ≤ A * ((9 : ℝ) ^ k * u) ^ 2) :
    |∑' k, ((1 : ℝ) / 9) ^ k * a k| ≤
      9 * (A * δ ^ 2 + B) * u / (8 * δ) := by
  by_cases hu0 : u = 0
  · have ha : ∀ k, a k = 0 := by
      intro k
      have h := hquad k (by simp [hu0, hδ.le])
      simpa [hu0] using h
    simp [ha, hu0]
  · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    obtain ⟨n, hn, hn'⟩ := exists_scale_nine hupos huδ
    apply paired_lipschitz_at_scale hA hB hu hδ hbound _ hn hn'.le
    intro k hk
    apply hquad k
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 9) hk) hu).trans hn

end SeriesEstimates
end Lorentz
