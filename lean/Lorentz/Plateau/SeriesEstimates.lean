module

public import Lorentz.SeriesEstimates

@[expose] public section

/-! Exit-scale estimates for the slower contraction in the plateau constructions. -/

namespace Lorentz.Plateau.SeriesEstimates

open scoped BigOperators

lemma summable_weighted {a : ℕ → ℝ} {B : ℝ} (hbound : ∀ k, |a k| ≤ B) :
    Summable (fun k ↦ (9 / 25 : ℝ) ^ k * a k) := by
  have hg := (summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 9 / 25) (by norm_num : (9 / 25 : ℝ) < 1)).mul_right B
  apply hg.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hbound k) (by positivity)

lemma sum_expanding_powers (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (81 / 25 : ℝ) ^ k) ≤ 2 * (81 / 25 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : 0 ≤ (81 / 25 : ℝ) ^ n := by positivity
    nlinarith

lemma tail_hasSum (B : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ ↦ (9 / 25 : ℝ) ^ (k + (n + 1)) * B)
      ((9 / 16 : ℝ) * (9 / 25 : ℝ) ^ n * B) := by
  have h := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 9 / 25) (by norm_num : (9 / 25 : ℝ) < 1)).mul_right
      ((9 / 25 : ℝ) ^ (n + 1) * B)
  convert h using 1
  · funext k
    rw [pow_add]
    ring
  · rw [pow_succ]
    norm_num
    ring

/-- A Lipschitz prefix and a bounded tail are controlled by the same weight
as the baseline's deficit at the last scale before exit. -/
theorem oscillation_at_scale {a : ℕ → ℝ} {D B u δ : ℝ} {n : ℕ}
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hu : 0 ≤ u)
    (hbound : ∀ k, |a k| ≤ B)
    (hlip : ∀ k ≤ n, |a k| ≤ D * (9 : ℝ) ^ k * u)
    (hscale : (9 : ℝ) ^ n * u ≤ δ) :
    |∑' k, (9 / 25 : ℝ) ^ k * a k| ≤ (2 * D * δ + B) * (9 / 25 : ℝ) ^ n := by
  have hprefix :
      |∑ k ∈ Finset.range (n + 1), (9 / 25 : ℝ) ^ k * a k| ≤
        2 * D * δ * (9 / 25 : ℝ) ^ n := by
    have hpoint : ∀ k ∈ Finset.range (n + 1),
        |(9 / 25 : ℝ) ^ k * a k| ≤ D * u * (81 / 25 : ℝ) ^ k := by
      intro k hk
      have hle := hlip k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      calc
        _ = (9 / 25 : ℝ) ^ k * |a k| := by rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ (9 / 25 : ℝ) ^ k * (D * (9 : ℝ) ^ k * u) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        _ = D * u * (81 / 25 : ℝ) ^ k := by
          rw [show (81 / 25 : ℝ) = (9 / 25) * 9 by norm_num, mul_pow]
          ring
    have hsum := (Finset.abs_sum_le_sum_abs
      (fun k ↦ (9 / 25 : ℝ) ^ k * a k) (Finset.range (n + 1))).trans
      (Finset.sum_le_sum hpoint)
    rw [← Finset.mul_sum] at hsum
    have hgeom := mul_le_mul_of_nonneg_left (sum_expanding_powers n) (mul_nonneg hD hu)
    have hscaled := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ 2 * D * (9 / 25 : ℝ) ^ n by positivity)
    have hpow : (81 / 25 : ℝ) ^ n = (9 / 25 : ℝ) ^ n * (9 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    rw [hpow] at hgeom
    nlinarith
  have htail :
      |∑' k : ℕ, (9 / 25 : ℝ) ^ (k + (n + 1)) * a (k + (n + 1))| ≤
        (9 / 16 : ℝ) * (9 / 25 : ℝ) ^ n * B := by
    have h := tsum_of_norm_bounded (tail_hasSum B n)
      (f := fun k : ℕ ↦ (9 / 25 : ℝ) ^ (k + (n + 1)) * a (k + (n + 1)))
      (fun k ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hbound _) (by positivity))
    simpa only [Real.norm_eq_abs] using h
  have hsplit := (summable_weighted hbound).sum_add_tsum_nat_add (n + 1)
  have htotal :
      |∑' k, (9 / 25 : ℝ) ^ k * a k| ≤
      |∑ k ∈ Finset.range (n + 1), (9 / 25 : ℝ) ^ k * a k| +
      |∑' k : ℕ, (9 / 25 : ℝ) ^ (k + (n + 1)) * a (k + (n + 1))| := by
    rw [← hsplit]
    exact abs_add_le _ _
  have hBpow : 0 ≤ (9 / 25 : ℝ) ^ n * B := mul_nonneg (by positivity) hB
  nlinarith

end Lorentz.Plateau.SeriesEstimates
