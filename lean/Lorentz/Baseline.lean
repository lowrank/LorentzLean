module

public import Lorentz.Trigonometry
public import Lorentz.PolynomialBounds

@[expose] public section

/-! The unperturbed self-similar function and its exact extrema. -/

namespace Lorentz.Baseline

open Set

noncomputable def G (x : ℝ) : ℝ := orbitSeries id (-1 / 3) x

noncomputable def B : ℝ := 3 * PolynomialBounds.a / 2

lemma B_pos : 0 < B := by
  have := PolynomialBounds.a_pos
  dsimp [B]
  positivity

lemma G_continuousOn : ContinuousOn G interval :=
  orbitSeries_continuousOn' (by norm_num) continuous_id

lemma G_odd : Function.Odd G := orbitSeries_odd (by intro x; rfl)

lemma G_zero : G 0 = 0 := orbitSeries_zero rfl

lemma cubic_a : Lorentz.cubic PolynomialBounds.a = -PolynomialBounds.a := by
  dsimp [Lorentz.cubic]
  linear_combination 4 * PolynomialBounds.a * PolynomialBounds.a_sq

lemma G_equation {x : ℝ} (hx : x ∈ interval) :
    G x = x - G (Lorentz.cubic x) / 3 := by
  have h := orbitSeries_equation' (q := id) (ρ := (-1 : ℝ) / 3)
    (by norm_num) continuous_id hx
  change G x = x + (-1 / 3) * G (Lorentz.cubic x) at h
  linarith

lemma G_at_a : G PolynomialBounds.a = B := by
  have h := G_equation PolynomialBounds.a_mem
  rw [cubic_a, G_odd] at h
  dsimp [B]
  linarith

lemma G_at_neg_a : G (-PolynomialBounds.a) = -B := by
  rw [G_odd, G_at_a]

lemma G_two_step {x : ℝ} (hx : x ∈ interval) :
    G x = PolynomialBounds.cubic x +
      G (Lorentz.cubic (Lorentz.cubic x)) / 9 := by
  have h := G_equation hx
  have h' := G_equation (cubic_maps_interval hx)
  dsimp [PolynomialBounds.cubic, Lorentz.cubic] at *
  linarith

lemma G_paired {x : ℝ} (hx : x ∈ interval) :
    G x = ∑' j : ℕ, ((1 : ℝ) / 9) ^ j *
      PolynomialBounds.cubic ((Lorentz.cubic^[2 * j]) x) := by
  rw [G, orbitSeries_paired continuous_id hx]
  apply tsum_congr
  intro j
  dsimp [PolynomialBounds.cubic, Lorentz.cubic]
  ring

lemma G_abs_le {x : ℝ} (hx : x ∈ interval) : |G x| ≤ B := by
  have hg := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 9) (by norm_num : (1 : ℝ) / 9 < 1)).mul_right
      (PolynomialBounds.cubic PolynomialBounds.a)
  have hb : ∀ j : ℕ,
      ‖((1 : ℝ) / 9) ^ j * PolynomialBounds.cubic ((Lorentz.cubic^[2 * j]) x)‖ ≤
      ((1 : ℝ) / 9) ^ j * PolynomialBounds.cubic PolynomialBounds.a := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((1 : ℝ) / 9) ^ j)]
    exact mul_le_mul_of_nonneg_left
      (PolynomialBounds.abs_cubic_le_max (cubic_iterate_mem (2 * j) hx)) (by positivity)
  have h := tsum_of_norm_bounded hg hb
  rw [Real.norm_eq_abs, ← G_paired hx] at h
  convert h using 1
  rw [PolynomialBounds.cubic_at_a]
  dsimp [B]
  norm_num
  ring

lemma G_lt_max {x : ℝ} (hx : x ∈ interval) (hxa : x ≠ PolynomialBounds.a) :
    G x < B := by
  have hbound := (abs_le.mp (G_abs_le (cubic_maps_interval (cubic_maps_interval hx)))).2
  have hquad := PolynomialBounds.cubic_quadratic_gap hx
  have hgap : 0 < PolynomialBounds.cubicGapConstant * (x - PolynomialBounds.a) ^ 2 :=
    mul_pos PolynomialBounds.cubicGapConstant_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxa))
  have h := G_two_step hx
  have heq : B = PolynomialBounds.cubic PolynomialBounds.a + B / 9 := by
    rw [PolynomialBounds.cubic_at_a]
    dsimp [B]
    ring
  linarith

lemma G_abs_lt {x : ℝ} (hx : x ∈ interval)
    (hxa : x ≠ PolynomialBounds.a) (hxna : x ≠ -PolynomialBounds.a) :
    |G x| < B := by
  apply abs_lt.mpr
  constructor
  · have hneg : -x ∈ interval := by constructor <;> linarith [hx.1, hx.2]
    have hneq : -x ≠ PolynomialBounds.a := by intro h; apply hxna; linarith
    have h := G_lt_max hneg hneq
    rw [G_odd] at h
    linarith
  · exact G_lt_max hx hxa

lemma G_paired_cos (θ : ℝ) :
    G (Real.cos θ) = ∑' j : ℕ, ((1 : ℝ) / 9) ^ j *
      PolynomialBounds.cubic (Real.cos ((9 : ℝ) ^ j * θ)) := by
  rw [G_paired (cosine_mem_interval θ)]
  apply tsum_congr
  intro j
  rw [cubic_even_iterate_cos]

lemma G_cosine_gap_series (u : ℝ) :
    B - G (Real.cos (Real.pi / 4 + u)) =
      ∑' j : ℕ, ((1 : ℝ) / 9) ^ j *
        (PolynomialBounds.cubic PolynomialBounds.a -
          PolynomialBounds.cubic (Real.cos (Real.pi / 4 + (9 : ℝ) ^ j * u))) := by
  have hconst := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 9) (by norm_num : (1 : ℝ) / 9 < 1)).mul_right
      (PolynomialBounds.cubic PolynomialBounds.a)
  have hconstval : (1 - (1 : ℝ) / 9)⁻¹ * PolynomialBounds.cubic PolynomialBounds.a = B := by
    rw [PolynomialBounds.cubic_at_a]
    dsimp [B]
    norm_num
    ring
  rw [hconstval] at hconst
  have hgeo : Summable (fun j : ℕ => ((1 : ℝ) / 9) ^ j *
      PolynomialBounds.cubic PolynomialBounds.a) := hconst.summable
  have hs : Summable (fun j : ℕ => ((1 : ℝ) / 9) ^ j *
      PolynomialBounds.cubic (Real.cos (Real.pi / 4 + (9 : ℝ) ^ j * u))) := by
    exact hgeo.of_norm_bounded (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((1 : ℝ) / 9) ^ j)]
      exact mul_le_mul_of_nonneg_left
        (PolynomialBounds.abs_cubic_le_max (cosine_mem_interval _)) (by positivity))
  have hG : G (Real.cos (Real.pi / 4 + u)) =
      ∑' j : ℕ, ((1 : ℝ) / 9) ^ j *
        PolynomialBounds.cubic (Real.cos (Real.pi / 4 + (9 : ℝ) ^ j * u)) := by
    rw [G_paired_cos]
    apply tsum_congr
    intro j
    have h := cosine_quarter_phase 1 j u
    norm_num at h
    rw [h]
  rw [hG, ← hconst.tsum_eq, ← hgeo.tsum_sub hs]
  apply tsum_congr
  intro j
  ring

end Lorentz.Baseline
