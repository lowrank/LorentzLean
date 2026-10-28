module

public import Lorentz.Baseline
public import Lorentz.Plateau.SeriesTools

@[expose] public section

/-!
# The baseline with contraction factor `-3/5`

The resolvent identity expresses this baseline as a positive combination of
signed translates of the already certified `-1/3` baseline. It gives the
exact extrema and a lower bound for the deficit from any even orbit term.
-/

namespace Lorentz.Plateau.Baseline

open Set

noncomputable def G (x : ℝ) : ℝ := orbitSeries id (-3 / 5) x

noncomputable def B : ℝ := 5 * PolynomialBounds.a / 2

lemma B_pos : 0 < B := by
  have := PolynomialBounds.a_pos
  dsimp [B]
  positivity

lemma G_continuousOn : ContinuousOn G interval :=
  orbitSeries_continuousOn' (by norm_num) continuous_id

lemma G_odd : Function.Odd G := orbitSeries_odd (by intro x; rfl)

lemma G_zero : G 0 = 0 := orbitSeries_zero rfl

lemma G_equation {x : ℝ} (hx : x ∈ interval) :
    G x = x - (3 / 5) * G (cubic x) := by
  have h := orbitSeries_equation' (q := id) (ρ := (-3 : ℝ) / 5)
    (by norm_num) continuous_id hx
  change G x = x + (-3 / 5) * G (cubic x) at h
  linarith

lemma G_at_a : G PolynomialBounds.a = B := by
  have h := G_equation PolynomialBounds.a_mem
  rw [Lorentz.Baseline.cubic_a, G_odd] at h
  dsimp [B]
  linarith

lemma G_at_neg_a : G (-PolynomialBounds.a) = -B := by
  rw [G_odd, G_at_a]

/-- Resolvent identity relating the two contraction parameters. -/
theorem resolvent {x : ℝ} (hx : x ∈ interval) :
    G x = (5 / 9) * Lorentz.Baseline.G x +
      (4 / 9) * orbitSeries Lorentz.Baseline.G (-3 / 5) x := by
  apply selfsimilar_unique (q := id) (ρ := (-3 : ℝ) / 5) (by norm_num)
    G_continuousOn
    ((continuousOn_const.mul Lorentz.Baseline.G_continuousOn).add
      (continuousOn_const.mul (orbitSeries_continuousOn_of_continuousOn
        (by norm_num) Lorentz.Baseline.G_continuousOn
        (fun _ hy ↦ Lorentz.Baseline.G_abs_le hy))))
    (fun y hy ↦ by have h := G_equation hy; dsimp only [id_eq]; linarith) ?_ x hx
  intro y hy
  have hb := Lorentz.Baseline.G_equation hy
  have hs := orbitSeries_equation (ρ := (-3 : ℝ) / 5) (by norm_num)
    (fun _ hz ↦ Lorentz.Baseline.G_abs_le hz) hy
  simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  linear_combination hb + (4 / 9) * hs

lemma G_abs_le {x : ℝ} (hx : x ∈ interval) : |G x| ≤ B := by
  have hb := Lorentz.Baseline.G_abs_le hx
  have hs := orbitSeries_bound (ρ := (-3 : ℝ) / 5) (by norm_num)
    (fun _ hy ↦ Lorentz.Baseline.G_abs_le hy) hx
  norm_num at hs
  rw [resolvent hx]
  calc
    _ ≤ |(5 / 9 : ℝ) * Lorentz.Baseline.G x| +
        |(4 / 9 : ℝ) * orbitSeries Lorentz.Baseline.G (-3 / 5) x| := abs_add_le _ _
    _ = (5 / 9) * |Lorentz.Baseline.G x| +
        (4 / 9) * |orbitSeries Lorentz.Baseline.G (-3 / 5) x| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ B := by
      dsimp [B, Lorentz.Baseline.B] at *
      linarith

lemma G_lt_max {x : ℝ} (hx : x ∈ interval) (hxa : x ≠ PolynomialBounds.a) :
    G x < B := by
  have hb := Lorentz.Baseline.G_lt_max hx hxa
  have hs := (le_abs_self _).trans (orbitSeries_bound (ρ := (-3 : ℝ) / 5)
    (by norm_num) (fun _ hy ↦ Lorentz.Baseline.G_abs_le hy) hx)
  norm_num at hs
  rw [resolvent hx]
  dsimp [B, Lorentz.Baseline.B] at *
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

lemma old_quadratic_gap {x : ℝ} (hx : x ∈ interval) :
    PolynomialBounds.cubicGapConstant * (x - PolynomialBounds.a) ^ 2 ≤
      Lorentz.Baseline.B - Lorentz.Baseline.G x := by
  have hg := Lorentz.Baseline.G_two_step hx
  have hb := (abs_le.mp (Lorentz.Baseline.G_abs_le
    (cubic_maps_interval (cubic_maps_interval hx)))).2
  have hq := PolynomialBounds.cubic_quadratic_gap hx
  have hmax : Lorentz.Baseline.B = PolynomialBounds.cubic PolynomialBounds.a +
      Lorentz.Baseline.B / 9 := by
    rw [PolynomialBounds.cubic_at_a]
    dsimp [Lorentz.Baseline.B]
    ring
  linarith

/-- Every signed orbit deficit is nonnegative. -/
lemma orbit_deficit_nonneg {x : ℝ} (hx : x ∈ interval) (j : ℕ) :
    0 ≤ (3 / 5 : ℝ) ^ j * Lorentz.Baseline.B -
      (-3 / 5 : ℝ) ^ j * Lorentz.Baseline.G ((cubic^[j]) x) := by
  have h := orbit_term_bound (ρ := (-3 : ℝ) / 5)
    (fun _ hy ↦ Lorentz.Baseline.G_abs_le hy) hx j
  simp only [Real.norm_eq_abs, show |(-3 : ℝ) / 5| = 3 / 5 by norm_num] at h
  exact sub_nonneg.mpr ((le_abs_self _).trans h)

/-- The positive resolvent retains a specified even orbit's deficit. -/
theorem even_orbit_gap {x : ℝ} (hx : x ∈ interval) (j : ℕ) :
    (4 / 9 : ℝ) * (9 / 25 : ℝ) ^ j *
        (Lorentz.Baseline.B - Lorentz.Baseline.G ((cubic^[2 * j]) x)) ≤
      B - G x := by
  have hconst := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 5) (by norm_num : (3 / 5 : ℝ) < 1)).mul_right
      Lorentz.Baseline.B
  have hs := orbit_summable (ρ := (-3 : ℝ) / 5) (by norm_num)
    (fun _ hy ↦ Lorentz.Baseline.G_abs_le hy) hx
  have hdiff := hconst.summable.sub hs
  have hterm := hdiff.le_tsum (2 * j) (fun i _ ↦ orbit_deficit_nonneg hx i)
  rw [hconst.summable.tsum_sub hs, hconst.tsum_eq] at hterm
  change (3 / 5 : ℝ) ^ (2 * j) * Lorentz.Baseline.B -
      (-3 / 5 : ℝ) ^ (2 * j) * Lorentz.Baseline.G ((cubic^[2 * j]) x) ≤
      (1 - (3 / 5 : ℝ))⁻¹ * Lorentz.Baseline.B -
      orbitSeries Lorentz.Baseline.G (-3 / 5) x at hterm
  norm_num only [pow_mul, show (3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num,
    show (-3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num] at hterm
  have hb := (abs_le.mp (Lorentz.Baseline.G_abs_le hx)).2
  rw [resolvent hx]
  dsimp [B, Lorentz.Baseline.B] at *
  norm_num at hterm
  nlinarith

end Lorentz.Plateau.Baseline
