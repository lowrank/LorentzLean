module

public import Lorentz.Plateau.Geometry

@[expose] public section

/-! The two seed maps and their residuals after the first self-similar term. -/

namespace Lorentz.Plateau

open Polynomial Set

noncomputable def seedMap (even : Bool) : ℝ[X] :=
  if even then Certificate.sixthPoly else Lorentz.cubicPoly

noncomputable def pullback (even high : Bool) : ℝ[X] :=
  if high then -(seedMap even).comp cubicPoly else seedMap even

noncomputable def basePolynomial (even high : Bool) : ℝ[X] :=
  if high then seedMap even else 0

noncomputable def amplitude (high : Bool) : ℝ := if high then 3 / 5 else 1

noncomputable def familyFunction (even : Bool) (h : ℝ[X]) (ε x : ℝ) : ℝ :=
  Baseline.G ((seedMap even).eval x) + ε * orbitSeries h.eval (-3 / 5) x

lemma seedMap_eval_false (x : ℝ) : (seedMap false).eval x = cubic x := by
  simp [seedMap, eval_cubicPoly]

lemma seedMap_eval_true (x : ℝ) : (seedMap true).eval x = 2 * cubic x ^ 2 - 1 := by
  simp [seedMap, Certificate.sixthPoly_eval, Certificate.sixth, Certificate.cubic, cubic]

lemma seedMap_maps (even : Bool) {x : ℝ} (hx : x ∈ interval) :
    (seedMap even).eval x ∈ interval := by
  have h := cubic_maps_interval hx
  cases even
  · simpa only [seedMap_eval_false] using h
  · rw [seedMap_eval_true]
    have hsq : cubic x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr h)
    constructor <;> nlinarith [sq_nonneg (cubic x)]

lemma seedMap_commutes (even : Bool) (x : ℝ) :
    (seedMap even).eval (cubic x) = cubic ((seedMap even).eval x) := by
  cases even
  · simp only [seedMap_eval_false]
  · simp only [seedMap_eval_true, cubic]
    ring

lemma pullback_eval (even high : Bool) (x : ℝ) :
    (pullback even high).eval x =
      if high then -(seedMap even).eval (cubic x) else (seedMap even).eval x := by
  cases high <;> simp [pullback, eval_cubicPoly]

lemma pullback_maps (even high : Bool) {x : ℝ} (hx : x ∈ interval) :
    (pullback even high).eval x ∈ interval := by
  rw [pullback_eval]
  cases high
  · simpa only [Bool.false_eq_true, ↓reduceIte] using seedMap_maps even hx
  · simp only [↓reduceIte]
    have h := seedMap_maps even (cubic_maps_interval hx)
    constructor <;> linarith [h.1, h.2]

lemma amplitude_pos (high : Bool) : 0 < amplitude high := by
  cases high <;> norm_num [amplitude]

lemma family_residual (even high : Bool) (h v : ℝ[X]) (ε : ℝ)
    {x : ℝ} (hx : x ∈ interval) :
    familyFunction even h ε x - (basePolynomial even high + C ε * v).eval x =
      amplitude high * Baseline.G ((pullback even high).eval x) +
        ε * (orbitSeries h.eval (-3 / 5) x - v.eval x) := by
  have hg := Baseline.G_equation (seedMap_maps even hx)
  rw [← seedMap_commutes] at hg
  cases high
  · simp [familyFunction, basePolynomial, amplitude, pullback_eval]
    ring
  · simp only [familyFunction, basePolynomial, amplitude, Bool.true_eq, ↓reduceIte,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, pullback_eval]
    rw [Baseline.G_odd]
    linarith

lemma family_continuous (even : Bool) (h : ℝ[X]) (ε : ℝ) :
    ContinuousOn (familyFunction even h ε) interval :=
  (Baseline.G_continuousOn.comp (seedMap even).continuous.continuousOn
    (fun _ hx ↦ seedMap_maps even hx)).add
    (continuousOn_const.mul (orbitSeries_continuousOn' (by norm_num) h.continuous))

lemma family_equation (even : Bool) (h : ℝ[X]) (ε : ℝ) {x : ℝ} (hx : x ∈ interval) :
    familyFunction even h ε x = (seedMap even + C ε * h).eval x +
      (-3 / 5) * familyFunction even h ε (cubic x) := by
  have hg := Baseline.G_equation (seedMap_maps even hx)
  rw [← seedMap_commutes] at hg
  have hh := orbitSeries_equation' (ρ := (-3 : ℝ) / 5) (by norm_num) h.continuous hx
  simp only [familyFunction, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination hg + ε * hh

lemma series_endpoint (h : ℝ[X]) {x : ℝ} (hx : x = 1 ∨ x = -1) :
    orbitSeries h.eval (-3 / 5) x = (5 / 8) * h.eval x := by
  have hi : x ∈ interval := by rcases hx with rfl | rfl <;> constructor <;> norm_num
  have hc : cubic x = x := by rcases hx with rfl | rfl <;> norm_num [cubic]
  have hh := orbitSeries_equation' (ρ := (-3 : ℝ) / 5) (by norm_num) h.continuous hi
  rw [hc] at hh
  linarith

lemma family_odd_defect (h : ℝ[X]) (ε : ℝ) :
    familyFunction false h ε 1 + familyFunction false h ε (-1) =
      ε * (5 / 8) * (h.eval 1 + h.eval (-1)) := by
  simp only [familyFunction, seedMap_eval_false, series_endpoint h (Or.inl rfl),
    series_endpoint h (Or.inr rfl)]
  norm_num only [cubic]
  rw [Baseline.G_odd]
  ring

lemma family_even_defect (h : ℝ[X]) (ε : ℝ) :
    familyFunction true h ε 1 - familyFunction true h ε (-1) =
      ε * (5 / 8) * (h.eval 1 - h.eval (-1)) := by
  simp only [familyFunction, seedMap_eval_true, series_endpoint h (Or.inl rfl),
    series_endpoint h (Or.inr rfl)]
  norm_num only [cubic]
  ring

lemma family_zero (h : ℝ[X]) (hh : h.eval 0 = 0) (ε : ℝ) :
    familyFunction false h ε 0 = 0 := by
  simp only [familyFunction, seedMap_eval_false]
  norm_num only [cubic, Baseline.G_zero, orbitSeries_zero (q := h.eval) hh, mul_zero, add_zero]

end Lorentz.Plateau
