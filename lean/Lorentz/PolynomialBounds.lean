module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Qualitative polynomial bounds and the cubic forcing gap

Stationarity is converted to a quadratic bound by exact polynomial
factorization, avoiding any numerical Taylor-remainder estimate.  Compactness
supplies a finite coefficient-independent bound for the quotient polynomial.
-/

namespace Lorentz
namespace PolynomialBounds

open Polynomial Set

noncomputable section

theorem exists_pos_eval_bound (p : ℝ[X]) :
    ∃ B > 0, ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ B := by
  have hcompact : IsCompact ((fun x => p.eval x) '' Icc (-1 : ℝ) 1) :=
    isCompact_Icc.image p.continuous
  obtain ⟨B, hB, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  exact ⟨B, hB, fun x hx => by
    simpa only [Real.norm_eq_abs] using hbound (p.eval x) ⟨x, hx, rfl⟩⟩

/-- A stationary polynomial has an exact double factor after its value at
the stationary point is subtracted. -/
theorem stationary_double_factor (p : ℝ[X]) (a : ℝ)
    (hstationary : p.derivative.eval a = 0) :
    ∃ q : ℝ[X], p - C (p.eval a) = (X - C a) ^ 2 * q := by
  obtain ⟨r, hr⟩ := (X_sub_C_dvd_sub_C_eval (p := p) (a := a))
  have hderiv : (p - C (p.eval a)).derivative.eval a = 0 := by
    simpa using hstationary
  rw [hr] at hderiv
  have hrzero : r.eval a = 0 := by
    simpa [derivative_mul] using hderiv
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot (p := r) (a := a)).2 hrzero
  refine ⟨q, ?_⟩
  rw [hr, hq]
  ring

/-- On the unit interval, stationarity gives a global quadratic bound
relative to the stationary point. -/
theorem exists_pos_quadratic_bound (p : ℝ[X]) (a : ℝ)
    (hstationary : p.derivative.eval a = 0) :
    ∃ A > 0, ∀ x ∈ Icc (-1 : ℝ) 1,
      |p.eval x - p.eval a| ≤ A * (x - a) ^ 2 := by
  obtain ⟨q, hfactor⟩ := stationary_double_factor p a hstationary
  obtain ⟨A, hA, hbound⟩ := exists_pos_eval_bound q
  refine ⟨A, hA, ?_⟩
  intro x hx
  have heval : p.eval x - p.eval a = (x - a) ^ 2 * q.eval x := by
    simpa using congrArg (fun r : ℝ[X] => r.eval x) hfactor
  rw [heval, abs_mul, abs_of_nonneg (sq_nonneg (x - a))]
  have h := mul_le_mul_of_nonneg_left (hbound x hx) (sq_nonneg (x - a))
  nlinarith

/-- Every polynomial is Lipschitz on the unit interval, with some positive
constant. -/
theorem exists_pos_lipschitz_bound (p : ℝ[X]) :
    ∃ L > 0, ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |p.eval y - p.eval x| ≤ L * |y - x| := by
  obtain ⟨L, hL, hbound⟩ := exists_pos_eval_bound p.derivative
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_hz : z ∈ Icc (-1 : ℝ) 1) => (p.hasDerivAt z).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hbound z hz)
    (convex_Icc (-1 : ℝ) 1) hx hy
  simpa only [Real.norm_eq_abs] using h

/-- The cosine function is globally 1-Lipschitz. -/
theorem abs_cos_sub_cos_le (x y : ℝ) :
    |Real.cos y - Real.cos x| ≤ |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (Set.univ : Set ℝ)) (C := (1 : ℝ))
    (fun z _ => (Real.hasDerivAt_cos z).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs, abs_neg] using Real.abs_sin_le_one z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- A stationary polynomial composed with cosine has a quadratic bound in
angular displacement, uniformly for every real displacement. -/
theorem exists_pos_cosine_quadratic_bound (p : ℝ[X]) (θ : ℝ)
    (hstationary : p.derivative.eval (Real.cos θ) = 0) :
    ∃ A > 0, ∀ u : ℝ,
      |p.eval (Real.cos (θ + u)) - p.eval (Real.cos θ)| ≤ A * u ^ 2 := by
  obtain ⟨A, hA, hbound⟩ := exists_pos_quadratic_bound p (Real.cos θ) hstationary
  refine ⟨A, hA, ?_⟩
  intro u
  have hcos : |Real.cos (θ + u) - Real.cos θ| ≤ |u| := by
    simpa using abs_cos_sub_cos_le θ (θ + u)
  have hsq : (Real.cos (θ + u) - Real.cos θ) ^ 2 ≤ u ^ 2 := sq_le_sq.mpr hcos
  exact (hbound (Real.cos (θ + u))
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩).trans
      (mul_le_mul_of_nonneg_left hsq hA.le)

noncomputable def a : ℝ := Real.sqrt 2 / 2

def cubic (x : ℝ) : ℝ := 2 * x - 4 * x ^ 3 / 3

lemma cubic_eq_pair (x : ℝ) : cubic x = x - (4 * x ^ 3 - 3 * x) / 3 := by
  dsimp [cubic]
  ring

lemma a_pos : 0 < a := by dsimp [a]; positivity

lemma a_sq : a ^ 2 = (1 : ℝ) / 2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [a]
  nlinarith

lemma a_lt_one : a < 1 := by
  have h := a_sq
  have hp := a_pos
  nlinarith

lemma one_lt_two_a : 1 < 2 * a := by
  have h := a_sq
  have hp := a_pos
  nlinarith

lemma a_mem : a ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [a_pos], a_lt_one.le⟩

lemma cubic_odd (x : ℝ) : cubic (-x) = -cubic x := by
  dsimp [cubic]
  ring

lemma cubic_at_a : cubic a = 4 * a / 3 := by
  dsimp [cubic]
  linear_combination -(4 * a / 3) * a_sq

/-- Exact factorization of the gap below the maximum of the cubic forcing. -/
lemma cubic_gap_factor (x : ℝ) :
    cubic a - cubic x = (4 : ℝ) / 3 * (x - a) ^ 2 * (x + 2 * a) := by
  dsimp [cubic]
  linear_combination 4 * (x - a) * a_sq

def cubicGapConstant : ℝ := (4 : ℝ) / 3 * (2 * a - 1)

lemma cubicGapConstant_pos : 0 < cubicGapConstant := by
  dsimp [cubicGapConstant]
  exact mul_pos (by norm_num) (by linarith [one_lt_two_a])

theorem cubic_quadratic_gap {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    cubicGapConstant * (x - a) ^ 2 ≤ cubic a - cubic x := by
  rw [cubic_gap_factor]
  dsimp [cubicGapConstant]
  have h := mul_nonneg (sq_nonneg (x - a)) (show 0 ≤ x + 1 by linarith [hx.1])
  nlinarith

theorem cubic_le_max {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    cubic x ≤ cubic a := by
  have h := cubic_quadratic_gap hx
  have hn := mul_nonneg cubicGapConstant_pos.le (sq_nonneg (x - a))
  linarith

theorem cubic_gap_pos {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hne : x ≠ a) :
    0 < cubic a - cubic x := by
  have hsq : 0 < (x - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  exact lt_of_lt_of_le (mul_pos cubicGapConstant_pos hsq) (cubic_quadratic_gap hx)

theorem cubic_eq_max_iff {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    cubic x = cubic a ↔ x = a := by
  constructor
  · intro heq
    by_contra hne
    have h := cubic_gap_pos hx hne
    rw [heq, sub_self] at h
    exact (lt_irrefl 0) h
  · rintro rfl
    rfl

theorem abs_cubic_le_max {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |cubic x| ≤ cubic a := by
  apply abs_le.mpr
  constructor
  · have h := cubic_le_max (x := -x) (by constructor <;> linarith [hx.1, hx.2])
    rw [cubic_odd] at h
    linarith
  · exact cubic_le_max hx

lemma cubic_at_a_pos : 0 < cubic a := by rw [cubic_at_a]; nlinarith [a_pos]

end
end PolynomialBounds
end Lorentz
