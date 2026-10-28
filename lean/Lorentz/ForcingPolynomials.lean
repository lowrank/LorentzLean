module

public import Lorentz.PolynomialBounds
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

/-!
# The polynomial perturbation and its stationary paired forcing

These are actual polynomials, so the qualitative quadratic and Lipschitz
bounds proved earlier apply directly.  The parameter `β` is arbitrary in the
stationarity proof; its particular algebraic value enters only the finite
contact certificate.
-/

namespace Lorentz
namespace ForcingPolynomials

open Polynomial

noncomputable section

def cheb3Poly : ℝ[X] := 4 * X ^ 3 - 3 * X

def hPoly (β : ℝ) : ℝ[X] :=
  (8 * X ^ 4 - 8 * X ^ 2) - 2 * (16 * X ^ 5 - 20 * X ^ 3 + 5 * X) +
    C β * (64 * X ^ 7 - 112 * X ^ 5 + 56 * X ^ 3 - 7 * X)

def pairedForcingPoly (β : ℝ) : ℝ[X] :=
  hPoly β - C ((1 : ℝ) / 3) * (hPoly β).comp cheb3Poly

@[simp] lemma eval_cheb3Poly (x : ℝ) :
    cheb3Poly.eval x = 4 * x ^ 3 - 3 * x := by simp [cheb3Poly]

@[simp] lemma eval_hPoly (β x : ℝ) :
    (hPoly β).eval x =
      (8 * x ^ 4 - 8 * x ^ 2) - 2 * (16 * x ^ 5 - 20 * x ^ 3 + 5 * x) +
        β * (64 * x ^ 7 - 112 * x ^ 5 + 56 * x ^ 3 - 7 * x) := by
  simp [hPoly]

lemma eval_pairedForcingPoly (β x : ℝ) :
    (pairedForcingPoly β).eval x =
      (hPoly β).eval x - (hPoly β).eval (4 * x ^ 3 - 3 * x) / 3 := by
  simp only [pairedForcingPoly, eval_sub, eval_mul, eval_C, eval_comp, eval_cheb3Poly]
  ring

@[simp] lemma hPoly_zero (β : ℝ) : (hPoly β).eval 0 = 0 := by simp

lemma natDegree_hPoly_le (β : ℝ) : (hPoly β).natDegree ≤ 7 := by
  unfold hPoly
  compute_degree

lemma derivative_eval_cheb3Poly (x : ℝ) :
    cheb3Poly.derivative.eval x = 12 * x ^ 2 - 3 := by
  norm_num [cheb3Poly, derivative_mul, derivative_X_pow]
  ring

lemma derivative_eval_hPoly (β x : ℝ) :
    (hPoly β).derivative.eval x =
      (32 * x ^ 3 - 16 * x) - 2 * (80 * x ^ 4 - 60 * x ^ 2 + 5) +
        β * (448 * x ^ 6 - 560 * x ^ 4 + 168 * x ^ 2 - 7) := by
  norm_num [hPoly, derivative_mul, derivative_X_pow]
  ring

lemma derivative_eval_pairedForcingPoly (β x : ℝ) :
    (pairedForcingPoly β).derivative.eval x =
      (hPoly β).derivative.eval x -
        (hPoly β).derivative.eval (4 * x ^ 3 - 3 * x) * (12 * x ^ 2 - 3) / 3 := by
  simp only [pairedForcingPoly, derivative_sub, derivative_mul, derivative_C,
    zero_mul, zero_add, derivative_comp, eval_sub, eval_mul, eval_C, eval_comp,
    eval_cheb3Poly, derivative_eval_cheb3Poly]
  ring

lemma cheb3_at_half_square {x : ℝ} (hx : x ^ 2 = (1 : ℝ) / 2) :
    4 * x ^ 3 - 3 * x = -x := by
  linear_combination 4 * x * hx

lemma derivative_hPoly_reflect {x : ℝ} (β : ℝ) (hx : x ^ 2 = (1 : ℝ) / 2) :
    (hPoly β).derivative.eval x = (hPoly β).derivative.eval (-x) := by
  rw [derivative_eval_hPoly, derivative_eval_hPoly]
  linear_combination 64 * x * hx

/-- The paired forcing is stationary at both points whose square is one
half.  The vanishing of the even perturbation's derivative is the key exact
feature of the construction. -/
theorem pairedForcing_stationary {x : ℝ} (β : ℝ) (hx : x ^ 2 = (1 : ℝ) / 2) :
    (pairedForcingPoly β).derivative.eval x = 0 := by
  rw [derivative_eval_pairedForcingPoly, cheb3_at_half_square hx,
    derivative_hPoly_reflect β hx, hx]
  ring

theorem pairedForcing_stationary_a (β : ℝ) :
    (pairedForcingPoly β).derivative.eval PolynomialBounds.a = 0 :=
  pairedForcing_stationary β PolynomialBounds.a_sq

theorem pairedForcing_stationary_neg_a (β : ℝ) :
    (pairedForcingPoly β).derivative.eval (-PolynomialBounds.a) = 0 := by
  apply pairedForcing_stationary β
  simpa using PolynomialBounds.a_sq

lemma hPoly_reflected_sum (β x : ℝ) :
    (hPoly β).eval x + (hPoly β).eval (-x) = 16 * x ^ 4 - 16 * x ^ 2 := by
  rw [eval_hPoly, eval_hPoly]
  ring

lemma hPoly_reflected_sum_at_a (β : ℝ) :
    (hPoly β).eval PolynomialBounds.a + (hPoly β).eval (-PolynomialBounds.a) = -4 := by
  have ha4 : PolynomialBounds.a ^ 4 = (1 : ℝ) / 4 := by
    calc
      _ = (PolynomialBounds.a ^ 2) ^ 2 := by ring
      _ = _ := by rw [PolynomialBounds.a_sq]; norm_num
  rw [hPoly_reflected_sum, ha4, PolynomialBounds.a_sq]
  norm_num

end
end ForcingPolynomials
end Lorentz
