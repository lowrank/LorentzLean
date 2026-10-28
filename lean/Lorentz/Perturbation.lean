module

public import Lorentz.QuarterSeries
public import Lorentz.AngularSeries
public import Lorentz.ForcingPolynomials

@[expose] public section

/-! The actual perturbation series and its local regularity at the two
extremal cycle points. -/

namespace Lorentz

open Set Polynomial

noncomputable def H (β x : ℝ) : ℝ :=
  orbitSeries (ForcingPolynomials.hPoly β).eval (-1 / 3) x

theorem H_continuousOn (β : ℝ) : ContinuousOn (H β) interval := by
  exact orbitSeries_continuousOn' (by norm_num) (ForcingPolynomials.hPoly β).continuous

theorem H_equation (β : ℝ) {x : ℝ} (hx : x ∈ interval) :
    H β x = (ForcingPolynomials.hPoly β).eval x - H β (cubic x) / 3 := by
  have h := orbitSeries_equation' (q := (ForcingPolynomials.hPoly β).eval)
    (ρ := (-1 / 3 : ℝ)) (by norm_num) (ForcingPolynomials.hPoly β).continuous hx
  change H β x = (ForcingPolynomials.hPoly β).eval x + (-1 / 3 : ℝ) * H β (cubic x) at h
  linarith

theorem H_paired_equation (β : ℝ) {x : ℝ} (hx : x ∈ interval) :
    H β x = (ForcingPolynomials.pairedForcingPoly β).eval x +
      H β (cubic (cubic x)) / 9 := by
  have h₁ := H_equation β hx
  have h₂ := H_equation β (cubic_maps_interval hx)
  rw [ForcingPolynomials.eval_pairedForcingPoly]
  change H β x = (ForcingPolynomials.hPoly β).eval x -
    (ForcingPolynomials.hPoly β).eval (cubic x) / 3 + H β (cubic (cubic x)) / 9
  linarith

@[simp] theorem H_zero (β : ℝ) : H β 0 = 0 :=
  orbitSeries_zero (ForcingPolynomials.hPoly_zero β)

theorem H_quarter_difference (β : ℝ) (k : ℕ) (u : ℝ) :
    H β (Real.cos ((k : ℝ) * Real.pi / 4 + u)) -
      H β (Real.cos ((k : ℝ) * Real.pi / 4)) =
      ∑' j : ℕ, ((1 : ℝ) / 9) ^ j *
        ((ForcingPolynomials.pairedForcingPoly β).eval
            (Real.cos ((k : ℝ) * Real.pi / 4 + (9 : ℝ) ^ j * u)) -
          (ForcingPolynomials.pairedForcingPoly β).eval
            (Real.cos ((k : ℝ) * Real.pi / 4))) := by
  unfold H
  rw [orbitSeries_quarter_difference (ForcingPolynomials.hPoly β).continuous]
  apply tsum_congr
  intro j
  simp only [ForcingPolynomials.eval_pairedForcingPoly, cubic]

/-- Local pointwise Lipschitz regularity at a quarter-period centre follows
from stationarity of the paired forcing there. -/
theorem H_local_lipschitz_quarter (β : ℝ) (k : ℕ)
    (hθ₀ : 0 ≤ (k : ℝ) * Real.pi / 4)
    (hθπ : (k : ℝ) * Real.pi / 4 ≤ Real.pi)
    (hsq : (Real.cos ((k : ℝ) * Real.pi / 4)) ^ 2 = (1 : ℝ) / 2) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ interval,
      |x - Real.cos ((k : ℝ) * Real.pi / 4)| ≤ r →
        |H β x - H β (Real.cos ((k : ℝ) * Real.pi / 4))| ≤
          C * |x - Real.cos ((k : ℝ) * Real.pi / 4)| := by
  have hsin : Real.sin ((k : ℝ) * Real.pi / 4) ≠ 0 := by
    intro hzero
    have h := Real.sin_sq_add_cos_sq ((k : ℝ) * Real.pi / 4)
    rw [hzero, hsq] at h
    norm_num at h
  obtain ⟨L, hL, hlip⟩ := AngularSeries.exists_paired_cosine_lipschitz
    (ForcingPolynomials.pairedForcingPoly β) ((k : ℝ) * Real.pi / 4)
    (ForcingPolynomials.pairedForcing_stationary β hsq)
  apply AngularSeries.angular_lipschitz_to_spatial
    (F := H β) hθ₀ hθπ hsin (by norm_num : (0 : ℝ) < 1) hL.le
  intro u hu
  rw [H_quarter_difference]
  exact hlip u hu

lemma cos_three_quarter : Real.cos (3 * Real.pi / 4) = -PolynomialBounds.a := by
  have hangle : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
  rw [hangle, Real.cos_pi_sub, Real.cos_pi_div_four]
  rfl

theorem H_local_lipschitz_a (β : ℝ) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ interval, |x - PolynomialBounds.a| ≤ r →
      |H β x - H β PolynomialBounds.a| ≤ C * |x - PolynomialBounds.a| := by
  have hsq : (Real.cos (((1 : ℕ) : ℝ) * Real.pi / 4)) ^ 2 = (1 : ℝ) / 2 := by
    simpa only [Nat.cast_one, one_mul, Real.cos_pi_div_four, PolynomialBounds.a]
      using PolynomialBounds.a_sq
  have h := H_local_lipschitz_quarter β 1
    (by norm_num; linarith [Real.pi_pos])
    (by norm_num; linarith [Real.pi_pos]) hsq
  simpa only [Nat.cast_one, one_mul, Real.cos_pi_div_four, PolynomialBounds.a] using h

theorem H_local_lipschitz_neg_a (β : ℝ) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ interval, |x - (-PolynomialBounds.a)| ≤ r →
      |H β x - H β (-PolynomialBounds.a)| ≤ C * |x - (-PolynomialBounds.a)| := by
  have hsq : (Real.cos (((3 : ℕ) : ℝ) * Real.pi / 4)) ^ 2 = (1 : ℝ) / 2 := by
    simpa only [Nat.cast_ofNat, cos_three_quarter, neg_sq] using PolynomialBounds.a_sq
  have h := H_local_lipschitz_quarter β 3
    (by norm_num; linarith [Real.pi_pos])
    (by norm_num; linarith [Real.pi_pos]) hsq
  simpa only [Nat.cast_ofNat, cos_three_quarter] using h

/-- The perturbation has a nonzero even part, independently of the algebraic
parameter used to select the finite contact certificate. -/
theorem H_reflected_sum_at_a (β : ℝ) :
    H β PolynomialBounds.a + H β (-PolynomialBounds.a) = -3 := by
  have ha : PolynomialBounds.a ∈ interval := PolynomialBounds.a_mem
  have hna : -PolynomialBounds.a ∈ interval := by
    constructor <;> linarith [ha.1, ha.2]
  have hcycle : cubic PolynomialBounds.a = -PolynomialBounds.a := by
    exact ForcingPolynomials.cheb3_at_half_square PolynomialBounds.a_sq
  have hncycle : cubic (-PolynomialBounds.a) = PolynomialBounds.a := by
    rw [cubic_neg, hcycle, neg_neg]
  have h₁ := H_equation β ha
  have h₂ := H_equation β hna
  rw [hcycle] at h₁
  rw [hncycle] at h₂
  have hsum := ForcingPolynomials.hPoly_reflected_sum_at_a β
  linarith

end Lorentz
