module

public import Lorentz.Composition
public import Lorentz.PolynomialBounds

@[expose] public section

/-! Uniqueness and continuity tools for the actual self-similar series. -/

open Set Polynomial

namespace Lorentz.Plateau

theorem orbitSeries_continuousOn_of_continuousOn {q : ℝ → ℝ} {ρ M : ℝ}
    (hρ : |ρ| < 1) (hq : ContinuousOn q interval)
    (hbound : ∀ x ∈ interval, |q x| ≤ M) :
    ContinuousOn (orbitSeries q ρ) interval := by
  apply continuousOn_tsum
    (f := fun j x ↦ ρ ^ j * q ((cubic^[j]) x))
    (u := fun j : ℕ ↦ |ρ| ^ j * M)
  · intro j
    exact continuousOn_const.mul (hq.comp (cubic_continuous.iterate j).continuousOn
      (fun x hx ↦ cubic_iterate_mem j hx))
  · exact (summable_geometric_of_norm_lt_one (by simpa using hρ)).mul_right M
  · intro j x hx
    exact orbit_term_bound hbound hx j

/-- A contraction equation has at most one continuous solution on the interval. -/
theorem selfsimilar_unique {f g q : ℝ → ℝ} {ρ : ℝ}
    (hρ : |ρ| < 1) (hf : ContinuousOn f interval) (hg : ContinuousOn g interval)
    (hfeq : ∀ x ∈ interval, f x = q x + ρ * f (cubic x))
    (hgeq : ∀ x ∈ interval, g x = q x + ρ * g (cubic x)) :
    ∀ x ∈ interval, f x = g x := by
  have hnonempty : interval.Nonempty := ⟨0, by constructor <;> norm_num⟩
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn hnonempty (hf.sub hg).abs
  have hnext := hmax (cubic_maps_interval hy)
  have heq : f y - g y = ρ * (f (cubic y) - g (cubic y)) := by
    rw [hfeq y hy, hgeq y hy]
    ring
  have hstep : |f y - g y| ≤ |ρ| * |f y - g y| := by
    calc
      _ = |ρ| * |f (cubic y) - g (cubic y)| := by rw [heq, abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hnext (abs_nonneg ρ)
  have hzero : |f y - g y| = 0 := by nlinarith [abs_nonneg (f y - g y)]
  intro x hx
  have h := hmax hx
  change |f x - g x| ≤ |f y - g y| at h
  rw [hzero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- A continuous solution is the uniformly convergent orbit series. -/
theorem eq_orbitSeries {f : ℝ → ℝ} {q : ℝ[X]} {ρ : ℝ}
    (hρ : |ρ| < 1) (hf : ContinuousOn f interval)
    (hself : ∀ x ∈ interval, f x = q.eval x + ρ * f (cubic x)) :
    ∀ x ∈ interval, f x = orbitSeries q.eval ρ x := by
  exact selfsimilar_unique hρ hf (orbitSeries_continuousOn' hρ q.continuous)
    hself (fun x hx ↦ orbitSeries_equation' hρ q.continuous hx)

/-- Subtracting a polynomial from a self-similar series changes its forcing
by the corresponding polynomial coboundary. -/
theorem series_sub_polynomial (h v : ℝ[X]) {ρ : ℝ} (hρ : |ρ| < 1) :
    ∀ x ∈ interval, orbitSeries h.eval ρ x - v.eval x =
      orbitSeries (h - v + C ρ * v.comp Lorentz.cubicPoly).eval ρ x := by
  apply eq_orbitSeries hρ
    ((orbitSeries_continuousOn' hρ h.continuous).sub v.continuous.continuousOn)
  intro x hx
  simp only [Pi.sub_apply]
  rw [orbitSeries_equation' hρ h.continuous hx]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Lorentz.eval_cubicPoly]
  ring

end Lorentz.Plateau
