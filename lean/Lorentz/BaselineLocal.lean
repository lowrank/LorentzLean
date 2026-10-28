module

public import Lorentz.Baseline
public import Lorentz.AngularSeries
public import Lorentz.LocalComposition

@[expose] public section

namespace Lorentz.Baseline

open Set

lemma exists_G_local_cusp_at_a :
    ∃ c > 0, ∃ δ > 0, ∀ x ∈ interval, |x - PolynomialBounds.a| ≤ δ →
      c * |x - PolynomialBounds.a| ≤ B - |G x| := by
  have hcos : Real.cos (Real.pi / 4) = PolynomialBounds.a :=
    Real.cos_pi_div_four
  obtain ⟨δ, hδ, c, hc, hgap⟩ := AngularSeries.exists_cubic_angular_cusp hcos
  have hgap' : ∀ u : ℝ, |u| ≤ δ → c * |u| ≤ B - G (Real.cos (Real.pi / 4 + u)) := by
    intro u hu
    rw [G_cosine_gap_series]
    exact hgap u hu
  obtain ⟨r, hr, hspatial⟩ := AngularSeries.angular_cusp_to_spatial
    (by positivity : 0 ≤ Real.pi / 4)
    (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) hδ hc.le hgap'
  rw [hcos] at hspatial
  obtain ⟨r', hr', hsign⟩ := LocalComposition.exists_local_signed_half
    (G_continuousOn _ PolynomialBounds.a_mem) (Or.inl (rfl : (1 : ℝ) = 1))
    B_pos (by simpa only [one_mul] using G_at_a)
  refine ⟨c, hc, min r r', lt_min hr hr', ?_⟩
  intro x hx hnear
  have hGpos : 0 ≤ G x := by
    have h := hsign x hx (hnear.trans (min_le_right _ _))
    simp only [one_mul] at h
    linarith [B_pos]
  rw [abs_of_nonneg hGpos]
  exact hspatial x hx (hnear.trans (min_le_left _ _))

lemma exists_G_local_cusp_at_neg_a :
    ∃ c > 0, ∃ δ > 0, ∀ x ∈ interval, |x - (-PolynomialBounds.a)| ≤ δ →
      c * |x - (-PolynomialBounds.a)| ≤ B - |G x| := by
  obtain ⟨c, hc, δ, hδ, hgap⟩ := exists_G_local_cusp_at_a
  refine ⟨c, hc, δ, hδ, ?_⟩
  intro x hx hnear
  have hdist : |-x - PolynomialBounds.a| = |x - (-PolynomialBounds.a)| := by
    rw [← abs_neg (x - (-PolynomialBounds.a))]
    congr 1
    ring
  have hxneg : -x ∈ interval := by constructor <;> linarith [hx.1, hx.2]
  have h := hgap (-x) hxneg (by rwa [hdist])
  rw [hdist, G_odd, abs_neg] at h
  exact h

lemma exists_G_local_cusp {w : ℝ}
    (hw : w = PolynomialBounds.a ∨ w = -PolynomialBounds.a) :
    ∃ c > 0, ∃ δ > 0, ∀ x ∈ interval, |x - w| ≤ δ →
      c * |x - w| ≤ B - |G x| := by
  rcases hw with rfl | rfl
  · exact exists_G_local_cusp_at_a
  · exact exists_G_local_cusp_at_neg_a

lemma cubic_hasDerivAt (x : ℝ) :
    HasDerivAt Lorentz.cubic (12 * x ^ 2 - 3) x := by
  have h := (((hasDerivAt_id x).pow 3).const_mul 4).sub
    ((hasDerivAt_id x).const_mul 3)
  convert h using 1
  · funext y
    simp only [Lorentz.cubic, Pi.sub_apply, Pi.pow_apply, id_eq]
  · simp only [id_eq]
    ring

lemma ninth_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => Lorentz.cubic (Lorentz.cubic y))
      ((12 * (Lorentz.cubic x) ^ 2 - 3) * (12 * x ^ 2 - 3)) x :=
  (cubic_hasDerivAt (Lorentz.cubic x)).comp x (cubic_hasDerivAt x)

lemma cubic_derivative_identity (x : ℝ) :
    (12 * x ^ 2 - 3) ^ 2 * (1 - x ^ 2) = 9 * (1 - (Lorentz.cubic x) ^ 2) := by
  dsimp [Lorentz.cubic]
  ring

lemma ninth_derivative_identity (x : ℝ) :
    ((12 * (Lorentz.cubic x) ^ 2 - 3) * (12 * x ^ 2 - 3)) ^ 2 * (1 - x ^ 2) =
      81 * (1 - (Lorentz.cubic (Lorentz.cubic x)) ^ 2) := by
  calc
    _ = (12 * (Lorentz.cubic x) ^ 2 - 3) ^ 2 *
        ((12 * x ^ 2 - 3) ^ 2 * (1 - x ^ 2)) := by ring
    _ = (12 * (Lorentz.cubic x) ^ 2 - 3) ^ 2 *
        (9 * (1 - (Lorentz.cubic x) ^ 2)) := by rw [cubic_derivative_identity]
    _ = 9 * ((12 * (Lorentz.cubic x) ^ 2 - 3) ^ 2 *
        (1 - (Lorentz.cubic x) ^ 2)) := by ring
    _ = _ := by rw [cubic_derivative_identity]; ring

lemma cubic_derivative_ne_zero {x : ℝ} (hx : (Lorentz.cubic x) ^ 2 = 1 / 2) :
    12 * x ^ 2 - 3 ≠ 0 := by
  intro hzero
  have h := cubic_derivative_identity x
  rw [hzero, hx] at h
  norm_num at h

lemma ninth_derivative_ne_zero {x : ℝ}
    (hx : (Lorentz.cubic (Lorentz.cubic x)) ^ 2 = 1 / 2) :
    (12 * (Lorentz.cubic x) ^ 2 - 3) * (12 * x ^ 2 - 3) ≠ 0 := by
  intro hzero
  have h := ninth_derivative_identity x
  rw [hzero, hx] at h
  norm_num at h

lemma square_half_iff (x : ℝ) :
    x ^ 2 = (1 : ℝ) / 2 ↔ x = PolynomialBounds.a ∨ x = -PolynomialBounds.a := by
  rw [← PolynomialBounds.a_sq, sq_eq_sq_iff_eq_or_eq_neg]

lemma exists_G_cubic_local_cusp {x : ℝ}
    (hx : (Lorentz.cubic x) ^ 2 = 1 / 2) :
    ∃ c > 0, ∃ δ > 0, ∀ y ∈ interval, |y - x| ≤ δ →
      c * |y - x| ≤ B - |G (Lorentz.cubic y)| := by
  obtain ⟨c, hc, δ, hδ, hgap⟩ := exists_G_local_cusp ((square_half_iff _).mp hx)
  exact LocalComposition.local_abs_cusp_comp
    (cubic_hasDerivAt x) (cubic_derivative_ne_zero hx) rfl
    (fun _ hy => cubic_maps_interval hy) hc hδ hgap

lemma exists_G_ninth_local_cusp {x : ℝ}
    (hx : (Lorentz.cubic (Lorentz.cubic x)) ^ 2 = 1 / 2) :
    ∃ c > 0, ∃ δ > 0, ∀ y ∈ interval, |y - x| ≤ δ →
      c * |y - x| ≤ B - |G (Lorentz.cubic (Lorentz.cubic y))| := by
  obtain ⟨c, hc, δ, hδ, hgap⟩ := exists_G_local_cusp ((square_half_iff _).mp hx)
  exact LocalComposition.local_abs_cusp_comp
    (ninth_hasDerivAt x) (ninth_derivative_ne_zero hx) rfl
    (fun _ hy => cubic_maps_interval (cubic_maps_interval hy)) hc hδ hgap

end Lorentz.Baseline
