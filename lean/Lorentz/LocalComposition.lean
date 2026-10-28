module

public import Mathlib

@[expose] public section

/-!
# Local contact estimates under composition

A nonzero derivative supplies a local lower bound for displacement. Any finite
derivative supplies a local upper bound. These transfer sharp residual cusps
and pointwise Lipschitz estimates to the preimages of a contact.
-/

namespace Lorentz
namespace LocalComposition

open Filter Set
open scoped Topology

/-- A derivative provides a local upper bound for displacement from its base
point. The bound is only relative to that point; no neighborhood-wide
Lipschitz assertion is made. -/
theorem exists_local_lipschitz_of_hasDerivAt
    {P : ℝ → ℝ} {d z : ℝ} (hP : HasDerivAt P d z) :
    ∃ L > 0, ∃ δ > 0, ∀ x : ℝ, |x - z| ≤ δ →
      |P x - P z| ≤ L * |x - z| := by
  obtain ⟨L, hL, hbound⟩ := hP.isBigO_sub.exists_pos
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  refine ⟨L, hL, δ / 2, by positivity, ?_⟩
  intro x hx
  have hx' : dist x z < δ := by rw [Real.dist_eq]; linarith
  simpa only [Real.norm_eq_abs] using hnear hx'

/-- A nonzero derivative provides a local lower bound for displacement from
its base point. -/
theorem exists_local_lower_of_hasDerivAt
    {P : ℝ → ℝ} {d z : ℝ} (hP : HasDerivAt P d z) (hd : d ≠ 0) :
    ∃ c > 0, ∃ δ > 0, ∀ x : ℝ, |x - z| ≤ δ →
      c * |x - z| ≤ |P x - P z| := by
  obtain ⟨C, hC, hbound⟩ := ((hP.isTheta_sub hd).isBigO_symm.comp_tendsto
    (tendsto_id.prodMk tendsto_const_pure)).exists_pos
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  refine ⟨1 / C, by positivity, δ / 2, by positivity, ?_⟩
  intro x hx
  have hx' : dist x z < δ := by rw [Real.dist_eq]; linarith
  have h : |x - z| ≤ C * |P x - P z| := by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs] using hnear hx'
  have h' : |x - z| / C ≤ |P x - P z| :=
    (div_le_iff₀ hC).mpr (by nlinarith)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h'

/-- Pulling back a local absolute cusp through a differentiable map with
nonzero derivative preserves a local absolute cusp. -/
theorem local_abs_cusp_comp
    {F P : ℝ → ℝ} {E a z c δ d : ℝ}
    (hP : HasDerivAt P d z) (hd : d ≠ 0) (hPa : P z = a)
    (hmap : ∀ x ∈ Icc (-1 : ℝ) 1, P x ∈ Icc (-1 : ℝ) 1)
    (hc : 0 < c) (hδ : 0 < δ)
    (hgap : ∀ y ∈ Icc (-1 : ℝ) 1, |y - a| ≤ δ →
      c * |y - a| ≤ E - |F y|) :
    ∃ c' > 0, ∃ δ' > 0, ∀ x ∈ Icc (-1 : ℝ) 1, |x - z| ≤ δ' →
      c' * |x - z| ≤ E - |F (P x)| := by
  obtain ⟨k, hk, δk, hδk, hlower⟩ := exists_local_lower_of_hasDerivAt hP hd
  obtain ⟨L, hL, δL, hδL, hupper⟩ := exists_local_lipschitz_of_hasDerivAt hP
  refine ⟨c * k, mul_pos hc hk, min δk (min δL (δ / L)),
    lt_min hδk (lt_min hδL (div_pos hδ hL)), ?_⟩
  intro x hx hdist
  have hdistk : |x - z| ≤ δk := hdist.trans (min_le_left _ _)
  have hdistL : |x - z| ≤ δL :=
    hdist.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdistδ : |x - z| ≤ δ / L :=
    hdist.trans ((min_le_right _ _).trans (min_le_right _ _))
  have himage : |P x - a| ≤ δ := by
    rw [← hPa]
    have h := (le_div_iff₀ hL).mp hdistδ
    exact (hupper x hdistL).trans (by nlinarith)
  have hlow := mul_le_mul_of_nonneg_left (hlower x hdistk) hc.le
  rw [hPa] at hlow
  have h := hgap (P x) (hmap x hx) himage
  calc
    (c * k) * |x - z| = c * (k * |x - z|) := by ring
    _ ≤ c * |P x - a| := hlow
    _ ≤ E - |F (P x)| := h

/-- Pulling back a pointwise Lipschitz estimate only requires a finite
derivative of the inner map, not a nonzero derivative. -/
theorem local_lipschitz_comp
    {H P : ℝ → ℝ} {a z L δ d : ℝ}
    (hP : HasDerivAt P d z) (hPa : P z = a)
    (hmap : ∀ x ∈ Icc (-1 : ℝ) 1, P x ∈ Icc (-1 : ℝ) 1)
    (hL : 0 ≤ L) (hδ : 0 < δ)
    (hlip : ∀ y ∈ Icc (-1 : ℝ) 1, |y - a| ≤ δ →
      |H y - H a| ≤ L * |y - a|) :
    ∃ L' ≥ 0, ∃ δ' > 0, ∀ x ∈ Icc (-1 : ℝ) 1, |x - z| ≤ δ' →
      |H (P x) - H (P z)| ≤ L' * |x - z| := by
  obtain ⟨K, hK, δK, hδK, hupper⟩ := exists_local_lipschitz_of_hasDerivAt hP
  refine ⟨L * K, mul_nonneg hL hK.le, min δK (δ / K),
    lt_min hδK (div_pos hδ hK), ?_⟩
  intro x hx hdist
  have hdistK : |x - z| ≤ δK := hdist.trans (min_le_left _ _)
  have hdistδ : |x - z| ≤ δ / K := hdist.trans (min_le_right _ _)
  have himage : |P x - a| ≤ δ := by
    rw [← hPa]
    have h := (le_div_iff₀ hK).mp hdistδ
    exact (hupper x hdistK).trans (by nlinarith)
  rw [hPa]
  calc
    |H (P x) - H a| ≤ L * |P x - a| := hlip (P x) (hmap x hx) himage
    _ = L * |P x - P z| := by rw [hPa]
    _ ≤ L * (K * |x - z|) := mul_le_mul_of_nonneg_left (hupper x hdistK) hL
    _ = (L * K) * |x - z| := by ring

/-- Nonzero scalar multiplication preserves a local absolute cusp. -/
theorem local_abs_cusp_mul
    {F : ℝ → ℝ} {E z c δ ρ : ℝ}
    (hρ : ρ ≠ 0) (hc : 0 < c)
    (hgap : ∀ x ∈ Icc (-1 : ℝ) 1, |x - z| ≤ δ →
      c * |x - z| ≤ E - |F x|) :
    0 < |ρ| * c ∧ ∀ x ∈ Icc (-1 : ℝ) 1, |x - z| ≤ δ →
      (|ρ| * c) * |x - z| ≤ |ρ| * E - |ρ * F x| := by
  refine ⟨mul_pos (abs_pos.mpr hρ) hc, ?_⟩
  intro x hx hdist
  have h := mul_le_mul_of_nonneg_left (hgap x hx hdist) (abs_nonneg ρ)
  rw [abs_mul]
  nlinarith

/-- Adding a differentiable function and multiplying a pointwise Lipschitz
function by a scalar preserves a pointwise Lipschitz estimate. -/
theorem local_lipschitz_affine
    {H S : ℝ → ℝ} {z L δ ρ d : ℝ}
    (hS : HasDerivAt S d z) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hlip : ∀ x ∈ Icc (-1 : ℝ) 1, |x - z| ≤ δ →
      |H x - H z| ≤ L * |x - z|) :
    ∃ L' ≥ 0, ∃ δ' > 0, ∀ x ∈ Icc (-1 : ℝ) 1, |x - z| ≤ δ' →
      |(S x + ρ * H x) - (S z + ρ * H z)| ≤ L' * |x - z| := by
  obtain ⟨K, hK, δK, hδK, hupper⟩ := exists_local_lipschitz_of_hasDerivAt hS
  refine ⟨K + |ρ| * L, add_nonneg hK.le (mul_nonneg (abs_nonneg ρ) hL),
    min δ δK, lt_min hδ hδK, ?_⟩
  intro x hx hdist
  have hdistδ := hdist.trans (min_le_left δ δK)
  have hdistK := hdist.trans (min_le_right δ δK)
  have heq : (S x + ρ * H x) - (S z + ρ * H z) =
      (S x - S z) + ρ * (H x - H z) := by ring
  rw [heq]
  calc
    |(S x - S z) + ρ * (H x - H z)| ≤ |S x - S z| + |ρ * (H x - H z)| :=
      abs_add_le _ _
    _ = |S x - S z| + |ρ| * |H x - H z| := by rw [abs_mul]
    _ ≤ K * |x - z| + |ρ| * (L * |x - z|) :=
      add_le_add (hupper x hdistK)
        (mul_le_mul_of_nonneg_left (hlip x hx hdistδ) (abs_nonneg ρ))
    _ = (K + |ρ| * L) * |x - z| := by ring

/-- A positive signed contact of a continuous residual stays above half its
contact magnitude in a sufficiently small relative neighborhood. -/
theorem exists_local_signed_half
    {b : ℝ → ℝ} {z s E : ℝ}
    (hb : ContinuousWithinAt b (Icc (-1 : ℝ) 1) z)
    (hs : s = 1 ∨ s = -1) (hE : 0 < E) (hcontact : s * b z = E) :
    ∃ δ > 0, ∀ x ∈ Icc (-1 : ℝ) 1, |x - z| ≤ δ → E / 2 ≤ s * b x := by
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousWithinAt_iff.mp hb (E / 2) (by positivity)
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x hx hdist
  have hx' : dist x z < δ := by rw [Real.dist_eq]; linarith
  have hdiff : |b x - b z| < E / 2 := by
    simpa only [Real.dist_eq] using hnear hx hx'
  have hlo := (abs_lt.mp hdiff).1
  have hhi := (abs_lt.mp hdiff).2
  rcases hs with rfl | rfl <;> norm_num at hcontact ⊢ <;> linarith

end LocalComposition
end Lorentz
