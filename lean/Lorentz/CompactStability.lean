module

public import Lorentz.Stability
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Real

@[expose] public section

/-!
# Compact patching of local contact estimates

Local linear gaps at the contacts suffice.  On the compact set outside fixed
contact neighborhoods, strict inequality gives a uniform positive gap.  The
diameter bound for `[-1,1]` then supplies the global witness inequality used in
`Stability.lean`.  This removes the need for an explicit global cusp constant.
-/

namespace Lorentz
namespace Stability

open Set

/-- Local sharpness at every possible extremum of a continuous function
extends to a global witness-gap inequality on the unit interval. -/
theorem local_gap_has_global_witness
    {S : Set ℝ} {b : ℝ → ℝ} {E c δ : ℝ}
    (hS : S.Nonempty) (hSsub : S ⊆ Icc (-1 : ℝ) 1)
    (hb : ContinuousOn b (Icc (-1 : ℝ) 1))
    (hc : 0 < c) (hδ : 0 < δ)
    (hstrict : ∀ x ∈ Icc (-1 : ℝ) 1, x ∉ S → |b x| < E)
    (hlocal : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ z ∈ S, |x - z| ≤ δ →
      c * |x - z| ≤ E - |b x|) :
    ∃ c' > 0, ∀ x ∈ Icc (-1 : ℝ) 1,
      ∃ z ∈ S, c' * |x - z| ≤ E - |b x| := by
  let A : Set ℝ := Icc (-1 : ℝ) 1 ∩ {x | ∀ z ∈ S, δ ≤ |x - z|}
  have hclosed : IsClosed {x : ℝ | ∀ z ∈ S, δ ≤ |x - z|} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun z => isClosed_iInter (fun _hz =>
      isClosed_le continuous_const (continuous_id.sub continuous_const).abs))
  have hcompact : IsCompact A := isCompact_Icc.inter_right hclosed
  have hpos : ∀ x ∈ A, 0 < E - |b x| := by
    intro x hx
    have hxnot : x ∉ S := by
      intro hxS
      have h := hx.2 x hxS
      simp only [sub_self, abs_zero] at h
      linarith
    exact sub_pos.mpr (hstrict x hx.1 hxnot)
  have hgap : ∃ η > 0, ∀ x ∈ A, η ≤ E - |b x| := by
    by_cases hA : A.Nonempty
    · have hcont : ContinuousOn (fun x => E - |b x|) A :=
        (continuousOn_const.sub hb.abs).mono (fun _ hx => hx.1)
      obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hA hcont
      exact ⟨E - |b y|, hpos y hy, hmin⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro x hx
      exact False.elim (hA ⟨x, hx⟩)
  obtain ⟨η, hη, hηbound⟩ := hgap
  let c' : ℝ := min c (η / 2)
  have hc' : 0 < c' := lt_min hc (by positivity)
  refine ⟨c', hc', ?_⟩
  intro x hx
  by_cases hnear : ∃ z ∈ S, |x - z| ≤ δ
  · obtain ⟨z, hz, hdist⟩ := hnear
    refine ⟨z, hz, ?_⟩
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)).trans
      (hlocal x hx z hz hdist)
  · obtain ⟨z, hz⟩ := hS
    refine ⟨z, hz, ?_⟩
    have hxA : x ∈ A := by
      refine ⟨hx, ?_⟩
      intro w hw
      exact le_of_lt (lt_of_not_ge (fun h => hnear ⟨w, hw, h⟩))
    have hdist : |x - z| ≤ 2 := by
      have hzI := hSsub hz
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2, hzI.1, hzI.2]
    have hmul := mul_le_mul_of_nonneg_left hdist hc'.le
    have hcle : c' ≤ η / 2 := min_le_right _ _
    have hηx := hηbound x hxA
    nlinarith

/-- A continuous perturbation of a compact residual with uniformly sharp
contacts preserves every finite signed contact certificate for sufficiently
small nonnegative amplitudes.  All analytic assumptions concern the base
residual and the perturbation separately. -/
theorem compact_contact_persistence
    {S : Set ℝ} {b r σ : ℝ → ℝ} {E c δ L ell : ℝ}
    (hS : S.Nonempty) (hSsub : S ⊆ Icc (-1 : ℝ) 1)
    (hb : ContinuousOn b (Icc (-1 : ℝ) 1))
    (hr : ContinuousOn r (Icc (-1 : ℝ) 1))
    (hE : 0 < E) (hc : 0 < c) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hsign : ∀ z ∈ S, σ z = 1 ∨ σ z = -1)
    (hstrict : ∀ x ∈ Icc (-1 : ℝ) 1, x ∉ S → |b x| < E)
    (hlocal : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ z ∈ S, |x - z| ≤ δ →
      c * |x - z| ≤ E - |b x| ∧ E / 2 ≤ σ z * b x ∧
        |r x - r z| ≤ L * |x - z|)
    (hcontact : ∀ z ∈ S, σ z * r z ≤ ell) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      0 < E + ε * ell ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
        |b x + ε * r x| ≤ E + ε * ell := by
  obtain ⟨c', hc', hcover⟩ := local_gap_has_global_witness hS hSsub hb hc hδ hstrict
    (fun x hx z hz hdist => (hlocal x hx z hz hdist).1)
  obtain ⟨R₀, hR₀bound⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    (f := r) hr
  let R : ℝ := max R₀ (|ell| + 1)
  have hR : 0 ≤ R := by
    have h := le_max_right R₀ (|ell| + 1)
    have ha := abs_nonneg ell
    dsimp [R]
    linarith
  have hell : |ell| ≤ R := by
    have h := le_max_right R₀ (|ell| + 1)
    dsimp [R]
    linarith
  have hrbound : ∀ x ∈ Icc (-1 : ℝ) 1, |r x| ≤ R := by
    intro x hx
    have h := hR₀bound x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  exact exists_contact_persistence_threshold hE le_rfl hc' hδ hL hR hell
    hsign hcover
    (fun x hx z hz hdist => (hlocal x hx z hz hdist).2)
    hcontact hrbound

/-- Finitely many local contact estimates can be made uniform by taking
minimum radii and gap constants and a maximum Lipschitz constant. -/
theorem uniformize_finite_local_bounds
    (S : Finset ℝ) {b r σ : ℝ → ℝ} {E : ℝ}
    (hlocal : ∀ z ∈ S, ∃ c > 0, ∃ δ > 0, ∃ L ≥ 0,
      ∀ x ∈ Icc (-1 : ℝ) 1, |x - z| ≤ δ →
        c * |x - z| ≤ E - |b x| ∧ E / 2 ≤ σ z * b x ∧
          |r x - r z| ≤ L * |x - z|) :
    ∃ c > 0, ∃ δ > 0, ∃ L ≥ 0,
      ∀ x ∈ Icc (-1 : ℝ) 1, ∀ z ∈ S, |x - z| ≤ δ →
        c * |x - z| ≤ E - |b x| ∧ E / 2 ≤ σ z * b x ∧
          |r x - r z| ≤ L * |x - z| := by
  classical
  revert hlocal
  induction S using Finset.induction_on with
  | empty =>
      intro _hlocal
      refine ⟨1, by norm_num, 1, by norm_num, 0, le_rfl, ?_⟩
      simp
  | @insert z S hz ih =>
      intro hlocal
      obtain ⟨cz, hcz, δz, hδz, Lz, hLz, hlocz⟩ :=
        hlocal z (Finset.mem_insert_self _ _)
      obtain ⟨cS, hcS, δS, hδS, LS, hLS, hlocS⟩ :=
        ih (fun w hw => hlocal w (Finset.mem_insert_of_mem hw))
      refine ⟨min cz cS, lt_min hcz hcS, min δz δS, lt_min hδz hδS,
        max Lz LS, hLz.trans (le_max_left _ _), ?_⟩
      intro x hx w hw hdist
      rcases Finset.mem_insert.mp hw with rfl | hw
      · obtain ⟨hgap, hsign, hlip⟩ := hlocz x hx (hdist.trans (min_le_left _ _))
        exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)).trans hgap,
          hsign, hlip.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))⟩
      · obtain ⟨hgap, hsign, hlip⟩ := hlocS x hx w hw (hdist.trans (min_le_right _ _))
        exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)).trans hgap,
          hsign, hlip.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))⟩

/-- The version requiring only individual local estimates at finitely many
contacts.  This is the qualitative persistence theorem used by the explicit
construction. -/
theorem finite_compact_contact_persistence
    (S : Finset ℝ) {b r σ : ℝ → ℝ} {E ell : ℝ}
    (hS : S.Nonempty)
    (hSsub : ∀ z ∈ S, z ∈ Icc (-1 : ℝ) 1)
    (hb : ContinuousOn b (Icc (-1 : ℝ) 1))
    (hr : ContinuousOn r (Icc (-1 : ℝ) 1))
    (hE : 0 < E)
    (hsign : ∀ z ∈ S, σ z = 1 ∨ σ z = -1)
    (hstrict : ∀ x ∈ Icc (-1 : ℝ) 1, x ∉ S → |b x| < E)
    (hlocal : ∀ z ∈ S, ∃ c > 0, ∃ δ > 0, ∃ L ≥ 0,
      ∀ x ∈ Icc (-1 : ℝ) 1, |x - z| ≤ δ →
        c * |x - z| ≤ E - |b x| ∧ E / 2 ≤ σ z * b x ∧
          |r x - r z| ≤ L * |x - z|)
    (hcontact : ∀ z ∈ S, σ z * r z ≤ ell) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      0 < E + ε * ell ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
        |b x + ε * r x| ≤ E + ε * ell := by
  obtain ⟨c, hc, δ, hδ, L, hL, hloc⟩ := uniformize_finite_local_bounds S hlocal
  exact compact_contact_persistence (S := (S : Set ℝ)) hS hSsub hb hr hE hc hδ hL
    hsign hstrict hloc hcontact

end Stability
end Lorentz
