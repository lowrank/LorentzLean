module

public import Lorentz.Plateau.RelativeGap
public import Lorentz.Stability

@[expose] public section

/-! Compact globalization of bounds relative to a nonnegative baseline deficit. -/

namespace Lorentz.Plateau

open Set

lemma uniformize_finite_domination (S : Finset ℝ) {f g : ℝ → ℝ}
    (hg : ∀ x ∈ interval, 0 ≤ g x)
    (hlocal : ∀ z ∈ S, ∃ C > 0, ∃ δ > 0,
      ∀ x ∈ interval, |x - z| ≤ δ → f x ≤ C * g x) :
    ∃ C > 0, ∃ δ > 0, ∀ x ∈ interval, ∀ z ∈ S,
      |x - z| ≤ δ → f x ≤ C * g x := by
  classical
  revert hlocal
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
      simp
  | @insert z S hz ih =>
      intro hlocal
      obtain ⟨Cz, hCz, δz, hδz, hzbound⟩ := hlocal z (Finset.mem_insert_self _ _)
      obtain ⟨CS, hCS, δS, hδS, hSbound⟩ :=
        ih (fun w hw ↦ hlocal w (Finset.mem_insert_of_mem hw))
      refine ⟨max Cz CS, hCz.trans_le (le_max_left _ _), min δz δS, lt_min hδz hδS, ?_⟩
      intro x hx w hw hdist
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (hzbound x hx (hdist.trans (min_le_left _ _))).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (hg x hx))
      · exact (hSbound x hx w hw (hdist.trans (min_le_right _ _))).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (hg x hx))

/-- Local domination at every possible zero of a continuous nonnegative
function extends over the compact approximation interval. -/
theorem finite_compact_domination (S : Finset ℝ) {f g : ℝ → ℝ}
    (hf : ContinuousOn f interval) (hg : ContinuousOn g interval)
    (hgnonneg : ∀ x ∈ interval, 0 ≤ g x)
    (hgpos : ∀ x ∈ interval, x ∉ S → 0 < g x)
    (hlocal : ∀ z ∈ S, ∃ C > 0, ∃ δ > 0,
      ∀ x ∈ interval, |x - z| ≤ δ → f x ≤ C * g x) :
    ∃ C > 0, ∀ x ∈ interval, f x ≤ C * g x := by
  obtain ⟨L, hL, δ, hδ, hloc⟩ := uniformize_finite_domination S hgnonneg hlocal
  let A : Set ℝ := interval ∩ {x | ∀ z ∈ S, δ ≤ |x - z|}
  have hclosed : IsClosed {x : ℝ | ∀ z ∈ S, δ ≤ |x - z|} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun z ↦ isClosed_iInter (fun _ ↦
      isClosed_le continuous_const (continuous_id.sub continuous_const).abs))
  have hcompact : IsCompact A := isCompact_Icc.inter_right hclosed
  have hpos : ∀ x ∈ A, 0 < g x := by
    intro x hx
    apply hgpos x hx.1
    intro hxS
    have h := hx.2 x hxS
    simp only [sub_self, abs_zero] at h
    linarith
  obtain ⟨η, hη, hηbound⟩ : ∃ η > 0, ∀ x ∈ A, η ≤ g x := by
    by_cases hA : A.Nonempty
    · obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hA (hg.mono (fun _ hx ↦ hx.1))
      exact ⟨g y, hpos y hy, hmin⟩
    · exact ⟨1, by norm_num, fun x hx ↦ False.elim (hA ⟨x, hx⟩)⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact interval).exists_bound_of_continuousOn
    (f := f) hf
  let R : ℝ := max M 0 + 1
  have hR : 0 < R := by dsimp [R]; have := le_max_right M 0; linarith
  have hfR : ∀ x ∈ interval, f x ≤ R := by
    intro x hx
    have h := hM x hx
    rw [Real.norm_eq_abs] at h
    dsimp [R]
    have hmax := le_max_left M 0
    linarith [le_abs_self (f x)]
  refine ⟨max L (R / η), hL.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  by_cases hnear : ∃ z ∈ S, |x - z| ≤ δ
  · obtain ⟨z, hz, hdist⟩ := hnear
    exact (hloc x hx z hz hdist).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hgnonneg x hx))
  · have hxA : x ∈ A := by
      refine ⟨hx, ?_⟩
      intro z hz
      exact le_of_lt (lt_of_not_ge (fun h ↦ hnear ⟨z, hz, h⟩))
    calc
      f x ≤ R := hfR x hx
      _ = (R / η) * η := (div_mul_cancel₀ R hη.ne').symm
      _ ≤ (R / η) * g x := mul_le_mul_of_nonneg_left (hηbound x hxA) (div_pos hR hη).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (hgnonneg x hx)

/-- A signed relative bound preserves the signed residual under the single
smallness condition `ε*C ≤ 1`. -/
theorem signed_relative_persistence {s b r E ell C ε : ℝ}
    (hgap : 0 ≤ E - s * b) (hr : s * r ≤ ell + C * (E - s * b))
    (hε : 0 ≤ ε) (hsmall : ε * C ≤ 1) :
    s * (b + ε * r) ≤ E + ε * ell := by
  have h1 := mul_le_mul_of_nonneg_left hr hε
  have h2 := mul_le_mul_of_nonneg_right hsmall hgap
  nlinarith

/-- Relative bounds for both signs give a positive uniform-error threshold. -/
theorem exists_relative_persistence_threshold {b r : ℝ → ℝ} {E ell C : ℝ}
    (hE : 0 < E) (hC : 0 < C)
    (hb : ∀ x ∈ interval, |b x| ≤ E)
    (hr : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ x ∈ interval,
      s * r x ≤ ell + C * (E - s * b x)) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      0 < E + ε * ell ∧ ∀ x ∈ interval, |b x + ε * r x| ≤ E + ε * ell := by
  refine ⟨min (1 / C) (E / (2 * (|ell| + 1))),
    lt_min (by positivity) (by positivity), ?_⟩
  intro ε hε hsmall
  have hεC : ε * C ≤ 1 :=
    (le_div_iff₀ hC).mp (hsmall.trans (min_le_left _ _))
  have hεE : ε * (2 * (|ell| + 1)) ≤ E :=
    (le_div_iff₀ (by positivity)).mp (hsmall.trans (min_le_right _ _))
  have hell : -ε * |ell| ≤ ε * ell := by
    have h := mul_le_mul_of_nonneg_left (neg_abs_le ell) hε
    nlinarith
  refine ⟨by nlinarith, ?_⟩
  intro x hx
  have hbx := abs_le.mp (hb x hx)
  have hp := signed_relative_persistence (s := 1) (by simpa using hbx.2)
    (hr 1 (Or.inl rfl) x hx) hε hεC
  have hn := signed_relative_persistence (s := -1) (by nlinarith [hbx.1])
    (hr (-1) (Or.inr rfl) x hx) hε hεC
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end Lorentz.Plateau
