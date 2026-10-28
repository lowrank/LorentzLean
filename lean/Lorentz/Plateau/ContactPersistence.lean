module

public import Lorentz.Plateau.CompactDomination

@[expose] public section

/-! Finite signed contact data imply uniform persistence for the plateau baseline. -/

namespace Lorentz.Plateau

open Set Polynomial

lemma baseline_sign_mul {s : ℝ} (hs : s = 1 ∨ s = -1) (y : ℝ) :
    Baseline.G (s * y) = s * Baseline.G y := by
  rcases hs with rfl | rfl
  · simp
  · simpa only [neg_one_mul] using Baseline.G_odd y

/-- For either sign, finite contact inequalities and simple interior contacts
give a global bound relative to the signed baseline deficit. -/
theorem signed_finite_contact_bound (S : Finset ℝ) (q : ℝ[X])
    {P : ℝ → ℝ} {ell s : ℝ} (hs : s = 1 ∨ s = -1)
    (hPcont : ContinuousOn P interval) (hmap : ∀ x ∈ interval, P x ∈ interval)
    (hcomplete : ∀ x ∈ interval, P x = PolynomialBounds.a ∨
      P x = -PolynomialBounds.a → x ∈ S)
    (hinterior : ∀ z ∈ S, z ∈ Ioo (-1 : ℝ) 1)
    (hsimple : ∀ z ∈ S, ∃ d, HasDerivAt P d z ∧ d ≠ 0)
    (hcontact : ∀ z ∈ S, P z = s * PolynomialBounds.a →
      s * orbitSeries q.eval (-3 / 5) z ≤ ell) :
    ∃ C > 0, ∀ x ∈ interval,
      s * orbitSeries q.eval (-3 / 5) x ≤ ell + C * (Baseline.B - s * Baseline.G (P x)) := by
  classical
  let T : Finset ℝ := S.filter (fun z ↦ P z = s * PolynomialBounds.a)
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hmap' : ∀ x ∈ interval, s * P x ∈ interval := by
    intro x hx
    apply abs_le.mp
    rw [Stability.abs_sign_mul hs]
    exact abs_le.mpr (hmap x hx)
  have hHcont := orbitSeries_continuousOn' (ρ := (-3 : ℝ) / 5) (by norm_num) q.continuous
  have hf : ContinuousOn (fun x ↦ s * orbitSeries q.eval (-3 / 5) x - ell) interval :=
    (continuousOn_const.mul hHcont).sub continuousOn_const
  have hg : ContinuousOn (fun x ↦ Baseline.B - s * Baseline.G (P x)) interval :=
    continuousOn_const.sub (continuousOn_const.mul (Baseline.G_continuousOn.comp hPcont hmap))
  have hnonneg : ∀ x ∈ interval, 0 ≤ Baseline.B - s * Baseline.G (P x) := by
    intro x hx
    have h := (Stability.sign_mul_le_abs hs (y := Baseline.G (P x))).trans
      (Baseline.G_abs_le (hmap x hx))
    linarith
  have hpos : ∀ x ∈ interval, x ∉ T → 0 < Baseline.B - s * Baseline.G (P x) := by
    intro x hx hxT
    have hneq : s * P x ≠ PolynomialBounds.a := by
      intro h
      have heq : P x = s * PolynomialBounds.a := by
        have h' := congrArg (fun y ↦ s * y) h
        rwa [← mul_assoc, hs2, one_mul] at h'
      have hxS : x ∈ S := hcomplete x hx (by
        rcases hs with hs | hs
        · exact Or.inl (by simpa [hs] using heq)
        · exact Or.inr (by simpa [hs] using heq))
      exact hxT (Finset.mem_filter.mpr ⟨hxS, heq⟩)
    have h := Baseline.G_lt_max (hmap' x hx) hneq
    rw [baseline_sign_mul hs] at h
    linarith
  have hlocal : ∀ z ∈ T, ∃ C > 0, ∃ δ > 0, ∀ x ∈ interval, |x - z| ≤ δ →
      s * orbitSeries q.eval (-3 / 5) x - ell ≤
        C * (Baseline.B - s * Baseline.G (P x)) := by
    intro z hz
    obtain ⟨hzS, hzP⟩ := Finset.mem_filter.mp hz
    obtain ⟨d, hd, hd0⟩ := hsimple z hzS
    have hzP' : s * P z = PolynomialBounds.a := by
      rw [hzP, ← mul_assoc, hs2, one_mul]
    obtain ⟨C, hC, δ, hδ, hrelative⟩ := exists_relative_gap_bound q
      (hd.const_mul s) (mul_ne_zero hs0 hd0) (hinterior z hzS) hzP' hmap'
    refine ⟨C, hC, δ, hδ, ?_⟩
    intro x hx hnear
    have h := hrelative x hx hnear
    rw [baseline_sign_mul hs] at h
    have hsign := Stability.sign_mul_le_abs hs
      (y := orbitSeries q.eval (-3 / 5) x - orbitSeries q.eval (-3 / 5) z)
    have hc := hcontact z hzS hzP
    nlinarith
  obtain ⟨C, hC, hbound⟩ := finite_compact_domination T hf hg hnonneg hpos hlocal
  refine ⟨C, hC, ?_⟩
  intro x hx
  have h := hbound x hx
  linarith

/-- All possible extrema of a polynomial pullback are finitely certified;
their signed perturbation inequalities then persist for a positive parameter. -/
theorem finite_contact_persistence (S : Finset ℝ) (q : ℝ[X])
    {P : ℝ → ℝ} {ell : ℝ}
    (hPcont : ContinuousOn P interval) (hmap : ∀ x ∈ interval, P x ∈ interval)
    (hcomplete : ∀ x ∈ interval, P x = PolynomialBounds.a ∨
      P x = -PolynomialBounds.a → x ∈ S)
    (hinterior : ∀ z ∈ S, z ∈ Ioo (-1 : ℝ) 1)
    (hsimple : ∀ z ∈ S, ∃ d, HasDerivAt P d z ∧ d ≠ 0)
    (hcontact : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ z ∈ S,
      P z = s * PolynomialBounds.a → s * orbitSeries q.eval (-3 / 5) z ≤ ell) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      0 < Baseline.B + ε * ell ∧ ∀ x ∈ interval,
        |Baseline.G (P x) + ε * orbitSeries q.eval (-3 / 5) x| ≤ Baseline.B + ε * ell := by
  obtain ⟨Cp, hCp, hp⟩ := signed_finite_contact_bound S q (Or.inl (rfl : (1 : ℝ) = 1))
    hPcont hmap hcomplete hinterior hsimple (hcontact 1 (Or.inl rfl))
  obtain ⟨Cn, hCn, hn⟩ := signed_finite_contact_bound S q (Or.inr (rfl : (-1 : ℝ) = -1))
    hPcont hmap hcomplete hinterior hsimple (hcontact (-1) (Or.inr rfl))
  apply exists_relative_persistence_threshold Baseline.B_pos
    (hCp.trans_le (le_max_left Cp Cn)) (fun _ hx ↦ Baseline.G_abs_le (hmap _ hx))
  intro s hs x hx
  have hnonneg : 0 ≤ Baseline.B - s * Baseline.G (P x) := by
    have h := (Stability.sign_mul_le_abs hs (y := Baseline.G (P x))).trans
      (Baseline.G_abs_le (hmap x hx))
    linarith
  rcases hs with rfl | rfl
  · exact (hp x hx).trans (add_le_add_right
      (mul_le_mul_of_nonneg_right (le_max_left Cp Cn) hnonneg) ell)
  · exact (hn x hx).trans (add_le_add_right
      (mul_le_mul_of_nonneg_right (le_max_right Cp Cn) hnonneg) ell)

end Lorentz.Plateau
