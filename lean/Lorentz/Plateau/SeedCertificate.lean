module

public import Lorentz.Plateau.Families
public import Lorentz.Plateau.Reduction

@[expose] public section

/-! Converting finite signed contact tables into initial minimax plateaus. -/

namespace Lorentz.Plateau

open Polynomial Set

theorem finite_seed_certificate {N n : ℕ} (even high : Bool) (h v : ℝ[X])
    (ell : ℝ) (g : Fin N → ℝ) (sign : Fin N → ℝ)
    (hg : StrictMono g) (hinterior : ∀ j, g j ∈ Ioo (-1 : ℝ) 1)
    (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (hcontact : ∀ j, (pullback even high).eval (g j) = sign j * PolynomialBounds.a)
    (hp : contactPolynomial (pullback even high) ≠ 0)
    (hdeg : (contactPolynomial (pullback even high)).natDegree ≤ N)
    (hslack : ∀ j, sign j * (orbitSeries h.eval (-3 / 5) (g j) - v.eval (g j)) ≤ ell)
    (chosen : Fin (n + 2) → Fin N) (hchosen : StrictMono chosen)
    (initial : ℝ) (hinitial : initial = 1 ∨ initial = -1)
    (halt : ∀ j, sign (chosen j) = initial * (-1 : ℝ) ^ (j : ℕ))
    (hactive : ∀ j, sign (chosen j) *
      (orbitSeries h.eval (-3 / 5) (g (chosen j)) - v.eval (g (chosen j))) = ell)
    (hv : v.natDegree < n) (hb : (basePolynomial even high).natDegree < n) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ → HasPlateauCertificate (familyFunction even h ε) n := by
  classical
  let P := pullback even high
  let S := Finset.univ.image g
  let q := h - v + C (-3 / 5) * v.comp cubicPoly
  have hq (x : ℝ) (hx : x ∈ interval) :
      orbitSeries q.eval (-3 / 5) x = orbitSeries h.eval (-3 / 5) x - v.eval x := by
    exact (series_sub_polynomial h v (by norm_num : |(-3 : ℝ) / 5| < 1) x hx).symm
  have hgeometry := polynomial_contact_geometry P g hp hdeg hg.injective (fun j ↦ by
    rw [hcontact]
    rcases hsign j with hs | hs <;> rw [hs] <;> simp [PolynomialBounds.a_sq])
  have hcomplete : ∀ x ∈ interval, P.eval x = PolynomialBounds.a ∨
      P.eval x = -PolynomialBounds.a → x ∈ S := by
    intro x _ hx
    obtain ⟨j, rfl⟩ := hgeometry.1 x hx
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hInt : ∀ z ∈ S, z ∈ Ioo (-1 : ℝ) 1 := by
    intro z hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    exact hinterior j
  have hsimple : ∀ z ∈ S, ∃ d, HasDerivAt P.eval d z ∧ d ≠ 0 := by
    intro z hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    exact hgeometry.2 j
  have hc : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ z ∈ S,
      P.eval z = s * PolynomialBounds.a → s * orbitSeries q.eval (-3 / 5) z ≤ ell := by
    intro s _ z hz hsz
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    have heq : s = sign j := mul_right_cancel₀ PolynomialBounds.a_pos.ne'
      (hsz.symm.trans (hcontact j))
    rw [heq, hq (g j) (Ioo_subset_Icc_self (hinterior j))]
    exact hslack j
  obtain ⟨δ, hδ, hbound⟩ := finite_contact_persistence S q P.continuous.continuousOn
    (fun _ hx ↦ pullback_maps even high hx) hcomplete hInt hsimple hc
  let A := amplitude high
  have hA : 0 < A := amplitude_pos high
  refine ⟨A * δ, mul_pos hA hδ, ?_⟩
  intro ε hε hεδ
  have hediv : ε / A ≤ δ := (div_le_iff₀ hA).mpr (by nlinarith)
  obtain ⟨hE, hB⟩ := hbound (ε / A) (div_nonneg hε hA.le) hediv
  let p := basePolynomial even high + C ε * v
  let E := A * (Baseline.B + (ε / A) * ell)
  have hE' : E = A * Baseline.B + ε * ell := by dsimp [E]; field_simp
  have hbnd : HasErrorBound (familyFunction even h ε) p E := by
    intro x hx
    rw [family_residual even high h v ε hx]
    have hscaled := mul_le_mul_of_nonneg_left (hB x hx) hA.le
    rw [hq x hx] at hscaled
    change _ ≤ E at hscaled
    calc
      |A * Baseline.G (P.eval x) + ε * (orbitSeries h.eval (-3 / 5) x - v.eval x)| =
          A * |Baseline.G (P.eval x) + (ε / A) * (orbitSeries h.eval (-3 / 5) x - v.eval x)| := by
            have he : A * Baseline.G (P.eval x) + ε * (orbitSeries h.eval (-3 / 5) x - v.eval x) =
                A * (Baseline.G (P.eval x) + (ε / A) * (orbitSeries h.eval (-3 / 5) x - v.eval x)) := by
              field_simp
            rw [he, abs_mul, abs_of_pos hA]
      _ ≤ E := hscaled
  refine ⟨p, E, ?_, mul_pos hA hE, hbnd, ⟨?_⟩⟩
  · exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hb
      (lt_of_le_of_lt (natDegree_C_mul_le _ _) hv))
  refine ⟨g ∘ chosen, hg.comp hchosen, fun j ↦ hinterior (chosen j), initial, hinitial, ?_⟩
  intro j
  have hsg := hsign (chosen j)
  have hs2 : sign (chosen j) * sign (chosen j) = 1 := by
    rcases hsg with hs | hs <;> rw [hs] <;> norm_num
  have hr : orbitSeries h.eval (-3 / 5) (g (chosen j)) - v.eval (g (chosen j)) =
      sign (chosen j) * ell := by
    have hh := congrArg (fun r ↦ sign (chosen j) * r) (hactive j)
    rwa [← mul_assoc, hs2, one_mul] at hh
  rw [Function.comp_apply, family_residual even high h v ε
    (Ioo_subset_Icc_self (hinterior (chosen j))), hcontact, baseline_sign_mul hsg,
    Baseline.G_at_a, hr, hE', ← halt]
  dsimp only [A]
  ring

end Lorentz.Plateau
