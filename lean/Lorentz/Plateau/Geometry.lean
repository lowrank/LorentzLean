module

public import Lorentz.CertificateCompleteness
public import Lorentz.Plateau.ContactPersistence

@[expose] public section

/-! A full set of distinct roots certifies both completeness and simple contacts. -/

namespace Lorentz.Plateau

open Polynomial Set

theorem finite_roots_simple {N : ℕ} (p : ℝ[X]) (g : Fin N → ℝ)
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ N) (hinj : Function.Injective g)
    (heval : ∀ j, p.eval (g j) = 0) (j : Fin N) :
    p.derivative.eval (g j) ≠ 0 := by
  classical
  let s : Finset ℝ := Finset.univ.image g
  have hcard : s.card = N := by
    simp only [s, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : s ⊆ p.roots.toFinset := by
    intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    simpa only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
      using heval k
  have hnodup : p.roots.Nodup := by
    apply Multiset.toFinset_card_eq_card_iff_nodup.mp
    apply le_antisymm (Multiset.toFinset_card_le _)
    calc
      p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
      _ ≤ N := hdeg
      _ = s.card := hcard.symm
      _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
  have hcount : p.rootMultiplicity (g j) ≤ 1 := by
    rw [← Polynomial.count_roots]
    exact Multiset.nodup_iff_count_le_one.mp hnodup _
  intro hd
  have hmult := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨heval j, hd⟩
  omega

noncomputable def contactPolynomial (P : ℝ[X]) : ℝ[X] := 2 * P ^ 2 - 1

lemma contactPolynomial_eval (P : ℝ[X]) (x : ℝ) :
    (contactPolynomial P).eval x = 2 * P.eval x ^ 2 - 1 := by
  simp [contactPolynomial]

/-- Distinct contacts exhaust the root degree and therefore have nonzero derivatives. -/
theorem polynomial_contact_geometry {N : ℕ} (P : ℝ[X]) (g : Fin N → ℝ)
    (hp : contactPolynomial P ≠ 0) (hdeg : (contactPolynomial P).natDegree ≤ N)
    (hinj : Function.Injective g)
    (heval : ∀ j, P.eval (g j) ^ 2 = (1 : ℝ) / 2) :
    (∀ x, P.eval x = PolynomialBounds.a ∨ P.eval x = -PolynomialBounds.a →
      ∃ j, g j = x) ∧
    (∀ j, ∃ d, HasDerivAt P.eval d (g j) ∧ d ≠ 0) := by
  have hroot : ∀ j, (contactPolynomial P).eval (g j) = 0 := by
    intro j
    rw [contactPolynomial_eval, heval]
    norm_num
  constructor
  · intro x hx
    apply (Certificate.finite_roots_complete (contactPolynomial P) g hp hdeg hinj hroot x).mp
    rw [contactPolynomial_eval]
    rcases hx with hx | hx <;> rw [hx] <;> simp [PolynomialBounds.a_sq]
  · intro j
    refine ⟨P.derivative.eval (g j), P.hasDerivAt (g j), ?_⟩
    intro hd
    have h := finite_roots_simple (contactPolynomial P) g hp hdeg hinj hroot j
    apply h
    simp [contactPolynomial, Polynomial.derivative_mul, Polynomial.derivative_pow, hd]

end Lorentz.Plateau
