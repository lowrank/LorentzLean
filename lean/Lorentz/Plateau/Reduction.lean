module

public import Lorentz.Composition

@[expose] public section

/-! Cubic self-similarity propagates the two consecutive-degree plateau patterns. -/

open Polynomial Set

namespace Lorentz.Plateau

/-- A degree-`n` alternation certificate whose polynomial has degree strictly
below `n`. It certifies the same minimizer at degrees `n-1` and `n`. -/
def HasPlateauCertificate (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ p : ℝ[X], ∃ E : ℝ, p.natDegree < n ∧ 0 < E ∧
    HasErrorBound f p E ∧ Nonempty (Alternates f n p E)

theorem HasPlateauCertificate.best_pair {f : ℝ → ℝ} {n : ℕ}
    (h : HasPlateauCertificate f n) :
    ∃ p : ℝ[X], IsBest f (n - 1) p ∧ IsBest f n p ∧
      ∀ q r : ℝ[X], IsBest f (n - 1) q → IsBest f n r → q = r := by
  obtain ⟨p, E, hp, _, hb, ⟨a⟩⟩ := h
  have hp' : p.natDegree ≤ n - 1 := by omega
  have b := a.restrict (Nat.sub_le n 1)
  refine ⟨p, b.isBest hp' hb, a.isBest hp.le hb, ?_⟩
  intro q r hq hr
  exact (b.eq_of_isBest hp' hb hq).trans (a.eq_of_isBest hp.le hb hr).symm

private theorem cubic_degree : cubicPoly.natDegree = 3 := by
  unfold cubicPoly
  compute_degree <;> norm_num

/-- A stronger alternation at a lower degree supplies the next plateau. -/
theorem HasPlateauCertificate.lift {f : ℝ → ℝ} {q : ℝ[X]} {ρ : ℝ} {m n : ℕ}
    (h : HasPlateauCertificate f m) (hρ : ρ < 0)
    (hself : ∀ x ∈ interval, f x = q.eval x + ρ * f (cubic x))
    (hq : q.natDegree < n) (hdegree : 3 * (m - 1) < n) (hn : n ≤ 3 * m + 2) :
    HasPlateauCertificate f n := by
  obtain ⟨p, E, hp, hE, hb, ⟨a⟩⟩ := h
  have hcomp : (p.comp cubicPoly).natDegree < n := by
    have h := Polynomial.natDegree_comp_le (p := p) (q := cubicPoly)
    rw [cubic_degree] at h
    omega
  have htrans : ∀ x ∈ interval, q.eval x + ρ * (f ∘ cubic) x = f x :=
    fun x hx ↦ (hself x hx).symm
  refine ⟨q + C ρ * (p.comp cubicPoly), (-ρ) * E, ?_,
    mul_pos (neg_pos.mpr hρ) hE, ?_, ?_⟩
  · exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
      (max_lt hq (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hcomp))
  · exact (hb.comp_cubic.affineNeg q hρ.le).congrOn htrans
  · exact ⟨(((a.comp_cubic).restrict hn).affineNeg q ρ).congrOn htrans⟩

/-- An initial block of one parity suffices for every plateau of that parity.
The parity refers to the higher degree in the consecutive pair. -/
theorem all_plateaus_of_selfsimilar
    {f : ℝ → ℝ} {q : ℝ[X]} {ρ : ℝ} {cut parity : ℕ}
    (hcut : 4 ≤ cut) (hq : q.natDegree < cut) (hρ : ρ < 0)
    (hself : ∀ x ∈ interval, f x = q.eval x + ρ * f (cubic x))
    (hbase : ∀ n, 0 < n → n < cut → n % 2 = parity → HasPlateauCertificate f n) :
    ∀ n, 0 < n → n % 2 = parity → HasPlateauCertificate f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hpar
    by_cases hsmall : n < cut
    · exact hbase n hn hsmall hpar
    let k := if n / 3 % 2 = n % 2 then n / 3 else n / 3 + 1
    have hkpos : 0 < k := by dsimp [k]; split_ifs <;> omega
    have hklt : k < n := by dsimp [k]; split_ifs <;> omega
    have hkpar : k % 2 = parity := by dsimp [k]; split_ifs <;> omega
    have hkdegree : 3 * (k - 1) < n := by dsimp [k]; split_ifs <;> omega
    have hknodes : n ≤ 3 * k + 2 := by dsimp [k]; split_ifs <;> omega
    exact (ih k hklt hkpos hkpar).lift hρ hself (by omega) hkdegree hknodes

end Lorentz.Plateau
