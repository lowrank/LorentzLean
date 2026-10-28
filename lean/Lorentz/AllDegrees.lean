module

public import Lorentz.Composition

@[expose] public section

/-!
# The finite-to-infinite reduction

Once degrees zero through six have bounded, vanishing alternation certificates,
a cubic self-similarity equation supplies such certificates for every degree.
This module is independent of the explicit algebraic finite certificate.
-/

open Polynomial Set

namespace Lorentz

/-- An explicit best-approximation certificate with a positive error and zero
constant coefficient. -/
def HasVanishingCertificate (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ p : ℝ[X], ∃ E : ℝ,
    p.natDegree ≤ n ∧ p.eval 0 = 0 ∧ 0 < E ∧
    HasErrorBound f p E ∧ Nonempty (Alternates f n p E)

private theorem natDegree_cubicPoly : cubicPoly.natDegree = 3 := by
  unfold cubicPoly
  compute_degree <;> norm_num

/-- The seven finite certificates imply certificates at every degree.

The induction passes from `n` to `n/3`. The pulled-back alternation has
`3*(n/3)+4` contacts, which is enough for degree `n`. -/
theorem all_degrees_of_selfsimilar
    {f : ℝ → ℝ} {q : ℝ[X]}
    (hq : q.natDegree ≤ 7) (hqzero : q.eval 0 = 0)
    (hself : ∀ x ∈ Icc (-1 : ℝ) 1, f x = q.eval x - f (cubic x) / 3)
    (hbase : ∀ n < 7, HasVanishingCertificate f n) :
    ∀ n, HasVanishingCertificate f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 7
      · exact hbase n hn
      have hn7 : 7 ≤ n := Nat.le_of_not_lt hn
      let m : ℕ := n / 3
      have hmn : m < n := by dsimp [m]; omega
      obtain ⟨p, E, hp, hpzero, hE, hbound, ⟨a⟩⟩ := ih m hmn
      let r : ℝ[X] := q + C (-1 / 3 : ℝ) * (p.comp cubicPoly)
      let E' : ℝ := (-(-1 / 3 : ℝ)) * E
      have hmnle : 3 * m ≤ n := by dsimp [m]; omega
      have hnmle : n ≤ 3 * m + 2 := by dsimp [m]; omega
      have hcomp : (p.comp cubicPoly).natDegree ≤ 3 * m := by
        calc
          (p.comp cubicPoly).natDegree ≤ p.natDegree * cubicPoly.natDegree :=
            Polynomial.natDegree_comp_le
          _ = p.natDegree * 3 := by rw [natDegree_cubicPoly]
          _ ≤ m * 3 := Nat.mul_le_mul_right 3 hp
          _ = 3 * m := Nat.mul_comm m 3
      have htrans : ∀ x ∈ Icc (-1 : ℝ) 1,
          q.eval x + (-1 / 3 : ℝ) * (f ∘ cubic) x = f x := by
        intro x hx
        rw [hself x hx]
        simp only [Function.comp_apply]
        ring
      refine ⟨r, E', ?_, ?_, ?_, ?_, ?_⟩
      · apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le (hq.trans hn7)
        exact (Polynomial.natDegree_C_mul_le _ _).trans (hcomp.trans hmnle)
      · simp [r, hqzero, Polynomial.eval_comp, hpzero, cubic_zero]
      · dsimp [E']
        positivity
      · exact (hbound.comp_cubic.affineNeg q (by norm_num : (-1 / 3 : ℝ) ≤ 0)).congrOn htrans
      · exact ⟨(((a.comp_cubic).restrict hnmle).affineNeg q (-1 / 3)).congrOn htrans⟩

/-- A vanishing alternation certificate proves that every best polynomial of
that degree vanishes at the origin. -/
theorem HasVanishingCertificate.all_best_vanish {f : ℝ → ℝ} {n : ℕ}
    (h : HasVanishingCertificate f n) :
    ∀ p : ℝ[X], IsBest f n p → p.eval 0 = 0 := by
  obtain ⟨p, E, hp, hpzero, _, hbound, ⟨a⟩⟩ := h
  exact a.all_best_vanish hp hbound hpzero

/-- The self-similarity equation and seven finite certificates establish the
origin condition for all best uniform polynomial approximations. -/
theorem all_best_vanish_of_selfsimilar
    {f : ℝ → ℝ} {q : ℝ[X]}
    (hq : q.natDegree ≤ 7) (hqzero : q.eval 0 = 0)
    (hself : ∀ x ∈ Icc (-1 : ℝ) 1, f x = q.eval x - f (cubic x) / 3)
    (hbase : ∀ n < 7, HasVanishingCertificate f n) :
    ∀ n, ∀ p : ℝ[X], IsBest f n p → p.eval 0 = 0 := by
  intro n
  exact (all_degrees_of_selfsimilar hq hqzero hself hbase n).all_best_vanish

/-- The same hypotheses also give existence of a best approximation at every
degree, without invoking any general existence theorem. -/
theorem exists_best_of_selfsimilar
    {f : ℝ → ℝ} {q : ℝ[X]}
    (hq : q.natDegree ≤ 7) (hqzero : q.eval 0 = 0)
    (hself : ∀ x ∈ Icc (-1 : ℝ) 1, f x = q.eval x - f (cubic x) / 3)
    (hbase : ∀ n < 7, HasVanishingCertificate f n) :
    ∀ n, ∃ p : ℝ[X], IsBest f n p := by
  intro n
  obtain ⟨p, E, hp, _, _, hbound, ⟨a⟩⟩ :=
    all_degrees_of_selfsimilar hq hqzero hself hbase n
  exact ⟨p, a.isBest hp hbound⟩

end Lorentz
