module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Uniform polynomial approximation and alternation

The definitions use pointwise error bounds, so no existence theorem for a best
approximation is required.  The weak alternation lemma includes zero values;
this is the fact needed for uniqueness, not merely for optimality.
-/

open Polynomial Set

namespace Lorentz

/-- A polynomial has uniform error at most `E` on the closed unit interval. -/
def HasErrorBound (f : ℝ → ℝ) (p : ℝ[X]) (E : ℝ) : Prop :=
  ∀ x ∈ Icc (-1 : ℝ) 1, |f x - p.eval x| ≤ E

/-- `p` is a best approximation among all real polynomials of degree at most `n`.

Every error bound achieved by a competitor is also achieved by `p`. -/
def IsBest (f : ℝ → ℝ) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧
    ∀ q : ℝ[X], q.natDegree ≤ n → ∀ E : ℝ,
      HasErrorBound f q E → HasErrorBound f p E

/-- Interior alternation data for an explicit polynomial.  Interior nodes are
convenient for subsequent lifting through the three branches of `T₃`. -/
structure Alternates (f : ℝ → ℝ) (n : ℕ) (p : ℝ[X]) (E : ℝ) where
  nodes : Fin (n + 2) → ℝ
  strictMono : StrictMono nodes
  interior : ∀ i, nodes i ∈ Ioo (-1 : ℝ) 1
  initialSign : ℝ
  initialSign_eq : initialSign = 1 ∨ initialSign = -1
  error_eq : ∀ i, f (nodes i) - p.eval (nodes i) =
    initialSign * (-1 : ℝ) ^ (i : ℕ) * E

private def skipSecond {n : ℕ} (i : Fin (n + 2)) : Fin (n + 3) :=
  if i = 0 then 0 else i.succ

private theorem strictMono_skipSecond (n : ℕ) :
    StrictMono (@skipSecond n) := by
  intro i j hij
  by_cases hi : i = 0
  · have hj : j ≠ 0 := by
      intro hj
      simp [hi, hj] at hij
    simp only [skipSecond, hi, hj, if_true, if_false]
    change (0 : ℕ) < j.val + 1
    omega
  · have hj : j ≠ 0 := by
      intro hj
      subst j
      exact (not_lt_of_ge (Fin.zero_le i)) hij
    simpa only [skipSecond, hi, hj, if_false] using (Fin.strictMono_succ hij)

/-- A polynomial of degree at most `n` with weak alternating signs at `n+2`
strictly increasing real nodes is zero.

The induction divides out one real root.  If the first node is a root it is
removed; otherwise the intermediate value theorem gives a root between the
first two nodes and the second node is removed.  In both cases the quotient,
with its sign reversed, has one fewer degree and one fewer alternation node. -/
theorem polynomial_eq_zero_of_weak_alternation (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) (x : Fin (n + 2) → ℝ)
    (hx : StrictMono x)
    (hs : ∀ i : Fin (n + 2), 0 ≤ (-1 : ℝ) ^ (i : ℕ) * p.eval (x i)) : p = 0 := by
  induction n generalizing p with
  | zero =>
      have hpC := Polynomial.eq_C_of_natDegree_le_zero hp
      have h0 := hs 0
      have h1 := hs 1
      rw [hpC] at h0 h1 ⊢
      norm_num at h0 h1
      have hc : p.coeff 0 = 0 := le_antisymm h1 h0
      simp [hc]
  | succ n ih =>
      by_contra hpzero
      have hfirst : 0 ≤ p.eval (x 0) := by simpa using hs 0
      by_cases hzero : p.eval (x 0) = 0
      · obtain ⟨q, hpq⟩ := Polynomial.dvd_iff_isRoot.mpr hzero
        have hqne : q ≠ 0 := by
          intro hq
          apply hpzero
          simpa [hq] using hpq
        have hpdeg : p.natDegree = 1 + q.natDegree := by
          rw [hpq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hqne,
            Polynomial.natDegree_X_sub_C]
        have hqdeg : (-q).natDegree ≤ n := by
          rw [Polynomial.natDegree_neg]
          omega
        have hqzero : -q = 0 := ih (-q) hqdeg (fun i => x i.succ)
            (hx.comp Fin.strictMono_succ) (by
          intro i
          have hpos : 0 < x i.succ - x 0 := sub_pos.mpr (hx (by simp))
          apply (mul_nonneg_iff_of_pos_left hpos).mp
          calc
            0 ≤ (-1 : ℝ) ^ (i.succ : ℕ) * p.eval (x i.succ) := hs i.succ
            _ = (x i.succ - x 0) *
                ((-1 : ℝ) ^ (i : ℕ) * (-q).eval (x i.succ)) := by
              rw [hpq]
              simp only [Polynomial.eval_mul, Polynomial.eval_sub,
                Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_neg,
                Fin.val_succ, pow_succ]
              ring)
        exact hqne (neg_eq_zero.mp hqzero)
      · have hpositive : 0 < p.eval (x 0) := lt_of_le_of_ne hfirst (Ne.symm hzero)
        have hsecond : p.eval (x 1) ≤ 0 := by
          have h := hs 1
          norm_num at h
          exact h
        have hx01 : x 0 < x 1 := hx (by norm_num)
        obtain ⟨r, hr, hroot⟩ :=
          intermediate_value_Ioc' hx01.le p.continuous.continuousOn
            (show (0 : ℝ) ∈ Ico (p.eval (x 1)) (p.eval (x 0)) from
              ⟨hsecond, hpositive⟩)
        obtain ⟨q, hpq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
        have hqne : q ≠ 0 := by
          intro hq
          apply hpzero
          simpa [hq] using hpq
        have hpdeg : p.natDegree = 1 + q.natDegree := by
          rw [hpq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hqne,
            Polynomial.natDegree_X_sub_C]
        have hqdeg : (-q).natDegree ≤ n := by
          rw [Polynomial.natDegree_neg]
          omega
        have hqzero : -q = 0 := ih (-q) hqdeg (x ∘ skipSecond)
            (hx.comp (strictMono_skipSecond n)) (by
          intro i
          by_cases hi : i = 0
          · subst i
            simp only [Function.comp_apply, skipSecond, if_true,
              Fin.val_zero, pow_zero, one_mul, Polynomial.eval_neg]
            have hprod : 0 < (x 0 - r) * q.eval (x 0) := by
              simpa only [hpq, Polynomial.eval_mul, Polynomial.eval_sub,
                Polynomial.eval_X, Polynomial.eval_C] using hpositive
            have hneg : x 0 - r < 0 := sub_neg.mpr hr.1
            rcases mul_pos_iff.mp hprod with ⟨h, _⟩ | ⟨_, h⟩
            · linarith
            · linarith
          · simp only [Function.comp_apply, skipSecond, hi, if_false]
            have hindex : (1 : Fin (n + 3)) < i.succ := by
              change 1 < i.val + 1
              have hi0 : i.val ≠ 0 := by
                intro hz
                apply hi
                exact Fin.ext hz
              omega
            have hpos : 0 < x i.succ - r := sub_pos.mpr (lt_of_le_of_lt hr.2 (hx hindex))
            apply (mul_nonneg_iff_of_pos_left hpos).mp
            calc
              0 ≤ (-1 : ℝ) ^ (i.succ : ℕ) * p.eval (x i.succ) := hs i.succ
              _ = (x i.succ - r) *
                  ((-1 : ℝ) ^ (i : ℕ) * (-q).eval (x i.succ)) := by
                rw [hpq]
                simp only [Polynomial.eval_mul, Polynomial.eval_sub,
                  Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_neg,
                  Fin.val_succ, pow_succ]
                ring)
        exact hqne (neg_eq_zero.mp hqzero)

/-- The same weak alternation statement with either initial sign. -/
theorem polynomial_eq_zero_of_signed_weak_alternation (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) (x : Fin (n + 2) → ℝ)
    (hx : StrictMono x) (s : ℝ) (hsign : s = 1 ∨ s = -1)
    (hs : ∀ i : Fin (n + 2), 0 ≤ s * (-1 : ℝ) ^ (i : ℕ) * p.eval (x i)) : p = 0 := by
  rcases hsign with rfl | rfl
  · exact polynomial_eq_zero_of_weak_alternation n p hp x hx (by simpa using hs)
  · have hneg : -p = 0 := polynomial_eq_zero_of_weak_alternation n (-p)
        (by simpa using hp) x hx (by
      intro i
      simpa only [Polynomial.eval_neg, neg_one_mul, neg_mul, mul_neg, one_mul] using hs i)
    exact neg_eq_zero.mp hneg

private theorem signed_difference_nonneg (s A B E : ℝ)
    (hs : s = 1 ∨ s = -1) (hA : A = s * E) (hB : |B| ≤ E) :
    0 ≤ s * (A - B) := by
  rcases abs_le.mp hB with ⟨hlo, hhi⟩
  rcases hs with rfl | rfl
  · simp only [one_mul] at hA ⊢
    linarith
  · simp only [neg_one_mul] at hA ⊢
    linarith

/-- The alternation certificate determines the only degree-`n` polynomial whose
uniform error is at most its certified error. -/
theorem Alternates.eq_of_errorBound {f : ℝ → ℝ} {n : ℕ} {p q : ℝ[X]} {E : ℝ}
    (a : Alternates f n p E) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hbound : HasErrorBound f q E) : q = p := by
  apply sub_eq_zero.mp
  apply polynomial_eq_zero_of_signed_weak_alternation n (q - p)
    ((Polynomial.natDegree_sub_le q p).trans (max_le hq hp))
    a.nodes a.strictMono a.initialSign a.initialSign_eq
  intro i
  have hsign : a.initialSign * (-1 : ℝ) ^ (i : ℕ) = 1 ∨
      a.initialSign * (-1 : ℝ) ^ (i : ℕ) = -1 := by
    rcases a.initialSign_eq with h | h <;>
      rcases neg_one_pow_eq_or ℝ (i : ℕ) with hpow | hpow <;> simp [h, hpow]
  have h := signed_difference_nonneg
    (a.initialSign * (-1 : ℝ) ^ (i : ℕ))
    (f (a.nodes i) - p.eval (a.nodes i))
    (f (a.nodes i) - q.eval (a.nodes i)) E hsign
    (a.error_eq i) (hbound (a.nodes i) (Ioo_subset_Icc_self (a.interior i)))
  simpa only [Polynomial.eval_sub, sub_sub_sub_cancel_left] using h

/-- A bounded polynomial with a full alternation certificate is best. -/
theorem Alternates.isBest {f : ℝ → ℝ} {n : ℕ} {p : ℝ[X]} {E : ℝ}
    (a : Alternates f n p E) (hp : p.natDegree ≤ n)
    (hbound : HasErrorBound f p E) : IsBest f n p := by
  refine ⟨hp, ?_⟩
  intro q hq E' hqbound
  by_cases hEE' : E ≤ E'
  · intro x hx
    exact (hbound x hx).trans hEE'
  · have hqE : HasErrorBound f q E := fun x hx =>
      (hqbound x hx).trans (le_of_lt (lt_of_not_ge hEE'))
    have hqp : q = p := a.eq_of_errorBound hp hq hqE
    simpa only [hqp] using hqbound

/-- Every best approximation equals an explicitly bounded polynomial with a full
alternation certificate.  This does not invoke a best-approximation operator or
any existence theorem. -/
theorem Alternates.eq_of_isBest {f : ℝ → ℝ} {n : ℕ} {p q : ℝ[X]} {E : ℝ}
    (a : Alternates f n p E) (hp : p.natDegree ≤ n)
    (hbound : HasErrorBound f p E) (hq : IsBest f n q) : q = p :=
  a.eq_of_errorBound hp hq.1 (hq.2 p hp E hbound)

/-- In particular, vanishing of the certified polynomial at the origin implies
vanishing of every best approximation of this degree. -/
theorem Alternates.all_best_vanish {f : ℝ → ℝ} {n : ℕ} {p : ℝ[X]} {E : ℝ}
    (a : Alternates f n p E) (hp : p.natDegree ≤ n)
    (hbound : HasErrorBound f p E) (hzero : p.eval 0 = 0) :
    ∀ q : ℝ[X], IsBest f n q → q.eval 0 = 0 := by
  intro q hq
  rw [a.eq_of_isBest hp hbound hq]
  exact hzero

end Lorentz
