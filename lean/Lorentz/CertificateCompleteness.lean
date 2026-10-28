module

public import Lorentz.CertificateGeometry

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Lorentz.Certificate

open Polynomial

noncomputable def cubicPoly : Polynomial ℝ := 4 * X ^ 3 - 3 * X

noncomputable def sixthPoly : Polynomial ℝ := 2 * cubicPoly ^ 2 - 1

noncomputable def eighteenthPoly : Polynomial ℝ := 2 * (4 * cubicPoly ^ 3 - 3 * cubicPoly) ^ 2 - 1

 theorem cubicPoly_eval (x : ℝ) : cubicPoly.eval x = cubic x := by
  simp [cubicPoly, cubic]

 theorem sixthPoly_eval (x : ℝ) : sixthPoly.eval x = sixth x := by
  simp [sixthPoly, sixth, cubicPoly_eval]

 theorem eighteenthPoly_eval (x : ℝ) : eighteenthPoly.eval x = eighteenth x := by
  simp [eighteenthPoly, eighteenth, cubicPoly_eval, cubic]

 theorem sixthPoly_degree : sixthPoly.natDegree ≤ 6 := by
  unfold sixthPoly cubicPoly
  compute_degree

 theorem eighteenthPoly_degree : eighteenthPoly.natDegree ≤ 18 := by
  unfold eighteenthPoly cubicPoly
  compute_degree

 theorem sixthPoly_ne_zero : sixthPoly ≠ 0 := by
  intro h
  have he := congrArg (fun p : Polynomial ℝ => p.eval 1) h
  norm_num [sixthPoly_eval, sixth, cubic] at he

 theorem eighteenthPoly_ne_zero : eighteenthPoly ≠ 0 := by
  intro h
  have he := congrArg (fun p : Polynomial ℝ => p.eval 1) h
  norm_num [eighteenthPoly_eval, eighteenth, cubic] at he

/-- A polynomial with degree at most `N` and `N` specified distinct roots has no
other roots.  This is the root-count step in the finite certificate. -/
 theorem finite_roots_complete {N : ℕ} (p : Polynomial ℝ) (g : Fin N → ℝ)
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ N) (hinj : Function.Injective g)
    (heval : ∀ j, p.eval (g j) = 0) (x : ℝ) :
    p.eval x = 0 ↔ ∃ j, g j = x := by
  classical
  let s : Finset ℝ := Finset.univ.image g
  have hcard : s.card = N := by
    simp only [s, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : s ⊆ p.roots.toFinset := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, _, rfl⟩
    simpa only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def] using heval j
  have hbound : p.roots.toFinset.card ≤ s.card := by
    calc
      p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ ≤ N := hdeg
      _ = s.card := hcard.symm
  have heq : s = p.roots.toFinset := Finset.eq_of_subset_of_card_le hsub hbound
  constructor
  · intro hx
    have hm : x ∈ p.roots.toFinset := by
      simpa only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def] using hx
    rw [← heq] at hm
    simpa [s] using hm
  · rintro ⟨j, rfl⟩
    exact heval j

 theorem coarseNodes_strictMono (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) :
    StrictMono (fun j : Fin 6 => node z (3 * j.val + 1)) := by
  intro i j hij
  have hi18 : 3 * i.val + 1 < 18 := by omega
  have hj18 : 3 * j.val + 1 < 18 := by omega
  have hij18 : (⟨3 * i.val + 1, hi18⟩ : Fin 18) < ⟨3 * j.val + 1, hj18⟩ := by
    change 3 * i.val + 1 < 3 * j.val + 1
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hij (by decide)) 1
  exact nodes_strictMono z hl hu hij18

 theorem fine_roots_complete (z : ℝ) (hm : modulus z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) (x : ℝ) :
    eighteenth x = 0 ↔ ∃ j : Fin 18, node z j = x := by
  simpa only [eighteenthPoly_eval] using finite_roots_complete eighteenthPoly
    (fun j : Fin 18 => node z j) eighteenthPoly_ne_zero eighteenthPoly_degree
    (nodes_strictMono z hl hu).injective
    (fun j => by rw [eighteenthPoly_eval]; exact fine_zero z hm j) x

 theorem coarse_roots_complete (z : ℝ) (hm : modulus z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) (x : ℝ) :
    sixth x = 0 ↔ ∃ j : Fin 6, node z (3 * j.val + 1) = x := by
  simpa only [sixthPoly_eval] using finite_roots_complete sixthPoly
    (fun j : Fin 6 => node z (3 * j.val + 1)) sixthPoly_ne_zero sixthPoly_degree
    (coarseNodes_strictMono z hl hu).injective
    (fun j => by rw [sixthPoly_eval]; exact coarse_zero z hm j) x

end Lorentz.Certificate
