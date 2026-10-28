module

public import Lorentz.CertificateFinite
public import Lorentz.Minimax

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Lorentz.Certificate

private theorem active_sign_pattern_int : ∀ n : Fin 7, ∀ k : Fin (n.val + 2),
    gridSignInt n (activeIndex n k) =
      gridSignInt n (activeIndex n 0) * (-1 : ℤ) ^ k.val := by
  decide +kernel

 theorem active_sign_pattern (n : Fin 7) (k : Fin (n.val + 2)) :
    gridSign n (activeIndex n k) =
      gridSign n (activeIndex n 0) * (-1 : ℝ) ^ k.val := by
  have h := active_sign_pattern_int n k
  rw [← gridSignInt_cast, ← gridSignInt_cast]
  exact_mod_cast h

 theorem gridSign_one_or_neg_one (n j : ℕ) : gridSign n j = 1 ∨ gridSign n j = -1 := by
  unfold gridSign coarseSign fineSign
  split_ifs <;> norm_num

/-- Converts the checked finite contact table into the alternation structure
used by the uniform-approximation proof. -/
 theorem alternates_of_active_errors (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))
    (n : Fin 7) (f : ℝ → ℝ) (p : Polynomial ℝ) (E : ℝ)
    (herr : ∀ k : Fin (n.val + 2),
      f (activeNode z n k) - p.eval (activeNode z n k) =
        gridSign n (activeIndex n k) * E) :
    Nonempty (Lorentz.Alternates f n p E) := by
  refine ⟨{
    nodes := activeNode z n
    strictMono := active_nodes_strictMono z hl hu n
    interior := fun i => active_node_bounds z hl hu n i
    initialSign := gridSign n (activeIndex n 0)
    initialSign_eq := gridSign_one_or_neg_one _ _
    error_eq := ?_
  }⟩
  intro i
  rw [herr i, active_sign_pattern]

 theorem alternates_of_node_errors (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))
    (n : ℕ) (hn : n < 7) (f : ℝ → ℝ) (p : Polynomial ℝ) (E : ℝ)
    (herr : ∀ k : Fin (n + 2),
      f (node z (gridIndex n (activeIndex n k))) -
        p.eval (node z (gridIndex n (activeIndex n k))) =
        gridSign n (activeIndex n k) * E) :
    Nonempty (Lorentz.Alternates f n p E) := by
  exact alternates_of_active_errors z hl hu ⟨n, hn⟩ f p E herr

end Lorentz.Certificate
