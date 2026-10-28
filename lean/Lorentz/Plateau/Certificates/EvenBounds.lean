module

public import Lorentz.Plateau.Certificates.EvenData
public import Lorentz.Plateau.Certificates.Checker

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Even

lemma root_nonneg (z : ℝ) (hl : (rootLower : ℝ) ≤ z) : 0 ≤ z :=
  le_trans (by exact_mod_cast (show (0 : ℚ) ≤ rootLower by decide +kernel)) hl

theorem rational_node_bounds : ∀ j : Fin 36,
    (-1 : ℚ) < Certificate.lower (nodeRows.getD j []) rootLower rootUpper ∧
    Certificate.upper (nodeRows.getD j []) rootLower rootUpper < 1 := by decide +kernel

theorem rational_node_order : ∀ j : Fin 35,
    Certificate.upper (nodeRows.getD j []) rootLower rootUpper <
    Certificate.lower (nodeRows.getD (j.val + 1) []) rootLower rootUpper := by decide +kernel

theorem node_bounds (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) (j : Fin 36) : -1 < node z j ∧ node z j < 1 := by
  have h := Certificate.eval_bounds (nodeRows.getD j []) z rootLower rootUpper hl hu (root_nonneg z hl)
  have hr := rational_node_bounds j
  exact ⟨lt_of_lt_of_le (by exact_mod_cast hr.1) h.1,
    lt_of_le_of_lt h.2 (by exact_mod_cast hr.2)⟩

theorem nodes_strictMono (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) : StrictMono (fun j : Fin 36 ↦ node z j) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  have hleft := (Certificate.eval_bounds (nodeRows.getD j []) z rootLower rootUpper hl hu (root_nonneg z hl)).2
  have hright := (Certificate.eval_bounds (nodeRows.getD (j.val + 1) []) z rootLower rootUpper hl hu (root_nonneg z hl)).1
  have hr := rational_node_order j
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le (by exact_mod_cast hr) hright)

theorem rational_slacks_0 : ∀ j : Fin 12, 0 ≤
    Certificate.lower ((slackRows.getD 0 []).getD j []) rootLower rootUpper := by decide +kernel

theorem slacks_nonneg_0 (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) (j : Fin 12) :
    0 ≤ Certificate.eval ((slackRows.getD 0 []).getD j []) z :=
  Certificate.eval_nonneg _ z rootLower rootUpper hl hu (root_nonneg z hl)
    (rational_slacks_0 j)

theorem rational_slacks_1 : ∀ j : Fin 12, 0 ≤
    Certificate.lower ((slackRows.getD 1 []).getD j []) rootLower rootUpper := by decide +kernel

theorem slacks_nonneg_1 (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) (j : Fin 12) :
    0 ≤ Certificate.eval ((slackRows.getD 1 []).getD j []) z :=
  Certificate.eval_nonneg _ z rootLower rootUpper hl hu (root_nonneg z hl)
    (rational_slacks_1 j)

theorem rational_slacks_2 : ∀ j : Fin 12, 0 ≤
    Certificate.lower ((slackRows.getD 2 []).getD j []) rootLower rootUpper := by decide +kernel

theorem slacks_nonneg_2 (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) (j : Fin 12) :
    0 ≤ Certificate.eval ((slackRows.getD 2 []).getD j []) z :=
  Certificate.eval_nonneg _ z rootLower rootUpper hl hu (root_nonneg z hl)
    (rational_slacks_2 j)

theorem rational_slacks_3 : ∀ j : Fin 36, 0 ≤
    Certificate.lower ((slackRows.getD 3 []).getD j []) rootLower rootUpper := by decide +kernel

theorem slacks_nonneg_3 (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) (j : Fin 36) :
    0 ≤ Certificate.eval ((slackRows.getD 3 []).getD j []) z :=
  Certificate.eval_nonneg _ z rootLower rootUpper hl hu (root_nonneg z hl)
    (rational_slacks_3 j)

end Lorentz.Plateau.Certificates.Even
