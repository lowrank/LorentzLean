module

public import Lorentz.CertificateGrid

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Lorentz.Certificate

private theorem rational_node_bounds : ∀ j : Fin 18,
    (-1 : ℚ) < lower (nodeCoeffs j) rootLower rootUpper ∧
    upper (nodeCoeffs j) rootLower rootUpper < 1 := by
  decide +kernel

private theorem rational_node_order : ∀ j : Fin 17,
    upper (nodeCoeffs j) rootLower rootUpper <
    lower (nodeCoeffs (j.val + 1)) rootLower rootUpper := by
  decide +kernel

 theorem node_bounds (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) (j : Fin 18) : -1 < node z j ∧ node z j < 1 := by
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  have h := eval_bounds (nodeCoeffs j) z rootLower rootUpper hl hu hz
  have hr := rational_node_bounds j
  constructor
  · exact lt_of_lt_of_le (by exact_mod_cast hr.1) h.1
  · exact lt_of_le_of_lt h.2 (by exact_mod_cast hr.2)

 theorem nodes_strictMono (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) : StrictMono (fun j : Fin 18 => node z j) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  have hleft := (eval_bounds (nodeCoeffs j) z rootLower rootUpper hl hu hz).2
  have hright := (eval_bounds (nodeCoeffs (j.val + 1)) z rootLower rootUpper hl hu hz).1
  have hr := rational_node_order j
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le (by exact_mod_cast hr) hright)

end Lorentz.Certificate
