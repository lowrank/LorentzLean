module

public import Lorentz.CertificateOrder

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Lorentz.Certificate

def cubic (x : ℝ) : ℝ := 4 * x ^ 3 - 3 * x
def sixth (x : ℝ) : ℝ := 2 * (cubic x) ^ 2 - 1
def eighteenth (x : ℝ) : ℝ := 2 * (cubic (cubic x)) ^ 2 - 1
def a (z : ℝ) : ℝ := node z 13

def cubicIndex : ℕ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 7
  | 3 => 10
  | 4 => 13
  | 5 => 16
  | 6 => 16
  | 7 => 13
  | 8 => 10
  | 9 => 7
  | 10 => 4
  | 11 => 1
  | 12 => 1
  | 13 => 4
  | 14 => 7
  | 15 => 10
  | 16 => 13
  | 17 => 16
  | _ => 0

theorem cubic_node_0 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 0) = node z 1 := by
  have h : cubic (node z 0) - node z 1 = eval [] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_1 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 1) = node z 4 := by
  have h : cubic (node z 1) - node z 4 = eval [] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_2 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 2) = node z 7 := by
  have h : cubic (node z 2) - node z 7 = eval [0, (3 / 2), 0, (-1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_3 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 3) = node z 10 := by
  have h : cubic (node z 3) - node z 10 = eval [0, (-9 / 2), 0, 15, 0, (-27 / 2), 0, (9 / 2), 0, (-1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_4 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 4) = node z 13 := by
  have h : cubic (node z 4) - node z 13 = eval [0, 9, 0, (-141 / 2), 0, 189, 0, -225, 0, (275 / 2), 0, -45, 0, (15 / 2), 0, (-1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_5 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 5) = node z 16 := by
  have h : cubic (node z 5) - node z 16 = eval [0, -15, 0, (415 / 2), 0, -1053, 0, (5157 / 2), 0, -3504, 0, (5733 / 2), 0, -1470, 0, 476, 0, (-189 / 2), 0, (21 / 2), 0, (-1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_6 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 6) = node z 16 := by
  have h : cubic (node z 6) - node z 16 = eval [0, (39 / 2), 0, -245, 0, 1128, 0, -2631, 0, 3519, 0, -2868, 0, 1470, 0, -476, 0, (189 / 2), 0, (-21 / 2), 0, (1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_7 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 7) = node z 13 := by
  have h : cubic (node z 7) - node z 13 = eval [0, (-45 / 2), 0, (231 / 2), 0, (-459 / 2), 0, (477 / 2), 0, -139, 0, 45, 0, (-15 / 2), 0, (1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_8 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 8) = node z 10 := by
  have h : cubic (node z 8) - node z 10 = eval [0, 24, 0, -44, 0, (51 / 2), 0, -6, 0, (1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_9 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 9) = node z 7 := by
  have h : cubic (node z 9) - node z 7 = eval [0, -24, 0, 44, 0, (-51 / 2), 0, 6, 0, (-1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_10 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 10) = node z 4 := by
  have h : cubic (node z 10) - node z 4 = eval [0, (45 / 2), 0, (-231 / 2), 0, (459 / 2), 0, (-477 / 2), 0, 139, 0, -45, 0, (15 / 2), 0, (-1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_11 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 11) = node z 1 := by
  have h : cubic (node z 11) - node z 1 = eval [0, (-39 / 2), 0, 245, 0, -1128, 0, 2631, 0, -3519, 0, 2868, 0, -1470, 0, 476, 0, (-189 / 2), 0, (21 / 2), 0, (-1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_12 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 12) = node z 1 := by
  have h : cubic (node z 12) - node z 1 = eval [0, 15, 0, (-415 / 2), 0, 1053, 0, (-5157 / 2), 0, 3504, 0, (-5733 / 2), 0, 1470, 0, -476, 0, (189 / 2), 0, (-21 / 2), 0, (1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_13 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 13) = node z 4 := by
  have h : cubic (node z 13) - node z 4 = eval [0, -9, 0, (141 / 2), 0, -189, 0, 225, 0, (-275 / 2), 0, 45, 0, (-15 / 2), 0, (1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_14 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 14) = node z 7 := by
  have h : cubic (node z 14) - node z 7 = eval [0, (9 / 2), 0, -15, 0, (27 / 2), 0, (-9 / 2), 0, (1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_15 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 15) = node z 10 := by
  have h : cubic (node z 15) - node z 10 = eval [0, (-3 / 2), 0, (1 / 2)] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_16 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 16) = node z 13 := by
  have h : cubic (node z 16) - node z 13 = eval [] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node_17 (z : ℝ) (hm : modulus z = 0) :
    cubic (node z 17) = node z 16 := by
  have h : cubic (node z 17) - node z 16 = eval [] z * modulus z := by
    norm_num [cubic, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem cubic_node (z : ℝ) (hm : modulus z = 0) (j : Fin 18) :
    cubic (node z j) = node z (cubicIndex j) := by
  fin_cases j
  · exact cubic_node_0 z hm
  · exact cubic_node_1 z hm
  · exact cubic_node_2 z hm
  · exact cubic_node_3 z hm
  · exact cubic_node_4 z hm
  · exact cubic_node_5 z hm
  · exact cubic_node_6 z hm
  · exact cubic_node_7 z hm
  · exact cubic_node_8 z hm
  · exact cubic_node_9 z hm
  · exact cubic_node_10 z hm
  · exact cubic_node_11 z hm
  · exact cubic_node_12 z hm
  · exact cubic_node_13 z hm
  · exact cubic_node_14 z hm
  · exact cubic_node_15 z hm
  · exact cubic_node_16 z hm
  · exact cubic_node_17 z hm

theorem node_four_neg_a (z : ℝ) : node z 4 = -a z := by
  norm_num [node, nodeCoeffs, a, eval]
  ring

theorem a_sq (z : ℝ) (hm : modulus z = 0) : (a z) ^ 2 = 1 / 2 := by
  have h : (a z) ^ 2 - 1 / 2 = eval [(-1 / 2), 0, (9 / 4), 0, (-3 / 2), 0, (1 / 4)] z * modulus z := by
    norm_num [a, node, nodeCoeffs, eval, modulus]
    ring
  rw [hm, mul_zero] at h
  exact sub_eq_zero.mp h

theorem a_pos (z : ℝ) (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    0 < a z := by
  have hz : 0 ≤ z := by
    have h : (0 : ℝ) ≤ (rootLower : ℝ) := by norm_num [rootLower]
    exact le_trans h hl
  exact eval_pos (nodeCoeffs 13) z rootLower rootUpper hl hu hz (by decide +kernel)

theorem a_eq_sqrt_two_div_two (z : ℝ) (hm : modulus z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    a z = Real.sqrt 2 / 2 := by
  have ha := a_sq z hm
  have hap := a_pos z hl hu
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem fineSign_sq (j : ℕ) : (fineSign j) ^ 2 = 1 := by
  unfold fineSign
  split_ifs <;> norm_num

theorem coarseSign_sq (j : ℕ) : (coarseSign j) ^ 2 = 1 := by
  simpa [coarseSign] using fineSign_sq j

theorem fine_mapping (z : ℝ) (hm : modulus z = 0) (j : Fin 18) :
    cubic (cubic (node z j)) = -fineSign j * a z := by
  fin_cases j
  · rw [cubic_node_0 z hm, cubic_node_1 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_1 z hm, cubic_node_4 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_2 z hm, cubic_node_7 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_3 z hm, cubic_node_10 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_4 z hm, cubic_node_13 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_5 z hm, cubic_node_16 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_6 z hm, cubic_node_16 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_7 z hm, cubic_node_13 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_8 z hm, cubic_node_10 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_9 z hm, cubic_node_7 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_10 z hm, cubic_node_4 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_11 z hm, cubic_node_1 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_12 z hm, cubic_node_1 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_13 z hm, cubic_node_4 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_14 z hm, cubic_node_7 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_15 z hm, cubic_node_10 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_16 z hm, cubic_node_13 z hm]
    simp [fineSign, node_four_neg_a, a]
  · rw [cubic_node_17 z hm, cubic_node_16 z hm]
    simp [fineSign, node_four_neg_a, a]

theorem coarse_mapping (z : ℝ) (hm : modulus z = 0) (j : Fin 6) :
    cubic (node z (3 * j.val + 1)) = coarseSign j * a z := by
  fin_cases j
  · change cubic (node z 1) = coarseSign 0 * a z
    rw [cubic_node_1 z hm]
    simp [coarseSign, fineSign, node_four_neg_a, a]
  · change cubic (node z 4) = coarseSign 1 * a z
    rw [cubic_node_4 z hm]
    simp [coarseSign, fineSign, node_four_neg_a, a]
  · change cubic (node z 7) = coarseSign 2 * a z
    rw [cubic_node_7 z hm]
    simp [coarseSign, fineSign, node_four_neg_a, a]
  · change cubic (node z 10) = coarseSign 3 * a z
    rw [cubic_node_10 z hm]
    simp [coarseSign, fineSign, node_four_neg_a, a]
  · change cubic (node z 13) = coarseSign 4 * a z
    rw [cubic_node_13 z hm]
    simp [coarseSign, fineSign, node_four_neg_a, a]
  · change cubic (node z 16) = coarseSign 5 * a z
    rw [cubic_node_16 z hm]
    simp [coarseSign, fineSign, node_four_neg_a, a]

theorem fine_zero (z : ℝ) (hm : modulus z = 0) (j : Fin 18) :
    eighteenth (node z j) = 0 := by
  simp [eighteenth, fine_mapping z hm j, mul_pow, fineSign_sq, a_sq z hm]

theorem coarse_zero (z : ℝ) (hm : modulus z = 0) (j : Fin 6) :
    sixth (node z (3 * j.val + 1)) = 0 := by
  simp [sixth, coarse_mapping z hm j, mul_pow, coarseSign_sq, a_sq z hm]

end Lorentz.Certificate
