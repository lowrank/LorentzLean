module

public import Lorentz.CertificateIdentities
public import Lorentz.CertificateNorms
public import Lorentz.CertificateCompleteness
public import Lorentz.CertificatePolynomials

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Lorentz.Certificate

theorem slack_identity (z : ℝ) (hm : modulus z = 0) (n j : ℕ)
    (hn : n < 7) (hj : j < gridSize n) :
    slope n z - gridSign n j *
      (gridPerturbation z (gridIndex n j) - correction n z (node z (gridIndex n j))) =
      eval (slackCoeffs n j) z := by
  interval_cases n
  · norm_num [gridSize] at hj
    interval_cases j
    · exact slack_identity_0_0 z hm
    · exact slack_identity_0_1 z hm
    · exact slack_identity_0_2 z hm
    · exact slack_identity_0_3 z hm
    · exact slack_identity_0_4 z hm
    · exact slack_identity_0_5 z hm
  · norm_num [gridSize] at hj
    interval_cases j
    · exact slack_identity_1_0 z hm
    · exact slack_identity_1_1 z hm
    · exact slack_identity_1_2 z hm
    · exact slack_identity_1_3 z hm
    · exact slack_identity_1_4 z hm
    · exact slack_identity_1_5 z hm
  · norm_num [gridSize] at hj
    interval_cases j
    · exact slack_identity_1_0 z hm
    · exact slack_identity_1_1 z hm
    · exact slack_identity_1_2 z hm
    · exact slack_identity_1_3 z hm
    · exact slack_identity_1_4 z hm
    · exact slack_identity_1_5 z hm
  · norm_num [gridSize] at hj
    interval_cases j
    · exact slack_identity_3_0 z hm
    · exact slack_identity_3_1 z hm
    · exact slack_identity_3_2 z hm
    · exact slack_identity_3_3 z hm
    · exact slack_identity_3_4 z hm
    · exact slack_identity_3_5 z hm
    · exact slack_identity_3_6 z hm
    · exact slack_identity_3_7 z hm
    · exact slack_identity_3_8 z hm
    · exact slack_identity_3_9 z hm
    · exact slack_identity_3_10 z hm
    · exact slack_identity_3_11 z hm
    · exact slack_identity_3_12 z hm
    · exact slack_identity_3_13 z hm
    · exact slack_identity_3_14 z hm
    · exact slack_identity_3_15 z hm
    · exact slack_identity_3_16 z hm
    · exact slack_identity_3_17 z hm
  · norm_num [gridSize] at hj
    interval_cases j
    · exact slack_identity_4_0 z hm
    · exact slack_identity_4_1 z hm
    · exact slack_identity_4_2 z hm
    · exact slack_identity_4_3 z hm
    · exact slack_identity_4_4 z hm
    · exact slack_identity_4_5 z hm
    · exact slack_identity_4_6 z hm
    · exact slack_identity_4_7 z hm
    · exact slack_identity_4_8 z hm
    · exact slack_identity_4_9 z hm
    · exact slack_identity_4_10 z hm
    · exact slack_identity_4_11 z hm
    · exact slack_identity_4_12 z hm
    · exact slack_identity_4_13 z hm
    · exact slack_identity_4_14 z hm
    · exact slack_identity_4_15 z hm
    · exact slack_identity_4_16 z hm
    · exact slack_identity_4_17 z hm
  · norm_num [gridSize] at hj
    interval_cases j
    · exact slack_identity_5_0 z hm
    · exact slack_identity_5_1 z hm
    · exact slack_identity_5_2 z hm
    · exact slack_identity_5_3 z hm
    · exact slack_identity_5_4 z hm
    · exact slack_identity_5_5 z hm
    · exact slack_identity_5_6 z hm
    · exact slack_identity_5_7 z hm
    · exact slack_identity_5_8 z hm
    · exact slack_identity_5_9 z hm
    · exact slack_identity_5_10 z hm
    · exact slack_identity_5_11 z hm
    · exact slack_identity_5_12 z hm
    · exact slack_identity_5_13 z hm
    · exact slack_identity_5_14 z hm
    · exact slack_identity_5_15 z hm
    · exact slack_identity_5_16 z hm
    · exact slack_identity_5_17 z hm
  · norm_num [gridSize] at hj
    interval_cases j
    · exact slack_identity_5_0 z hm
    · exact slack_identity_5_1 z hm
    · exact slack_identity_5_2 z hm
    · exact slack_identity_5_3 z hm
    · exact slack_identity_5_4 z hm
    · exact slack_identity_5_5 z hm
    · exact slack_identity_5_6 z hm
    · exact slack_identity_5_7 z hm
    · exact slack_identity_5_8 z hm
    · exact slack_identity_5_9 z hm
    · exact slack_identity_5_10 z hm
    · exact slack_identity_5_11 z hm
    · exact slack_identity_5_12 z hm
    · exact slack_identity_5_13 z hm
    · exact slack_identity_5_14 z hm
    · exact slack_identity_5_15 z hm
    · exact slack_identity_5_16 z hm
    · exact slack_identity_5_17 z hm

private theorem list_getD_mem {α : Type} (xs : List α) (i : ℕ) (d : α)
    (hi : i < xs.length) : xs.getD i d ∈ xs := by
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    using List.getElem_mem hi

theorem slack_row_length (n : ℕ) (hn : n < 7) :
    (slackRows.getD n []).length = gridSize n := by
  interval_cases n <;> rfl

theorem slack_member (n j : ℕ) (hn : n < 7) (hj : j < gridSize n) :
    slackCoeffs n j ∈ slackRows.flatten := by
  apply List.mem_flatten_of_mem (list_getD_mem slackRows n [] (by simpa [slackRows] using hn))
  apply list_getD_mem
  rwa [slack_row_length n hn]

theorem grid_inequality (z : ℝ) (hm : modulus z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))
    (n j : ℕ) (hn : n < 7) (hj : j < gridSize n) :
    gridSign n j *
      (gridPerturbation z (gridIndex n j) - correction n z (node z (gridIndex n j))) ≤
      slope n z := by
  have hid := slack_identity z hm n j hn hj
  have hs := slacks_nonnegative z hl hu (slackCoeffs n j) (slack_member n j hn hj)
  apply sub_nonneg.mp
  rw [hid]
  exact hs

def activeIndex (n k : ℕ) : ℕ := (activeRows.getD n []).getD k 0

def gridSignInt (n j : ℕ) : ℤ :=
  (if n < 3 then -1 else 1) * (if j % 4 = 0 ∨ j % 4 = 3 then 1 else -1)

theorem gridSignInt_cast (n j : ℕ) : (gridSignInt n j : ℝ) = gridSign n j := by
  unfold gridSignInt gridSign coarseSign fineSign
  split_ifs <;> norm_num

theorem active_index_bound : ∀ n : Fin 7, ∀ k : Fin (n.val + 2),
    activeIndex n k < gridSize n := by
  decide +kernel

theorem active_indices_strictMono : ∀ n : Fin 7,
    StrictMono (fun k : Fin (n.val + 2) => activeIndex n k) := by
  decide +kernel

theorem active_slack_zero : ∀ n : Fin 7, ∀ k : Fin (n.val + 2),
    slackCoeffs n (activeIndex n k) = [] := by
  decide +kernel

private theorem active_signs_int : ∀ n : Fin 7, ∀ k : Fin (n.val + 1),
    gridSignInt n (activeIndex n k) = -gridSignInt n (activeIndex n (k.val + 1)) := by
  decide +kernel

theorem active_signs (n : Fin 7) (k : Fin (n.val + 1)) :
    gridSign n (activeIndex n k) = -gridSign n (activeIndex n (k.val + 1)) := by
  have h := active_signs_int n k
  rw [← gridSignInt_cast, ← gridSignInt_cast]
  exact_mod_cast h

theorem active_equality (z : ℝ) (hm : modulus z = 0)
    (n : Fin 7) (k : Fin (n.val + 2)) :
    gridSign n (activeIndex n k) *
      (gridPerturbation z (gridIndex n (activeIndex n k)) -
      correction n z (node z (gridIndex n (activeIndex n k)))) = slope n z := by
  have h := slack_identity z hm n (activeIndex n k) n.isLt (active_index_bound n k)
  rw [active_slack_zero n k] at h
  simp only [eval] at h
  exact (sub_eq_zero.mp h).symm

theorem gridIndex_bound (n j : ℕ) (hj : j < gridSize n) : gridIndex n j < 18 := by
  unfold gridIndex gridSize at *
  split_ifs at * <;> omega

theorem gridIndex_strictMono (n : ℕ) : StrictMono (gridIndex n) := by
  intro i j hij
  unfold gridIndex
  split_ifs <;> omega

def activeNode (z : ℝ) (n : Fin 7) (k : Fin (n.val + 2)) : ℝ :=
  node z (gridIndex n (activeIndex n k))

theorem active_node_bounds (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) (n : Fin 7) (k : Fin (n.val + 2)) :
    -1 < activeNode z n k ∧ activeNode z n k < 1 := by
  exact node_bounds z hl hu ⟨gridIndex n (activeIndex n k),
    gridIndex_bound n _ (active_index_bound n k)⟩

theorem active_nodes_strictMono (z : ℝ) (hl : (rootLower : ℝ) ≤ z)
    (hu : z ≤ (rootUpper : ℝ)) (n : Fin 7) : StrictMono (activeNode z n) := by
  intro i j hij
  have hidx := gridIndex_strictMono n (active_indices_strictMono n hij)
  have hi := gridIndex_bound n _ (active_index_bound n i)
  have hj := gridIndex_bound n _ (active_index_bound n j)
  exact nodes_strictMono z hl hu (show (⟨_, hi⟩ : Fin 18) < ⟨_, hj⟩ from hidx)

theorem gridSign_sq (n j : ℕ) : (gridSign n j) ^ 2 = 1 := by
  unfold gridSign
  split_ifs
  · exact coarseSign_sq j
  · exact fineSign_sq j

theorem slope_bounds (n : Fin 7) (z : ℝ)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    0 < slope n z ∧ slope n z < 2 := by
  fin_cases n
  · exact t0_bounds z hl hu
  · exact t1_bounds z hl hu
  · exact t1_bounds z hl hu
  · exact t3_bounds z hl hu
  · exact t4_bounds z hl hu
  · exact t5_bounds z hl hu
  · exact t5_bounds z hl hu

end Lorentz.Certificate
