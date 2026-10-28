module

public import Lorentz.BaselineLocal
public import Lorentz.Composition
public import Lorentz.CertificateCompleteness
public import Lorentz.CertificateAlternation

@[expose] public section

namespace Lorentz.Construction

open Set Polynomial

noncomputable def F (x : ℝ) : ℝ := Baseline.G (Lorentz.cubic x)

noncomputable def basePolynomial (n : ℕ) : ℝ[X] :=
  if n < 3 then 0 else Lorentz.cubicPoly

noncomputable def baseResidual (n : ℕ) (x : ℝ) : ℝ :=
  if n < 3 then Baseline.G (Lorentz.cubic x)
  else -Baseline.G (Lorentz.cubic (Lorentz.cubic x)) / 3

noncomputable def baseError (n : ℕ) : ℝ :=
  if n < 3 then Baseline.B else Baseline.B / 3

noncomputable def contacts (z : ℝ) (n : ℕ) : Finset ℝ := by
  classical
  exact if n < 3 then Finset.univ.image (fun j : Fin 6 => Certificate.node z (3 * j.val + 1))
    else Finset.univ.image (fun j : Fin 18 => Certificate.node z j.val)

noncomputable def contactSign (n : ℕ) (x : ℝ) : ℝ := baseResidual n x / baseError n

lemma baseError_pos (n : ℕ) : 0 < baseError n := by
  have := Baseline.B_pos
  unfold baseError
  split_ifs <;> positivity

lemma F_continuousOn : ContinuousOn F interval :=
  Baseline.G_continuousOn.comp cubic_continuous.continuousOn
    (fun _ hx => cubic_maps_interval hx)

lemma baseResidual_continuousOn (n : ℕ) : ContinuousOn (baseResidual n) interval := by
  unfold baseResidual
  by_cases hn : n < 3
  · simp only [if_pos hn]
    exact F_continuousOn
  · simp only [if_neg hn]
    have h := Baseline.G_continuousOn.comp
      (cubic_continuous.comp cubic_continuous).continuousOn
      (fun _ hx => cubic_maps_interval (cubic_maps_interval hx))
    exact h.neg.div_const 3

lemma basePolynomial_degree (n : ℕ) : (basePolynomial n).natDegree ≤ n := by
  by_cases hn : n < 3
  · simp [basePolynomial, hn]
  · have hdegree : Lorentz.cubicPoly.natDegree ≤ 3 := by
      unfold Lorentz.cubicPoly
      compute_degree
    simpa only [basePolynomial, if_neg hn] using hdegree.trans (by omega)

lemma basePolynomial_zero (n : ℕ) : (basePolynomial n).eval 0 = 0 := by
  unfold basePolynomial
  split_ifs <;> simp [Lorentz.cubicPoly]

lemma baseResidual_eq (n : ℕ) {x : ℝ} (hx : x ∈ interval) :
    F x - (basePolynomial n).eval x = baseResidual n x := by
  by_cases hn : n < 3
  · simp [F, basePolynomial, baseResidual, hn]
  · have h := Baseline.G_equation (cubic_maps_interval hx)
    simp only [F, basePolynomial, baseResidual, if_neg hn, eval_cubicPoly]
    linarith

lemma mem_contacts_iff (z : ℝ) (n : ℕ) (x : ℝ) :
    x ∈ contacts z n ↔ ∃ j : ℕ, j < Certificate.gridSize n ∧
      Certificate.node z (Certificate.gridIndex n j) = x := by
  classical
  by_cases hn : n < 3
  · simp only [contacts, if_pos hn, Certificate.gridSize, Certificate.gridIndex,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j.val, j.isLt, hj⟩
    · rintro ⟨j, hj, heq⟩
      exact ⟨⟨j, hj⟩, heq⟩
  · simp only [contacts, if_neg hn, Certificate.gridSize, Certificate.gridIndex,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j.val, j.isLt, hj⟩
    · rintro ⟨j, hj, heq⟩
      exact ⟨⟨j, hj⟩, heq⟩

lemma contacts_nonempty (z : ℝ) (n : ℕ) : (contacts z n).Nonempty := by
  refine ⟨Certificate.node z (Certificate.gridIndex n 0), ?_⟩
  rw [mem_contacts_iff]
  refine ⟨0, ?_, rfl⟩
  unfold Certificate.gridSize
  split_ifs <;> norm_num

lemma contacts_interior (z : ℝ) (n : ℕ)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    {x : ℝ} (hx : x ∈ contacts z n) : x ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨j, hj, rfl⟩ := (mem_contacts_iff z n x).mp hx
  exact Certificate.node_bounds z hl hu
    ⟨_, Certificate.gridIndex_bound n j hj⟩

lemma contacts_subset (z : ℝ) (n : ℕ)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    {x : ℝ} (hx : x ∈ contacts z n) : x ∈ interval :=
  Ioo_subset_Icc_self (contacts_interior z n hl hu hx)

lemma baseResidual_at_grid (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n j : ℕ) (hj : j < Certificate.gridSize n) :
    baseResidual n (Certificate.node z (Certificate.gridIndex n j)) =
      Certificate.gridSign n j * baseError n := by
  have ha : Certificate.a z = PolynomialBounds.a :=
    Certificate.a_eq_sqrt_two_div_two z hm hl hu
  by_cases hn : n < 3
  · have hj6 : j < 6 := by simpa [Certificate.gridSize, hn] using hj
    have hmap := Certificate.coarse_mapping z hm ⟨j, hj6⟩
    change Lorentz.cubic (Certificate.node z (3 * j + 1)) =
      Certificate.coarseSign j * Certificate.a z at hmap
    rw [ha] at hmap
    simp only [baseResidual, baseError, Certificate.gridIndex, Certificate.gridSign, if_pos hn]
    rw [hmap]
    have hs : Certificate.coarseSign j = 1 ∨ Certificate.coarseSign j = -1 := by
      simpa [Certificate.gridSign, hn] using Certificate.gridSign_one_or_neg_one n j
    rcases hs with hs | hs
    · rw [hs]
      simpa only [one_mul] using Baseline.G_at_a
    · rw [hs]
      simpa only [neg_one_mul] using Baseline.G_at_neg_a
  · have hj18 : j < 18 := by simpa [Certificate.gridSize, hn] using hj
    have hmap := Certificate.fine_mapping z hm ⟨j, hj18⟩
    change Lorentz.cubic (Lorentz.cubic (Certificate.node z j)) =
      -Certificate.fineSign j * Certificate.a z at hmap
    rw [ha] at hmap
    simp only [baseResidual, baseError, Certificate.gridIndex, Certificate.gridSign, if_neg hn]
    rw [hmap]
    have hs : Certificate.fineSign j = 1 ∨ Certificate.fineSign j = -1 := by
      simpa [Certificate.gridSign, hn] using Certificate.gridSign_one_or_neg_one n j
    rcases hs with hs | hs
    · rw [hs]
      simp [Baseline.G_at_neg_a]
    · rw [hs]
      simp [Baseline.G_at_a, neg_div]

lemma contactSign_at_grid (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n j : ℕ) (hj : j < Certificate.gridSize n) :
    contactSign n (Certificate.node z (Certificate.gridIndex n j)) = Certificate.gridSign n j := by
  rw [contactSign, baseResidual_at_grid z hm hl hu n j hj]
  exact mul_div_cancel_right₀ _ (baseError_pos n).ne'

lemma contactSign_values (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : ℕ) {x : ℝ} (hx : x ∈ contacts z n) :
    contactSign n x = 1 ∨ contactSign n x = -1 := by
  obtain ⟨j, hj, rfl⟩ := (mem_contacts_iff z n x).mp hx
  rw [contactSign_at_grid z hm hl hu n j hj]
  exact Certificate.gridSign_one_or_neg_one n j

lemma contact_signed_value (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : ℕ) {x : ℝ} (hx : x ∈ contacts z n) :
    contactSign n x * baseResidual n x = baseError n := by
  obtain ⟨j, hj, rfl⟩ := (mem_contacts_iff z n x).mp hx
  rw [contactSign_at_grid z hm hl hu n j hj, baseResidual_at_grid z hm hl hu n j hj]
  calc
    Certificate.gridSign n j * (Certificate.gridSign n j * baseError n) =
        (Certificate.gridSign n j) ^ 2 * baseError n := by ring
    _ = baseError n := by rw [Certificate.gridSign_sq, one_mul]

lemma contact_root (z : ℝ) (hm : Certificate.modulus z = 0)
    (n : ℕ) {x : ℝ} (hx : x ∈ contacts z n) :
    if n < 3 then (Lorentz.cubic x) ^ 2 = (1 : ℝ) / 2
    else (Lorentz.cubic (Lorentz.cubic x)) ^ 2 = (1 : ℝ) / 2 := by
  obtain ⟨j, hj, rfl⟩ := (mem_contacts_iff z n x).mp hx
  by_cases hn : n < 3
  · have hj6 : j < 6 := by simpa [Certificate.gridSize, hn] using hj
    have h := Certificate.coarse_zero z hm ⟨j, hj6⟩
    change 2 * (Lorentz.cubic (Certificate.node z (3 * j + 1))) ^ 2 - 1 = 0 at h
    simp only [if_pos hn, Certificate.gridIndex]
    linarith
  · have hj18 : j < 18 := by simpa [Certificate.gridSize, hn] using hj
    have h := Certificate.fine_zero z hm ⟨j, hj18⟩
    change 2 * (Lorentz.cubic (Lorentz.cubic (Certificate.node z j))) ^ 2 - 1 = 0 at h
    simp only [if_neg hn, Certificate.gridIndex]
    linarith

lemma baseResidual_strict (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : ℕ) {x : ℝ} (hx : x ∈ interval) (hnot : x ∉ contacts z n) :
    |baseResidual n x| < baseError n := by
  by_cases hn : n < 3
  · have hneq : (Lorentz.cubic x) ^ 2 ≠ (1 : ℝ) / 2 := by
      intro heq
      have hzero : Certificate.sixth x = 0 := by
        change 2 * (Lorentz.cubic x) ^ 2 - 1 = 0
        rw [heq]
        norm_num
      obtain ⟨j, hj⟩ := (Certificate.coarse_roots_complete z hm hl hu x).mp hzero
      apply hnot
      rw [mem_contacts_iff]
      exact ⟨j.val, by simpa [Certificate.gridSize, hn] using j.isLt,
        by simpa [Certificate.gridIndex, hn] using hj⟩
    have hpa : Lorentz.cubic x ≠ PolynomialBounds.a := by
      intro heq; apply hneq; rw [heq, PolynomialBounds.a_sq]
    have hpna : Lorentz.cubic x ≠ -PolynomialBounds.a := by
      intro heq; apply hneq; rw [heq, neg_sq, PolynomialBounds.a_sq]
    simpa only [baseResidual, baseError, if_pos hn] using
      Baseline.G_abs_lt (cubic_maps_interval hx) hpa hpna
  · have hneq : (Lorentz.cubic (Lorentz.cubic x)) ^ 2 ≠ (1 : ℝ) / 2 := by
      intro heq
      have hzero : Certificate.eighteenth x = 0 := by
        change 2 * (Lorentz.cubic (Lorentz.cubic x)) ^ 2 - 1 = 0
        rw [heq]
        norm_num
      obtain ⟨j, hj⟩ := (Certificate.fine_roots_complete z hm hl hu x).mp hzero
      apply hnot
      rw [mem_contacts_iff]
      exact ⟨j.val, by simpa [Certificate.gridSize, hn] using j.isLt,
        by simpa [Certificate.gridIndex, hn] using hj⟩
    have hpa : Lorentz.cubic (Lorentz.cubic x) ≠ PolynomialBounds.a := by
      intro heq; apply hneq; rw [heq, PolynomialBounds.a_sq]
    have hpna : Lorentz.cubic (Lorentz.cubic x) ≠ -PolynomialBounds.a := by
      intro heq; apply hneq; rw [heq, neg_sq, PolynomialBounds.a_sq]
    have h := Baseline.G_abs_lt (cubic_maps_interval (cubic_maps_interval hx)) hpa hpna
    simpa only [baseResidual, baseError, if_neg hn, abs_div, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 3)] using
      (div_lt_div_of_pos_right h (by norm_num : (0 : ℝ) < 3))

lemma baseResidual_local_cusp (z : ℝ) (hm : Certificate.modulus z = 0)
    (n : ℕ) {x : ℝ} (hx : x ∈ contacts z n) :
    ∃ c > 0, ∃ δ > 0, ∀ y ∈ interval, |y - x| ≤ δ →
      c * |y - x| ≤ baseError n - |baseResidual n y| := by
  have hroot := contact_root z hm n hx
  by_cases hn : n < 3
  · rw [if_pos hn] at hroot
    simpa only [baseResidual, baseError, if_pos hn] using
      Baseline.exists_G_cubic_local_cusp hroot
  · rw [if_neg hn] at hroot
    obtain ⟨c, hc, δ, hδ, hgap⟩ := Baseline.exists_G_ninth_local_cusp hroot
    refine ⟨c / 3, by positivity, δ, hδ, ?_⟩
    intro y hy hnear
    have h := hgap y hy hnear
    simp only [baseResidual, baseError, if_neg hn, abs_div, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith

end Lorentz.Construction
