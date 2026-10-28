module

public import Lorentz.Minimax
public import Lorentz.Series

@[expose] public section

/-!
# Lifting alternation through the cubic Chebyshev map

An interior alternation with `m+2` contacts lifts through the three monotone
branches of `T₃`. Removing one repeated sign at each fold leaves `3m+4`
strictly ordered contacts. This provides the all-degree induction without
assuming a general best-approximation operator or a converse alternation theorem.
-/

open Polynomial Set

namespace Lorentz

/-- The polynomial whose real evaluation is the self-similarity map. -/
noncomputable def cubicPoly : ℝ[X] := C 4 * X ^ 3 - C 3 * X

@[simp] theorem eval_cubicPoly (x : ℝ) : cubicPoly.eval x = cubic x := by
  simp [cubicPoly, cubic]

lemma cubic_strictMono_right : StrictMonoOn cubic (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxy' : 0 ≤ (x - 1 / 2) * (y - 1 / 2) :=
    mul_nonneg (by linarith [hx.1]) (by linarith [hy.1])
  have hfactor : 0 < 4 * (x ^ 2 + x * y + y ^ 2) - 3 := by
    nlinarith [hx.1, hy.1, sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]
  have hprod := mul_pos (sub_pos.mpr hxy) hfactor
  have heq : cubic y - cubic x =
      (y - x) * (4 * (x ^ 2 + x * y + y ^ 2) - 3) := by
    unfold cubic
    ring
  linarith

lemma cubic_strictMono_left : StrictMonoOn cubic (Icc (-1 : ℝ) (-1 / 2)) := by
  intro x hx y hy hxy
  have hx' : -x ∈ Icc (1 / 2 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hy' : -y ∈ Icc (1 / 2 : ℝ) 1 := by constructor <;> linarith [hy.1, hy.2]
  have h := cubic_strictMono_right hy' hx' (neg_lt_neg hxy)
  rw [cubic_neg, cubic_neg] at h
  linarith

lemma cubic_strictAnti_middle : StrictAntiOn cubic (Icc (-1 / 2 : ℝ) (1 / 2)) := by
  intro x hx y hy hxy
  have hx' : 0 ≤ (1 / 2 - x) * (1 / 2 + x) :=
    mul_nonneg (by linarith [hx.2]) (by linarith [hx.1])
  have hy' : 0 ≤ (1 / 2 - y) * (1 / 2 + y) :=
    mul_nonneg (by linarith [hy.2]) (by linarith [hy.1])
  have hxy' : 0 ≤ (1 / 2 + x) * (1 / 2 - y) :=
    mul_nonneg (by linarith [hx.1]) (by linarith [hy.2])
  have hfactor : 4 * (x ^ 2 + x * y + y ^ 2) - 3 < 0 := by nlinarith
  have hprod := mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hfactor
  have heq : cubic y - cubic x =
      (y - x) * (4 * (x ^ 2 + x * y + y ^ 2) - 3) := by
    unfold cubic
    ring
  linarith

lemma exists_cubic_left_preimage {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    ∃ x ∈ Ioo (-1 : ℝ) (-1 / 2), cubic x = y := by
  have hend : y ∈ Ioo (cubic (-1)) (cubic (-1 / 2)) := by
    norm_num [cubic]
    exact hy
  exact intermediate_value_Ioo (by norm_num) cubic_continuous.continuousOn hend

lemma exists_cubic_middle_preimage {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    ∃ x ∈ Ioo (-1 / 2 : ℝ) (1 / 2), cubic x = y := by
  have hend : y ∈ Ioo (cubic (1 / 2)) (cubic (-1 / 2)) := by
    norm_num [cubic]
    exact hy
  exact intermediate_value_Ioo' (by norm_num) cubic_continuous.continuousOn hend

lemma exists_cubic_right_preimage {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    ∃ x ∈ Ioo (1 / 2 : ℝ) 1, cubic x = y := by
  have hend : y ∈ Ioo (cubic (1 / 2)) (cubic 1) := by
    norm_num [cubic]
    exact hy
  exact intermediate_value_Ioo (by norm_num) cubic_continuous.continuousOn hend

/-- An initial segment of alternation nodes is still an alternation. -/
def Alternates.restrict {f : ℝ → ℝ} {N n : ℕ} {p : ℝ[X]} {E : ℝ}
    (a : Alternates f N p E) (h : n ≤ N) : Alternates f n p E where
  nodes i := a.nodes ⟨i.val, by omega⟩
  strictMono := by
    intro i j hij
    exact a.strictMono hij
  interior i := a.interior _
  initialSign := a.initialSign
  initialSign_eq := a.initialSign_eq
  error_eq i := a.error_eq ⟨i.val, by omega⟩

/-- Polynomial translation and a sign-reversing scalar preserve alternation.
The new error is written `(-ρ)*E`, as used when `ρ < 0`. -/
def Alternates.affineNeg {f : ℝ → ℝ} {n : ℕ} {p : ℝ[X]} {E : ℝ}
    (a : Alternates f n p E) (q : ℝ[X]) (ρ : ℝ) :
    Alternates (fun x => q.eval x + ρ * f x) n
      (q + C ρ * p) ((-ρ) * E) where
  nodes := a.nodes
  strictMono := a.strictMono
  interior := a.interior
  initialSign := -a.initialSign
  initialSign_eq := by
    rcases a.initialSign_eq with h | h <;> simp [h]
  error_eq i := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    calc
      q.eval (a.nodes i) + ρ * f (a.nodes i) -
          (q.eval (a.nodes i) + ρ * p.eval (a.nodes i)) =
          ρ * (f (a.nodes i) - p.eval (a.nodes i)) := by ring
      _ = ρ * (a.initialSign * (-1 : ℝ) ^ (i : ℕ) * E) := by rw [a.error_eq]
      _ = -a.initialSign * (-1 : ℝ) ^ (i : ℕ) * ((-ρ) * E) := by ring

def cubicLiftNodes {m : ℕ}
    (l c r : Fin (m + 2) → ℝ) (i : Fin (3 * m + 4)) : ℝ :=
  if h₁ : i.val < m + 2 then l ⟨i.val, h₁⟩
  else if h₂ : i.val < 2 * m + 3 then c ⟨2 * m + 2 - i.val, by omega⟩
  else r ⟨i.val - (2 * m + 2), by omega⟩

theorem cubicLiftNodes_interior {m : ℕ}
    (l c r : Fin (m + 2) → ℝ)
    (hl : ∀ i, l i ∈ Ioo (-1 : ℝ) (-1 / 2))
    (hc : ∀ i, c i ∈ Ioo (-1 / 2 : ℝ) (1 / 2))
    (hr : ∀ i, r i ∈ Ioo (1 / 2 : ℝ) 1)
    (i : Fin (3 * m + 4)) : cubicLiftNodes l c r i ∈ Ioo (-1 : ℝ) 1 := by
  unfold cubicLiftNodes
  split_ifs with h₁ h₂
  · exact ⟨(hl _).1, lt_trans (hl _).2 (by norm_num)⟩
  · exact ⟨lt_trans (by norm_num) (hc _).1, lt_trans (hc _).2 (by norm_num)⟩
  · exact ⟨lt_trans (by norm_num) (hr _).1, (hr _).2⟩

theorem cubicLiftNodes_strictMono {m : ℕ}
    (l c r : Fin (m + 2) → ℝ)
    (hl : ∀ i, l i ∈ Ioo (-1 : ℝ) (-1 / 2))
    (hc : ∀ i, c i ∈ Ioo (-1 / 2 : ℝ) (1 / 2))
    (hr : ∀ i, r i ∈ Ioo (1 / 2 : ℝ) 1)
    (hlmono : StrictMono l) (hcanti : StrictAnti c) (hrmono : StrictMono r) :
    StrictMono (cubicLiftNodes l c r) := by
  intro i j hij
  change i.val < j.val at hij
  by_cases hi₁ : i.val < m + 2
  · by_cases hj₁ : j.val < m + 2
    · simp only [cubicLiftNodes, hi₁, hj₁, dif_pos]
      exact hlmono hij
    · by_cases hj₂ : j.val < 2 * m + 3
      · simp only [cubicLiftNodes, hi₁, hj₁, hj₂, dif_pos]
        exact lt_trans (hl _).2 (hc _).1
      · simp only [cubicLiftNodes, hi₁, hj₁, hj₂, dif_pos]
        exact lt_trans (hl _).2 (lt_trans (by norm_num) (hr _).1)
  · by_cases hi₂ : i.val < 2 * m + 3
    · by_cases hj₁ : j.val < m + 2
      · omega
      · by_cases hj₂ : j.val < 2 * m + 3
        · simp only [cubicLiftNodes, hi₁, hi₂, hj₁, hj₂, dif_pos]
          apply hcanti
          change 2 * m + 2 - j.val < 2 * m + 2 - i.val
          omega
        · simp only [cubicLiftNodes, hi₁, hi₂, hj₁, hj₂, dif_pos]
          exact lt_trans (hc _).2 (hr _).1
    · have hj₁ : ¬j.val < m + 2 := by omega
      have hj₂ : ¬j.val < 2 * m + 3 := by omega
      simp only [cubicLiftNodes, hi₁, hi₂, hj₁, hj₂]
      apply hrmono
      change i.val - (2 * m + 2) < j.val - (2 * m + 2)
      omega

theorem neg_one_pow_eq_of_mod_two_eq {u v : ℕ} (h : u % 2 = v % 2) :
    (-1 : ℝ) ^ u = (-1 : ℝ) ^ v := by
  rw [neg_one_pow_eq_pow_mod_two u, neg_one_pow_eq_pow_mod_two v, h]

/-- Pullback through the cubic produces enough interior alternation contacts
for every degree up to `3*m+2`. -/
noncomputable def Alternates.comp_cubic {g : ℝ → ℝ} {m : ℕ} {p : ℝ[X]} {E : ℝ}
    (a : Alternates g m p E) :
    Alternates (g ∘ cubic) (3 * m + 2) (p.comp cubicPoly) E := by
  choose l hl hleq using (fun i => exists_cubic_left_preimage (a.interior i))
  choose c hc hceq using (fun i => exists_cubic_middle_preimage (a.interior i))
  choose r hr hreq using (fun i => exists_cubic_right_preimage (a.interior i))
  have hlmono : StrictMono l := by
    intro i j hij
    by_contra hn
    have hle := cubic_strictMono_left.monotoneOn
      (Ioo_subset_Icc_self (hl j)) (Ioo_subset_Icc_self (hl i)) (le_of_not_gt hn)
    rw [hleq, hleq] at hle
    exact not_le_of_gt (a.strictMono hij) hle
  have hcanti : StrictAnti c := by
    intro i j hij
    by_contra hn
    have hle := cubic_strictAnti_middle.antitoneOn
      (Ioo_subset_Icc_self (hc i)) (Ioo_subset_Icc_self (hc j)) (le_of_not_gt hn)
    rw [hceq, hceq] at hle
    exact not_le_of_gt (a.strictMono hij) hle
  have hrmono : StrictMono r := by
    intro i j hij
    by_contra hn
    have hle := cubic_strictMono_right.monotoneOn
      (Ioo_subset_Icc_self (hr j)) (Ioo_subset_Icc_self (hr i)) (le_of_not_gt hn)
    rw [hreq, hreq] at hle
    exact not_le_of_gt (a.strictMono hij) hle
  refine {
    nodes := cubicLiftNodes l c r
    strictMono := cubicLiftNodes_strictMono l c r hl hc hr hlmono hcanti hrmono
    interior := cubicLiftNodes_interior l c r hl hc hr
    initialSign := a.initialSign
    initialSign_eq := a.initialSign_eq
    error_eq := ?_
  }
  intro i
  simp only [Function.comp_apply, Polynomial.eval_comp, eval_cubicPoly]
  unfold cubicLiftNodes
  split_ifs with h₁ h₂
  · rw [hleq]
    exact a.error_eq ⟨i.val, h₁⟩
  · rw [hceq]
    have hparity : (2 * m + 2 - i.val) % 2 = i.val % 2 := by omega
    have hsign := neg_one_pow_eq_of_mod_two_eq hparity
    simpa only [hsign] using a.error_eq ⟨2 * m + 2 - i.val, by omega⟩
  · rw [hreq]
    have hparity : (i.val - (2 * m + 2)) % 2 = i.val % 2 := by omega
    have hsign := neg_one_pow_eq_of_mod_two_eq hparity
    simpa only [hsign] using a.error_eq ⟨i.val - (2 * m + 2), by omega⟩

/-- Cubic pullback preserves a uniform error bound on the interval. -/
theorem HasErrorBound.comp_cubic {g : ℝ → ℝ} {p : ℝ[X]} {E : ℝ}
    (h : HasErrorBound g p E) : HasErrorBound (g ∘ cubic) (p.comp cubicPoly) E := by
  intro x hx
  simpa only [Function.comp_apply, Polynomial.eval_comp, eval_cubicPoly] using
    h (cubic x) (cubic_maps_interval hx)

/-- The uniform-bound counterpart of `Alternates.affineNeg`. -/
theorem HasErrorBound.affineNeg {f : ℝ → ℝ} {p : ℝ[X]} {E : ℝ}
    (h : HasErrorBound f p E) (q : ℝ[X]) {ρ : ℝ} (hρ : ρ ≤ 0) :
    HasErrorBound (fun x => q.eval x + ρ * f x)
      (q + C ρ * p) ((-ρ) * E) := by
  intro x hx
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have heq : q.eval x + ρ * f x - (q.eval x + ρ * p.eval x) =
      ρ * (f x - p.eval x) := by ring
  rw [heq, abs_mul, abs_of_nonpos hρ]
  exact mul_le_mul_of_nonneg_left (h x hx) (neg_nonneg.mpr hρ)

/-- An alternation only depends on function values inside the approximation
interval. This is useful for a self-similarity identity proved on that interval. -/
def Alternates.congrOn {f g : ℝ → ℝ} {n : ℕ} {p : ℝ[X]} {E : ℝ}
    (a : Alternates f n p E)
    (h : ∀ x ∈ Icc (-1 : ℝ) 1, f x = g x) : Alternates g n p E where
  nodes := a.nodes
  strictMono := a.strictMono
  interior := a.interior
  initialSign := a.initialSign
  initialSign_eq := a.initialSign_eq
  error_eq i := by
    rw [← h _ (Ioo_subset_Icc_self (a.interior i))]
    exact a.error_eq i

/-- Uniform error bounds also depend only on values inside the interval. -/
theorem HasErrorBound.congrOn {f g : ℝ → ℝ} {p : ℝ[X]} {E : ℝ}
    (hf : HasErrorBound f p E)
    (h : ∀ x ∈ Icc (-1 : ℝ) 1, f x = g x) : HasErrorBound g p E := by
  intro x hx
  rw [← h x hx]
  exact hf x hx

end Lorentz
