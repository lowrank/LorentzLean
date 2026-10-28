module

public import Lorentz.PerturbationContacts
public import Lorentz.CompactStability
public import Lorentz.AllDegrees

@[expose] public section

namespace Lorentz.Construction

open Polynomial Set

noncomputable def candidateFunction (z ε x : ℝ) : ℝ :=
  F x + ε * H (Certificate.beta z) x

noncomputable def candidatePolynomial (z ε : ℝ) (n : ℕ) : ℝ[X] :=
  basePolynomial n + C ε * Certificate.correctionPoly n z

noncomputable def candidateError (z ε : ℝ) (n : ℕ) : ℝ :=
  baseError n + ε * Certificate.slope n z

lemma candidatePolynomial_degree (z ε : ℝ) (n : ℕ) :
    (candidatePolynomial z ε n).natDegree ≤ n := by
  apply (Polynomial.natDegree_add_le _ _).trans
  exact max_le (basePolynomial_degree n)
    ((Polynomial.natDegree_C_mul_le _ _).trans (Certificate.correctionPoly_degree n z))

lemma candidatePolynomial_zero (z ε : ℝ) (n : ℕ) :
    (candidatePolynomial z ε n).eval 0 = 0 := by
  simp [candidatePolynomial, basePolynomial_zero, Certificate.correctionPoly_zero]

lemma candidate_error_eq (z ε : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ interval) :
    candidateFunction z ε x - (candidatePolynomial z ε n).eval x =
      baseResidual n x + ε * perturbationResidual z n x := by
  have h := baseResidual_eq n hx
  simp only [candidateFunction, candidatePolynomial, eval_add, eval_mul, eval_C,
    perturbationResidual]
  linarith

lemma local_contact_conditions (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : ℕ) {x : ℝ} (hx : x ∈ contacts z n) :
    ∃ c > 0, ∃ δ > 0, ∃ L ≥ 0, ∀ y ∈ interval, |y - x| ≤ δ →
      c * |y - x| ≤ baseError n - |baseResidual n y| ∧
      baseError n / 2 ≤ contactSign n x * baseResidual n y ∧
      |perturbationResidual z n y - perturbationResidual z n x| ≤ L * |y - x| := by
  obtain ⟨c, hc, δg, hδg, hgap⟩ := baseResidual_local_cusp z hm n hx
  obtain ⟨L, hL, δr, hδr, hlip⟩ := perturbationResidual_local_lipschitz z hm hl hu n hx
  obtain ⟨δs, hδs, hsign⟩ := LocalComposition.exists_local_signed_half
    (baseResidual_continuousOn n _ (contacts_subset z n hl hu hx))
    (contactSign_values z hm hl hu n hx) (baseError_pos n)
    (contact_signed_value z hm hl hu n hx)
  refine ⟨c, hc, min δg (min δr δs), lt_min hδg (lt_min hδr hδs), L, hL, ?_⟩
  intro y hy hnear
  exact ⟨hgap y hy (hnear.trans (min_le_left _ _)),
    hsign y hy (hnear.trans ((min_le_right _ _).trans (min_le_right _ _))),
    hlip y hy (hnear.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩

lemma exists_base_error_threshold (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : ℕ) (hn : n < 7) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      0 < candidateError z ε n ∧
      HasErrorBound (candidateFunction z ε) (candidatePolynomial z ε n) (candidateError z ε n) := by
  obtain ⟨ε₀, hε₀, hbound⟩ := Stability.finite_compact_contact_persistence
    (contacts z n) (contacts_nonempty z n) (fun _ hx => contacts_subset z n hl hu hx)
    (baseResidual_continuousOn n) (perturbationResidual_continuousOn z n) (baseError_pos n)
    (fun _ hx => contactSign_values z hm hl hu n hx)
    (fun _ hx hnot => baseResidual_strict z hm hl hu n hx hnot)
    (fun _ hx => local_contact_conditions z hm hl hu n hx)
    (fun _ hx => perturbationResidual_contact_bound z hm hl hu n hn hx)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨hpositive, herror⟩ := hbound ε hε hsmall
  refine ⟨hpositive, ?_⟩
  intro x hx
  rw [candidate_error_eq z ε n hx]
  exact herror x hx

lemma candidate_alternates (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (ε : ℝ) (n : ℕ) (hn : n < 7) :
    Nonempty (Alternates (candidateFunction z ε) n (candidatePolynomial z ε n)
      (candidateError z ε n)) := by
  apply Certificate.alternates_of_node_errors z hl hu n hn
  intro k
  let nf : Fin 7 := ⟨n, hn⟩
  have hj := Certificate.active_index_bound nf k
  have hmem : Certificate.node z (Certificate.gridIndex n (Certificate.activeIndex n k)) ∈
      contacts z n := by
    rw [mem_contacts_iff]
    exact ⟨_, hj, rfl⟩
  rw [candidate_error_eq z ε n (contacts_subset z n hl hu hmem),
    baseResidual_at_grid z hm hl hu n _ hj]
  have hr := perturbationResidual_active_equality z hm hl hu nf k
  change perturbationResidual z n
    (Certificate.node z (Certificate.gridIndex n (Certificate.activeIndex n k))) = _ at hr
  rw [hr]
  dsimp [candidateError]
  ring

lemma exists_base_certificate_threshold (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : ℕ) (hn : n < 7) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      HasVanishingCertificate (candidateFunction z ε) n := by
  obtain ⟨ε₀, hε₀, hbound⟩ := exists_base_error_threshold z hm hl hu n hn
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨hpositive, herror⟩ := hbound ε hε hsmall
  exact ⟨candidatePolynomial z ε n, candidateError z ε n,
    candidatePolynomial_degree z ε n, candidatePolynomial_zero z ε n,
    hpositive, herror, candidate_alternates z hm hl hu ε n hn⟩

theorem exists_seven_base_certificates (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ)) :
    ∃ ε > 0, ∀ n < 7, HasVanishingCertificate (candidateFunction z ε) n := by
  classical
  have h : ∀ n : Fin 7, ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      HasVanishingCertificate (candidateFunction z ε) n :=
    fun n => exists_base_certificate_threshold z hm hl hu n n.isLt
  choose δ hδ hsmall using h
  let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hε : 0 < ε := by
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun n _ => hδ n)
  refine ⟨ε, hε, ?_⟩
  intro n hn
  exact hsmall ⟨n, hn⟩ ε hε.le
    (Finset.inf'_le δ (Finset.mem_univ (⟨n, hn⟩ : Fin 7)))

end Lorentz.Construction
