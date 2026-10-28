module

public import Lorentz.ContactGeometry
public import Lorentz.Perturbation
public import Lorentz.CertificatePerturbation
public import Lorentz.CertificatePolynomials

@[expose] public section

namespace Lorentz.Construction

open Polynomial Set

lemma H_two_step (β : ℝ) {x : ℝ} (hx : x ∈ interval) :
    H β x = (ForcingPolynomials.pairedForcingPoly β).eval x +
      H β (Lorentz.cubic (Lorentz.cubic x)) / 9 :=
  H_paired_equation β hx

lemma H_local_lipschitz_half_square (β : ℝ) {w : ℝ} (hw : w ^ 2 = (1 : ℝ) / 2) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ interval, |x - w| ≤ r →
      |H β x - H β w| ≤ C * |x - w| := by
  rcases (Baseline.square_half_iff w).mp hw with rfl | rfl
  · exact H_local_lipschitz_a β
  · exact H_local_lipschitz_neg_a β

lemma H_local_lipschitz_of_representation (β : ℝ) (q : ℝ[X])
    {P : ℝ → ℝ} {ρ d x : ℝ} (hx : x ∈ interval)
    (hP : HasDerivAt P d x)
    (hmap : ∀ y ∈ interval, P y ∈ interval)
    (hroot : (P x) ^ 2 = (1 : ℝ) / 2)
    (hrep : ∀ y ∈ interval, H β y = q.eval y + ρ * H β (P y)) :
    ∃ L ≥ 0, ∃ δ > 0, ∀ y ∈ interval, |y - x| ≤ δ →
      |H β y - H β x| ≤ L * |y - x| := by
  obtain ⟨r, hr, C, hC, hlip⟩ := H_local_lipschitz_half_square β hroot
  obtain ⟨L, hL, δ, hδ, hcomp⟩ := LocalComposition.local_lipschitz_comp
    hP rfl hmap hC.le hr hlip
  obtain ⟨L', hL', δ', hδ', haffine⟩ := LocalComposition.local_lipschitz_affine
    (ρ := ρ) (q.hasDerivAt x) hL hδ hcomp
  refine ⟨L', hL', δ', hδ', ?_⟩
  intro y hy hnear
  simpa only [← hrep y hy, ← hrep x hx] using haffine y hy hnear

lemma H_local_lipschitz_at_contact (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : ℕ) {x : ℝ} (hx : x ∈ contacts z n) :
    ∃ L ≥ 0, ∃ δ > 0, ∀ y ∈ interval, |y - x| ≤ δ →
      |H (Certificate.beta z) y - H (Certificate.beta z) x| ≤ L * |y - x| := by
  have hxI := contacts_subset z n hl hu hx
  have hroot := contact_root z hm n hx
  by_cases hn : n < 3
  · rw [if_pos hn] at hroot
    apply H_local_lipschitz_of_representation (Certificate.beta z)
      (ForcingPolynomials.hPoly (Certificate.beta z)) (ρ := -1 / 3)
      hxI (Baseline.cubic_hasDerivAt x) (fun _ hy => cubic_maps_interval hy) hroot
    intro y hy
    rw [H_equation _ hy]
    ring
  · rw [if_neg hn] at hroot
    apply H_local_lipschitz_of_representation (Certificate.beta z)
      (ForcingPolynomials.pairedForcingPoly (Certificate.beta z)) (ρ := 1 / 9)
      hxI (Baseline.ninth_hasDerivAt x)
      (fun _ hy => cubic_maps_interval (cubic_maps_interval hy)) hroot
    intro y hy
    rw [H_two_step _ hy]
    ring

noncomputable def perturbationResidual (z : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  H (Certificate.beta z) x - (Certificate.correctionPoly n z).eval x

lemma perturbationResidual_continuousOn (z : ℝ) (n : ℕ) :
    ContinuousOn (perturbationResidual z n) interval :=
  (H_continuousOn _).sub (Certificate.correctionPoly n z).continuous.continuousOn

lemma perturbationResidual_local_lipschitz (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : ℕ) {x : ℝ} (hx : x ∈ contacts z n) :
    ∃ L ≥ 0, ∃ δ > 0, ∀ y ∈ interval, |y - x| ≤ δ →
      |perturbationResidual z n y - perturbationResidual z n x| ≤ L * |y - x| := by
  obtain ⟨L, hL, δ, hδ, hlip⟩ := H_local_lipschitz_at_contact z hm hl hu n hx
  obtain ⟨L', hL', δ', hδ', h⟩ := LocalComposition.local_lipschitz_affine
    (ρ := 1) ((-Certificate.correctionPoly n z).hasDerivAt x) hL hδ hlip
  refine ⟨L', hL', δ', hδ', ?_⟩
  intro y hy hnear
  have heq (w : ℝ) : (-Certificate.correctionPoly n z).eval w +
      1 * H (Certificate.beta z) w = perturbationResidual z n w := by
    simp only [Polynomial.eval_neg, one_mul, perturbationResidual]
    ring
  simpa only [heq] using h y hy hnear

lemma perturbSeed_eq_hPoly (z x : ℝ) :
    Certificate.perturbSeed z x = (ForcingPolynomials.hPoly (Certificate.beta z)).eval x := by
  rw [ForcingPolynomials.eval_hPoly]
  rfl

lemma H_at_grid (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (j : Fin 18) : H (Certificate.beta z) (Certificate.node z j) =
      Certificate.gridPerturbation z j := by
  apply Certificate.gridPerturbation_eq_actualH z hm hl hu (H (Certificate.beta z)) ?_ j
  intro x hx
  rw [perturbSeed_eq_hPoly]
  exact H_equation _ hx

lemma perturbationResidual_contact_bound (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : ℕ) (hn : n < 7) {x : ℝ} (hx : x ∈ contacts z n) :
    contactSign n x * perturbationResidual z n x ≤ Certificate.slope n z := by
  obtain ⟨j, hj, rfl⟩ := (mem_contacts_iff z n x).mp hx
  rw [contactSign_at_grid z hm hl hu n j hj, perturbationResidual,
    Certificate.correctionPoly_eval]
  have h := H_at_grid z hm hl hu ⟨_, Certificate.gridIndex_bound n j hj⟩
  change H (Certificate.beta z) (Certificate.node z (Certificate.gridIndex n j)) = _ at h
  rw [h]
  exact Certificate.grid_inequality z hm hl hu n j hn hj

lemma perturbationResidual_active_equality (z : ℝ) (hm : Certificate.modulus z = 0)
    (hl : (Certificate.rootLower : ℝ) ≤ z) (hu : z ≤ (Certificate.rootUpper : ℝ))
    (n : Fin 7) (k : Fin (n.val + 2)) :
    perturbationResidual z n (Certificate.activeNode z n k) =
      Certificate.gridSign n (Certificate.activeIndex n k) * Certificate.slope n z := by
  have hj := Certificate.active_index_bound n k
  have hH := H_at_grid z hm hl hu
    ⟨_, Certificate.gridIndex_bound n (Certificate.activeIndex n k) hj⟩
  change H (Certificate.beta z) (Certificate.activeNode z n k) = _ at hH
  have heq := Certificate.active_equality z hm n k
  rw [perturbationResidual, Certificate.correctionPoly_eval, hH]
  dsimp [Certificate.activeNode] at *
  rcases Certificate.gridSign_one_or_neg_one n (Certificate.activeIndex n k) with hs | hs
  · rw [hs] at heq ⊢
    linarith
  · rw [hs] at heq ⊢
    linarith

end Lorentz.Construction
