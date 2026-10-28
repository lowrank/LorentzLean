module

public import Lorentz.Plateau.Certificates.OddSeed0
public import Lorentz.Plateau.Certificates.OddSeed1
public import Lorentz.Plateau.Certificates.OddSeed2
public import Lorentz.Plateau.Certificates.OddAsymmetry

@[expose] public section

namespace Lorentz.Plateau

open Polynomial Set Certificates.Odd

/-- A nonodd continuous function, zero at the origin, whose best approximants
coincide at every pair of degrees `2k+1` and `2k+2`. -/
theorem odd_plateau_counterexample :
    ∃ f : ℝ → ℝ, ContinuousOn f interval ∧ f 0 = 0 ∧
      (∃ x ∈ interval, f (-x) ≠ -f x) ∧
      ∀ k : ℕ, ∃ p : ℝ[X], IsBest f (2 * k + 1) p ∧ IsBest f (2 * k + 2) p ∧
        ∀ q r : ℝ[X], IsBest f (2 * k + 1) q → IsBest f (2 * k + 2) r → q = r := by
  obtain ⟨z, hl, hu, hm⟩ := exists_root
  obtain ⟨e0, he0, h0⟩ := seed_0 z hm hl hu
  obtain ⟨e1, he1, h1⟩ := seed_1 z hm hl hu
  obtain ⟨e2, he2, h2⟩ := seed_2 z hm hl hu
  let ε := min e0 (min e1 e2) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hb0 : ε ≤ e0 := by dsimp [ε]; linarith [min_le_left e0 (min e1 e2)]
  have hb1 : ε ≤ e1 := by
    dsimp [ε]; linarith [min_le_right e0 (min e1 e2), min_le_left e1 e2]
  have hb2 : ε ≤ e2 := by
    dsimp [ε]; linarith [min_le_right e0 (min e1 e2), min_le_right e1 e2]
  let f := familyFunction false (forcing z) ε
  have hbase : ∀ n, 0 < n → n < 8 → n % 2 = 0 → HasPlateauCertificate f n := by
    intro n hn hc hp
    have hn' : n = 2 ∨ n = 4 ∨ n = 6 := by omega
    rcases hn' with rfl | rfl | rfl
    · exact h0 ε hε.le hb0
    · exact h1 ε hε.le hb1
    · exact h2 ε hε.le hb2
  have hdegree : (seedMap false + C ε * forcing z).natDegree < 8 := by
    apply lt_of_le_of_lt (natDegree_add_le _ _)
    apply max_lt
    · unfold seedMap cubicPoly
      simp only [Bool.false_eq_true, ↓reduceIte]
      compute_degree <;> norm_num
    · exact lt_of_le_of_lt (natDegree_C_mul_le _ _)
        (lt_of_le_of_lt (forcing_degree z) (by decide))
  have hall := all_plateaus_of_selfsimilar (cut := 8) (parity := 0) (by decide)
    hdegree (by norm_num : (-3 : ℝ) / 5 < 0)
    (fun _ hx ↦ family_equation false (forcing z) ε hx) hbase
  refine ⟨f, family_continuous false (forcing z) ε, family_zero _ (forcing_zero z) ε, ?_, ?_⟩
  · refine ⟨1, by constructor <;> norm_num, ?_⟩
    intro heq
    have hd := family_odd_defect (forcing z) ε
    have hn : ε * (5 / 8) * ((forcing z).eval 1 + (forcing z).eval (-1)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hε.ne' (by norm_num)) (forcing_asymmetry_ne z hm hl hu)
    apply hn
    change f 1 + f (-1) = _ at hd
    change f (-1) = -f 1 at heq
    linarith
  · intro k
    have h := (hall (2 * k + 2) (by omega) (by omega)).best_pair
    simpa using h

end Lorentz.Plateau
