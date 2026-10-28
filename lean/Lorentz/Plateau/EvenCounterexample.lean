module

public import Lorentz.Plateau.Certificates.EvenSeed0
public import Lorentz.Plateau.Certificates.EvenSeed1
public import Lorentz.Plateau.Certificates.EvenSeed2
public import Lorentz.Plateau.Certificates.EvenSeed3
public import Lorentz.Plateau.Certificates.EvenAsymmetry

@[expose] public section

namespace Lorentz.Plateau

open Polynomial Set Certificates.Even

/-- A noneven continuous function whose best approximants coincide at every
pair of degrees `2k` and `2k+1`. -/
theorem even_plateau_counterexample :
    ∃ f : ℝ → ℝ, ContinuousOn f interval ∧
      (∃ x ∈ interval, f (-x) ≠ f x) ∧
      ∀ k : ℕ, ∃ p : ℝ[X], IsBest f (2 * k) p ∧ IsBest f (2 * k + 1) p ∧
        ∀ q r : ℝ[X], IsBest f (2 * k) q → IsBest f (2 * k + 1) r → q = r := by
  obtain ⟨z, hl, hu, hm⟩ := exists_root
  obtain ⟨e0, he0, h0⟩ := seed_0 z hm hl hu
  obtain ⟨e1, he1, h1⟩ := seed_1 z hm hl hu
  obtain ⟨e2, he2, h2⟩ := seed_2 z hm hl hu
  obtain ⟨e3, he3, h3⟩ := seed_3 z hm hl hu
  let ε := min (min e0 e1) (min e2 e3) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hb0 : ε ≤ e0 := by
    dsimp [ε]; linarith [min_le_left (min e0 e1) (min e2 e3), min_le_left e0 e1]
  have hb1 : ε ≤ e1 := by
    dsimp [ε]; linarith [min_le_left (min e0 e1) (min e2 e3), min_le_right e0 e1]
  have hb2 : ε ≤ e2 := by
    dsimp [ε]; linarith [min_le_right (min e0 e1) (min e2 e3), min_le_left e2 e3]
  have hb3 : ε ≤ e3 := by
    dsimp [ε]; linarith [min_le_right (min e0 e1) (min e2 e3), min_le_right e2 e3]
  let f := familyFunction true (forcing z) ε
  have hbase : ∀ n, 0 < n → n < 9 → n % 2 = 1 → HasPlateauCertificate f n := by
    intro n hn hc hp
    have hn' : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 := by omega
    rcases hn' with rfl | rfl | rfl | rfl
    · exact h0 ε hε.le hb0
    · exact h1 ε hε.le hb1
    · exact h2 ε hε.le hb2
    · exact h3 ε hε.le hb3
  have hdegree : (seedMap true + C ε * forcing z).natDegree < 9 := by
    apply lt_of_le_of_lt (natDegree_add_le _ _)
    apply max_lt
    · unfold seedMap Certificate.sixthPoly Certificate.cubicPoly
      simp only [↓reduceIte]
      compute_degree <;> norm_num
    · exact lt_of_le_of_lt (natDegree_C_mul_le _ _)
        (lt_of_le_of_lt (forcing_degree z) (by decide))
  have hall := all_plateaus_of_selfsimilar (cut := 9) (parity := 1) (by decide)
    hdegree (by norm_num : (-3 : ℝ) / 5 < 0)
    (fun _ hx ↦ family_equation true (forcing z) ε hx) hbase
  refine ⟨f, family_continuous true (forcing z) ε, ?_, ?_⟩
  · refine ⟨1, by constructor <;> norm_num, ?_⟩
    intro heq
    have hd := family_even_defect (forcing z) ε
    have hn : ε * (5 / 8) * ((forcing z).eval 1 - (forcing z).eval (-1)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hε.ne' (by norm_num)) (forcing_asymmetry_ne z hm hl hu)
    apply hn
    change f 1 - f (-1) = _ at hd
    change f (-1) = f 1 at heq
    linarith
  · intro k
    have h := (hall (2 * k + 1) (by omega) (by omega)).best_pair
    simpa using h

end Lorentz.Plateau
