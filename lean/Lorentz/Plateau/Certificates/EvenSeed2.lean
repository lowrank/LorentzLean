module

public import Lorentz.Plateau.Certificates.EvenData
public import Lorentz.Plateau.Certificates.Checker
public import Lorentz.Plateau.Certificates.EvenContacts
public import Lorentz.Plateau.Certificates.EvenValues
public import Lorentz.Plateau.Certificates.EvenSlacks2
public import Lorentz.Plateau.SeedCertificate

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Even

def contactIndex2 (j : Fin 12) : Fin 36 :=
  ⟨gridIndex 2 j, (show ∀ k : Fin 12, gridIndex 2 k < 36 by decide +kernel) j⟩

def chosen2 (j : Fin 7) : Fin 12 :=
  ⟨(activeRows.getD 2 []).getD j 0,
    (show ∀ k : Fin 7, (activeRows.getD 2 []).getD k 0 < 12 by decide +kernel) j⟩

theorem seed_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      HasPlateauCertificate (familyFunction true (forcing z) ε) 5 := by
  have hsg (j : Fin 12) : (gridSign 2 j : ℝ) = 1 ∨ (gridSign 2 j : ℝ) = -1 := by
    exact_mod_cast (show ∀ k : Fin 12, gridSign 2 k = 1 ∨ gridSign 2 k = -1 by decide +kernel) j
  have hs (j : Fin 12) := all_slacks_2 z hm j
  have hv (j : Fin 12) : orbitSeries (forcing z).eval (-3 / 5)
      (node z (gridIndex 2 j)) = value z (gridIndex 2 j) :=
    series_at_node z hm hl hu (contactIndex2 j)
  apply finite_seed_certificate true false (forcing z) (correction 2 z) (slope z 2)
    (fun j : Fin 12 ↦ node z (gridIndex 2 j)) (fun j ↦ (gridSign 2 j : ℝ))
    ((nodes_strictMono z hl hu).comp (show StrictMono contactIndex2 by decide +kernel))
    (fun j ↦ node_bounds z hl hu (contactIndex2 j)) hsg (contacts_2 z hm hl hu)
    ?_ ?_ ?_ chosen2 (by decide +kernel) (1) (by norm_num) ?_ ?_ ?_ ?_
  · intro hp
    have he := congrArg (fun p : Polynomial ℝ ↦ p.eval 1) hp
    norm_num [contactPolynomial_eval, pullback_eval, seedMap_eval_false, seedMap_eval_true, cubic] at he
  · unfold contactPolynomial pullback seedMap Certificate.sixthPoly Certificate.cubicPoly Lorentz.cubicPoly
    simp only [Bool.false_eq_true, ↓reduceIte, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp, Polynomial.natCast_comp, Polynomial.X_comp]
    compute_degree <;> norm_num
  · intro j
    have hh := slacks_nonneg_2 z hl hu j
    have hid := hs j
    rw [hv j]
    linarith
  · intro j
    exact_mod_cast (show ∀ k : Fin 7, gridSign 2 (chosen2 k) =
      (1 : ℚ) * (-1 : ℚ) ^ (k : ℕ) by decide +kernel) j
  · intro j
    have hid := hs (chosen2 j)
    have hz : ((slackRows.getD 2 []).getD (chosen2 j) []) = [] :=
      (show ∀ k : Fin 7, ((slackRows.getD 2 []).getD (chosen2 k) []) = [] by decide +kernel) j
    rw [hz] at hid
    rw [hv (chosen2 j)]
    change _ = 0 at hid
    linarith
  · exact lt_of_le_of_lt (FiniteTools.fieldPolynomial_degree (correctionRows.getD 2 []) z) (by decide +kernel)
  · unfold basePolynomial seedMap Certificate.sixthPoly Certificate.cubicPoly Lorentz.cubicPoly
    norm_num only [Bool.false_eq_true, ↓reduceIte]
    compute_degree <;> norm_num

end Lorentz.Plateau.Certificates.Even
