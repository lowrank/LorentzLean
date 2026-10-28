module

public import Lorentz.Plateau.Certificates.OddData
public import Lorentz.Plateau.Certificates.Checker
public import Lorentz.Plateau.Certificates.OddContacts
public import Lorentz.Plateau.Certificates.OddValues
public import Lorentz.Plateau.Certificates.OddSlacks0
public import Lorentz.Plateau.SeedCertificate

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Odd

def contactIndex0 (j : Fin 6) : Fin 18 :=
  ⟨gridIndex 0 j, (show ∀ k : Fin 6, gridIndex 0 k < 18 by decide +kernel) j⟩

def chosen0 (j : Fin 4) : Fin 6 :=
  ⟨(activeRows.getD 0 []).getD j 0,
    (show ∀ k : Fin 4, (activeRows.getD 0 []).getD k 0 < 6 by decide +kernel) j⟩

theorem seed_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      HasPlateauCertificate (familyFunction false (forcing z) ε) 2 := by
  have hsg (j : Fin 6) : (gridSign 0 j : ℝ) = 1 ∨ (gridSign 0 j : ℝ) = -1 := by
    exact_mod_cast (show ∀ k : Fin 6, gridSign 0 k = 1 ∨ gridSign 0 k = -1 by decide +kernel) j
  have hs (j : Fin 6) := all_slacks_0 z hm j
  have hv (j : Fin 6) : orbitSeries (forcing z).eval (-3 / 5)
      (node z (gridIndex 0 j)) = value z (gridIndex 0 j) :=
    series_at_node z hm hl hu (contactIndex0 j)
  apply finite_seed_certificate false false (forcing z) (correction 0 z) (slope z 0)
    (fun j : Fin 6 ↦ node z (gridIndex 0 j)) (fun j ↦ (gridSign 0 j : ℝ))
    ((nodes_strictMono z hl hu).comp (show StrictMono contactIndex0 by decide +kernel))
    (fun j ↦ node_bounds z hl hu (contactIndex0 j)) hsg (contacts_0 z hm hl hu)
    ?_ ?_ ?_ chosen0 (by decide +kernel) (-1) (by norm_num) ?_ ?_ ?_ ?_
  · intro hp
    have he := congrArg (fun p : Polynomial ℝ ↦ p.eval 1) hp
    norm_num [contactPolynomial_eval, pullback_eval, seedMap_eval_false, seedMap_eval_true, cubic] at he
  · unfold contactPolynomial pullback seedMap Certificate.sixthPoly Certificate.cubicPoly Lorentz.cubicPoly
    simp only [Bool.false_eq_true, ↓reduceIte, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp, Polynomial.natCast_comp, Polynomial.X_comp]
    compute_degree <;> norm_num
  · intro j
    have hh := slacks_nonneg_0 z hl hu j
    have hid := hs j
    rw [hv j]
    linarith
  · intro j
    exact_mod_cast (show ∀ k : Fin 4, gridSign 0 (chosen0 k) =
      (-1 : ℚ) * (-1 : ℚ) ^ (k : ℕ) by decide +kernel) j
  · intro j
    have hid := hs (chosen0 j)
    have hz : ((slackRows.getD 0 []).getD (chosen0 j) []) = [] :=
      (show ∀ k : Fin 4, ((slackRows.getD 0 []).getD (chosen0 k) []) = [] by decide +kernel) j
    rw [hz] at hid
    rw [hv (chosen0 j)]
    change _ = 0 at hid
    linarith
  · exact lt_of_le_of_lt (FiniteTools.fieldPolynomial_degree (correctionRows.getD 0 []) z) (by decide +kernel)
  · unfold basePolynomial seedMap Certificate.sixthPoly Certificate.cubicPoly Lorentz.cubicPoly
    norm_num only [Bool.false_eq_true, ↓reduceIte]
    compute_degree <;> norm_num

end Lorentz.Plateau.Certificates.Odd
