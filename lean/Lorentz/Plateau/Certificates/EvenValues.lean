module

public import Lorentz.Plateau.Certificates.EvenData
public import Lorentz.Plateau.Certificates.Checker
public import Lorentz.Plateau.Certificates.EvenBounds
public import Lorentz.Plateau.Certificates.EvenCubicGrid
public import Lorentz.Plateau.Certificates.EvenRecurrences

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Even

def nextNode (j : Fin 36) : Fin 36 :=
  ⟨cubicMap.getD j 0, (show ∀ k : Fin 36, cubicMap.getD k 0 < 36 by decide +kernel) j⟩

theorem series_at_node (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))
    (j : Fin 36) : orbitSeries (forcing z).eval (-3 / 5) (node z j) = value z j := by
  exact FiniteTools.finite_orbit_values (forcing z) (by norm_num)
    (fun k : Fin 36 ↦ node z k) (fun k ↦ value z k) nextNode
    (fun k ↦ Set.Ioo_subset_Icc_self (node_bounds z hl hu k))
    (cubic_at_node z hm) (all_recurrences z hm) j

end Lorentz.Plateau.Certificates.Even
