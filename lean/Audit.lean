module

public import Lorentz
public import Solution

@[expose] public section

/-! The dependency list below should contain only Lean's standard logical
axioms: `propext`, `Classical.choice`, and `Quot.sound`. -/

#check Lorentz.Construction.lorentz_counterexample
#print axioms Lorentz.Construction.lorentz_counterexample
#print axioms Lorentz.all_degrees_of_selfsimilar
#print axioms Lorentz.Alternates.isBest
#print axioms Lorentz.Certificate.gridPerturbation_eq_actualH
#print axioms Lorentz.Certificate.PolynomialCertificate.checked_slack
#print axioms Lorentz.Stability.signed_contact_persistence_bound
#print axioms LorentzSubmission.common_origin_counterexample
#print axioms Lorentz.Plateau.all_plateaus_of_selfsimilar
#print axioms Lorentz.Plateau.selfsimilar_unique
#print axioms Lorentz.Plateau.series_sub_polynomial
#print axioms Lorentz.Plateau.Baseline.resolvent
#print axioms Lorentz.Plateau.Baseline.even_orbit_gap
