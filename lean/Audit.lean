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
#print axioms Lorentz.Plateau.exists_relative_gap_bound
#print axioms Lorentz.Plateau.finite_contact_persistence
#print axioms Lorentz.Plateau.FiniteTools.finite_orbit_values
#print axioms Lorentz.Plateau.Certificates.Odd.exists_root
#print axioms Lorentz.Plateau.Certificates.Even.exists_root
#print axioms Lorentz.Plateau.finite_roots_simple
#print axioms Lorentz.Plateau.finite_seed_certificate
#print axioms Lorentz.Plateau.odd_plateau_counterexample
#print axioms Lorentz.Plateau.even_plateau_counterexample
#print axioms LorentzSubmission.odd_plateau_counterexample
#print axioms LorentzSubmission.even_plateau_counterexample
