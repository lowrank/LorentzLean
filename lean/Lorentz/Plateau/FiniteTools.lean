module

public import Lorentz.PolynomialCertificate
public import Lorentz.Plateau.SeriesTools

@[expose] public section

/-! Shared algebraic and finite-orbit certificate interfaces, with proved soundness. -/

namespace Lorentz.Plateau.FiniteTools

open Set Polynomial
open Lorentz.Certificate.PolynomialCertificate

def evalRational : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: cs, z => c + z * evalRational cs z

lemma cast_evalRational (cs : List ℚ) (z : ℚ) :
    (evalRational cs z : ℝ) = Certificate.eval cs z := by
  induction cs with
  | nil => simp [evalRational, Certificate.eval]
  | cons c cs ih => simp [evalRational, Certificate.eval, ih]

lemma eval_continuous (cs : List ℚ) : Continuous (Certificate.eval cs) := by
  induction cs with
  | nil => exact continuous_const
  | cons c cs ih =>
    exact continuous_const.add (continuous_id.mul ih)

lemma exists_root (m : List ℚ) (l u : ℚ) (hlu : l ≤ u)
    (hl : evalRational m l ≤ 0) (hu : 0 ≤ evalRational m u) :
    ∃ z : ℝ, (l : ℝ) ≤ z ∧ z ≤ (u : ℝ) ∧ Certificate.eval m z = 0 := by
  have hle : (l : ℝ) ≤ (u : ℝ) := by exact_mod_cast hlu
  have hlo : Certificate.eval m l ≤ 0 := by rw [← cast_evalRational]; exact_mod_cast hl
  have hhi : (0 : ℝ) ≤ Certificate.eval m u := by rw [← cast_evalRational]; exact_mod_cast hu
  obtain ⟨z, hz, heq⟩ := intermediate_value_Icc hle (eval_continuous m).continuousOn ⟨hlo, hhi⟩
  exact ⟨z, hz.1, hz.2, heq⟩

/-- A coefficient identity modulo any vanishing polynomial is sound at its root. -/
theorem eq_of_modulus_certificate (p q quotient m : List ℚ) (z : ℝ)
    (hm : Certificate.eval m z = 0)
    (hc : isZero (sub (sub p q) (mul quotient m)) = true) :
    Certificate.eval p z = Certificate.eval q z := by
  have h := Certificate.PolynomialCertificate.eval_zero _ hc z
  rw [Certificate.PolynomialCertificate.eval_sub, Certificate.PolynomialCertificate.eval_sub, Certificate.PolynomialCertificate.eval_mul, hm, mul_zero, sub_zero] at h
  exact sub_eq_zero.mp h

/-- A real polynomial whose coefficients are represented in an algebraic field. -/
noncomputable def fieldPolynomial : List (List ℚ) → ℝ → ℝ[X]
  | [], _ => 0
  | c :: cs, z => C (Certificate.eval c z) + X * fieldPolynomial cs z

def substitute : List (List ℚ) → List ℚ → List ℚ
  | [], _ => []
  | c :: cs, x => add c (mul x (substitute cs x))

lemma eval_substitute (cs : List (List ℚ)) (x : List ℚ) (z : ℝ) :
    Certificate.eval (substitute cs x) z = (fieldPolynomial cs z).eval (Certificate.eval x z) := by
  induction cs with
  | nil => simp [substitute, fieldPolynomial, Certificate.eval]
  | cons c cs ih =>
    simp only [substitute, fieldPolynomial, Certificate.PolynomialCertificate.eval_add, Certificate.PolynomialCertificate.eval_mul, ih,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

lemma fieldPolynomial_degree (cs : List (List ℚ)) (z : ℝ) :
    (fieldPolynomial cs z).natDegree ≤ cs.length - 1 := by
  induction cs with
  | nil => simp [fieldPolynomial]
  | cons c cs ih =>
    cases cs with
    | nil => simp [fieldPolynomial]
    | cons d ds =>
      change (C (Certificate.eval c z) + X * fieldPolynomial (d :: ds) z).natDegree ≤
        (c :: d :: ds).length - 1
      apply (natDegree_add_le _ _).trans
      apply max_le
      · simp
      · have h : (X * fieldPolynomial (d :: ds) z).natDegree ≤
            (X : ℝ[X]).natDegree + (fieldPolynomial (d :: ds) z).natDegree := natDegree_mul_le
        rw [natDegree_X] at h
        simp only [List.length_cons] at *
        omega

/-- A finite invariant grid identifies actual orbit-series values from its
exact contraction recurrences; no finite-sum truncation is assumed. -/
theorem finite_orbit_values {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ℝ[X]) {ρ : ℝ} (hρ : |ρ| < 1) (nodes values : ι → ℝ) (next : ι → ι)
    (hnodes : ∀ i, nodes i ∈ interval)
    (hnext : ∀ i, cubic (nodes i) = nodes (next i))
    (hvalues : ∀ i, values i = q.eval (nodes i) + ρ * values (next i)) :
    ∀ i, orbitSeries q.eval ρ (nodes i) = values i := by
  classical
  let D : ι → ℝ := fun i ↦ |orbitSeries q.eval ρ (nodes i) - values i|
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ D Finset.univ_nonempty
  have heq : orbitSeries q.eval ρ (nodes i) - values i =
      ρ * (orbitSeries q.eval ρ (nodes (next i)) - values (next i)) := by
    have h := orbitSeries_equation' hρ q.continuous (hnodes i)
    rw [hnext] at h
    linear_combination h - hvalues i
  have hstep : D i ≤ |ρ| * D i := by
    calc
      D i = |ρ| * D (next i) := by dsimp [D]; rw [heq, abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmax (next i) (Finset.mem_univ _)) (abs_nonneg ρ)
  have hzero : D i = 0 := by
    have hnonneg : 0 ≤ D i := abs_nonneg _
    nlinarith
  intro j
  have hj := hmax j (Finset.mem_univ _)
  rw [hzero] at hj
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hj (abs_nonneg _)))

end Lorentz.Plateau.FiniteTools
