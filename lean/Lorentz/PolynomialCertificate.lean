module

public import Lorentz.CertificateGrid

@[expose] public section

/-! Exact coefficient certificates for polynomial identities at the algebraic root. -/

namespace Lorentz.Certificate.PolynomialCertificate

def add : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℚ) : List ℚ → List ℚ
  | [] => []
  | b :: p => (a * b) :: scale a p

def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

theorem eval_add (p q : List ℚ) (z : ℝ) :
    eval (add p q) z = eval p z + eval q z := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add, eval]
    | cons b q => simp only [add, eval, ih, Rat.cast_add]; ring

theorem eval_scale (a : ℚ) (p : List ℚ) (z : ℝ) :
    eval (scale a p) z = (a : ℝ) * eval p z := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih => simp only [scale, eval, ih, Rat.cast_mul]; ring

theorem eval_mul (p q : List ℚ) (z : ℝ) :
    eval (mul p q) z = eval p z * eval q z := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih =>
    rw [mul, eval_add, eval_scale]
    simp only [eval, Rat.cast_zero, zero_add, ih]
    ring

def isZero (p : List ℚ) : Bool := p.all (fun x ↦ decide (x = 0))

theorem eval_zero (p : List ℚ) (hp : isZero p = true) (z : ℝ) :
    eval p z = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [isZero, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    simp [eval, hp.1, ih hp.2]


def sub (p q : List ℚ) : List ℚ := add p (scale (-1) q)

def power (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => mul (power p n) p

theorem eval_sub (p q : List ℚ) (z : ℝ) :
    eval (sub p q) z = eval p z - eval q z := by
  simp [sub, eval_add, eval_scale, sub_eq_add_neg]

theorem eval_power (p : List ℚ) (n : ℕ) (z : ℝ) :
    eval (power p n) z = (eval p z) ^ n := by
  induction n with
  | zero => simp [power, eval]
  | succ n ih => simp only [power, eval_mul, ih, pow_succ]

def modulusCoeffs : List ℚ := [1, 0, -36, 0, 105, 0, -112, 0, 54, 0, -12, 0, 1]

theorem eval_modulus (z : ℝ) : eval modulusCoeffs z = modulus z := by
  norm_num [modulusCoeffs, eval, modulus]
  ring

theorem eq_of_certificate (p q quotient : List ℚ) (z : ℝ) (hm : modulus z = 0)
    (hc : isZero (sub (sub p q) (mul quotient modulusCoeffs)) = true) :
    eval p z = eval q z := by
  have h := eval_zero _ hc z
  rw [eval_sub, eval_sub, eval_mul, eval_modulus, hm, mul_zero, sub_zero] at h
  exact sub_eq_zero.mp h

def slopeCoeffs : ℕ → List ℚ
  | 0 => t0Coeffs
  | 1 | 2 => t1Coeffs
  | 3 => t3Coeffs
  | 4 => t4Coeffs
  | 5 | 6 => t5Coeffs
  | _ => []

def correctionCoeffs (n : ℕ) (x : List ℚ) : List ℚ := match n with
  | 0 => []
  | 1 | 2 => mul v1Coeffs x
  | 3 => add (add (mul v31Coeffs x) (mul v32Coeffs (power x 2)))
      (mul v33Coeffs (power x 3))
  | 4 => add (add (sub (scale 8 (power x 4)) (scale 8 (power x 2)))
      (mul v41Coeffs x)) (mul v43Coeffs (sub (scale 4 (power x 3)) (scale 3 x)))
  | 5 | 6 => add
      (add (add (sub (scale 8 (power x 4)) (scale 8 (power x 2)))
        (mul v51Coeffs x)) (mul v53Coeffs (sub (scale 4 (power x 3)) (scale 3 x))))
      (mul v55Coeffs (add (sub (scale 16 (power x 5)) (scale 20 (power x 3)))
        (scale 5 x)))
  | _ => []

def perturbationCoeffs (j : ℕ) : List ℚ :=
  add (h0Coeffs j) (mul betaCoeffs (h1Coeffs j))

def sign (n j : ℕ) : ℚ :=
  let s := if j % 4 = 0 ∨ j % 4 = 3 then 1 else -1
  if n < 3 then -s else s

def slack (n j : ℕ) : List ℚ :=
  sub (slopeCoeffs n)
    (scale (sign n j) (sub (perturbationCoeffs (gridIndex n j))
      (correctionCoeffs n (nodeCoeffs (gridIndex n j)))))

theorem eval_slope (n : ℕ) (z : ℝ) : eval (slopeCoeffs n) z = slope n z := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => rfl

theorem eval_correction (n : ℕ) (x : List ℚ) (z : ℝ) :
    eval (correctionCoeffs n x) z = correction n z (eval x z) := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 =>
    simp [correctionCoeffs, correction, eval_add, eval_sub, eval_scale, eval_mul, eval_power,
      eval, v1, v31, v32, v33, v41, v43, v51, v53, v55]

theorem eval_sign (n j : ℕ) : ((sign n j) : ℝ) = gridSign n j := by
  simp only [sign, gridSign, coarseSign, fineSign]
  split_ifs <;> norm_num

theorem eval_slack (n j : ℕ) (z : ℝ) :
    eval (slack n j) z =
      slope n z - gridSign n j *
        (gridPerturbation z (gridIndex n j) - correction n z (node z (gridIndex n j))) := by
  simp only [slack, eval_sub, eval_scale, eval_slope, eval_sign, eval_correction,
    perturbationCoeffs, eval_add, eval_mul, gridPerturbation, beta, node]

theorem checked_slack (n j : ℕ) (quotient : List ℚ) (z : ℝ) (hm : modulus z = 0)
    (hc : isZero (sub (sub (slack n j) (slackCoeffs n j))
      (mul quotient modulusCoeffs)) = true) :
    slope n z - gridSign n j *
      (gridPerturbation z (gridIndex n j) - correction n z (node z (gridIndex n j))) =
        eval (slackCoeffs n j) z := by
  rw [← eval_slack]
  exact eq_of_certificate _ _ quotient z hm hc

end Lorentz.Certificate.PolynomialCertificate
