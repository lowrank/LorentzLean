module

public import Lorentz.CertificateGrid

@[expose] public section

namespace Lorentz.Certificate

open Polynomial

noncomputable def correctionPoly (n : ℕ) (z : ℝ) : Polynomial ℝ := match n with
  | 0 => 0
  | 1 | 2 => C (v1 z) * X
  | 3 => C (v31 z) * X + C (v32 z) * X ^ 2 + C (v33 z) * X ^ 3
  | 4 => 8 * X ^ 4 - 8 * X ^ 2 + C (v41 z) * X + C (v43 z) * (4 * X ^ 3 - 3 * X)
  | 5 | 6 => 8 * X ^ 4 - 8 * X ^ 2 + C (v51 z) * X + C (v53 z) * (4 * X ^ 3 - 3 * X) +
      C (v55 z) * (16 * X ^ 5 - 20 * X ^ 3 + 5 * X)
  | _ => 0

 theorem correctionPoly_eval (n : ℕ) (z x : ℝ) : (correctionPoly n z).eval x = correction n z x := by
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [correctionPoly, correction]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm 7 k]
    simp [correctionPoly, correction]

 theorem correctionPoly_degree (n : ℕ) (z : ℝ) : (correctionPoly n z).natDegree ≤ n := by
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp only [correctionPoly] <;> compute_degree <;> norm_num
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm 7 k]
    simp [correctionPoly]

 theorem correctionPoly_zero (n : ℕ) (z : ℝ) : (correctionPoly n z).eval 0 = 0 := by
  rw [correctionPoly_eval, correction_zero]

end Lorentz.Certificate
