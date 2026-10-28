module

public import Lorentz.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace Lorentz

lemma cubic_cos (θ : ℝ) : cubic (Real.cos θ) = Real.cos (3 * θ) := by
  simpa only [cubic] using (Real.cos_three_mul θ).symm

lemma cubic_iterate_cos (n : ℕ) (θ : ℝ) :
    (cubic^[n]) (Real.cos θ) = Real.cos ((3 : ℝ) ^ n * θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, cubic_cos, pow_succ]
    congr 1
    ring

lemma cubic_even_iterate_cos (n : ℕ) (θ : ℝ) :
    (cubic^[2 * n]) (Real.cos θ) = Real.cos ((9 : ℝ) ^ n * θ) := by
  rw [cubic_iterate_cos, pow_mul]
  norm_num

lemma cosine_mem_interval (θ : ℝ) : Real.cos θ ∈ interval :=
  ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩

lemma orbitSeries_paired_cos {q : ℝ → ℝ} (hq : Continuous q) (θ : ℝ) :
    orbitSeries q (-1 / 3) (Real.cos θ) =
      ∑' j : ℕ, ((1 : ℝ) / 9) ^ j *
        (q (Real.cos ((9 : ℝ) ^ j * θ)) -
          q (cubic (Real.cos ((9 : ℝ) ^ j * θ))) / 3) := by
  rw [orbitSeries_paired hq (cosine_mem_interval θ)]
  apply tsum_congr
  intro j
  rw [cubic_even_iterate_cos]

lemma cosine_quarter_phase (k n : ℕ) (u : ℝ) :
    Real.cos ((9 : ℝ) ^ n * ((k : ℝ) * Real.pi / 4 + u)) =
      Real.cos ((k : ℝ) * Real.pi / 4 + (9 : ℝ) ^ n * u) := by
  let m : ℕ := ∑ j ∈ Finset.range n, (9 : ℕ) ^ j
  have hm : (m : ℝ) = ∑ j ∈ Finset.range n, (9 : ℝ) ^ j := by
    simp [m]
  have hgeom : (9 : ℝ) ^ n = 1 + 8 * (m : ℝ) := by
    have h := mul_geom_sum (9 : ℝ) n
    rw [← hm] at h
    nlinarith
  have hangle : (9 : ℝ) ^ n * ((k : ℝ) * Real.pi / 4 + u) =
      ((k : ℝ) * Real.pi / 4 + (9 : ℝ) ^ n * u) +
        ((k * m : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    rw [hgeom]
    ring
  rw [hangle, Real.cos_add_nat_mul_two_pi]

end Lorentz
