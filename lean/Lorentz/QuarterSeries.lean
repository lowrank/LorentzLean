module

public import Lorentz.Trigonometry

@[expose] public section

namespace Lorentz

/-- At quarter-period angles the paired dynamics fixes the centre exactly. -/
lemma orbitSeries_quarter_difference {q : ℝ → ℝ} (hq : Continuous q)
    (k : ℕ) (u : ℝ) :
    orbitSeries q (-1 / 3) (Real.cos ((k : ℝ) * Real.pi / 4 + u)) -
      orbitSeries q (-1 / 3) (Real.cos ((k : ℝ) * Real.pi / 4)) =
      ∑' j : ℕ, ((1 : ℝ) / 9) ^ j *
        ((q (Real.cos ((k : ℝ) * Real.pi / 4 + (9 : ℝ) ^ j * u)) -
            q (cubic (Real.cos ((k : ℝ) * Real.pi / 4 + (9 : ℝ) ^ j * u))) / 3) -
          (q (Real.cos ((k : ℝ) * Real.pi / 4)) -
            q (cubic (Real.cos ((k : ℝ) * Real.pi / 4))) / 3)) := by
  let r : ℝ → ℝ := fun x => q x - q (cubic x) / 3
  have hr : Continuous r := hq.sub ((hq.comp cubic_continuous).div_const 3)
  obtain ⟨M, hM⟩ := continuous_bounded_on_interval hr
  have hg : Summable (fun j : ℕ => ((1 : ℝ) / 9) ^ j * M) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 : ℝ) / 9‖ < 1)).mul_right M
  have hs : Summable (fun j : ℕ => ((1 : ℝ) / 9) ^ j *
      r (Real.cos ((k : ℝ) * Real.pi / 4 + (9 : ℝ) ^ j * u))) := by
    exact hg.of_norm_bounded (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((1 : ℝ) / 9) ^ j)]
      exact mul_le_mul_of_nonneg_left (hM _ (cosine_mem_interval _)) (by positivity))
  have ht : Summable (fun j : ℕ => ((1 : ℝ) / 9) ^ j *
      r (Real.cos ((k : ℝ) * Real.pi / 4))) := by
    exact hg.of_norm_bounded (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((1 : ℝ) / 9) ^ j)]
      exact mul_le_mul_of_nonneg_left (hM _ (cosine_mem_interval _)) (by positivity))
  have hphase (v : ℝ) :
      orbitSeries q (-1 / 3) (Real.cos ((k : ℝ) * Real.pi / 4 + v)) =
        ∑' j : ℕ, ((1 : ℝ) / 9) ^ j *
          r (Real.cos ((k : ℝ) * Real.pi / 4 + (9 : ℝ) ^ j * v)) := by
    rw [orbitSeries_paired_cos hq]
    apply tsum_congr
    intro j
    rw [cosine_quarter_phase]
  have hzero := hphase 0
  simp only [add_zero, mul_zero] at hzero
  rw [hphase u, hzero, ← hs.tsum_sub ht]
  apply tsum_congr
  intro j
  dsimp [r]
  ring

end Lorentz
