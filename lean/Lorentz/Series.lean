module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

set_option maxHeartbeats 1000000

/-! Continuous self-similar series on the approximation interval. -/

namespace Lorentz

abbrev interval : Set ℝ := Set.Icc (-1) 1

def cubic (x : ℝ) : ℝ := 4 * x ^ 3 - 3 * x

lemma cubic_continuous : Continuous cubic := by
  unfold cubic
  fun_prop

lemma cubic_maps_interval {x : ℝ} (hx : x ∈ interval) : cubic x ∈ interval := by
  have h₁ : 0 ≤ (1 - x) * (2 * x + 1) ^ 2 :=
    mul_nonneg (by linarith [hx.2]) (sq_nonneg _)
  have h₂ : 0 ≤ (1 + x) * (2 * x - 1) ^ 2 :=
    mul_nonneg (by linarith [hx.1]) (sq_nonneg _)
  constructor <;> dsimp [cubic] <;> nlinarith

lemma cubic_iterate_mem (n : ℕ) {x : ℝ} (hx : x ∈ interval) :
    (cubic^[n]) x ∈ interval := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using cubic_maps_interval ih

lemma cubic_zero : cubic 0 = 0 := by norm_num [cubic]

lemma cubic_neg (x : ℝ) : cubic (-x) = -cubic x := by
  dsimp [cubic]
  ring

lemma cubic_iterate_zero (n : ℕ) : (cubic^[n]) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, cubic_zero]

lemma cubic_iterate_neg (n : ℕ) (x : ℝ) : (cubic^[n]) (-x) = -(cubic^[n]) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, cubic_neg]

noncomputable def orbitSeries (q : ℝ → ℝ) (ρ : ℝ) (x : ℝ) : ℝ :=
  ∑' j : ℕ, ρ ^ j * q ((cubic^[j]) x)

lemma orbit_term_bound {q : ℝ → ℝ} {ρ M x : ℝ}
    (hq : ∀ y ∈ interval, |q y| ≤ M) (hx : x ∈ interval) (j : ℕ) :
    ‖ρ ^ j * q ((cubic^[j]) x)‖ ≤ |ρ| ^ j * M := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hq _ (cubic_iterate_mem j hx))
    (pow_nonneg (abs_nonneg ρ) j)

lemma orbit_summable {q : ℝ → ℝ} {ρ M x : ℝ}
    (hρ : |ρ| < 1) (hq : ∀ y ∈ interval, |q y| ≤ M) (hx : x ∈ interval) :
    Summable (fun j : ℕ => ρ ^ j * q ((cubic^[j]) x)) := by
  have hg : Summable (fun j : ℕ => |ρ| ^ j * M) :=
    (summable_geometric_of_norm_lt_one (by simpa using hρ)).mul_right M
  exact hg.of_norm_bounded (fun j => orbit_term_bound hq hx j)

lemma orbitSeries_continuousOn {q : ℝ → ℝ} {ρ M : ℝ}
    (hρ : |ρ| < 1) (hqcont : Continuous q)
    (hq : ∀ y ∈ interval, |q y| ≤ M) :
    ContinuousOn (orbitSeries q ρ) interval := by
  apply continuousOn_tsum
    (f := fun j x => ρ ^ j * q ((cubic^[j]) x))
    (u := fun j : ℕ => |ρ| ^ j * M)
  · intro j
    exact (continuous_const.mul (hqcont.comp (cubic_continuous.iterate j))).continuousOn
  · exact (summable_geometric_of_norm_lt_one (by simpa using hρ)).mul_right M
  · intro j x hx
    exact orbit_term_bound hq hx j

lemma orbitSeries_equation {q : ℝ → ℝ} {ρ M x : ℝ}
    (hρ : |ρ| < 1) (hq : ∀ y ∈ interval, |q y| ≤ M) (hx : x ∈ interval) :
    orbitSeries q ρ x = q x + ρ * orbitSeries q ρ (cubic x) := by
  have hs := orbit_summable hρ hq hx
  have hs' := orbit_summable hρ hq (cubic_maps_interval hx)
  rw [orbitSeries, hs.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Function.iterate_zero, id_eq]
  congr 1
  rw [orbitSeries, ← hs'.tsum_mul_left]
  apply tsum_congr
  intro j
  rw [pow_succ', Function.iterate_succ_apply]
  ring

lemma orbitSeries_zero {q : ℝ → ℝ} {ρ : ℝ} (hq : q 0 = 0) :
    orbitSeries q ρ 0 = 0 := by
  simp [orbitSeries, cubic_iterate_zero, hq]

lemma orbitSeries_odd {q : ℝ → ℝ} {ρ : ℝ} (hq : Function.Odd q) :
    Function.Odd (orbitSeries q ρ) := by
  intro x
  change (∑' j : ℕ, ρ ^ j * q ((cubic^[j]) (-x))) =
    -(∑' j : ℕ, ρ ^ j * q ((cubic^[j]) x))
  calc
    (∑' j : ℕ, ρ ^ j * q ((cubic^[j]) (-x))) =
        ∑' j : ℕ, -(ρ ^ j * q ((cubic^[j]) x)) := by
      apply tsum_congr
      intro j
      rw [cubic_iterate_neg, hq]
      ring
    _ = _ := tsum_neg

lemma continuous_bounded_on_interval {q : ℝ → ℝ} (hq : Continuous q) :
    ∃ M : ℝ, ∀ y ∈ interval, |q y| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
  exact ⟨M, by simpa only [Real.norm_eq_abs] using hM⟩

lemma orbitSeries_continuousOn' {q : ℝ → ℝ} {ρ : ℝ}
    (hρ : |ρ| < 1) (hq : Continuous q) :
    ContinuousOn (orbitSeries q ρ) interval := by
  obtain ⟨M, hM⟩ := continuous_bounded_on_interval hq
  exact orbitSeries_continuousOn hρ hq hM

lemma orbitSeries_equation' {q : ℝ → ℝ} {ρ x : ℝ}
    (hρ : |ρ| < 1) (hq : Continuous q) (hx : x ∈ interval) :
    orbitSeries q ρ x = q x + ρ * orbitSeries q ρ (cubic x) := by
  obtain ⟨M, hM⟩ := continuous_bounded_on_interval hq
  exact orbitSeries_equation hρ hM hx

lemma orbitSeries_bound {q : ℝ → ℝ} {ρ M x : ℝ}
    (hρ : |ρ| < 1) (hq : ∀ y ∈ interval, |q y| ≤ M) (hx : x ∈ interval) :
    |orbitSeries q ρ x| ≤ M / (1 - |ρ|) := by
  have hg := (hasSum_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right M
  have h := tsum_of_norm_bounded hg (fun j => orbit_term_bound hq hx j)
  simpa only [orbitSeries, Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using h

lemma orbitSeries_linear {q r : ℝ → ℝ} {ρ M N x ε : ℝ}
    (hρ : |ρ| < 1) (hq : ∀ y ∈ interval, |q y| ≤ M)
    (hr : ∀ y ∈ interval, |r y| ≤ N) (hx : x ∈ interval) :
    orbitSeries (fun y => q y + ε * r y) ρ x =
      orbitSeries q ρ x + ε * orbitSeries r ρ x := by
  have hs := orbit_summable hρ hq hx
  have ht := orbit_summable hρ hr hx
  unfold orbitSeries
  calc
    (∑' j : ℕ, ρ ^ j * (q ((cubic^[j]) x) + ε * r ((cubic^[j]) x))) =
      ∑' j : ℕ, (ρ ^ j * q ((cubic^[j]) x) + ε * (ρ ^ j * r ((cubic^[j]) x))) := by
        apply tsum_congr
        intro j
        ring
    _ = _ := by rw [hs.tsum_add (ht.mul_left ε), ht.tsum_mul_left]

lemma orbitSeries_linear' {q r : ℝ → ℝ} {ρ x ε : ℝ}
    (hρ : |ρ| < 1) (hq : Continuous q) (hr : Continuous r) (hx : x ∈ interval) :
    orbitSeries (fun y => q y + ε * r y) ρ x =
      orbitSeries q ρ x + ε * orbitSeries r ρ x := by
  obtain ⟨M, hM⟩ := continuous_bounded_on_interval hq
  obtain ⟨N, hN⟩ := continuous_bounded_on_interval hr
  exact orbitSeries_linear hρ hM hN hx

lemma orbitSeries_pair {q : ℝ → ℝ} {ρ M x : ℝ}
    (hρ : |ρ| < 1) (hq : ∀ y ∈ interval, |q y| ≤ M) (hx : x ∈ interval) :
    orbitSeries q ρ x =
      ∑' j : ℕ, (ρ ^ 2) ^ j *
        (q ((cubic^[2 * j]) x) + ρ * q (cubic ((cubic^[2 * j]) x))) := by
  have hs := orbit_summable hρ hq hx
  have he : Summable (fun j : ℕ => ρ ^ (2 * j) * q ((cubic^[2 * j]) x)) := by
    have hi : Function.Injective (fun j : ℕ => 2 * j) := by
      intro i j hij
      dsimp at hij
      omega
    simpa only [Function.comp_def] using hs.comp_injective hi
  have ho : Summable (fun j : ℕ => ρ ^ (2 * j + 1) * q ((cubic^[2 * j + 1]) x)) := by
    have hi : Function.Injective (fun j : ℕ => 2 * j + 1) := by
      intro i j hij
      dsimp at hij
      omega
    simpa only [Function.comp_def] using hs.comp_injective hi
  unfold orbitSeries
  rw [← tsum_even_add_odd (f := fun j : ℕ ↦ ρ ^ j * q ((cubic^[j]) x)) he ho,
    ← he.tsum_add ho]
  apply tsum_congr
  intro j
  simp only [pow_add, pow_mul, pow_one, Function.iterate_succ_apply']
  ring

lemma orbitSeries_paired {q : ℝ → ℝ} {x : ℝ}
    (hq : Continuous q) (hx : x ∈ interval) :
    orbitSeries q (-1 / 3) x =
      ∑' j : ℕ, ((1 : ℝ) / 9) ^ j *
        (q ((cubic^[2 * j]) x) - q (cubic ((cubic^[2 * j]) x)) / 3) := by
  obtain ⟨M, hM⟩ := continuous_bounded_on_interval hq
  rw [orbitSeries_pair (by norm_num : |(-1 : ℝ) / 3| < 1) hM hx]
  apply tsum_congr
  intro j
  norm_num
  ring

lemma orbitSeries_comp_cubic (q : ℝ → ℝ) (ρ x : ℝ) :
    orbitSeries (fun y => q (cubic y)) ρ x = orbitSeries q ρ (cubic x) := by
  unfold orbitSeries
  apply tsum_congr
  intro j
  change ρ ^ j * q (cubic ((cubic^[j]) x)) = _
  rw [← Function.iterate_succ_apply' cubic j x, Function.iterate_succ_apply]

end Lorentz
