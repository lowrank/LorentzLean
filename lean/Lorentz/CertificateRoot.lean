module

public import Lorentz.CertificateBounds

@[expose] public section

namespace Lorentz.Certificate

def rootLower : ℚ := 199238939 / 100000000
def rootUpper : ℚ := 199238940 / 100000000

def s6 (z : ℝ) : ℝ := (z ^ 2 - 3) ^ 3 + 3 * (z ^ 2 - 3) ^ 2 - 2

def modulus (z : ℝ) : ℝ := z ^ 12 - 12 * z ^ 10 + 54 * z ^ 8 -
  112 * z ^ 6 + 105 * z ^ 4 - 36 * z ^ 2 + 1

 theorem modulus_eq (z : ℝ) : modulus z = (s6 z) ^ 2 - 3 := by
  dsimp [modulus, s6]
  ring

 theorem s6_monotone {x y : ℝ} (hx : (99 : ℝ) / 50 ≤ x) (hxy : x ≤ y) :
    s6 x ≤ s6 y := by
  have hx0 : 0 ≤ x := by linarith
  have hx3 : 0 ≤ x ^ 2 - 3 := by nlinarith
  have hxy2 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0 hxy 2
  have hshift : x ^ 2 - 3 ≤ y ^ 2 - 3 := by linarith
  have hsquare := pow_le_pow_left₀ hx3 hshift 2
  have hcube := pow_le_pow_left₀ hx3 hshift 3
  dsimp [s6]
  linarith

 theorem s6_positive {x : ℝ} (hx : (99 : ℝ) / 50 ≤ x) : 0 < s6 x := by
  have h := s6_monotone (x := (99 : ℝ) / 50) (by rfl) hx
  have hpos : 0 < s6 ((99 : ℝ) / 50) := by norm_num [s6]
  linarith

 theorem modulus_monotone {x y : ℝ} (hx : (99 : ℝ) / 50 ≤ x) (hxy : x ≤ y) :
    modulus x ≤ modulus y := by
  rw [modulus_eq, modulus_eq]
  have h := pow_le_pow_left₀ (le_of_lt (s6_positive hx)) (s6_monotone hx hxy) 2
  linarith

 theorem modulus_lower_negative : modulus (rootLower : ℝ) < 0 := by
  norm_num [modulus, rootLower]

 theorem modulus_upper_positive : 0 < modulus (rootUpper : ℝ) := by
  norm_num [modulus, rootUpper]

 theorem root_localization (z : ℝ) (hz : modulus z = 0)
    (hcoarse : (99 : ℝ) / 50 ≤ z) :
    (rootLower : ℝ) ≤ z ∧ z ≤ (rootUpper : ℝ) := by
  constructor
  · by_contra h
    have hm := modulus_monotone hcoarse (le_of_lt (lt_of_not_ge h))
    have hneg := modulus_lower_negative
    linarith
  · by_contra h
    have hbase : (99 : ℝ) / 50 ≤ (rootUpper : ℝ) := by norm_num [rootUpper]
    have hm := modulus_monotone hbase (le_of_lt (lt_of_not_ge h))
    have hpos := modulus_upper_positive
    linarith

 theorem exists_certificate_root : ∃ z : ℝ,
    (rootLower : ℝ) ≤ z ∧ z ≤ (rootUpper : ℝ) ∧ modulus z = 0 := by
  have hlu : (rootLower : ℝ) ≤ (rootUpper : ℝ) := by norm_num [rootLower, rootUpper]
  have hc : Continuous modulus := by unfold modulus; fun_prop
  have hz : (0 : ℝ) ∈ Set.Icc (modulus (rootLower : ℝ)) (modulus (rootUpper : ℝ)) :=
    ⟨le_of_lt modulus_lower_negative, le_of_lt modulus_upper_positive⟩
  rcases intermediate_value_Icc hlu hc.continuousOn hz with ⟨z, hzrange, hz0⟩
  exact ⟨z, hzrange.1, hzrange.2, hz0⟩

end Lorentz.Certificate
