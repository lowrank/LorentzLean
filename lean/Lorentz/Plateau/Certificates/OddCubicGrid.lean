module

public import Lorentz.Plateau.Certificates.OddData
public import Lorentz.Plateau.Certificates.Checker

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Odd

def cubicQuotient0 : List ℚ :=
  []

theorem cubic_at_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 0) = node z 1 :=
  Checker.cubic_map (nodeRows.getD 0 []) (nodeRows.getD 1 []) cubicQuotient0
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient1 : List ℚ :=
  []

theorem cubic_at_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 1) = node z 4 :=
  Checker.cubic_map (nodeRows.getD 1 []) (nodeRows.getD 4 []) cubicQuotient1
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient2 : List ℚ :=
  [0, (3 / 2), 0, (-1 / 2)]

theorem cubic_at_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 2) = node z 7 :=
  Checker.cubic_map (nodeRows.getD 2 []) (nodeRows.getD 7 []) cubicQuotient2
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient3 : List ℚ :=
  [0, (-9 / 2), 0, 15, 0, (-27 / 2), 0, (9 / 2), 0, (-1 / 2)]

theorem cubic_at_3 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 3) = node z 10 :=
  Checker.cubic_map (nodeRows.getD 3 []) (nodeRows.getD 10 []) cubicQuotient3
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient4 : List ℚ :=
  [0, 9, 0, (-141 / 2), 0, 189, 0, -225, 0, (275 / 2), 0, -45, 0, (15 / 2), 0, (-1 / 2)]

theorem cubic_at_4 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 4) = node z 13 :=
  Checker.cubic_map (nodeRows.getD 4 []) (nodeRows.getD 13 []) cubicQuotient4
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient5 : List ℚ :=
  [0, -15, 0, (415 / 2), 0, -1053, 0, (5157 / 2), 0, -3504, 0, (5733 / 2), 0, -1470, 0, 476, 0,
    (-189 / 2), 0, (21 / 2), 0, (-1 / 2)]

theorem cubic_at_5 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 5) = node z 16 :=
  Checker.cubic_map (nodeRows.getD 5 []) (nodeRows.getD 16 []) cubicQuotient5
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient6 : List ℚ :=
  [0, (39 / 2), 0, -245, 0, 1128, 0, -2631, 0, 3519, 0, -2868, 0, 1470, 0, -476, 0, (189 / 2), 0,
    (-21 / 2), 0, (1 / 2)]

theorem cubic_at_6 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 6) = node z 16 :=
  Checker.cubic_map (nodeRows.getD 6 []) (nodeRows.getD 16 []) cubicQuotient6
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient7 : List ℚ :=
  [0, (-45 / 2), 0, (231 / 2), 0, (-459 / 2), 0, (477 / 2), 0, -139, 0, 45, 0, (-15 / 2), 0,
    (1 / 2)]

theorem cubic_at_7 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 7) = node z 13 :=
  Checker.cubic_map (nodeRows.getD 7 []) (nodeRows.getD 13 []) cubicQuotient7
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient8 : List ℚ :=
  [0, 24, 0, -44, 0, (51 / 2), 0, -6, 0, (1 / 2)]

theorem cubic_at_8 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 8) = node z 10 :=
  Checker.cubic_map (nodeRows.getD 8 []) (nodeRows.getD 10 []) cubicQuotient8
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient9 : List ℚ :=
  [0, -24, 0, 44, 0, (-51 / 2), 0, 6, 0, (-1 / 2)]

theorem cubic_at_9 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 9) = node z 7 :=
  Checker.cubic_map (nodeRows.getD 9 []) (nodeRows.getD 7 []) cubicQuotient9
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient10 : List ℚ :=
  [0, (45 / 2), 0, (-231 / 2), 0, (459 / 2), 0, (-477 / 2), 0, 139, 0, -45, 0, (15 / 2), 0,
    (-1 / 2)]

theorem cubic_at_10 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 10) = node z 4 :=
  Checker.cubic_map (nodeRows.getD 10 []) (nodeRows.getD 4 []) cubicQuotient10
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient11 : List ℚ :=
  [0, (-39 / 2), 0, 245, 0, -1128, 0, 2631, 0, -3519, 0, 2868, 0, -1470, 0, 476, 0, (-189 / 2),
    0, (21 / 2), 0, (-1 / 2)]

theorem cubic_at_11 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 11) = node z 1 :=
  Checker.cubic_map (nodeRows.getD 11 []) (nodeRows.getD 1 []) cubicQuotient11
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient12 : List ℚ :=
  [0, 15, 0, (-415 / 2), 0, 1053, 0, (-5157 / 2), 0, 3504, 0, (-5733 / 2), 0, 1470, 0, -476, 0,
    (189 / 2), 0, (-21 / 2), 0, (1 / 2)]

theorem cubic_at_12 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 12) = node z 1 :=
  Checker.cubic_map (nodeRows.getD 12 []) (nodeRows.getD 1 []) cubicQuotient12
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient13 : List ℚ :=
  [0, -9, 0, (141 / 2), 0, -189, 0, 225, 0, (-275 / 2), 0, 45, 0, (-15 / 2), 0, (1 / 2)]

theorem cubic_at_13 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 13) = node z 4 :=
  Checker.cubic_map (nodeRows.getD 13 []) (nodeRows.getD 4 []) cubicQuotient13
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient14 : List ℚ :=
  [0, (9 / 2), 0, -15, 0, (27 / 2), 0, (-9 / 2), 0, (1 / 2)]

theorem cubic_at_14 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 14) = node z 7 :=
  Checker.cubic_map (nodeRows.getD 14 []) (nodeRows.getD 7 []) cubicQuotient14
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient15 : List ℚ :=
  [0, (-3 / 2), 0, (1 / 2)]

theorem cubic_at_15 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 15) = node z 10 :=
  Checker.cubic_map (nodeRows.getD 15 []) (nodeRows.getD 10 []) cubicQuotient15
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient16 : List ℚ :=
  []

theorem cubic_at_16 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 16) = node z 13 :=
  Checker.cubic_map (nodeRows.getD 16 []) (nodeRows.getD 13 []) cubicQuotient16
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient17 : List ℚ :=
  []

theorem cubic_at_17 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 17) = node z 16 :=
  Checker.cubic_map (nodeRows.getD 17 []) (nodeRows.getD 16 []) cubicQuotient17
    modulusCoeffs z hm (by decide +kernel)

theorem cubic_at_node (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (j : Fin 18) : cubic (node z j) = node z (cubicMap.getD j 0) := by
  fin_cases j
  · exact cubic_at_0 z hm
  · exact cubic_at_1 z hm
  · exact cubic_at_2 z hm
  · exact cubic_at_3 z hm
  · exact cubic_at_4 z hm
  · exact cubic_at_5 z hm
  · exact cubic_at_6 z hm
  · exact cubic_at_7 z hm
  · exact cubic_at_8 z hm
  · exact cubic_at_9 z hm
  · exact cubic_at_10 z hm
  · exact cubic_at_11 z hm
  · exact cubic_at_12 z hm
  · exact cubic_at_13 z hm
  · exact cubic_at_14 z hm
  · exact cubic_at_15 z hm
  · exact cubic_at_16 z hm
  · exact cubic_at_17 z hm
end Lorentz.Plateau.Certificates.Odd
