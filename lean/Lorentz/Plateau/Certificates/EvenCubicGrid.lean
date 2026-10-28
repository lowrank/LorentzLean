module

public import Lorentz.Plateau.Certificates.EvenData
public import Lorentz.Plateau.Certificates.Checker

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Even

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
  []

theorem cubic_at_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 2) = node z 7 :=
  Checker.cubic_map (nodeRows.getD 2 []) (nodeRows.getD 7 []) cubicQuotient2
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient3 : List ℚ :=
  []

theorem cubic_at_3 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 3) = node z 10 :=
  Checker.cubic_map (nodeRows.getD 3 []) (nodeRows.getD 10 []) cubicQuotient3
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient4 : List ℚ :=
  [0, (3 / 2), 0, (-1 / 2)]

theorem cubic_at_4 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 4) = node z 13 :=
  Checker.cubic_map (nodeRows.getD 4 []) (nodeRows.getD 13 []) cubicQuotient4
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient5 : List ℚ :=
  [0, (-9 / 2), 0, 15, 0, (-27 / 2), 0, (9 / 2), 0, (-1 / 2)]

theorem cubic_at_5 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 5) = node z 16 :=
  Checker.cubic_map (nodeRows.getD 5 []) (nodeRows.getD 16 []) cubicQuotient5
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient6 : List ℚ :=
  [0, (15 / 2), 0, -70, 0, 189, 0, -225, 0, (275 / 2), 0, -45, 0, (15 / 2), 0, (-1 / 2)]

theorem cubic_at_6 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 6) = node z 19 :=
  Checker.cubic_map (nodeRows.getD 6 []) (nodeRows.getD 19 []) cubicQuotient6
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient7 : List ℚ :=
  [0, (-21 / 2), 0, (385 / 2), 0, (-2079 / 2), 0, 2574, 0, (-7007 / 2), 0, (5733 / 2), 0, -1470,
    0, 476, 0, (-189 / 2), 0, (21 / 2), 0, (-1 / 2)]

theorem cubic_at_7 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 7) = node z 22 :=
  Checker.cubic_map (nodeRows.getD 7 []) (nodeRows.getD 22 []) cubicQuotient7
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient8 : List ℚ :=
  [0, 15, 0, -410, 0, (7371 / 2), 0, -15444, 0, 36465, 0, -53703, 0, 52326, 0, -34884, 0,
    (32319 / 2), 0, (-10395 / 2), 0, (2277 / 2), 0, -162, 0, (27 / 2), 0, (-1 / 2)]

theorem cubic_at_8 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 8) = node z 25 :=
  Checker.cubic_map (nodeRows.getD 8 []) (nodeRows.getD 25 []) cubicQuotient8
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient9 : List ℚ :=
  [0, -21, 0, 763, 0, (-20223 / 2), 0, (127917 / 2), 0, (-461891 / 2), 0, 529074, 0, -820743, 0,
    898909, 0, (-1427679 / 2), 0, 417450, 0, -180895, 0, 57915, 0, (-27027 / 2), 0, 2233, 0,
    (-495 / 2), 0, (33 / 2), 0, (-1 / 2)]

theorem cubic_at_9 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 9) = node z 28 :=
  Checker.cubic_map (nodeRows.getD 9 []) (nodeRows.getD 28 []) cubicQuotient9
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient10 : List ℚ :=
  [0, 27, 0, -1305, 0, (47061 / 2), 0, (-416151 / 2), 0, (2124969 / 2), 0, -3476817, 0,
    (15600915 / 2), 0, (-25110021 / 2), 0, (29910465 / 2), 0, -13468455, 0, (18599295 / 2), 0,
    (-9924525 / 2), 0, (4102137 / 2), 0, -654472, 0, 159588, 0, -29172, 0, (7735 / 2), 0, -351,
    0, (39 / 2), 0, (-1 / 2)]

theorem cubic_at_10 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 10) = node z 31 :=
  Checker.cubic_map (nodeRows.getD 10 []) (nodeRows.getD 31 []) cubicQuotient10
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient11 : List ℚ :=
  [0, -33, 0, 2090, 0, (-97713 / 2), 0, 571824, 0, -3909191, 0, 17258904, 0, (-105309015 / 2), 0,
    116338616, 0, -192471282, 0, 244247073, 0, (-483841801 / 2), 0, 189329400, 0, -118015326,
    0, 58839550, 0, -23477850, 0, 7472520, 0, (-3764565 / 2), 0, (740259 / 2), 0, -55575, 0,
    6150, 0, (-945 / 2), 0, (45 / 2), 0, (-1 / 2)]

theorem cubic_at_11 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 11) = node z 34 :=
  Checker.cubic_map (nodeRows.getD 11 []) (nodeRows.getD 34 []) cubicQuotient11
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient12 : List ℚ :=
  [0, (75 / 2), 0, (-4543 / 2), 0, (101343 / 2), 0, (-1157805 / 2), 0, 3923348, 0,
    (-34550841 / 2), 0, (105333039 / 2), 0, -116344226, 0, 192472965, 0, (-488494773 / 2), 0,
    (483841867 / 2), 0, (-378658803 / 2), 0, 118015326, 0, -58839550, 0, 23477850, 0, -7472520,
    0, (3764565 / 2), 0, (-740259 / 2), 0, 55575, 0, -6150, 0, (945 / 2), 0, (-45 / 2), 0,
    (1 / 2)]

theorem cubic_at_12 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 12) = node z 34 :=
  Checker.cubic_map (nodeRows.getD 12 []) (nodeRows.getD 34 []) cubicQuotient12
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient13 : List ℚ :=
  [0, (-81 / 2), 0, 1674, 0, -26082, 0, (430245 / 2), 0, (-2145165 / 2), 0, (6970563 / 2), 0,
    -7804845, 0, 12556437, 0, -14955516, 0, (26936973 / 2), 0, -9299649, 0, (9924525 / 2), 0,
    (-4102137 / 2), 0, 654472, 0, -159588, 0, 29172, 0, (-7735 / 2), 0, 351, 0, (-39 / 2), 0,
    (1 / 2)]

theorem cubic_at_13 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 13) = node z 31 :=
  Checker.cubic_map (nodeRows.getD 13 []) (nodeRows.getD 31 []) cubicQuotient13
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient14 : List ℚ :=
  [0, (87 / 2), 0, -1153, 0, (23907 / 2), 0, -67707, 0, (470039 / 2), 0, (-1063335 / 2), 0,
    (1643481 / 2), 0, -899137, 0, 713868, 0, (-834903 / 2), 0, 180895, 0, -57915, 0,
    (27027 / 2), 0, -2233, 0, (495 / 2), 0, (-33 / 2), 0, (1 / 2)]

theorem cubic_at_14 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 14) = node z 28 :=
  Checker.cubic_map (nodeRows.getD 14 []) (nodeRows.getD 28 []) cubicQuotient14
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient15 : List ℚ :=
  [0, (-93 / 2), 0, (1471 / 2), 0, -4767, 0, (34257 / 2), 0, (-75735 / 2), 0, 54366, 0,
    (-105009 / 2), 0, (69819 / 2), 0, -16161, 0, (10395 / 2), 0, (-2277 / 2), 0, 162, 0,
    (-27 / 2), 0, (1 / 2)]

theorem cubic_at_15 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 15) = node z 25 :=
  Checker.cubic_map (nodeRows.getD 15 []) (nodeRows.getD 25 []) cubicQuotient15
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient16 : List ℚ :=
  [0, 48, 0, -448, 0, 1647, 0, (-6525 / 2), 0, (7835 / 2), 0, (-6003 / 2), 0, (2985 / 2), 0,
    (-955 / 2), 0, (189 / 2), 0, (-21 / 2), 0, (1 / 2)]

theorem cubic_at_16 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 16) = node z 22 :=
  Checker.cubic_map (nodeRows.getD 16 []) (nodeRows.getD 22 []) cubicQuotient16
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient17 : List ℚ :=
  [0, -48, 0, 304, 0, -591, 0, (1059 / 2), 0, -252, 0, 66, 0, -9, 0, (1 / 2)]

theorem cubic_at_17 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 17) = node z 19 :=
  Checker.cubic_map (nodeRows.getD 17 []) (nodeRows.getD 19 []) cubicQuotient17
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient18 : List ℚ :=
  [0, 48, 0, -304, 0, 591, 0, (-1059 / 2), 0, 252, 0, -66, 0, 9, 0, (-1 / 2)]

theorem cubic_at_18 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 18) = node z 16 :=
  Checker.cubic_map (nodeRows.getD 18 []) (nodeRows.getD 16 []) cubicQuotient18
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient19 : List ℚ :=
  [0, -48, 0, 448, 0, -1647, 0, (6525 / 2), 0, (-7835 / 2), 0, (6003 / 2), 0, (-2985 / 2), 0,
    (955 / 2), 0, (-189 / 2), 0, (21 / 2), 0, (-1 / 2)]

theorem cubic_at_19 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 19) = node z 13 :=
  Checker.cubic_map (nodeRows.getD 19 []) (nodeRows.getD 13 []) cubicQuotient19
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient20 : List ℚ :=
  [0, (93 / 2), 0, (-1471 / 2), 0, 4767, 0, (-34257 / 2), 0, (75735 / 2), 0, -54366, 0,
    (105009 / 2), 0, (-69819 / 2), 0, 16161, 0, (-10395 / 2), 0, (2277 / 2), 0, -162, 0,
    (27 / 2), 0, (-1 / 2)]

theorem cubic_at_20 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 20) = node z 10 :=
  Checker.cubic_map (nodeRows.getD 20 []) (nodeRows.getD 10 []) cubicQuotient20
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient21 : List ℚ :=
  [0, (-87 / 2), 0, 1153, 0, (-23907 / 2), 0, 67707, 0, (-470039 / 2), 0, (1063335 / 2), 0,
    (-1643481 / 2), 0, 899137, 0, -713868, 0, (834903 / 2), 0, -180895, 0, 57915, 0,
    (-27027 / 2), 0, 2233, 0, (-495 / 2), 0, (33 / 2), 0, (-1 / 2)]

theorem cubic_at_21 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 21) = node z 7 :=
  Checker.cubic_map (nodeRows.getD 21 []) (nodeRows.getD 7 []) cubicQuotient21
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient22 : List ℚ :=
  [0, (81 / 2), 0, -1674, 0, 26082, 0, (-430245 / 2), 0, (2145165 / 2), 0, (-6970563 / 2), 0,
    7804845, 0, -12556437, 0, 14955516, 0, (-26936973 / 2), 0, 9299649, 0, (-9924525 / 2), 0,
    (4102137 / 2), 0, -654472, 0, 159588, 0, -29172, 0, (7735 / 2), 0, -351, 0, (39 / 2), 0,
    (-1 / 2)]

theorem cubic_at_22 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 22) = node z 4 :=
  Checker.cubic_map (nodeRows.getD 22 []) (nodeRows.getD 4 []) cubicQuotient22
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient23 : List ℚ :=
  [0, (-75 / 2), 0, (4543 / 2), 0, (-101343 / 2), 0, (1157805 / 2), 0, -3923348, 0,
    (34550841 / 2), 0, (-105333039 / 2), 0, 116344226, 0, -192472965, 0, (488494773 / 2), 0,
    (-483841867 / 2), 0, (378658803 / 2), 0, -118015326, 0, 58839550, 0, -23477850, 0, 7472520,
    0, (-3764565 / 2), 0, (740259 / 2), 0, -55575, 0, 6150, 0, (-945 / 2), 0, (45 / 2), 0,
    (-1 / 2)]

theorem cubic_at_23 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 23) = node z 1 :=
  Checker.cubic_map (nodeRows.getD 23 []) (nodeRows.getD 1 []) cubicQuotient23
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient24 : List ℚ :=
  [0, 33, 0, -2090, 0, (97713 / 2), 0, -571824, 0, 3909191, 0, -17258904, 0, (105309015 / 2), 0,
    -116338616, 0, 192471282, 0, -244247073, 0, (483841801 / 2), 0, -189329400, 0, 118015326,
    0, -58839550, 0, 23477850, 0, -7472520, 0, (3764565 / 2), 0, (-740259 / 2), 0, 55575, 0,
    -6150, 0, (945 / 2), 0, (-45 / 2), 0, (1 / 2)]

theorem cubic_at_24 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 24) = node z 1 :=
  Checker.cubic_map (nodeRows.getD 24 []) (nodeRows.getD 1 []) cubicQuotient24
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient25 : List ℚ :=
  [0, -27, 0, 1305, 0, (-47061 / 2), 0, (416151 / 2), 0, (-2124969 / 2), 0, 3476817, 0,
    (-15600915 / 2), 0, (25110021 / 2), 0, (-29910465 / 2), 0, 13468455, 0, (-18599295 / 2), 0,
    (9924525 / 2), 0, (-4102137 / 2), 0, 654472, 0, -159588, 0, 29172, 0, (-7735 / 2), 0, 351,
    0, (-39 / 2), 0, (1 / 2)]

theorem cubic_at_25 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 25) = node z 4 :=
  Checker.cubic_map (nodeRows.getD 25 []) (nodeRows.getD 4 []) cubicQuotient25
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient26 : List ℚ :=
  [0, 21, 0, -763, 0, (20223 / 2), 0, (-127917 / 2), 0, (461891 / 2), 0, -529074, 0, 820743, 0,
    -898909, 0, (1427679 / 2), 0, -417450, 0, 180895, 0, -57915, 0, (27027 / 2), 0, -2233, 0,
    (495 / 2), 0, (-33 / 2), 0, (1 / 2)]

theorem cubic_at_26 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 26) = node z 7 :=
  Checker.cubic_map (nodeRows.getD 26 []) (nodeRows.getD 7 []) cubicQuotient26
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient27 : List ℚ :=
  [0, -15, 0, 410, 0, (-7371 / 2), 0, 15444, 0, -36465, 0, 53703, 0, -52326, 0, 34884, 0,
    (-32319 / 2), 0, (10395 / 2), 0, (-2277 / 2), 0, 162, 0, (-27 / 2), 0, (1 / 2)]

theorem cubic_at_27 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 27) = node z 10 :=
  Checker.cubic_map (nodeRows.getD 27 []) (nodeRows.getD 10 []) cubicQuotient27
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient28 : List ℚ :=
  [0, (21 / 2), 0, (-385 / 2), 0, (2079 / 2), 0, -2574, 0, (7007 / 2), 0, (-5733 / 2), 0, 1470,
    0, -476, 0, (189 / 2), 0, (-21 / 2), 0, (1 / 2)]

theorem cubic_at_28 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 28) = node z 13 :=
  Checker.cubic_map (nodeRows.getD 28 []) (nodeRows.getD 13 []) cubicQuotient28
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient29 : List ℚ :=
  [0, (-15 / 2), 0, 70, 0, -189, 0, 225, 0, (-275 / 2), 0, 45, 0, (-15 / 2), 0, (1 / 2)]

theorem cubic_at_29 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 29) = node z 16 :=
  Checker.cubic_map (nodeRows.getD 29 []) (nodeRows.getD 16 []) cubicQuotient29
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient30 : List ℚ :=
  [0, (9 / 2), 0, -15, 0, (27 / 2), 0, (-9 / 2), 0, (1 / 2)]

theorem cubic_at_30 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 30) = node z 19 :=
  Checker.cubic_map (nodeRows.getD 30 []) (nodeRows.getD 19 []) cubicQuotient30
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient31 : List ℚ :=
  [0, (-3 / 2), 0, (1 / 2)]

theorem cubic_at_31 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 31) = node z 22 :=
  Checker.cubic_map (nodeRows.getD 31 []) (nodeRows.getD 22 []) cubicQuotient31
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient32 : List ℚ :=
  []

theorem cubic_at_32 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 32) = node z 25 :=
  Checker.cubic_map (nodeRows.getD 32 []) (nodeRows.getD 25 []) cubicQuotient32
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient33 : List ℚ :=
  []

theorem cubic_at_33 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 33) = node z 28 :=
  Checker.cubic_map (nodeRows.getD 33 []) (nodeRows.getD 28 []) cubicQuotient33
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient34 : List ℚ :=
  []

theorem cubic_at_34 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 34) = node z 31 :=
  Checker.cubic_map (nodeRows.getD 34 []) (nodeRows.getD 31 []) cubicQuotient34
    modulusCoeffs z hm (by decide +kernel)

def cubicQuotient35 : List ℚ :=
  []

theorem cubic_at_35 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    cubic (node z 35) = node z 34 :=
  Checker.cubic_map (nodeRows.getD 35 []) (nodeRows.getD 34 []) cubicQuotient35
    modulusCoeffs z hm (by decide +kernel)

theorem cubic_at_node (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (j : Fin 36) : cubic (node z j) = node z (cubicMap.getD j 0) := by
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
  · exact cubic_at_18 z hm
  · exact cubic_at_19 z hm
  · exact cubic_at_20 z hm
  · exact cubic_at_21 z hm
  · exact cubic_at_22 z hm
  · exact cubic_at_23 z hm
  · exact cubic_at_24 z hm
  · exact cubic_at_25 z hm
  · exact cubic_at_26 z hm
  · exact cubic_at_27 z hm
  · exact cubic_at_28 z hm
  · exact cubic_at_29 z hm
  · exact cubic_at_30 z hm
  · exact cubic_at_31 z hm
  · exact cubic_at_32 z hm
  · exact cubic_at_33 z hm
  · exact cubic_at_34 z hm
  · exact cubic_at_35 z hm
end Lorentz.Plateau.Certificates.Even
