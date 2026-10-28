module

public import Lorentz.Plateau.Certificates.EvenData
public import Lorentz.Plateau.Certificates.Checker

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Even

def slackQuotient1_0 : List ℚ :=
  []

theorem slack_1_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 1 -
      (correction 1 z).eval (node z 1)) =
      Certificate.eval ((slackRows.getD 1 []).getD 0 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 1 [])
      (gridValues.getD 1 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 0 []) slackQuotient1_0 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_1 : List ℚ :=
  []

theorem slack_1_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 4 -
      (correction 1 z).eval (node z 4)) =
      Certificate.eval ((slackRows.getD 1 []).getD 1 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 4 [])
      (gridValues.getD 4 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 1 []) slackQuotient1_1 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_2 : List ℚ :=
  [1, 0, (-9 / 2), 0, 3, 0, (-1 / 2)]

theorem slack_1_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 7 -
      (correction 1 z).eval (node z 7)) =
      Certificate.eval ((slackRows.getD 1 []).getD 2 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 7 [])
      (gridValues.getD 7 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 2 []) slackQuotient1_2 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_3 : List ℚ :=
  [-1, 0, (81 / 2), 0, -270, 0, 693, 0, -891, 0, (1287 / 2), 0, -273, 0, (135 / 2), 0, -9, 0,
    (1 / 2)]

theorem slack_1_3 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 10 -
      (correction 1 z).eval (node z 10)) =
      Certificate.eval ((slackRows.getD 1 []).getD 3 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 10 [])
      (gridValues.getD 10 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 3 []) slackQuotient1_3 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_4 : List ℚ :=
  [-2, 0, (81 / 2), 0, -270, 0, 693, 0, -891, 0, (1287 / 2), 0, -273, 0, (135 / 2), 0, -9, 0,
    (1 / 2)]

theorem slack_1_4 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 13 -
      (correction 1 z).eval (node z 13)) =
      Certificate.eval ((slackRows.getD 1 []).getD 4 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 13 [])
      (gridValues.getD 13 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 4 []) slackQuotient1_4 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_5 : List ℚ :=
  [2, 0, (-9 / 2), 0, 3, 0, (-1 / 2)]

theorem slack_1_5 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 16 -
      (correction 1 z).eval (node z 16)) =
      Certificate.eval ((slackRows.getD 1 []).getD 5 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 16 [])
      (gridValues.getD 16 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 5 []) slackQuotient1_5 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_6 : List ℚ :=
  [2, 0, (-9 / 2), 0, 3, 0, (-1 / 2)]

theorem slack_1_6 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 19 -
      (correction 1 z).eval (node z 19)) =
      Certificate.eval ((slackRows.getD 1 []).getD 6 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 19 [])
      (gridValues.getD 19 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 6 []) slackQuotient1_6 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_7 : List ℚ :=
  [-2, 0, (81 / 2), 0, -270, 0, 693, 0, -891, 0, (1287 / 2), 0, -273, 0, (135 / 2), 0, -9, 0,
    (1 / 2)]

theorem slack_1_7 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 22 -
      (correction 1 z).eval (node z 22)) =
      Certificate.eval ((slackRows.getD 1 []).getD 7 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 22 [])
      (gridValues.getD 22 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 7 []) slackQuotient1_7 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_8 : List ℚ :=
  [-1, 0, (81 / 2), 0, -270, 0, 693, 0, -891, 0, (1287 / 2), 0, -273, 0, (135 / 2), 0, -9, 0,
    (1 / 2)]

theorem slack_1_8 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 25 -
      (correction 1 z).eval (node z 25)) =
      Certificate.eval ((slackRows.getD 1 []).getD 8 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 25 [])
      (gridValues.getD 25 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 8 []) slackQuotient1_8 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_9 : List ℚ :=
  [1, 0, (-9 / 2), 0, 3, 0, (-1 / 2)]

theorem slack_1_9 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 28 -
      (correction 1 z).eval (node z 28)) =
      Certificate.eval ((slackRows.getD 1 []).getD 9 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 28 [])
      (gridValues.getD 28 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 9 []) slackQuotient1_9 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_10 : List ℚ :=
  []

theorem slack_1_10 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 31 -
      (correction 1 z).eval (node z 31)) =
      Certificate.eval ((slackRows.getD 1 []).getD 10 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 31 [])
      (gridValues.getD 31 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 10 []) slackQuotient1_10 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_11 : List ℚ :=
  []

theorem slack_1_11 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 34 -
      (correction 1 z).eval (node z 34)) =
      Certificate.eval ((slackRows.getD 1 []).getD 11 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 34 [])
      (gridValues.getD 34 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 11 []) slackQuotient1_11 modulusCoeffs
      (1) z hm (by decide +kernel)

theorem all_slacks_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (j : Fin 12) : slope z 1 - (gridSign 1 j : ℝ) *
      (value z (gridIndex 1 j) - (correction 1 z).eval (node z (gridIndex 1 j))) =
      Certificate.eval ((slackRows.getD 1 []).getD j []) z := by
  fin_cases j
  · simpa [gridSign, gridIndex] using slack_1_0 z hm
  · simpa [gridSign, gridIndex] using slack_1_1 z hm
  · simpa [gridSign, gridIndex] using slack_1_2 z hm
  · simpa [gridSign, gridIndex] using slack_1_3 z hm
  · simpa [gridSign, gridIndex] using slack_1_4 z hm
  · simpa [gridSign, gridIndex] using slack_1_5 z hm
  · simpa [gridSign, gridIndex] using slack_1_6 z hm
  · simpa [gridSign, gridIndex] using slack_1_7 z hm
  · simpa [gridSign, gridIndex] using slack_1_8 z hm
  · simpa [gridSign, gridIndex] using slack_1_9 z hm
  · simpa [gridSign, gridIndex] using slack_1_10 z hm
  · simpa [gridSign, gridIndex] using slack_1_11 z hm
end Lorentz.Plateau.Certificates.Even
