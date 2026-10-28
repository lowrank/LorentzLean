module

public import Lorentz.Plateau.Certificates.EvenData
public import Lorentz.Plateau.Certificates.Checker

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Even

def slackQuotient0_0 : List ℚ :=
  []

theorem slack_0_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (1 : ℝ) * (value z 1 -
      (correction 0 z).eval (node z 1)) =
      Certificate.eval ((slackRows.getD 0 []).getD 0 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 1 [])
      (gridValues.getD 1 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 0 []) slackQuotient0_0 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient0_1 : List ℚ :=
  []

theorem slack_0_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (-1 : ℝ) * (value z 4 -
      (correction 0 z).eval (node z 4)) =
      Certificate.eval ((slackRows.getD 0 []).getD 1 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 4 [])
      (gridValues.getD 4 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 1 []) slackQuotient0_1 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient0_2 : List ℚ :=
  []

theorem slack_0_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (-1 : ℝ) * (value z 7 -
      (correction 0 z).eval (node z 7)) =
      Certificate.eval ((slackRows.getD 0 []).getD 2 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 7 [])
      (gridValues.getD 7 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 2 []) slackQuotient0_2 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient0_3 : List ℚ :=
  []

theorem slack_0_3 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (1 : ℝ) * (value z 10 -
      (correction 0 z).eval (node z 10)) =
      Certificate.eval ((slackRows.getD 0 []).getD 3 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 10 [])
      (gridValues.getD 10 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 3 []) slackQuotient0_3 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient0_4 : List ℚ :=
  []

theorem slack_0_4 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (1 : ℝ) * (value z 13 -
      (correction 0 z).eval (node z 13)) =
      Certificate.eval ((slackRows.getD 0 []).getD 4 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 13 [])
      (gridValues.getD 13 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 4 []) slackQuotient0_4 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient0_5 : List ℚ :=
  []

theorem slack_0_5 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (-1 : ℝ) * (value z 16 -
      (correction 0 z).eval (node z 16)) =
      Certificate.eval ((slackRows.getD 0 []).getD 5 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 16 [])
      (gridValues.getD 16 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 5 []) slackQuotient0_5 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient0_6 : List ℚ :=
  []

theorem slack_0_6 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (-1 : ℝ) * (value z 19 -
      (correction 0 z).eval (node z 19)) =
      Certificate.eval ((slackRows.getD 0 []).getD 6 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 19 [])
      (gridValues.getD 19 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 6 []) slackQuotient0_6 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient0_7 : List ℚ :=
  []

theorem slack_0_7 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (1 : ℝ) * (value z 22 -
      (correction 0 z).eval (node z 22)) =
      Certificate.eval ((slackRows.getD 0 []).getD 7 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 22 [])
      (gridValues.getD 22 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 7 []) slackQuotient0_7 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient0_8 : List ℚ :=
  []

theorem slack_0_8 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (1 : ℝ) * (value z 25 -
      (correction 0 z).eval (node z 25)) =
      Certificate.eval ((slackRows.getD 0 []).getD 8 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 25 [])
      (gridValues.getD 25 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 8 []) slackQuotient0_8 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient0_9 : List ℚ :=
  []

theorem slack_0_9 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (-1 : ℝ) * (value z 28 -
      (correction 0 z).eval (node z 28)) =
      Certificate.eval ((slackRows.getD 0 []).getD 9 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 28 [])
      (gridValues.getD 28 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 9 []) slackQuotient0_9 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient0_10 : List ℚ :=
  []

theorem slack_0_10 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (-1 : ℝ) * (value z 31 -
      (correction 0 z).eval (node z 31)) =
      Certificate.eval ((slackRows.getD 0 []).getD 10 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 31 [])
      (gridValues.getD 31 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 10 []) slackQuotient0_10 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient0_11 : List ℚ :=
  []

theorem slack_0_11 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (1 : ℝ) * (value z 34 -
      (correction 0 z).eval (node z 34)) =
      Certificate.eval ((slackRows.getD 0 []).getD 11 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 34 [])
      (gridValues.getD 34 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 11 []) slackQuotient0_11 modulusCoeffs
      (1) z hm (by decide +kernel)

theorem all_slacks_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (j : Fin 12) : slope z 0 - (gridSign 0 j : ℝ) *
      (value z (gridIndex 0 j) - (correction 0 z).eval (node z (gridIndex 0 j))) =
      Certificate.eval ((slackRows.getD 0 []).getD j []) z := by
  fin_cases j
  · simpa [gridSign, gridIndex] using slack_0_0 z hm
  · simpa [gridSign, gridIndex] using slack_0_1 z hm
  · simpa [gridSign, gridIndex] using slack_0_2 z hm
  · simpa [gridSign, gridIndex] using slack_0_3 z hm
  · simpa [gridSign, gridIndex] using slack_0_4 z hm
  · simpa [gridSign, gridIndex] using slack_0_5 z hm
  · simpa [gridSign, gridIndex] using slack_0_6 z hm
  · simpa [gridSign, gridIndex] using slack_0_7 z hm
  · simpa [gridSign, gridIndex] using slack_0_8 z hm
  · simpa [gridSign, gridIndex] using slack_0_9 z hm
  · simpa [gridSign, gridIndex] using slack_0_10 z hm
  · simpa [gridSign, gridIndex] using slack_0_11 z hm
end Lorentz.Plateau.Certificates.Even
