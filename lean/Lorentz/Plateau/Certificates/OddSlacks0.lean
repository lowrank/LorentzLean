module

public import Lorentz.Plateau.Certificates.OddData
public import Lorentz.Plateau.Certificates.Checker

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Odd

def slackQuotient0_0 : List ℚ :=
  [(6219749 / 7132971), (1082880 / 2377657), (-389272 / 7132971)]

theorem slack_0_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (-1 : ℝ) * (value z 1 -
      (correction 0 z).eval (node z 1)) =
      Certificate.eval ((slackRows.getD 0 []).getD 0 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 1 [])
      (gridValues.getD 1 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 0 []) slackQuotient0_0 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient0_1 : List ℚ :=
  [(33326765 / 14265942), (8537895 / 4755314), (-17294117 / 2377657), (-25163835 / 4755314),
    (78130967 / 14265942), (14670855 / 4755314), (-8555381 / 7132971), (-1082880 / 2377657),
    (389272 / 7132971)]

theorem slack_0_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (1 : ℝ) * (value z 4 -
      (correction 0 z).eval (node z 4)) =
      Certificate.eval ((slackRows.getD 0 []).getD 1 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 4 [])
      (gridValues.getD 4 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 1 []) slackQuotient0_1 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient0_2 : List ℚ :=
  [(-15255421 / 4755314), (-10703655 / 4755314), (52271623 / 7132971), (25163835 / 4755314),
    (-78130967 / 14265942), (-14670855 / 4755314), (8555381 / 7132971), (1082880 / 2377657),
    (-389272 / 7132971)]

theorem slack_0_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (1 : ℝ) * (value z 7 -
      (correction 0 z).eval (node z 7)) =
      Certificate.eval ((slackRows.getD 0 []).getD 2 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 7 [])
      (gridValues.getD 7 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 2 []) slackQuotient0_2 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient0_3 : List ℚ :=
  [(-15255421 / 4755314), (-10703655 / 4755314), (52271623 / 7132971), (25163835 / 4755314),
    (-78130967 / 14265942), (-14670855 / 4755314), (8555381 / 7132971), (1082880 / 2377657),
    (-389272 / 7132971)]

theorem slack_0_3 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (-1 : ℝ) * (value z 10 -
      (correction 0 z).eval (node z 10)) =
      Certificate.eval ((slackRows.getD 0 []).getD 3 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 10 [])
      (gridValues.getD 10 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 3 []) slackQuotient0_3 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient0_4 : List ℚ :=
  [(33326765 / 14265942), (8537895 / 4755314), (-17294117 / 2377657), (-25163835 / 4755314),
    (78130967 / 14265942), (14670855 / 4755314), (-8555381 / 7132971), (-1082880 / 2377657),
    (389272 / 7132971)]

theorem slack_0_4 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (-1 : ℝ) * (value z 13 -
      (correction 0 z).eval (node z 13)) =
      Certificate.eval ((slackRows.getD 0 []).getD 4 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 13 [])
      (gridValues.getD 13 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 4 []) slackQuotient0_4 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient0_5 : List ℚ :=
  [(6219749 / 7132971), (1082880 / 2377657), (-389272 / 7132971)]

theorem slack_0_5 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 0 - (1 : ℝ) * (value z 16 -
      (correction 0 z).eval (node z 16)) =
      Certificate.eval ((slackRows.getD 0 []).getD 5 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 0 []) (nodeRows.getD 16 [])
      (gridValues.getD 16 []) (slopeRows.getD 0 [])
      ((slackRows.getD 0 []).getD 5 []) slackQuotient0_5 modulusCoeffs
      (1) z hm (by decide +kernel)

theorem all_slacks_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (j : Fin 6) : slope z 0 - (gridSign 0 j : ℝ) *
      (value z (gridIndex 0 j) - (correction 0 z).eval (node z (gridIndex 0 j))) =
      Certificate.eval ((slackRows.getD 0 []).getD j []) z := by
  fin_cases j
  · simpa [gridSign, gridIndex] using slack_0_0 z hm
  · simpa [gridSign, gridIndex] using slack_0_1 z hm
  · simpa [gridSign, gridIndex] using slack_0_2 z hm
  · simpa [gridSign, gridIndex] using slack_0_3 z hm
  · simpa [gridSign, gridIndex] using slack_0_4 z hm
  · simpa [gridSign, gridIndex] using slack_0_5 z hm
end Lorentz.Plateau.Certificates.Odd
