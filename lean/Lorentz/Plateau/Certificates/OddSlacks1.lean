module

public import Lorentz.Plateau.Certificates.OddData
public import Lorentz.Plateau.Certificates.Checker

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/

namespace Lorentz.Plateau.Certificates.Odd

def slackQuotient1_0 : List ℚ :=
  [(2842537 / 11888285), (4723166 / 2377657), (16552778 / 35664855)]

theorem slack_1_0 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 0 -
      (correction 1 z).eval (node z 0)) =
      Certificate.eval ((slackRows.getD 1 []).getD 0 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 0 [])
      (gridValues.getD 0 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 0 []) slackQuotient1_0 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_1 : List ℚ :=
  [(-47299279 / 71329710), (26720390 / 2377657), (252673273 / 23776570), (-118525883 / 4755314),
    (-780230917 / 71329710), (63928377 / 4755314), (138449603 / 35664855),
    (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 1 -
      (correction 1 z).eval (node z 1)) =
      Certificate.eval ((slackRows.getD 1 []).getD 1 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 1 [])
      (gridValues.getD 1 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 1 []) slackQuotient1_1 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_2 : List ℚ :=
  [(2039020 / 2377657), (-44254981 / 2377657), (-2028917843 / 71329710), (656392011 / 4755314),
    (2663265717 / 23776570), (-1474142949 / 4755314), (-11383368463 / 71329710),
    (1352275791 / 4755314), (2574038629 / 23776570), (-587113133 / 4755314),
    (-451444436 / 11888285), (120606369 / 4755314), (237766271 / 35664855),
    (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_2 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 2 -
      (correction 1 z).eval (node z 2)) =
      Certificate.eval ((slackRows.getD 1 []).getD 2 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 2 [])
      (gridValues.getD 2 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 2 []) slackQuotient1_2 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_3 : List ℚ :=
  [(-3836872 / 35664855), (-60761152 / 2377657), (-2275037671 / 23776570),
    (1943070821 / 4755314), (22443203051 / 35664855), (-9221813271 / 4755314),
    (-40237234523 / 23776570), (9970409012 / 2377657), (5881984858 / 2377657),
    (-11419694873 / 2377657), (-30801020249 / 14265942), (7556514315 / 2377657),
    (13918128588 / 11888285), (-2989652287 / 2377657), (-4725171519 / 11888285),
    (1395768335 / 4755314), (976635312 / 11888285), (-177284361 / 4755314),
    (-337082939 / 35664855), (4723166 / 2377657), (16552778 / 35664855)]

theorem slack_1_3 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 3 -
      (correction 1 z).eval (node z 3)) =
      Certificate.eval ((slackRows.getD 1 []).getD 3 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 3 [])
      (gridValues.getD 3 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 3 []) slackQuotient1_3 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_4 : List ℚ :=
  [(71663777 / 71329710), (182948533 / 4755314), (1746958334 / 11888285),
    (-4382222063 / 4755314), (-42784010513 / 23776570), (35040281589 / 4755314),
    (62606643848 / 7132971), (-133124398513 / 4755314), (-54680977989 / 2377657),
    (281771406539 / 4755314), (1307111479181 / 35664855), (-182260055838 / 2377657),
    (-452046627269 / 11888285), (152471788493 / 2377657), (952043676271 / 35664855),
    (-85061419681 / 2377657), (-153558222484 / 11888285), (63905339811 / 4755314),
    (61534135055 / 14265942), (-15968366497 / 4755314), (-6964360436 / 7132971),
    (2544491489 / 4755314), (1700459524 / 11888285), (-233962353 / 4755314),
    (-436399607 / 35664855), (4723166 / 2377657), (16552778 / 35664855)]

theorem slack_1_4 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 4 -
      (correction 1 z).eval (node z 4)) =
      Certificate.eval ((slackRows.getD 1 []).getD 4 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 4 [])
      (gridValues.getD 4 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 4 []) slackQuotient1_4 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_5 : List ℚ :=
  [(49354096 / 11888285), (129640280 / 2377657), (6322150269 / 23776570),
    (-8482163527 / 4755314), (-361697729333 / 71329710), (50572274631 / 2377657),
    (425794708586 / 11888285), (-587666536193 / 4755314), (-9911875678309 / 71329710),
    (1953149116511 / 4755314), (12081488066591 / 35664855), (-110367076137 / 128522),
    (-535746945053 / 963915), (5708335123885 / 4755314), (45653963028353 / 71329710),
    (-2776117089929 / 2377657), (-37901145469451 / 71329710), (3852920523111 / 4755314),
    (11525338359482 / 35664855), (-1932755958119 / 4755314), (-5170592231024 / 35664855),
    (702359159679 / 4755314), (3414602249623 / 71329710), (-91541943450 / 2377657),
    (-273034238053 / 23776570), (16679934636 / 2377657), (69390775631 / 35664855),
    (-22532305 / 26566), (-14653168 / 66415), (290640345 / 4755314), (107143255 / 7132971),
    (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_5 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 5 -
      (correction 1 z).eval (node z 5)) =
      Certificate.eval ((slackRows.getD 1 []).getD 5 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 5 [])
      (gridValues.getD 5 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 5 []) slackQuotient1_5 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_6 : List ℚ :=
  [(-171749453 / 35664855), (-309884285 / 4755314), (-7494663657 / 23776570),
    (10632027991 / 4755314), (198543397816 / 35664855), (-59549644620 / 2377657),
    (-545111322167 / 14265942), (3622017631 / 26566), (3851191719 / 26566),
    (-2057594124803 / 4755314), (-8256669231989 / 23776570), (2092820794005 / 2377657),
    (20080484445689 / 35664855), (-2884173414839 / 2377657), (-7654416001256 / 11888285),
    (2786942111747 / 2377657), (12663826057123 / 23776570), (-3857611342203 / 4755314),
    (-3844823825651 / 11888285), (966658075099 / 2377657), (5171622228634 / 35664855),
    (-702387498675 / 4755314), (-3414701566291 / 71329710), (91541943450 / 2377657),
    (273034238053 / 23776570), (-16679934636 / 2377657), (-69390775631 / 35664855),
    (22532305 / 26566), (14653168 / 66415), (-290640345 / 4755314), (-107143255 / 7132971),
    (4723166 / 2377657), (16552778 / 35664855)]

theorem slack_1_6 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 6 -
      (correction 1 z).eval (node z 6)) =
      Certificate.eval ((slackRows.getD 1 []).getD 6 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 6 [])
      (gridValues.getD 6 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 6 []) slackQuotient1_6 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_7 : List ℚ :=
  [(-225986387 / 23776570), (-152130586 / 2377657), (-29975909713 / 71329710),
    (4776158927 / 2377657), (270892086353 / 71329710), (-62366374485 / 4755314),
    (-508275149189 / 35664855), (192899620925 / 4755314), (2204254002059 / 71329710),
    (-350289575777 / 4755314), (-3096548208191 / 71329710), (570834537 / 6623),
    (1654099859 / 39738), (-161440745354 / 2377657), (-995064772598 / 35664855),
    (174310144367 / 4755314), (469495294801 / 35664855), (-32218596447 / 2377657),
    (-309693172909 / 71329710), (15996705493 / 4755314), (34871460514 / 35664855),
    (-2544491489 / 4755314), (-1700459524 / 11888285), (233962353 / 4755314),
    (436399607 / 35664855), (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_7 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 7 -
      (correction 1 z).eval (node z 7)) =
      Certificate.eval ((slackRows.getD 1 []).getD 7 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 7 [])
      (gridValues.getD 7 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 7 []) slackQuotient1_7 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_8 : List ℚ :=
  [(4094327 / 642610), (159530759 / 2377657), (2788378966 / 7132971), (-4483470268 / 2377657),
    (-166719642671 / 71329710), (17732854551 / 2377657), (76658738717 / 14265942),
    (-60125820259 / 4755314), (-155607912263 / 23776570), (27422473038 / 2377657),
    (169137077011 / 35664855), (-29516096799 / 4755314), (-76709317174 / 35664855),
    (4836270912 / 2377657), (4404038932 / 7132971), (-949641211 / 2377657),
    (-1297165473 / 11888285), (205623357 / 4755314), (386741273 / 35664855),
    (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_8 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 8 -
      (correction 1 z).eval (node z 8)) =
      Certificate.eval ((slackRows.getD 1 []).getD 8 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 8 [])
      (gridValues.getD 8 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 8 []) slackQuotient1_8 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_9 : List ℚ :=
  [(19094647 / 1927830), (159530759 / 2377657), (5435095296 / 11888285), (-4483470268 / 2377657),
    (-179478150133 / 71329710), (17732854551 / 2377657), (78941289437 / 14265942),
    (-60125820259 / 4755314), (-471426880741 / 71329710), (27422473038 / 2377657),
    (11304654039 / 2377657), (-29516096799 / 4755314), (-15348045343 / 7132971),
    (4836270912 / 2377657), (4404038932 / 7132971), (-949641211 / 2377657),
    (-1297165473 / 11888285), (205623357 / 4755314), (386741273 / 35664855),
    (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_9 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 9 -
      (correction 1 z).eval (node z 9)) =
      Certificate.eval ((slackRows.getD 1 []).getD 9 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 9 [])
      (gridValues.getD 9 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 9 []) slackQuotient1_9 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_10 : List ℚ :=
  [(-79479127 / 14265942), (-152130586 / 2377657), (-5175365809 / 14265942),
    (4776158927 / 2377657), (82977348767 / 23776570), (-62366374485 / 4755314),
    (-487446873869 / 35664855), (192899620925 / 4755314), (432813368689 / 14265942),
    (-350289575777 / 4755314), (-3075063699539 / 71329710), (570834537 / 6623),
    (550178895 / 13246), (-161440745354 / 2377657), (-994570219942 / 35664855),
    (174310144367 / 4755314), (31297625684 / 2377657), (-32218596447 / 2377657),
    (-309693172909 / 71329710), (15996705493 / 4755314), (34871460514 / 35664855),
    (-2544491489 / 4755314), (-1700459524 / 11888285), (233962353 / 4755314),
    (436399607 / 35664855), (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_10 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 10 -
      (correction 1 z).eval (node z 10)) =
      Certificate.eval ((slackRows.getD 1 []).getD 10 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 10 [])
      (gridValues.getD 10 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 10 []) slackQuotient1_10 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_11 : List ℚ :=
  [(-53846678 / 7132971), (-309884285 / 4755314), (-25213541207 / 71329710),
    (10632027991 / 4755314), (217455281594 / 35664855), (-59549644620 / 2377657),
    (-2863879184467 / 71329710), (3622017631 / 26566), (59117216057 / 398490),
    (-2057594124803 / 4755314), (-1667020676221 / 4755314), (2092820794005 / 2377657),
    (20149046562941 / 35664855), (-2884173414839 / 2377657), (-22987709338984 / 35664855),
    (2786942111747 / 2377657), (38001954128111 / 71329710), (-3857611342203 / 4755314),
    (-11535089667773 / 35664855), (966658075099 / 2377657), (1034330627635 / 7132971),
    (-702387498675 / 4755314), (-3414701566291 / 71329710), (91541943450 / 2377657),
    (273034238053 / 23776570), (-16679934636 / 2377657), (-69390775631 / 35664855),
    (22532305 / 26566), (14653168 / 66415), (-290640345 / 4755314), (-107143255 / 7132971),
    (4723166 / 2377657), (16552778 / 35664855)]

theorem slack_1_11 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 11 -
      (correction 1 z).eval (node z 11)) =
      Certificate.eval ((slackRows.getD 1 []).getD 11 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 11 [])
      (gridValues.getD 11 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 11 []) slackQuotient1_11 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_12 : List ℚ :=
  [(71977264 / 35664855), (129640280 / 2377657), (5637385053 / 23776570),
    (-8482163527 / 4755314), (-327250234717 / 71329710), (50572274631 / 2377657),
    (1209858666958 / 35664855), (-587666536193 / 4755314), (-3223818837699 / 23776570),
    (1953149116511 / 4755314), (11963898661999 / 35664855), (-110367076137 / 128522),
    (-533893914857 / 963915), (5708335123885 / 4755314), (15201680119307 / 23776570),
    (-2776117089929 / 2377657), (-12630223170903 / 23776570), (3852920523111 / 4755314),
    (3841573389554 / 11888285), (-1932755958119 / 4755314), (-5170561321483 / 35664855),
    (702359159679 / 4755314), (3414602249623 / 71329710), (-91541943450 / 2377657),
    (-273034238053 / 23776570), (16679934636 / 2377657), (69390775631 / 35664855),
    (-22532305 / 26566), (-14653168 / 66415), (290640345 / 4755314), (107143255 / 7132971),
    (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_12 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 12 -
      (correction 1 z).eval (node z 12)) =
      Certificate.eval ((slackRows.getD 1 []).getD 12 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 12 [])
      (gridValues.getD 12 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 12 []) slackQuotient1_12 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_13 : List ℚ :=
  [(55590019 / 23776570), (182948533 / 4755314), (6220469686 / 35664855),
    (-4382222063 / 4755314), (-144591428849 / 71329710), (35040281589 / 4755314),
    (331731113888 / 35664855), (-133124398513 / 4755314), (-839690058322 / 35664855),
    (281771406539 / 4755314), (87852794295 / 2377657), (-182260055838 / 2377657),
    (-1359337830472 / 35664855), (152471788493 / 2377657), (952538228927 / 35664855),
    (-85061419681 / 2377657), (-460705576993 / 35664855), (63905339811 / 4755314),
    (61534135055 / 14265942), (-15968366497 / 4755314), (-6964360436 / 7132971),
    (2544491489 / 4755314), (1700459524 / 11888285), (-233962353 / 4755314),
    (-436399607 / 35664855), (4723166 / 2377657), (16552778 / 35664855)]

theorem slack_1_13 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 13 -
      (correction 1 z).eval (node z 13)) =
      Certificate.eval ((slackRows.getD 1 []).getD 13 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 13 [])
      (gridValues.getD 13 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 13 []) slackQuotient1_13 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_14 : List ℚ :=
  [(15184384 / 35664855), (-60761152 / 2377657), (-356097003 / 4755314), (1943070821 / 4755314),
    (6518909151 / 11888285), (-9221813271 / 4755314), (-114054263969 / 71329710),
    (9970409012 / 2377657), (17315460251 / 7132971), (-11419694873 / 2377657),
    (-153263272261 / 71329710), (7556514315 / 2377657), (41723476223 / 35664855),
    (-2989652287 / 2377657), (-4725171519 / 11888285), (1395768335 / 4755314),
    (976635312 / 11888285), (-177284361 / 4755314), (-337082939 / 35664855),
    (4723166 / 2377657), (16552778 / 35664855)]

theorem slack_1_14 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 14 -
      (correction 1 z).eval (node z 14)) =
      Certificate.eval ((slackRows.getD 1 []).getD 14 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 14 [])
      (gridValues.getD 14 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 14 []) slackQuotient1_14 modulusCoeffs
      (-1) z hm (by decide +kernel)

def slackQuotient1_15 : List ℚ :=
  [(32962957 / 35664855), (-44254981 / 2377657), (-2884874363 / 71329710), (656392011 / 4755314),
    (9192891593 / 71329710), (-1474142949 / 4755314), (-11877921119 / 71329710),
    (1352275791 / 4755314), (7783934969 / 71329710), (-587113133 / 4755314),
    (-451444436 / 11888285), (120606369 / 4755314), (237766271 / 35664855),
    (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_15 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 15 -
      (correction 1 z).eval (node z 15)) =
      Certificate.eval ((slackRows.getD 1 []).getD 15 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 15 [])
      (gridValues.getD 15 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 15 []) slackQuotient1_15 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_16 : List ℚ :=
  [(43051687 / 71329710), (26720390 / 2377657), (510743491 / 71329710), (-118525883 / 4755314),
    (-143682367 / 14265942), (63928377 / 4755314), (138449603 / 35664855),
    (-4723166 / 2377657), (-16552778 / 35664855)]

theorem slack_1_16 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (1 : ℝ) * (value z 16 -
      (correction 1 z).eval (node z 16)) =
      Certificate.eval ((slackRows.getD 1 []).getD 16 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 16 [])
      (gridValues.getD 16 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 16 []) slackQuotient1_16 modulusCoeffs
      (1) z hm (by decide +kernel)

def slackQuotient1_17 : List ℚ :=
  [(-4476386 / 7132971), (4723166 / 2377657), (16552778 / 35664855)]

theorem slack_1_17 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :
    slope z 1 - (-1 : ℝ) * (value z 17 -
      (correction 1 z).eval (node z 17)) =
      Certificate.eval ((slackRows.getD 1 []).getD 17 []) z := by
  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using
    Checker.slack (correctionRows.getD 1 []) (nodeRows.getD 17 [])
      (gridValues.getD 17 []) (slopeRows.getD 1 [])
      ((slackRows.getD 1 []).getD 17 []) slackQuotient1_17 modulusCoeffs
      (-1) z hm (by decide +kernel)

theorem all_slacks_1 (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)
    (j : Fin 18) : slope z 1 - (gridSign 1 j : ℝ) *
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
  · simpa [gridSign, gridIndex] using slack_1_12 z hm
  · simpa [gridSign, gridIndex] using slack_1_13 z hm
  · simpa [gridSign, gridIndex] using slack_1_14 z hm
  · simpa [gridSign, gridIndex] using slack_1_15 z hm
  · simpa [gridSign, gridIndex] using slack_1_16 z hm
  · simpa [gridSign, gridIndex] using slack_1_17 z hm
end Lorentz.Plateau.Certificates.Odd
