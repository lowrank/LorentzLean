module

public import Lorentz.PolynomialCertificate

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Lorentz.Certificate

theorem slack_identity_0_0 (z : ℝ) (hm : modulus z = 0) :
    slope 0 z - gridSign 0 0 *
      (gridPerturbation z (gridIndex 0 0) - correction 0 z (node z (gridIndex 0 0))) =
        eval (slackCoeffs 0 0) z := by
  exact PolynomialCertificate.checked_slack 0 0
    [(-45 / 214), (93 / 107), (583 / 428), (-217 / 107), (-242 / 107), (189 / 214),
      (425 / 428), (-11 / 107), (-27 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_0_1 (z : ℝ) (hm : modulus z = 0) :
    slope 0 z - gridSign 0 1 *
      (gridPerturbation z (gridIndex 0 1) - correction 0 z (node z (gridIndex 0 1))) =
        eval (slackCoeffs 0 1) z := by
  exact PolynomialCertificate.checked_slack 0 1
    [(-84 / 107), (-213 / 107), (-1425 / 428), (651 / 107), (726 / 107), (-567 / 214),
      (-1275 / 428), (33 / 107), (81 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_0_2 (z : ℝ) (hm : modulus z = 0) :
    slope 0 z - gridSign 0 2 *
      (gridPerturbation z (gridIndex 0 2) - correction 0 z (node z (gridIndex 0 2))) =
        eval (slackCoeffs 0 2) z := by
  exact PolynomialCertificate.checked_slack 0 2
    [(45 / 214), (-93 / 107), (-583 / 428), (217 / 107), (242 / 107), (-189 / 214),
      (-425 / 428), (11 / 107), (27 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_0_3 (z : ℝ) (hm : modulus z = 0) :
    slope 0 z - gridSign 0 3 *
      (gridPerturbation z (gridIndex 0 3) - correction 0 z (node z (gridIndex 0 3))) =
        eval (slackCoeffs 0 3) z := by
  exact PolynomialCertificate.checked_slack 0 3
    [(45 / 214), (-93 / 107), (-583 / 428), (217 / 107), (242 / 107), (-189 / 214),
      (-425 / 428), (11 / 107), (27 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_0_4 (z : ℝ) (hm : modulus z = 0) :
    slope 0 z - gridSign 0 4 *
      (gridPerturbation z (gridIndex 0 4) - correction 0 z (node z (gridIndex 0 4))) =
        eval (slackCoeffs 0 4) z := by
  exact PolynomialCertificate.checked_slack 0 4
    [(-84 / 107), (-213 / 107), (-1425 / 428), (651 / 107), (726 / 107), (-567 / 214),
      (-1275 / 428), (33 / 107), (81 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_0_5 (z : ℝ) (hm : modulus z = 0) :
    slope 0 z - gridSign 0 5 *
      (gridPerturbation z (gridIndex 0 5) - correction 0 z (node z (gridIndex 0 5))) =
        eval (slackCoeffs 0 5) z := by
  exact PolynomialCertificate.checked_slack 0 5
    [(-45 / 214), (93 / 107), (583 / 428), (-217 / 107), (-242 / 107), (189 / 214),
      (425 / 428), (-11 / 107), (-27 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_1_0 (z : ℝ) (hm : modulus z = 0) :
    slope 1 z - gridSign 1 0 *
      (gridPerturbation z (gridIndex 1 0) - correction 1 z (node z (gridIndex 1 0))) =
        eval (slackCoeffs 1 0) z := by
  exact PolynomialCertificate.checked_slack 1 0
    [(28 / 107), (71 / 107), (475 / 428), (-217 / 107), (-242 / 107), (189 / 214), (425 / 428),
      (-11 / 107), (-27 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_1_1 (z : ℝ) (hm : modulus z = 0) :
    slope 1 z - gridSign 1 1 *
      (gridPerturbation z (gridIndex 1 1) - correction 1 z (node z (gridIndex 1 1))) =
        eval (slackCoeffs 1 1) z := by
  exact PolynomialCertificate.checked_slack 1 1
    [(-140 / 107), (-355 / 107), (-2375 / 428), (1085 / 107), (1210 / 107), (-945 / 214),
      (-2125 / 428), (55 / 107), (135 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_1_2 (z : ℝ) (hm : modulus z = 0) :
    slope 1 z - gridSign 1 2 *
      (gridPerturbation z (gridIndex 1 2) - correction 1 z (node z (gridIndex 1 2))) =
        eval (slackCoeffs 1 2) z := by
  exact PolynomialCertificate.checked_slack 1 2
    [(28 / 107), (71 / 107), (475 / 428), (-217 / 107), (-242 / 107), (189 / 214), (425 / 428),
      (-11 / 107), (-27 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_1_3 (z : ℝ) (hm : modulus z = 0) :
    slope 1 z - gridSign 1 3 *
      (gridPerturbation z (gridIndex 1 3) - correction 1 z (node z (gridIndex 1 3))) =
        eval (slackCoeffs 1 3) z := by
  exact PolynomialCertificate.checked_slack 1 3
    [(28 / 107), (71 / 107), (475 / 428), (-217 / 107), (-242 / 107), (189 / 214), (425 / 428),
      (-11 / 107), (-27 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_1_4 (z : ℝ) (hm : modulus z = 0) :
    slope 1 z - gridSign 1 4 *
      (gridPerturbation z (gridIndex 1 4) - correction 1 z (node z (gridIndex 1 4))) =
        eval (slackCoeffs 1 4) z := by
  exact PolynomialCertificate.checked_slack 1 4
    [(-140 / 107), (-355 / 107), (-2375 / 428), (1085 / 107), (1210 / 107), (-945 / 214),
      (-2125 / 428), (55 / 107), (135 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_1_5 (z : ℝ) (hm : modulus z = 0) :
    slope 1 z - gridSign 1 5 *
      (gridPerturbation z (gridIndex 1 5) - correction 1 z (node z (gridIndex 1 5))) =
        eval (slackCoeffs 1 5) z := by
  exact PolynomialCertificate.checked_slack 1 5
    [(28 / 107), (71 / 107), (475 / 428), (-217 / 107), (-242 / 107), (189 / 214), (425 / 428),
      (-11 / 107), (-27 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_3_0 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 0 *
      (gridPerturbation z (gridIndex 3 0) - correction 3 z (node z (gridIndex 3 0))) =
        eval (slackCoeffs 3 0) z := by
  exact PolynomialCertificate.checked_slack 3 0
    [(137 / 214), (449 / 321), (939 / 428), (-652 / 321), (-1435 / 642), (1 / 2), (7 / 12),
      (-11 / 321), (-9 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_3_1 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 1 *
      (gridPerturbation z (gridIndex 3 1) - correction 3 z (node z (gridIndex 3 1))) =
        eval (slackCoeffs 3 1) z := by
  exact PolynomialCertificate.checked_slack 3 1
    [(-287 / 107), (-865 / 321), (3205 / 428), (341 / 321), (-1454 / 321), (-313 / 214),
      (399 / 428), (109 / 321), (-17 / 321)]
    z hm (by decide +kernel)

theorem slack_identity_3_2 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 2 *
      (gridPerturbation z (gridIndex 3 2) - correction 3 z (node z (gridIndex 3 2))) =
        eval (slackCoeffs 3 2) z := by
  exact PolynomialCertificate.checked_slack 3 2
    [(-77 / 214), (1052 / 321), (-6537 / 428), (-6059 / 321), (9439 / 214), (8763 / 214),
      (-51227 / 1284), (-13510 / 321), (4411 / 321), (6788 / 321), (-239 / 321), -5, (-1 / 2),
      (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_3 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 3 *
      (gridPerturbation z (gridIndex 3 3) - correction 3 z (node z (gridIndex 3 3))) =
        eval (slackCoeffs 3 3) z := by
  exact PolynomialCertificate.checked_slack 3 3
    [(242 / 107), (110 / 321), (-32669 / 428), (-14857 / 321), (120346 / 321), (53191 / 214),
      (-977843 / 1284), (-180701 / 321), (507127 / 642), (220405 / 321), (-288859 / 642),
      (-52889 / 107), (14441 / 107), (68978 / 321), (-9001 / 642), (-17696 / 321),
      (-1871 / 642), (819 / 107), (201 / 214), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_4 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 4 *
      (gridPerturbation z (gridIndex 3 4) - correction 3 z (node z (gridIndex 3 4))) =
        eval (slackCoeffs 3 4) z := by
  exact PolynomialCertificate.checked_slack 3 4
    [(1083 / 214), (980 / 321), (27663 / 428), (11828 / 321), (-322028 / 321), (-1437 / 2),
      (17661 / 4), (1099285 / 321), (-6206509 / 642), (-2525441 / 321), (7841633 / 642),
      (1151911 / 107), (-2037483 / 214), (-3067864 / 321), (2992217 / 642), (1828535 / 321),
      (-293355 / 214), (-245571 / 107), (20381 / 107), (197551 / 321), (1291 / 107),
      (-33716 / 321), (-2956 / 321), (1103 / 107), (295 / 214), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_5 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 5 *
      (gridPerturbation z (gridIndex 3 5) - correction 3 z (node z (gridIndex 3 5))) =
        eval (slackCoeffs 3 5) z := by
  exact PolynomialCertificate.checked_slack 3 5
    [(-251 / 214), (4835 / 321), (110661 / 428), (-5609 / 107), (-1157074 / 321),
      (-277735 / 214), (27729089 / 1284), (1361988 / 107), (-45877411 / 642),
      (-16080575 / 321), (93765781 / 642), (12099763 / 107), (-42031125 / 214),
      (-53419543 / 321), (57850733 / 321), (54509989 / 321), (-73623013 / 642),
      (-13263567 / 107), (5384170 / 107), (21064451 / 321), (-9365119 / 642), (-2698068 / 107),
      (766282 / 321), (744027 / 107), (-3472 / 107), (-143304 / 107), (-51277 / 642),
      (54848 / 321), (11645 / 642), (-1387 / 107), (-389 / 214), (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_6 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 6 *
      (gridPerturbation z (gridIndex 3 6) - correction 3 z (node z (gridIndex 3 6))) =
        eval (slackCoeffs 3 6) z := by
  exact PolynomialCertificate.checked_slack 3 6
    [(-1264 / 107), (-7015 / 321), (-61273 / 428), (15556 / 321), (696195 / 214),
      (362373 / 214), (-27019195 / 1284), (-4609915 / 321), (45461989 / 642), (17042471 / 321),
      (-46663091 / 321), (-12435028 / 107), (20952668 / 107), (54062002 / 321),
      (-57738272 / 321), (-54763492 / 321), (36768395 / 321), (13283578 / 107),
      (-10761633 / 214), (-21072248 / 321), (9362527 / 642), (2698210 / 107), (-1532423 / 642),
      (-744027 / 107), (3472 / 107), (143304 / 107), (51277 / 642), (-54848 / 321),
      (-11645 / 642), (1387 / 107), (389 / 214), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_7 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 7 *
      (gridPerturbation z (gridIndex 3 7) - correction 3 z (node z (gridIndex 3 7))) =
        eval (slackCoeffs 3 7) z := by
  exact PolynomialCertificate.checked_slack 3 7
    [(137 / 214), (-7030 / 321), (-147773 / 428), (-34816 / 321), (770374 / 321),
      (304243 / 214), (-3111311 / 428), (-1638482 / 321), (8111303 / 642), (3186458 / 321),
      (-4461883 / 321), (-1310578 / 107), (1073032 / 107), (3274798 / 321), (-1514746 / 321),
      (-1881623 / 321), (145849 / 107), (248028 / 107), (-40159 / 214), (-197977 / 321),
      (-2629 / 214), (33716 / 321), (2956 / 321), (-1103 / 107), (-295 / 214), (142 / 321),
      (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_8 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 8 *
      (gridPerturbation z (gridIndex 3 8) - correction 3 z (node z (gridIndex 3 8))) =
        eval (slackCoeffs 3 8) z := by
  exact PolynomialCertificate.checked_slack 3 8
    [(3347 / 214), (6845 / 321), (106499 / 428), 207, (-7021 / 6), (-205949 / 214),
      (2583259 / 1284), (185200 / 107), (-368219 / 214), (-182264 / 107), (254098 / 321),
      (107163 / 107), (-19415 / 107), (-38421 / 107), (5009 / 642), (24641 / 321),
      (3539 / 642), (-961 / 107), (-124 / 107), (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_9 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 9 *
      (gridPerturbation z (gridIndex 3 9) - correction 3 z (node z (gridIndex 3 9))) =
        eval (slackCoeffs 3 9) z := by
  exact PolynomialCertificate.checked_slack 3 9
    [(137 / 214), (6845 / 321), (151011 / 428), 207, (-8371 / 6), (-205949 / 214),
      (2827219 / 1284), (185200 / 107), (-384269 / 214), (-182264 / 107), (258592 / 321),
      (107163 / 107), (-19522 / 107), (-38421 / 107), (5009 / 642), (24641 / 321),
      (3539 / 642), (-961 / 107), (-124 / 107), (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_10 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 10 *
      (gridPerturbation z (gridIndex 3 10) - correction 3 z (node z (gridIndex 3 10))) =
        eval (slackCoeffs 3 10) z := by
  exact PolynomialCertificate.checked_slack 3 10
    [(-2859 / 214), (-7030 / 321), (-91277 / 428), (-34816 / 321), (626566 / 321),
      (304243 / 214), (-2792879 / 428), (-1638482 / 321), (7674743 / 642), (3186458 / 321),
      (-4348249 / 321), (-1310578 / 107), (1061904 / 107), (3274798 / 321), (-1509610 / 321),
      (-1881623 / 321), (145742 / 107), (248028 / 107), (-40159 / 214), (-197977 / 321),
      (-2629 / 214), (33716 / 321), (2956 / 321), (-1103 / 107), (-295 / 214), (142 / 321),
      (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_11 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 11 *
      (gridPerturbation z (gridIndex 3 11) - correction 3 z (node z (gridIndex 3 11))) =
        eval (slackCoeffs 3 11) z := by
  exact PolynomialCertificate.checked_slack 3 11
    [(234 / 107), (-7015 / 321), (-140025 / 428), (15556 / 321), (911265 / 214),
      (362373 / 214), (-30578443 / 1284), (-4609915 / 321), (48241207 / 642), (17042471 / 321),
      (-47949659 / 321), (-12435028 / 107), (21196093 / 107), (54062002 / 321),
      (-57995072 / 321), (-54763492 / 321), (36822965 / 321), (13283578 / 107),
      (-10765913 / 214), (-21072248 / 321), (9363169 / 642), (2698210 / 107), (-1532423 / 642),
      (-744027 / 107), (3472 / 107), (143304 / 107), (51277 / 642), (-54848 / 321),
      (-11645 / 642), (1387 / 107), (389 / 214), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_12 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 12 *
      (gridPerturbation z (gridIndex 3 12) - correction 3 z (node z (gridIndex 3 12))) =
        eval (slackCoeffs 3 12) z := by
  exact PolynomialCertificate.checked_slack 3 12
    [(1675 / 214), (4835 / 321), (39613 / 428), (-5609 / 107), (-853729 / 321),
      (-277735 / 214), (24239177 / 1284), (1361988 / 107), (-43109749 / 642),
      (-16080575 / 321), (91193929 / 642), (12099763 / 107), (-41544275 / 214),
      (-53419543 / 321), (57593933 / 321), (54509989 / 321), (-73513873 / 642),
      (-13263567 / 107), (5382030 / 107), (21064451 / 321), (-9364477 / 642), (-2698068 / 107),
      (766282 / 321), (744027 / 107), (-3472 / 107), (-143304 / 107), (-51277 / 642),
      (54848 / 321), (11645 / 642), (-1387 / 107), (-389 / 214), (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_13 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 13 *
      (gridPerturbation z (gridIndex 3 13) - correction 3 z (node z (gridIndex 3 13))) =
        eval (slackCoeffs 3 13) z := by
  exact PolynomialCertificate.checked_slack 3 13
    [(-629 / 214), (980 / 321), (64471 / 428), (11828 / 321), (-434057 / 321), (-1437 / 2),
      (20357 / 4), (1099285 / 321), (-6630229 / 642), (-2525441 / 321), (8067617 / 642),
      (1151911 / 107), (-2059739 / 214), (-3067864 / 321), (3002489 / 642), (1828535 / 321),
      (-293569 / 214), (-245571 / 107), (20381 / 107), (197551 / 321), (1291 / 107),
      (-33716 / 321), (-2956 / 321), (1103 / 107), (295 / 214), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_14 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 14 *
      (gridPerturbation z (gridIndex 3 14) - correction 3 z (node z (gridIndex 3 14))) =
        eval (slackCoeffs 3 14) z := by
  exact PolynomialCertificate.checked_slack 3 14
    [(-507 / 107), (110 / 321), (-16405 / 428), (-14857 / 321), (86641 / 321), (53191 / 214),
      (-834035 / 1284), (-180701 / 321), (472459 / 642), (220405 / 321), (-281155 / 642),
      (-52889 / 107), (14334 / 107), (68978 / 321), (-9001 / 642), (-17696 / 321),
      (-1871 / 642), (819 / 107), (201 / 214), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_15 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 15 *
      (gridPerturbation z (gridIndex 3 15) - correction 3 z (node z (gridIndex 3 15))) =
        eval (slackCoeffs 3 15) z := by
  exact PolynomialCertificate.checked_slack 3 15
    [(351 / 214), (1052 / 321), (-13385 / 428), (-6059 / 321), (13719 / 214), (8763 / 214),
      (-61499 / 1284), (-13510 / 321), (4732 / 321), (6788 / 321), (-239 / 321), -5, (-1 / 2),
      (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_3_16 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 16 *
      (gridPerturbation z (gridIndex 3 16) - correction 3 z (node z (gridIndex 3 16))) =
        eval (slackCoeffs 3 16) z := by
  exact PolynomialCertificate.checked_slack 3 16
    [(-73 / 107), (-865 / 321), (1493 / 428), (341 / 321), (-1133 / 321), (-313 / 214),
      (399 / 428), (109 / 321), (-17 / 321)]
    z hm (by decide +kernel)

theorem slack_identity_3_17 (z : ℝ) (hm : modulus z = 0) :
    slope 3 z - gridSign 3 17 *
      (gridPerturbation z (gridIndex 3 17) - correction 3 z (node z (gridIndex 3 17))) =
        eval (slackCoeffs 3 17) z := by
  exact PolynomialCertificate.checked_slack 3 17
    [(-77 / 214), (449 / 321), (939 / 428), (-652 / 321), (-1435 / 642), (1 / 2), (7 / 12),
      (-11 / 321), (-9 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_4_0 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 0 *
      (gridPerturbation z (gridIndex 4 0) - correction 4 z (node z (gridIndex 4 0))) =
        eval (slackCoeffs 4 0) z := by
  exact PolynomialCertificate.checked_slack 4 0
    [(152 / 321), (449 / 321), (939 / 428), (-652 / 321), (-1435 / 642), (1 / 2), (7 / 12),
      (-11 / 321), (-9 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_4_1 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 1 *
      (gridPerturbation z (gridIndex 4 1) - correction 4 z (node z (gridIndex 4 1))) =
        eval (slackCoeffs 4 1) z := by
  exact PolynomialCertificate.checked_slack 4 1
    [(-545 / 642), (-865 / 321), (637 / 428), (341 / 321), (-598 / 321), (-313 / 214),
      (769 / 1284), (109 / 321), (-17 / 321)]
    z hm (by decide +kernel)

theorem slack_identity_4_2 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 2 *
      (gridPerturbation z (gridIndex 4 2) - correction 4 z (node z (gridIndex 4 2))) =
        eval (slackCoeffs 4 2) z := by
  exact PolynomialCertificate.checked_slack 4 2
    [(-169 / 321), (1052 / 321), (2451 / 428), (-6059 / 321), (-684 / 107), (8763 / 214),
      (7837 / 1284), (-13510 / 321), (-2009 / 321), (6788 / 321), (2197 / 642), -5, (-5 / 6),
      (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_3 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 3 *
      (gridPerturbation z (gridIndex 4 3) - correction 4 z (node z (gridIndex 4 3))) =
        eval (slackCoeffs 4 3) z := by
  exact PolynomialCertificate.checked_slack 4 3
    [(1345 / 642), (110 / 321), (-16191 / 428), (-14857 / 321), (39963 / 214), (53191 / 214),
      (-155889 / 428), (-180701 / 321), (100928 / 321), (220405 / 321), (-11246 / 107),
      (-52889 / 107), (-5683 / 321), (68978 / 321), (16679 / 642), (-17696 / 321),
      (-5509 / 642), (819 / 107), (817 / 642), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_4 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 4 *
      (gridPerturbation z (gridIndex 4 4) - correction 4 z (node z (gridIndex 4 4))) =
        eval (slackCoeffs 4 4) z := by
  exact PolynomialCertificate.checked_slack 4 4
    [(287 / 321), (980 / 321), (-35253 / 428), (11828 / 321), (259517 / 321), (-1437 / 2),
      (-44389 / 12), (1099285 / 321), (5906105 / 642), (-2525441 / 321), (-2941277 / 214),
      (1151911 / 107), (8470153 / 642), (-3067864 / 321), (-5441737 / 642), (1828535 / 321),
      (2388143 / 642), (-245571 / 107), (-358832 / 321), (197551 / 321), (24189 / 107),
      (-33716 / 321), (-18859 / 642), (1103 / 107), (710 / 321), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_5 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 5 *
      (gridPerturbation z (gridIndex 4 5) - correction 4 z (node z (gridIndex 4 5))) =
        eval (slackCoeffs 4 5) z := by
  exact PolynomialCertificate.checked_slack 4 5
    [(-751 / 321), (4835 / 321), (84553 / 428), (-5609 / 107), (-1102718 / 321),
      (-277735 / 214), (33295015 / 1284), (1361988 / 107), (-69243643 / 642),
      (-16080575 / 321), (178099115 / 642), (12099763 / 107), (-303676781 / 642),
      (-53419543 / 321), (179668949 / 321), (54509989 / 321), (-50683841 / 107),
      (-13263567 / 107), (93737675 / 321), (21064451 / 321), (-84904765 / 642),
      (-2698068 / 107), (28212479 / 642), (744027 / 107), (-2264537 / 214), (-143304 / 107),
      (1153115 / 642), (54848 / 321), (-65386 / 321), (-1387 / 107), (8891 / 642), (142 / 321),
      (-137 / 321)]
    z hm (by decide +kernel)

theorem slack_identity_4_6 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 6 *
      (gridPerturbation z (gridIndex 4 6) - correction 4 z (node z (gridIndex 4 6))) =
        eval (slackCoeffs 4 6) z := by
  exact PolynomialCertificate.checked_slack 4 6
    [(-475 / 321), (-7015 / 321), (93877 / 428), (15556 / 321), (-2360047 / 642),
      (362373 / 214), (11387873 / 428), (-4609915 / 321), (-34759624 / 321), (17042471 / 321),
      (89322995 / 321), (-12435028 / 107), (-154613183 / 321), (54062002 / 321),
      (187532692 / 321), (-54763492 / 321), (-54478734 / 107), (13283578 / 107),
      (103909999 / 321), (-21072248 / 321), (-97042553 / 642), (2698210 / 107),
      (16607753 / 321), (-744027 / 107), (-2743063 / 214), (143304 / 107), (1435429 / 642),
      (-54848 / 321), (-83558 / 321), (1387 / 107), (11653 / 642), (-142 / 321), (-184 / 321)]
    z hm (by decide +kernel)

theorem slack_identity_4_7 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 7 *
      (gridPerturbation z (gridIndex 4 7) - correction 4 z (node z (gridIndex 4 7))) =
        eval (slackCoeffs 4 7) z := by
  exact PolynomialCertificate.checked_slack 4 7
    [(152 / 321), (-7030 / 321), (-128299 / 428), (-34816 / 321), (732068 / 321),
      (304243 / 214), (-9524393 / 1284), (-1638482 / 321), (4410196 / 321), (3186458 / 321),
      (-3444925 / 214), (-1310578 / 107), (7988729 / 642), (3274798 / 321), (-2047927 / 321),
      (-1881623 / 321), (1350067 / 642), (248028 / 107), (-257009 / 642), (-197977 / 321),
      (5503 / 214), (33716 / 321), (3451 / 642), (-1103 / 107), (-389 / 321), (142 / 321),
      (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_8 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 8 *
      (gridPerturbation z (gridIndex 4 8) - correction 4 z (node z (gridIndex 4 8))) =
        eval (slackCoeffs 4 8) z := by
  exact PolynomialCertificate.checked_slack 4 8
    [(152 / 321), (6845 / 321), (-110283 / 428), 207, (1783 / 2), (-205949 / 214),
      (-1637035 / 1284), (185200 / 107), (111585 / 107), (-182264 / 107), (-184709 / 321),
      (107163 / 107), (49659 / 214), (-38421 / 107), (-21731 / 321), (24641 / 321),
      (8461 / 642), (-961 / 107), (-479 / 321), (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_9 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 9 *
      (gridPerturbation z (gridIndex 4 9) - correction 4 z (node z (gridIndex 4 9))) =
        eval (slackCoeffs 4 9) z := by
  exact PolynomialCertificate.checked_slack 4 9
    [(152 / 321), (6845 / 321), (134533 / 428), 207, (-2151 / 2), (-205949 / 214),
      (1788677 / 1284), (185200 / 107), (-87970 / 107), (-182264 / 107), (51547 / 321),
      (107163 / 107), (14135 / 214), (-38421 / 107), (-15311 / 321), (24641 / 321),
      (7819 / 642), (-961 / 107), (-479 / 321), (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_10 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 10 *
      (gridPerturbation z (gridIndex 4 10) - correction 4 z (node z (gridIndex 4 10))) =
        eval (slackCoeffs 4 10) z := by
  exact PolynomialCertificate.checked_slack 4 10
    [(-169 / 321), (-7030 / 321), (102821 / 428), (-34816 / 321), (-605539 / 321),
      (304243 / 214), (8302663 / 1284), (-1638482 / 321), (-4126799 / 321), (3186458 / 321),
      (3540035 / 214), (-1310578 / 107), (-9306109 / 642), (3274798 / 321), (2840261 / 321),
      (-1881623 / 321), (-2428745 / 642), (248028 / 107), (721399 / 642), (-197977 / 321),
      (-48425 / 214), (33716 / 321), (18859 / 642), (-1103 / 107), (-710 / 321), (142 / 321),
      (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_11 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 11 *
      (gridPerturbation z (gridIndex 4 11) - correction 4 z (node z (gridIndex 4 11))) =
        eval (slackCoeffs 4 11) z := by
  exact PolynomialCertificate.checked_slack 4 11
    [(167 / 321), (-7015 / 321), (-116699 / 428), (15556 / 321), (2824103 / 642),
      (362373 / 214), (-13033807 / 428), (-4609915 / 321), (38004656 / 321), (17042471 / 321),
      (-93508333 / 321), (-12435028 / 107), (155405086 / 321), (54062002 / 321),
      (-181463228 / 321), (-54763492 / 321), (50874108 / 107), (13283578 / 107),
      (-93849113 / 321), (-21072248 / 321), (84929137 / 642), (2698210 / 107),
      (-14106811 / 321), (-744027 / 107), (2264537 / 214), (143304 / 107), (-1153115 / 642),
      (-54848 / 321), (65386 / 321), (1387 / 107), (-8891 / 642), (-142 / 321), (137 / 321)]
    z hm (by decide +kernel)

theorem slack_identity_4_12 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 12 *
      (gridPerturbation z (gridIndex 4 12) - correction 4 z (node z (gridIndex 4 12))) =
        eval (slackCoeffs 4 12) z := by
  exact PolynomialCertificate.checked_slack 4 12
    [(533 / 321), (4835 / 321), (-67815 / 428), (-5609 / 107), (908347 / 321), (-277735 / 214),
      (-28768409 / 1284), (1361988 / 107), (62906921 / 642), (-16080575 / 321),
      (-169528477 / 642), (12099763 / 107), (301633561 / 642), (-53419543 / 321),
      (-185552011 / 321), (54509989 / 321), (54261545 / 107), (-13263567 / 107),
      (-103778761 / 321), (21064451 / 321), (97012997 / 642), (-2698068 / 107),
      (-33214081 / 642), (744027 / 107), (2743063 / 214), (-143304 / 107), (-1435429 / 642),
      (54848 / 321), (83558 / 321), (-1387 / 107), (-11653 / 642), (142 / 321), (184 / 321)]
    z hm (by decide +kernel)

theorem slack_identity_4_13 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 13 *
      (gridPerturbation z (gridIndex 4 13) - correction 4 z (node z (gridIndex 4 13))) =
        eval (slackCoeffs 4 13) z := by
  exact PolynomialCertificate.checked_slack 4 13
    [(-997 / 321), (980 / 321), (41787 / 428), (11828 / 321), (-325024 / 321), (-1437 / 2),
      (53051 / 12), (1099285 / 321), (-6522373 / 642), (-2525441 / 321), (2936875 / 214),
      (1151911 / 107), (-7421273 / 642), (-3067864 / 321), (3987959 / 642), (1828535 / 321),
      (-1344445 / 642), (-245571 / 107), (129088 / 321), (197551 / 321), (-2775 / 107),
      (-33716 / 321), (-3451 / 642), (1103 / 107), (389 / 321), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_14 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 14 *
      (gridPerturbation z (gridIndex 4 14) - correction 4 z (node z (gridIndex 4 14))) =
        eval (slackCoeffs 4 14) z := by
  exact PolynomialCertificate.checked_slack 4 14
    [(-1223 / 642), (110 / 321), (12913 / 428), (-14857 / 321), (-32155 / 214), (53191 / 214),
      (131727 / 428), (-180701 / 321), (-110932 / 321), (220405 / 321), (26418 / 107),
      (-52889 / 107), (-39067 / 321), (68978 / 321), (26951 / 642), (-17696 / 321),
      (-6151 / 642), (819 / 107), (817 / 642), (-142 / 321), (-47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_15 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 15 *
      (gridPerturbation z (gridIndex 4 15) - correction 4 z (node z (gridIndex 4 15))) =
        eval (slackCoeffs 4 15) z := by
  exact PolynomialCertificate.checked_slack 4 15
    [(473 / 321), (1052 / 321), (-4397 / 428), (-6059 / 321), (1456 / 107), (8763 / 214),
      (-2435 / 1284), (-13510 / 321), (-1688 / 321), (6788 / 321), (2197 / 642), -5, (-5 / 6),
      (142 / 321), (47 / 642)]
    z hm (by decide +kernel)

theorem slack_identity_4_16 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 16 *
      (gridPerturbation z (gridIndex 4 16) - correction 4 z (node z (gridIndex 4 16))) =
        eval (slackCoeffs 4 16) z := by
  exact PolynomialCertificate.checked_slack 4 16
    [(97 / 642), (-865 / 321), (637 / 428), (341 / 321), (-598 / 321), (-313 / 214),
      (769 / 1284), (109 / 321), (-17 / 321)]
    z hm (by decide +kernel)

theorem slack_identity_4_17 (z : ℝ) (hm : modulus z = 0) :
    slope 4 z - gridSign 4 17 *
      (gridPerturbation z (gridIndex 4 17) - correction 4 z (node z (gridIndex 4 17))) =
        eval (slackCoeffs 4 17) z := by
  exact PolynomialCertificate.checked_slack 4 17
    [(152 / 321), (449 / 321), (939 / 428), (-652 / 321), (-1435 / 642), (1 / 2), (7 / 12),
      (-11 / 321), (-9 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_5_0 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 0 *
      (gridPerturbation z (gridIndex 5 0) - correction 5 z (node z (gridIndex 5 0))) =
        eval (slackCoeffs 5 0) z := by
  exact PolynomialCertificate.checked_slack 5 0
    [(791 / 642), (623 / 321), (1609 / 1284), (-586 / 321), (-1273 / 642), (1 / 2), (7 / 12),
      (-11 / 321), (-9 / 214)]
    z hm (by decide +kernel)

theorem slack_identity_5_1 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 1 *
      (gridPerturbation z (gridIndex 5 1) - correction 5 z (node z (gridIndex 5 1))) =
        eval (slackCoeffs 5 1) z := by
  exact PolynomialCertificate.checked_slack 5 1
    [(-152 / 321), (3176 / 321), (-2375 / 1284), (-76 / 321), (16379 / 642), (-8415 / 214),
      (-73093 / 1284), (13105 / 321), (10197 / 214), (-1766 / 107), (-2002 / 107), 3, (7 / 2),
      (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_2 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 2 *
      (gridPerturbation z (gridIndex 5 2) - correction 5 z (node z (gridIndex 5 2))) =
        eval (slackCoeffs 5 2) z := by
  exact PolynomialCertificate.checked_slack 5 2
    [(-283 / 642), (-6424 / 321), (4309 / 1284), (30931 / 321), (-10580 / 107), (66305 / 214),
      (1103029 / 1284), (-645145 / 321), (-1864831 / 642), (1300292 / 321), (1618030 / 321),
      (-467187 / 107), (-3298391 / 642), (920185 / 321), (705215 / 214), (-128450 / 107),
      (-146700 / 107), (34486 / 107), (79171 / 214), (-5746 / 107), (-6692 / 107), (541 / 107),
      (1289 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_3 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 3 *
      (gridPerturbation z (gridIndex 5 3) - correction 5 z (node z (gridIndex 5 3))) =
        eval (slackCoeffs 5 3) z := by
  exact PolynomialCertificate.checked_slack 5 3
    [(1643 / 642), (-12376 / 321), (-68099 / 1284), (173273 / 321), (41818 / 321),
      (-128505 / 214), (4088903 / 1284), (-4796417 / 321), (-6486641 / 214), (27828460 / 321),
      (40691131 / 321), (-25476017 / 107), (-99732803 / 321), (129257681 / 321),
      (159346322 / 321), (-147563108 / 321), (-175900513 / 321), (39670476 / 107),
      (277876997 / 642), (-69490435 / 321), (-53429223 / 214), (9901867 / 107),
      (22716119 / 214), (-3099219 / 107), (-7111725 / 214), (702020 / 107), (809675 / 107),
      (-111981 / 107), (-130413 / 107), (11926 / 107), (14082 / 107), (-761 / 107),
      (-1829 / 214), (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_4 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 4 *
      (gridPerturbation z (gridIndex 5 4) - correction 5 z (node z (gridIndex 5 4))) =
        eval (slackCoeffs 5 4) z := by
  exact PolynomialCertificate.checked_slack 5 4
    [(196 / 321), (19151 / 321), (-65951 / 1284), (-564721 / 321), (295751 / 642),
      (2460573 / 214), (-13251787 / 1284), (7157563 / 321), (33192723 / 214),
      (-198356393 / 321), (-767243809 / 642), (384921935 / 107), (1744886806 / 321),
      (-3818768236 / 321), (-5198237458 / 321), (8446437056 / 321), (3614218407 / 107),
      (-4464100192 / 107), (-33096232847 / 642), (15826530061 / 321), (19043025440 / 321),
      (-14286089078 / 321), (-33736241717 / 642), (3335684541 / 107), (11661530419 / 321),
      (-5491905919 / 321), (-2115190138 / 107), (790609301 / 107), (909286721 / 107),
      (-268579302 / 107), (-308522629 / 107), (71363479 / 107), (164259677 / 214),
      (-14654123 / 107), (-16944084 / 107), (2277840 / 107), (2653075 / 107), (-258976 / 107),
      (-609181 / 214), (20306 / 107), (24172 / 107), (-981 / 107), (-2369 / 214), (22 / 107),
      (27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_5 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 5 *
      (gridPerturbation z (gridIndex 5 5) - correction 5 z (node z (gridIndex 5 5))) =
        eval (slackCoeffs 5 5) z := by
  exact PolynomialCertificate.checked_slack 5 5
    [(-925 / 642), (24578 / 321), (313849 / 1284), (-447862 / 107), (-3117131 / 642),
      (12377227 / 214), (11075429 / 428), (-24137053 / 107), (94517897 / 321),
      (-541215452 / 321), (-1885022332 / 321), (2666701103 / 107), (30140874623 / 642),
      (-47632508542 / 321), (-24696431551 / 107), (178454452054 / 321), (503802397601 / 642),
      (-157530328946 / 107), (-1256687236099 / 642), (935106882551 / 321),
      (2386614375211 / 642), (-476434659758 / 107), (-3540553007821 / 642),
      (575232586563 / 107), (1393290498041 / 214), (-557272874815 / 107),
      (-3980906976901 / 642), (1314076735748 / 321), (3089064305867 / 642),
      (-281479535562 / 107), (-983203732813 / 321), (445736545714 / 321), (171867785625 / 107),
      (-64555727393 / 107), (-74377378762 / 107), (23076086703 / 107), (26541749534 / 107),
      (-6764294188 / 107), (-15566395229 / 214), (1615515409 / 107), (3726361621 / 214),
      (-311087521 / 107), (-720528995 / 214), (47536552 / 107), (55373768 / 107),
      (-5627910 / 107), (-6604900 / 107), (497471 / 107), (589118 / 107), (-30886 / 107),
      (-36962 / 107), (1201 / 107), (2909 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_6 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 6 *
      (gridPerturbation z (gridIndex 5 6) - correction 5 z (node z (gridIndex 5 6))) =
        eval (slackCoeffs 5 6) z := by
  exact PolynomialCertificate.checked_slack 5 6
    [(-1507 / 642), (-26365 / 321), (213643 / 1284), (1910293 / 321), (-316595 / 214),
      (-16328045 / 214), (35848009 / 1284), (69764987 / 321), (-451839259 / 642),
      (877032671 / 321), (5484134417 / 642), (-3460016166 / 107), (-38133895979 / 642),
      (56624242318 / 321), (28973107440 / 107), (-200571372454 / 321), (-561936454703 / 642),
      (170313865481 / 107), (676344339710 / 321), (-984073767494 / 321),
      (-2505336307255 / 642), (492202145273 / 107), (1826377803101 / 321),
      (-586959764758 / 107), (-1420693131631 / 214), (564061280355 / 107),
      (2014015303775 / 321), (-1323301336223 / 321), (-1555146116605 / 321),
      (282569779377 / 107), (1973920511375 / 642), (-446639809354 / 321),
      (-172214100212 / 107), (64619755188 / 107), (74451352927 / 107), (-23086361098 / 107),
      (-26553705954 / 107), (6765496798 / 107), (7784610877 / 107), (-1615612254 / 107),
      (-1863296018 / 107), (311092316 / 107), (360270285 / 107), (-47536662 / 107),
      (-55373903 / 107), (5627910 / 107), (6604900 / 107), (-497471 / 107), (-589118 / 107),
      (30886 / 107), (36962 / 107), (-1201 / 107), (-2909 / 214), (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_7 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 7 *
      (gridPerturbation z (gridIndex 5 7) - correction 5 z (node z (gridIndex 5 7))) =
        eval (slackCoeffs 5 7) z := by
  exact PolynomialCertificate.checked_slack 5 7
    [(-335 / 321), (-21547 / 321), (-454139 / 1284), (1964717 / 321), (1416985 / 321),
      (-5050125 / 214), (23510567 / 1284), (-57805637 / 321), (-101427327 / 214),
      (605201321 / 321), (1986838177 / 642), (-863920538 / 107), (-7359735557 / 642),
      (6934914583 / 321), (9152749399 / 321), (-13061819033 / 321), (-5493278791 / 107),
      (6103406563 / 107), (22400240632 / 321), (-19708355596 / 321), (-47162589913 / 642),
      (16593781208 / 321), (39071783999 / 642), (-3682796586 / 107), (-25716435341 / 642),
      (5848683544 / 321), (2251672373 / 107), (-821314811 / 107), (-944621571 / 107),
      (274451757 / 107), (630648503 / 214), (-72169624 / 107), (-166145647 / 214),
      (14729193 / 107), (17033054 / 107), (-2282085 / 107), (-5316375 / 214), (259086 / 107),
      (609451 / 214), (-20306 / 107), (-24172 / 107), (981 / 107), (2369 / 214), (-22 / 107),
      (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_8 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 8 *
      (gridPerturbation z (gridIndex 5 8) - correction 5 z (node z (gridIndex 5 8))) =
        eval (slackCoeffs 5 8) z := by
  exact PolynomialCertificate.checked_slack 5 8
    [(359 / 642), (18545 / 321), (-265553 / 1284), (-671392 / 107), (-807179 / 642),
      (-1168791 / 214), (-17388167 / 428), (22346264 / 107), (218086327 / 642),
      (-90067283 / 107), (-730832071 / 642), (187705183 / 107), (235440350 / 107),
      (-248023310 / 107), (-1791552055 / 642), (676519121 / 321), (794626441 / 321),
      (-147131257 / 107), (-1021891697 / 642), (211334308 / 321), (161888937 / 214),
      (-24989358 / 107), (-57326873 / 214), (6560246 / 107), (7546492 / 107), (-1258450 / 107),
      (-2915145 / 214), (171501 / 107), (200688 / 107), (-15731 / 107), (-37309 / 214),
      (871 / 107), (2099 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_9 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 9 *
      (gridPerturbation z (gridIndex 5 9) - correction 5 z (node z (gridIndex 5 9))) =
        eval (slackCoeffs 5 9) z := by
  exact PolynomialCertificate.checked_slack 5 9
    [(359 / 642), (18545 / 321), (468895 / 1284), (-671392 / 107), (-2069993 / 642),
      (-1168791 / 214), (-16246263 / 428), (22346264 / 107), (216888997 / 642),
      (-90067283 / 107), (-730359559 / 642), (187705183 / 107), (235422588 / 107),
      (-248023310 / 107), (-1791539215 / 642), (676519121 / 321), (794626120 / 321),
      (-147131257 / 107), (-1021891697 / 642), (211334308 / 321), (161888937 / 214),
      (-24989358 / 107), (-57326873 / 214), (6560246 / 107), (7546492 / 107), (-1258450 / 107),
      (-2915145 / 214), (171501 / 107), (200688 / 107), (-15731 / 107), (-37309 / 214),
      (871 / 107), (2099 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_10 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 10 *
      (gridPerturbation z (gridIndex 5 10) - correction 5 z (node z (gridIndex 5 10))) =
        eval (slackCoeffs 5 10) z := by
  exact PolynomialCertificate.checked_slack 5 10
    [(-656 / 321), (-21547 / 321), (239221 / 1284), (1964717 / 321), (79378 / 321),
      (-5050125 / 214), (41337623 / 1284), (-57805637 / 321), (-107118657 / 214),
      (605201321 / 321), (2007793057 / 642), (-863920538 / 107), (-7377030395 / 642),
      (6934914583 / 321), (9157637587 / 321), (-13061819033 / 321), (-5493908593 / 107),
      (6103406563 / 107), (22400729836 / 321), (-19708355596 / 321), (-47162751697 / 642),
      (16593781208 / 321), (39071799407 / 642), (-3682796586 / 107), (-25716435983 / 642),
      (5848683544 / 321), (2251672373 / 107), (-821314811 / 107), (-944621571 / 107),
      (274451757 / 107), (630648503 / 214), (-72169624 / 107), (-166145647 / 214),
      (14729193 / 107), (17033054 / 107), (-2282085 / 107), (-5316375 / 214), (259086 / 107),
      (609451 / 214), (-20306 / 107), (-24172 / 107), (981 / 107), (2369 / 214), (-22 / 107),
      (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_11 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 11 *
      (gridPerturbation z (gridIndex 5 11) - correction 5 z (node z (gridIndex 5 11))) =
        eval (slackCoeffs 5 11) z := by
  exact PolynomialCertificate.checked_slack 5 11
    [(-223 / 642), (-26365 / 321), (-418085 / 1284), (1910293 / 321), (1411455 / 214),
      (-16328045 / 214), (-37417031 / 1284), (69764987 / 321), (-306310699 / 642),
      (877032671 / 321), (5118471761 / 642), (-3460016166 / 107), (-37513859441 / 642),
      (56624242318 / 321), (28850108800 / 107), (-200571372454 / 321), (-561304337651 / 642),
      (170313865481 / 107), (676146580598 / 321), (-984073767494 / 321),
      (-2505154335565 / 642), (492202145273 / 107), (1826347088537 / 321),
      (-586959764758 / 107), (-1420688124031 / 214), (564061280355 / 107),
      (2014014009503 / 321), (-1323301336223 / 321), (-1555145967661 / 321),
      (282569779377 / 107), (1973920490831 / 642), (-446639809354 / 321),
      (-172214100105 / 107), (64619755188 / 107), (74451352927 / 107), (-23086361098 / 107),
      (-26553705954 / 107), (6765496798 / 107), (7784610877 / 107), (-1615612254 / 107),
      (-1863296018 / 107), (311092316 / 107), (360270285 / 107), (-47536662 / 107),
      (-55373903 / 107), (5627910 / 107), (6604900 / 107), (-497471 / 107), (-589118 / 107),
      (30886 / 107), (36962 / 107), (-1201 / 107), (-2909 / 214), (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_12 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 12 *
      (gridPerturbation z (gridIndex 5 12) - correction 5 z (node z (gridIndex 5 12))) =
        eval (slackCoeffs 5 12) z := by
  exact PolynomialCertificate.checked_slack 5 12
    [(1643 / 642), (24578 / 321), (-143255 / 1284), (-447862 / 107), (904999 / 642),
      (12377227 / 214), (-9612379 / 428), (-24137053 / 107), (160593179 / 321),
      (-541215452 / 321), (-2058836128 / 321), (2666701103 / 107), (30746184965 / 642),
      (-47632508542 / 321), (-24818171871 / 107), (178454452054 / 321), (504432069917 / 642),
      (-157530328946 / 107), (-1257082268971 / 642), (935106882551 / 321),
      (2386796292973 / 642), (-476434659758 / 107), (-3540614434381 / 642),
      (575232586563 / 107), (1393295505641 / 214), (-557272874815 / 107),
      (-3980909565445 / 642), (1314076735748 / 321), (3089064603755 / 642),
      (-281479535562 / 107), (-983203743085 / 321), (445736545714 / 321), (171867785732 / 107),
      (-64555727393 / 107), (-74377378762 / 107), (23076086703 / 107), (26541749534 / 107),
      (-6764294188 / 107), (-15566395229 / 214), (1615515409 / 107), (3726361621 / 214),
      (-311087521 / 107), (-720528995 / 214), (47536552 / 107), (55373768 / 107),
      (-5627910 / 107), (-6604900 / 107), (497471 / 107), (589118 / 107), (-30886 / 107),
      (-36962 / 107), (1201 / 107), (2909 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_13 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 13 *
      (gridPerturbation z (gridIndex 5 13) - correction 5 z (node z (gridIndex 5 13))) =
        eval (slackCoeffs 5 13) z := by
  exact PolynomialCertificate.checked_slack 5 13
    [(-1088 / 321), (19151 / 321), (165169 / 1284), (-564721 / 321), (-873331 / 642),
      (2460573 / 214), (-2825707 / 1284), (7157563 / 321), (29049897 / 214),
      (-198356393 / 321), (-749609353 / 642), (384921935 / 107), (1736941093 / 321),
      (-3818768236 / 321), (-5193522610 / 321), (8446437056 / 321), (3613596309 / 107),
      (-4464100192 / 107), (-33095257007 / 642), (15826530061 / 321), (19042944548 / 321),
      (-14286089078 / 321), (-33736226309 / 642), (3335684541 / 107), (11661530098 / 321),
      (-5491905919 / 321), (-2115190138 / 107), (790609301 / 107), (909286721 / 107),
      (-268579302 / 107), (-308522629 / 107), (71363479 / 107), (164259677 / 214),
      (-14654123 / 107), (-16944084 / 107), (2277840 / 107), (2653075 / 107), (-258976 / 107),
      (-609181 / 214), (20306 / 107), (24172 / 107), (-981 / 107), (-2369 / 214), (22 / 107),
      (27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_14 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 14 *
      (gridPerturbation z (gridIndex 5 14) - correction 5 z (node z (gridIndex 5 14))) =
        eval (slackCoeffs 5 14) z := by
  exact PolynomialCertificate.checked_slack 5 14
    [(-925 / 642), (-12376 / 321), (19213 / 1284), (173273 / 321), (-66359 / 321),
      (-128505 / 214), (4951751 / 1284), (-4796417 / 321), (-6627881 / 214), (27828460 / 321),
      (40804123 / 321), (-25476017 / 107), (-99766187 / 321), (129257681 / 321),
      (159351458 / 321), (-147563108 / 321), (-175900834 / 321), (39670476 / 107),
      (277876997 / 642), (-69490435 / 321), (-53429223 / 214), (9901867 / 107),
      (22716119 / 214), (-3099219 / 107), (-7111725 / 214), (702020 / 107), (809675 / 107),
      (-111981 / 107), (-130413 / 107), (11926 / 107), (14082 / 107), (-761 / 107),
      (-1829 / 214), (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_15 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 15 *
      (gridPerturbation z (gridIndex 5 15) - correction 5 z (node z (gridIndex 5 15))) =
        eval (slackCoeffs 5 15) z := by
  exact PolynomialCertificate.checked_slack 5 15
    [(1001 / 642), (-6424 / 321), (-16235 / 1284), (30931 / 321), (-8440 / 107), (66305 / 214),
      (1092757 / 1284), (-645145 / 321), (-1864189 / 642), (1300292 / 321), (1618030 / 321),
      (-467187 / 107), (-3298391 / 642), (920185 / 321), (705215 / 214), (-128450 / 107),
      (-146700 / 107), (34486 / 107), (79171 / 214), (-5746 / 107), (-6692 / 107), (541 / 107),
      (1289 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_16 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 16 *
      (gridPerturbation z (gridIndex 5 16) - correction 5 z (node z (gridIndex 5 16))) =
        eval (slackCoeffs 5 16) z := by
  exact PolynomialCertificate.checked_slack 5 16
    [(169 / 321), (3176 / 321), (-2375 / 1284), (-76 / 321), (16379 / 642), (-8415 / 214),
      (-73093 / 1284), (13105 / 321), (10197 / 214), (-1766 / 107), (-2002 / 107), 3, (7 / 2),
      (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem slack_identity_5_17 (z : ℝ) (hm : modulus z = 0) :
    slope 5 z - gridSign 5 17 *
      (gridPerturbation z (gridIndex 5 17) - correction 5 z (node z (gridIndex 5 17))) =
        eval (slackCoeffs 5 17) z := by
  exact PolynomialCertificate.checked_slack 5 17
    [(791 / 642), (623 / 321), (1609 / 1284), (-586 / 321), (-1273 / 642), (1 / 2), (7 / 12),
      (-11 / 321), (-9 / 214)]
    z hm (by decide +kernel)

end Lorentz.Certificate
