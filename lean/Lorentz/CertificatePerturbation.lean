module

public import Lorentz.CertificateCompleteness
public import Lorentz.PolynomialCertificate

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Lorentz.Certificate

def perturbSeed (z x : ℝ) : ℝ :=
  8 * x ^ 4 - 8 * x ^ 2 - 2 * (16 * x ^ 5 - 20 * x ^ 3 + 5 * x) +
  beta z * (64 * x ^ 7 - 112 * x ^ 5 + 56 * x ^ 3 - 7 * x)

def shortSeed (z x y : ℝ) : ℝ :=
  2 * x * y - 2 * x ^ 2 - 2 * (4 * x ^ 2 * y - 2 * y - x) +
  beta z * (4 * x * y ^ 2 - 4 * x ^ 2 * y + 2 * y - x)

theorem perturbSeed_eq_short (z x : ℝ) : perturbSeed z x = shortSeed z x (cubic x) := by
  unfold perturbSeed shortSeed cubic
  ring

private theorem rearrange_zero {u v w : ℝ} (h : u - v - w = 0) : v = u - w := by
  linarith


open PolynomialCertificate in
private def shortSeedCoeffs (x y : List ℚ) : List ℚ :=
  add
    (sub (sub (scale 2 (mul x y)) (scale 2 (power x 2)))
      (scale 2 (sub (sub (scale 4 (mul (power x 2) y)) (scale 2 y)) x)))
    (mul betaCoeffs
      (sub (add (sub (scale 4 (mul x (power y 2))) (scale 4 (mul (power x 2) y)))
        (scale 2 y)) x))

open PolynomialCertificate in
private theorem eval_shortSeed (x y : List ℚ) (z : ℝ) :
    eval (shortSeedCoeffs x y) z = shortSeed z (eval x z) (eval y z) := by
  simp [shortSeedCoeffs, eval_add, eval_sub, eval_scale, eval_mul, eval_power, shortSeed,
    beta, mul_assoc]

open PolynomialCertificate in
private theorem checked_recurrence (j k : ℕ) (quotient : List ℚ) (z : ℝ)
    (hm : modulus z = 0)
    (hc : isZero (sub (sub
      (sub (shortSeedCoeffs (nodeCoeffs j) (nodeCoeffs k)) (perturbationCoeffs j))
      (scale (1 / 3) (perturbationCoeffs k))) (mul quotient modulusCoeffs)) = true) :
    gridPerturbation z j = shortSeed z (node z j) (node z k) - gridPerturbation z k / 3 := by
  have h := eq_of_certificate
    (sub (shortSeedCoeffs (nodeCoeffs j) (nodeCoeffs k)) (perturbationCoeffs j))
    (scale (1 / 3) (perturbationCoeffs k)) quotient z hm hc
  simp only [eval_sub, eval_shortSeed, eval_scale, perturbationCoeffs, eval_add, eval_mul,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  change shortSeed z (node z j) (node z k) - gridPerturbation z j =
    (1 / 3 : ℝ) * gridPerturbation z k at h
  linarith

theorem grid_recurrence_0 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 0 = perturbSeed z (node z 0) - gridPerturbation z 1 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_0 z hm]
  exact checked_recurrence 0 1
    []
    z hm (by decide +kernel)

theorem grid_recurrence_1 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 1 = perturbSeed z (node z 1) - gridPerturbation z 4 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_1 z hm]
  exact checked_recurrence 1 4
    [(1 / 2), (-51 / 107), (-369 / 107), (-5680 / 107), (-5862 / 107), (30294 / 107),
      (75963 / 214), (-67920 / 107), (-164991 / 214), (76824 / 107), (89683 / 107),
      (-48612 / 107), (-55565 / 107), (18020 / 107), (41089 / 214), (-3890 / 107),
      (-4492 / 107), (453 / 107), (1073 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_2 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 2 = perturbSeed z (node z 2) - gridPerturbation z 7 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_2 z hm]
  exact checked_recurrence 2 7
    [1, (16 / 107), (2189 / 214), (16076 / 107), (18825 / 107), (-85776 / 107),
      (-106788 / 107), (191783 / 107), (465857 / 214), (-237060 / 107), (-558889 / 214),
      (178820 / 107), (206261 / 107), (-85382 / 107), (-97511 / 107), (25844 / 107),
      (59165 / 214), (-4796 / 107), (-5565 / 107), (497 / 107), (1181 / 214), (-22 / 107),
      (-27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_3 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 3 = perturbSeed z (node z 3) - gridPerturbation z 10 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_3 z hm]
  exact checked_recurrence 3 10
    [2, (-422 / 107), (-4061 / 214), (-22299 / 107), (-52983 / 214), (160109 / 107),
      (407255 / 214), (-455591 / 107), (-563108 / 107), (702617 / 107), (839750 / 107),
      (-658578 / 107), (-1534071 / 214), (395058 / 107), (453240 / 107), (-154681 / 107),
      (-176738 / 107), (39304 / 107), (90355 / 214), (-6243 / 107), (-14565 / 214),
      (563 / 107), (1343 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_4 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 4 = perturbSeed z (node z 4) - gridPerturbation z 13 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_4 z hm]
  exact checked_recurrence 4 13
    [2, (846 / 107), (513 / 107), (12921 / 107), (17448 / 107), (-188136 / 107),
      (-253121 / 107), (838806 / 107), (1083255 / 107), (-1875533 / 107), (-2311153 / 107),
      (2443278 / 107), (2902463 / 107), (-2003219 / 107), (-2323535 / 107), (1076805 / 107),
      (1233915 / 107), (-385296 / 107), (-440666 / 107), (90962 / 107), (104758 / 107),
      (-13612 / 107), (-15908 / 107), (1170 / 107), (1397 / 107), (-44 / 107), (-54 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_5 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 5 = perturbSeed z (node z 5) - gridPerturbation z 16 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_5 z hm]
  exact checked_recurrence 5 16
    [2, (-389 / 107), (-1883 / 107), (-737 / 107), (-3419 / 107), (48673 / 107),
      (152251 / 214), (-215857 / 107), (-286009 / 107), (422318 / 107), (1034021 / 214),
      (-458874 / 107), (-1077039 / 214), (304111 / 107), (349478 / 107), (-128063 / 107),
      (-292489 / 214), (34464 / 107), (79117 / 214), (-5746 / 107), (-6692 / 107), (541 / 107),
      (1289 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_6 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 6 = perturbSeed z (node z 6) - gridPerturbation z 16 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_6 z hm]
  exact checked_recurrence 6 16
    [1, (-997 / 107), (-1530 / 107), (2975 / 107), (981 / 107), (35473 / 107), (119209 / 214),
      (-197037 / 107), (-263972 / 107), (409848 / 107), (1005689 / 214), (-454700 / 107),
      (-1067533 / 214), (303425 / 107), (348675 / 107), (-128019 / 107), (-292381 / 214),
      (34464 / 107), (79117 / 214), (-5746 / 107), (-6692 / 107), (541 / 107), (1289 / 214),
      (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_7 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 7 = perturbSeed z (node z 7) - gridPerturbation z 13 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_7 z hm]
  exact checked_recurrence 7 13
    [(1 / 2), (3261 / 107), (369 / 107), (-15613 / 107), (5862 / 107), (15930 / 107),
      (-75963 / 214), (17844 / 107), (164991 / 214), (-47185 / 107), (-89683 / 107),
      (38982 / 107), (55565 / 107), (-16415 / 107), (-41089 / 214), (3783 / 107), (4492 / 107),
      (-453 / 107), (-1073 / 214), (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_8 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 8 = perturbSeed z (node z 8) - gridPerturbation z 10 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_8 z hm]
  exact checked_recurrence 8 10
    [0, (-5106 / 107), (173 / 107), (15449 / 107), (-5619 / 214), (-43551 / 107),
      (-61063 / 214), (154126 / 107), (365479 / 214), (-325927 / 107), (-787863 / 214),
      (386834 / 107), (908579 / 214), (-274322 / 107), (-315443 / 107), (121101 / 107),
      (276451 / 214), (-33602 / 107), (-77079 / 214), (5702 / 107), (6638 / 107), (-541 / 107),
      (-1289 / 214), (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_9 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 9 = perturbSeed z (node z 9) - gridPerturbation z 7 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_9 z hm]
  exact checked_recurrence 9 7
    [0, (5106 / 107), (255 / 107), (-15449 / 107), (5405 / 214), (43551 / 107), (61063 / 214),
      (-154126 / 107), (-365479 / 214), (325927 / 107), (787863 / 214), (-386834 / 107),
      (-908579 / 214), (274322 / 107), (315443 / 107), (-121101 / 107), (-276451 / 214),
      (33602 / 107), (77079 / 214), (-5702 / 107), (-6638 / 107), (541 / 107), (1289 / 214),
      (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_10 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 10 = perturbSeed z (node z 10) - gridPerturbation z 4 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_10 z hm]
  exact checked_recurrence 10 4
    [(1 / 2), (-3261 / 107), (-369 / 107), (15613 / 107), (-5862 / 107), (-15930 / 107),
      (75963 / 214), (-17844 / 107), (-164991 / 214), (47185 / 107), (89683 / 107),
      (-38982 / 107), (-55565 / 107), (16415 / 107), (41089 / 214), (-3783 / 107),
      (-4492 / 107), (453 / 107), (1073 / 214), (-22 / 107), (-27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_11 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 11 = perturbSeed z (node z 11) - gridPerturbation z 1 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_11 z hm]
  exact checked_recurrence 11 1
    [1, (997 / 107), (-1038 / 107), (-2975 / 107), (4369 / 107), (-35473 / 107),
      (-126699 / 214), (197037 / 107), (265042 / 107), (-409848 / 107), (-1005903 / 214),
      (454700 / 107), (1067533 / 214), (-303425 / 107), (-348675 / 107), (128019 / 107),
      (292381 / 214), (-34464 / 107), (-79117 / 214), (5746 / 107), (6692 / 107), (-541 / 107),
      (-1289 / 214), (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_12 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 12 = perturbSeed z (node z 12) - gridPerturbation z 1 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_12 z hm]
  exact checked_recurrence 12 1
    [2, (389 / 107), (-899 / 107), (737 / 107), (8769 / 107), (-48673 / 107), (-159741 / 214),
      (215857 / 107), (287079 / 107), (-422318 / 107), (-1034235 / 214), (458874 / 107),
      (1077039 / 214), (-304111 / 107), (-349478 / 107), (128063 / 107), (292489 / 214),
      (-34464 / 107), (-79117 / 214), (5746 / 107), (6692 / 107), (-541 / 107), (-1289 / 214),
      (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_13 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 13 = perturbSeed z (node z 13) - gridPerturbation z 4 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_13 z hm]
  exact checked_recurrence 13 4
    [2, (-846 / 107), (-2439 / 107), (-12921 / 107), (-16164 / 107), (188136 / 107),
      (252907 / 107), (-838806 / 107), (-1083255 / 107), (1875533 / 107), (2311153 / 107),
      (-2443278 / 107), (-2902463 / 107), (2003219 / 107), (2323535 / 107), (-1076805 / 107),
      (-1233915 / 107), (385296 / 107), (440666 / 107), (-90962 / 107), (-104758 / 107),
      (13612 / 107), (15908 / 107), (-1170 / 107), (-1397 / 107), (44 / 107), (54 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_14 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 14 = perturbSeed z (node z 14) - gridPerturbation z 7 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_14 z hm]
  exact checked_recurrence 14 7
    [2, (422 / 107), (2991 / 214), (22299 / 107), (53197 / 214), (-160109 / 107),
      (-407255 / 214), (455591 / 107), (563108 / 107), (-702617 / 107), (-839750 / 107),
      (658578 / 107), (1534071 / 214), (-395058 / 107), (-453240 / 107), (154681 / 107),
      (176738 / 107), (-39304 / 107), (-90355 / 214), (6243 / 107), (14565 / 214),
      (-563 / 107), (-1343 / 214), (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_15 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 15 = perturbSeed z (node z 15) - gridPerturbation z 10 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_15 z hm]
  exact checked_recurrence 15 10
    [1, (-16 / 107), (-2403 / 214), (-16076 / 107), (-18825 / 107), (85776 / 107),
      (106788 / 107), (-191783 / 107), (-465857 / 214), (237060 / 107), (558889 / 214),
      (-178820 / 107), (-206261 / 107), (85382 / 107), (97511 / 107), (-25844 / 107),
      (-59165 / 214), (4796 / 107), (5565 / 107), (-497 / 107), (-1181 / 214), (22 / 107),
      (27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_16 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 16 = perturbSeed z (node z 16) - gridPerturbation z 13 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_16 z hm]
  exact checked_recurrence 16 13
    [(1 / 2), (51 / 107), (369 / 107), (5680 / 107), (5862 / 107), (-30294 / 107),
      (-75963 / 214), (67920 / 107), (164991 / 214), (-76824 / 107), (-89683 / 107),
      (48612 / 107), (55565 / 107), (-18020 / 107), (-41089 / 214), (3890 / 107), (4492 / 107),
      (-453 / 107), (-1073 / 214), (22 / 107), (27 / 107)]
    z hm (by decide +kernel)

theorem grid_recurrence_17 (z : ℝ) (hm : modulus z = 0) :
    gridPerturbation z 17 = perturbSeed z (node z 17) - gridPerturbation z 16 / 3 := by
  rw [perturbSeed_eq_short, cubic_node_17 z hm]
  exact checked_recurrence 17 16
    []
    z hm (by decide +kernel)

theorem grid_recurrence (z : ℝ) (hm : modulus z = 0) (j : Fin 18) :
    gridPerturbation z j = perturbSeed z (node z j) - gridPerturbation z (cubicIndex j) / 3 := by
  fin_cases j
  · exact grid_recurrence_0 z hm
  · exact grid_recurrence_1 z hm
  · exact grid_recurrence_2 z hm
  · exact grid_recurrence_3 z hm
  · exact grid_recurrence_4 z hm
  · exact grid_recurrence_5 z hm
  · exact grid_recurrence_6 z hm
  · exact grid_recurrence_7 z hm
  · exact grid_recurrence_8 z hm
  · exact grid_recurrence_9 z hm
  · exact grid_recurrence_10 z hm
  · exact grid_recurrence_11 z hm
  · exact grid_recurrence_12 z hm
  · exact grid_recurrence_13 z hm
  · exact grid_recurrence_14 z hm
  · exact grid_recurrence_15 z hm
  · exact grid_recurrence_16 z hm
  · exact grid_recurrence_17 z hm

private theorem grid_homogeneous_zero (D : ℕ → ℝ)
    (hrec : ∀ j : Fin 18, D j = -D (cubicIndex j) / 3) :
    ∀ j : Fin 18, D j = 0 := by
  have h4rec := hrec ⟨4, by decide⟩
  have h13rec := hrec ⟨13, by decide⟩
  change D 4 = -D 13 / 3 at h4rec
  change D 13 = -D 4 / 3 at h13rec
  have h4 : D 4 = 0 := by linarith
  have h13 : D 13 = 0 := by linarith
  intro j
  fin_cases j
  · have hj := hrec ⟨0, by decide⟩
    have hk := hrec ⟨1, by decide⟩
    change D 0 = -D 1 / 3 at hj
    change D 1 = -D 4 / 3 at hk
    change D 0 = 0
    linarith
  · have hj := hrec ⟨1, by decide⟩
    have hk := hrec ⟨4, by decide⟩
    change D 1 = -D 4 / 3 at hj
    change D 4 = -D 13 / 3 at hk
    change D 1 = 0
    linarith
  · have hj := hrec ⟨2, by decide⟩
    have hk := hrec ⟨7, by decide⟩
    change D 2 = -D 7 / 3 at hj
    change D 7 = -D 13 / 3 at hk
    change D 2 = 0
    linarith
  · have hj := hrec ⟨3, by decide⟩
    have hk := hrec ⟨10, by decide⟩
    change D 3 = -D 10 / 3 at hj
    change D 10 = -D 4 / 3 at hk
    change D 3 = 0
    linarith
  · have hj := hrec ⟨4, by decide⟩
    have hk := hrec ⟨13, by decide⟩
    change D 4 = -D 13 / 3 at hj
    change D 13 = -D 4 / 3 at hk
    change D 4 = 0
    linarith
  · have hj := hrec ⟨5, by decide⟩
    have hk := hrec ⟨16, by decide⟩
    change D 5 = -D 16 / 3 at hj
    change D 16 = -D 13 / 3 at hk
    change D 5 = 0
    linarith
  · have hj := hrec ⟨6, by decide⟩
    have hk := hrec ⟨16, by decide⟩
    change D 6 = -D 16 / 3 at hj
    change D 16 = -D 13 / 3 at hk
    change D 6 = 0
    linarith
  · have hj := hrec ⟨7, by decide⟩
    have hk := hrec ⟨13, by decide⟩
    change D 7 = -D 13 / 3 at hj
    change D 13 = -D 4 / 3 at hk
    change D 7 = 0
    linarith
  · have hj := hrec ⟨8, by decide⟩
    have hk := hrec ⟨10, by decide⟩
    change D 8 = -D 10 / 3 at hj
    change D 10 = -D 4 / 3 at hk
    change D 8 = 0
    linarith
  · have hj := hrec ⟨9, by decide⟩
    have hk := hrec ⟨7, by decide⟩
    change D 9 = -D 7 / 3 at hj
    change D 7 = -D 13 / 3 at hk
    change D 9 = 0
    linarith
  · have hj := hrec ⟨10, by decide⟩
    have hk := hrec ⟨4, by decide⟩
    change D 10 = -D 4 / 3 at hj
    change D 4 = -D 13 / 3 at hk
    change D 10 = 0
    linarith
  · have hj := hrec ⟨11, by decide⟩
    have hk := hrec ⟨1, by decide⟩
    change D 11 = -D 1 / 3 at hj
    change D 1 = -D 4 / 3 at hk
    change D 11 = 0
    linarith
  · have hj := hrec ⟨12, by decide⟩
    have hk := hrec ⟨1, by decide⟩
    change D 12 = -D 1 / 3 at hj
    change D 1 = -D 4 / 3 at hk
    change D 12 = 0
    linarith
  · have hj := hrec ⟨13, by decide⟩
    have hk := hrec ⟨4, by decide⟩
    change D 13 = -D 4 / 3 at hj
    change D 4 = -D 13 / 3 at hk
    change D 13 = 0
    linarith
  · have hj := hrec ⟨14, by decide⟩
    have hk := hrec ⟨7, by decide⟩
    change D 14 = -D 7 / 3 at hj
    change D 7 = -D 13 / 3 at hk
    change D 14 = 0
    linarith
  · have hj := hrec ⟨15, by decide⟩
    have hk := hrec ⟨10, by decide⟩
    change D 15 = -D 10 / 3 at hj
    change D 10 = -D 4 / 3 at hk
    change D 15 = 0
    linarith
  · have hj := hrec ⟨16, by decide⟩
    have hk := hrec ⟨13, by decide⟩
    change D 16 = -D 13 / 3 at hj
    change D 13 = -D 4 / 3 at hk
    change D 16 = 0
    linarith
  · have hj := hrec ⟨17, by decide⟩
    have hk := hrec ⟨16, by decide⟩
    change D 17 = -D 16 / 3 at hj
    change D 16 = -D 13 / 3 at hk
    change D 17 = 0
    linarith

/-- Exact values of every solution of the perturbation functional equation
on the algebraic contact grid.  No regularity assumption on `H` is required. -/
theorem gridPerturbation_eq_actualH (z : ℝ) (hm : modulus z = 0)
    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))
    (H : ℝ → ℝ)
    (hH : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      H x = perturbSeed z x - H (cubic x) / 3) :
    ∀ j : Fin 18, H (node z j) = gridPerturbation z j := by
  let D : ℕ → ℝ := fun j => H (node z j) - gridPerturbation z j
  have hrec (j : Fin 18) : D j = -D (cubicIndex j) / 3 := by
    have hb := node_bounds z hl hu j
    have hactual := hH (node z j) ⟨le_of_lt hb.1, le_of_lt hb.2⟩
    rw [cubic_node z hm j] at hactual
    have hgrid := grid_recurrence z hm j
    dsimp [D]
    linarith only [hactual, hgrid]
  intro j
  exact sub_eq_zero.mp (grid_homogeneous_zero D hrec j)

theorem perturbSeed_zero (z : ℝ) : perturbSeed z 0 = 0 := by
  simp [perturbSeed]

theorem perturbSeed_add_neg (z x : ℝ) :
    perturbSeed z x + perturbSeed z (-x) = 16 * x ^ 4 - 16 * x ^ 2 := by
  unfold perturbSeed
  ring

theorem perturbSeed_contact_even (z : ℝ) (hm : modulus z = 0) :
    perturbSeed z (a z) + perturbSeed z (-a z) = -4 := by
  rw [perturbSeed_add_neg]
  rw [show (a z) ^ 4 = ((a z) ^ 2) ^ 2 from pow_mul (a z) 2 2, a_sq z hm]
  norm_num

end Lorentz.Certificate
