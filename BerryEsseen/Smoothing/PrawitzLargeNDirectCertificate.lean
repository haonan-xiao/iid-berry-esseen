import BerryEsseen.Certificate.LargeN.LeafTree
/-!
# Applying the direct large-`n` certificates

This module inverts the two unit-square parametrizations and shows that they
cover the actual Route B parameters in the ranges `1/16 ≤ L ≤ 1/10` and
`1/10 ≤ L ≤ 56/45`.
-/

namespace BerryEsseen

noncomputable section

def routeBLargeMiddleX (L : ℝ) : ℝ :=
  (L - (1 : ℝ) / 16) / ((1 : ℝ) / 10 - (1 : ℝ) / 16)

def routeBLargeMiddleZ (rho eta : ℝ) : ℝ := eta / rho

def routeBLargeUpperX (L : ℝ) : ℝ :=
  (L - (1 : ℝ) / 10) / ((56 : ℝ) / 45 - (1 : ℝ) / 10)

def routeBLargeUpperZ (n : ℕ) (eta : ℝ) : ℝ :=
  10 * eta / Real.sqrt (n : ℝ)

theorem routeBLargeMiddleX_nonnegative
    {L : ℝ} (hL : (1 : ℝ) / 16 ≤ L) :
    0 ≤ routeBLargeMiddleX L := by
  unfold routeBLargeMiddleX
  apply div_nonneg (sub_nonneg.mpr hL)
  norm_num

theorem routeBLargeMiddleX_le_one
    {L : ℝ} (hL : L ≤ (1 : ℝ) / 10) :
    routeBLargeMiddleX L ≤ 1 := by
  unfold routeBLargeMiddleX
  norm_num
  linarith

theorem routeBLargeMiddleZ_nonnegative
    {rho eta : ℝ} (hrho : 1 ≤ rho) (heta : 0 ≤ eta) :
    0 ≤ routeBLargeMiddleZ rho eta := by
  unfold routeBLargeMiddleZ
  positivity

theorem routeBLargeMiddleZ_le_one
    {rho eta : ℝ} (hrho : 1 ≤ rho) (heta : eta ≤ 1) :
    routeBLargeMiddleZ rho eta ≤ 1 := by
  unfold routeBLargeMiddleZ
  rw [div_le_one (zero_lt_one.trans_le hrho)]
  linarith

theorem routeBLargeMiddleL_inverse (L : ℝ) :
    routeBLargeDirectRegionL .middle (routeBLargeMiddleX L) = L := by
  unfold routeBLargeDirectRegionL routeBLargeMiddleX
  ring

theorem routeBLargeMiddleR_inverse
    {rho eta : ℝ} (hrho : 0 < rho) :
    routeBLargeDirectRegionR .middle 0 (routeBLargeMiddleZ rho eta) =
      routeBDboundR rho eta := by
  rw [routeBDboundR_eq_one_add hrho.ne']
  rfl

theorem routeBLargeUpperX_nonnegative
    {L : ℝ} (hL : (1 : ℝ) / 10 ≤ L) :
    0 ≤ routeBLargeUpperX L := by
  unfold routeBLargeUpperX
  apply div_nonneg (sub_nonneg.mpr hL)
  norm_num

theorem routeBLargeUpperX_le_one
    {L : ℝ} (hL : L ≤ (56 : ℝ) / 45) :
    routeBLargeUpperX L ≤ 1 := by
  unfold routeBLargeUpperX
  norm_num
  linarith

theorem routeBLargeUpperZ_nonnegative
    {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ routeBLargeUpperZ n eta := by
  unfold routeBLargeUpperZ
  positivity

theorem routeBLarge_sqrt_ten_le
    {n : ℕ} (hn : 100 ≤ n) : 10 ≤ Real.sqrt (n : ℝ) := by
  have hnR : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrt100 : Real.sqrt (100 : ℝ) = 10 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 100)
    have hnonneg := Real.sqrt_nonneg (100 : ℝ)
    nlinarith
  calc
    (10 : ℝ) = Real.sqrt (100 : ℝ) := hsqrt100.symm
    _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hnR

theorem routeBLargeUpperZ_le_one
    {n : ℕ} (hn : 100 ≤ n) {eta : ℝ} (heta1 : eta ≤ 1) :
    routeBLargeUpperZ n eta ≤ 1 := by
  have hsqrt := routeBLarge_sqrt_ten_le hn
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := lt_of_lt_of_le (by norm_num) hsqrt
  unfold routeBLargeUpperZ
  rw [div_le_one hsqrtPos]
  nlinarith

theorem routeBLargeUpperL_inverse (L : ℝ) :
    routeBLargeDirectRegionL .upper (routeBLargeUpperX L) = L := by
  unfold routeBLargeDirectRegionL routeBLargeUpperX
  ring

theorem routeBLargeUpperR_inverse
    {n : ℕ} (hn : 0 < n) {rho eta : ℝ} (hrho : 0 < rho) :
    routeBLargeDirectRegionR .upper
        (routeBLargeUpperX (routeBSmoothingScale n rho))
        (routeBLargeUpperZ n eta) =
      routeBDboundR rho eta := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  change 1 + routeBLargeUpperZ n eta /
      (10 * routeBLargeDirectRegionL .upper
        (routeBLargeUpperX (routeBSmoothingScale n rho))) =
    routeBDboundR rho eta
  rw [routeBLargeUpperL_inverse, routeBDboundR_eq_one_add hrho.ne']
  unfold routeBLargeUpperZ routeBSmoothingScale
  field_simp [hrho.ne', hsqrt.ne']

/-- A checked middle-region leaf code proves the normalized Route B bound
for every actual parameter with `1/16 ≤ rho/sqrt n ≤ 1/10`. -/
theorem routeB_normalizedRouteBU_lt_threshold_of_largeMiddleCertificate
    {code : String}
    (hcertificate :
      dyadicRouteBLargeLeafCodeCertificate .middle code = true)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hL0 : (1 : ℝ) / 16 ≤ routeBSmoothingScale n rho)
    (hL1 : routeBSmoothingScale n rho ≤ (1 : ℝ) / 10) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  apply routeB_normalizedRouteBU_lt_threshold_of_largeLeafCodeCertificate
    hcertificate
  · exact routeBLargeMiddleX_nonnegative hL0
  · exact routeBLargeMiddleX_le_one hL1
  · exact routeBLargeMiddleZ_nonnegative hrho heta0
  · exact routeBLargeMiddleZ_le_one hrho heta1
  · exact hn
  · exact hrho
  · exact heta0
  · exact routeBLargeMiddleL_inverse _
  · exact routeBLargeMiddleR_inverse (zero_lt_one.trans_le hrho)

/-- A checked upper-region leaf code proves the normalized Route B bound
for every actual parameter with `1/10 ≤ rho/sqrt n ≤ 56/45`. -/
theorem routeB_normalizedRouteBU_lt_threshold_of_largeUpperCertificate
    {code : String}
    (hcertificate :
      dyadicRouteBLargeLeafCodeCertificate .upper code = true)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hL0 : (1 : ℝ) / 10 ≤ routeBSmoothingScale n rho)
    (hL1 : routeBSmoothingScale n rho ≤ (56 : ℝ) / 45) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  apply routeB_normalizedRouteBU_lt_threshold_of_largeLeafCodeCertificate
    hcertificate
  · exact routeBLargeUpperX_nonnegative hL0
  · exact routeBLargeUpperX_le_one hL1
  · exact routeBLargeUpperZ_nonnegative hnPos heta0
  · exact routeBLargeUpperZ_le_one hn heta1
  · exact hn
  · exact hrho
  · exact heta0
  · exact routeBLargeUpperL_inverse _
  · exact routeBLargeUpperR_inverse hnPos (zero_lt_one.trans_le hrho)

end

end BerryEsseen
