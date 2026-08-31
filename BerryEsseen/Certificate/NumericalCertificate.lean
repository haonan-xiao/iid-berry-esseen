import BerryEsseen.Certificate.Finite.LeafTree
import BerryEsseen.Smoothing.PrawitzLargeNDirectCertificate
import BerryEsseen.Certificate.LargeN.SmallLeafTree
import BerryEsseen.Certificate.LargeN.UpperLeafTree
/-!
# Assembly of the Route B numerical certificate

This module turns checked finite-`n` leaf codes and the three checked large-`n`
region codes into the continuous numerical lemma required by the analytic
proof.  It contains no concrete generated code; the concrete certificate
module supplies those four finite pieces of evidence.
-/

namespace BerryEsseen

noncomputable section

/-- Certificate-facing reparametrization of `1 <= r <= 1 + 1/rho`. -/
def routeBNumericalEta (rho r : ℝ) : ℝ := rho * (r - 1)

theorem routeBNumericalEta_nonnegative
    {rho r : ℝ} (hrho : 0 ≤ rho) (hr : 1 ≤ r) :
    0 ≤ routeBNumericalEta rho r := by
  unfold routeBNumericalEta
  exact mul_nonneg hrho (sub_nonneg.mpr hr)

theorem routeBNumericalEta_le_one
    {rho r : ℝ} (hrho : 0 < rho) (hr : r ≤ 1 + 1 / rho) :
    routeBNumericalEta rho r ≤ 1 := by
  have hdiff : r - 1 ≤ 1 / rho := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hrho.le
  have hcancel : rho * (1 / rho) = 1 := by field_simp
  simpa only [routeBNumericalEta, hcancel] using hmul

theorem routeBDboundR_numericalEta
    {rho r : ℝ} (hrho : 0 < rho) :
    routeBDboundR rho (routeBNumericalEta rho r) = r := by
  rw [routeBDboundR_eq_one_add hrho.ne']
  unfold routeBNumericalEta
  field_simp
  ring

theorem routeBSmoothingScale_le_cutoff
    {n : ℕ} (hn : 0 < n) {rho : ℝ}
    (hrho : rho ≤ cutoff * Real.sqrt (n : ℝ)) :
    routeBSmoothingScale n rho ≤ (56 : ℝ) / 45 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  unfold routeBSmoothingScale
  rw [div_le_iff₀ hsqrt]
  simpa [cutoff] using hrho

theorem routeBU_le_normalizedRate_of_normalized_lt
    {n : ℕ} (hn : 0 < n) {rho U : ℝ} (hrho : 0 < rho)
    (hU : Real.sqrt (n : ℝ) / rho * U < (4495 : ℝ) / 10000) :
    U ≤ normalizedRate certificateConstant rho n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hfactor : 0 < Real.sqrt (n : ℝ) / rho := div_pos hsqrt hrho
  have hdiv : U < ((4495 : ℝ) / 10000) /
      (Real.sqrt (n : ℝ) / rho) :=
    (lt_div_iff₀' hfactor).2 hU
  have heq : ((4495 : ℝ) / 10000) /
        (Real.sqrt (n : ℝ) / rho) =
      ((4495 : ℝ) / 10000) * rho / Real.sqrt (n : ℝ) := by
    field_simp
  rw [heq] at hdiv
  simpa [normalizedRate, certificateConstant] using hdiv.le

/-- Soundness of the complete numerical lemma from finite leaf codes and the
three large-`n` leaf codes.  The code-producing process is not trusted: each
Boolean premise is the exact Lean checker result. -/
theorem routeB_certifiedNumericalBound_of_leaf_certificates
    (hfinite : ∀ n : ℕ, 1 ≤ n → n < 100 →
      ∃ code : String, dyadicRouteBLeafCodeCertificate n code = true)
    {smallCode middleCode upperCode : String}
    (hsmall :
      dyadicRouteBLargeSmallLeafCodeCertificate smallCode = true)
    (hmiddle :
      dyadicRouteBLargeLeafCodeCertificate .middle middleCode = true)
    (hupper :
      dyadicRouteBLargeUpperLeafCodeCertificate upperCode = true) :
    CertifiedNumericalBound
      (routeBU routeBKappa routeBTheta) := by
  intro n rho r hdomain
  have hnPos : 0 < n := hdomain.n_pos
  have hrhoPos : 0 < rho := hdomain.rho_pos
  let eta := routeBNumericalEta rho r
  have heta0 : 0 ≤ eta := by
    dsimp only [eta]
    exact routeBNumericalEta_nonnegative hrhoPos.le hdomain.r_lower
  have heta1 : eta ≤ 1 := by
    dsimp only [eta]
    exact routeBNumericalEta_le_one hrhoPos hdomain.r_upper
  have hrEq : routeBDboundR rho eta = r := by
    dsimp only [eta]
    exact routeBDboundR_numericalEta hrhoPos
  have hnormalized :
      Real.sqrt (n : ℝ) / rho *
          routeBU routeBKappa routeBTheta n rho r <
        (4495 : ℝ) / 10000 := by
    by_cases hnLarge : 100 ≤ n
    · have hLmax : routeBSmoothingScale n rho ≤ (56 : ℝ) / 45 :=
        routeBSmoothingScale_le_cutoff hnPos hdomain.rho_upper
      by_cases hsmallL : routeBSmoothingScale n rho ≤ (1 : ℝ) / 16
      · rw [← hrEq]
        exact routeB_normalizedRouteBU_lt_threshold_of_largeSmallCertificate
          hsmall hnLarge hdomain.rho_lower heta0 heta1 hsmallL
      · have hmiddleL0 : (1 : ℝ) / 16 ≤
            routeBSmoothingScale n rho := le_of_lt (lt_of_not_ge hsmallL)
        by_cases hmiddleL1 :
            routeBSmoothingScale n rho ≤ (1 : ℝ) / 10
        · rw [← hrEq]
          exact routeB_normalizedRouteBU_lt_threshold_of_largeMiddleCertificate
            hmiddle hnLarge hdomain.rho_lower heta0 heta1
              hmiddleL0 hmiddleL1
        · have hupperL0 : (1 : ℝ) / 10 ≤
              routeBSmoothingScale n rho :=
            le_of_lt (lt_of_not_ge hmiddleL1)
          rw [← hrEq]
          apply
            routeB_normalizedRouteBU_lt_threshold_of_largeUpperLeafCodeCertificate
              hupper
          · exact routeBLargeUpperX_nonnegative hupperL0
          · exact routeBLargeUpperX_le_one hLmax
          · exact routeBLargeUpperZ_nonnegative hnPos heta0
          · exact routeBLargeUpperZ_le_one hnLarge heta1
          · exact hnLarge
          · exact hdomain.rho_lower
          · exact heta0
          · exact routeBLargeUpperL_inverse _
          · exact routeBLargeUpperR_inverse hnPos hrhoPos
    · have hnFinite : n < 100 := Nat.lt_of_not_ge hnLarge
      obtain ⟨code, hcode⟩ := hfinite n hdomain.n_lower hnFinite
      rw [← hrEq]
      exact routeB_normalizedRouteBU_lt_threshold_of_leafCodeCertificate
        hnPos hcode hdomain.rho_lower hdomain.rho_upper heta0 heta1
  exact routeBU_le_normalizedRate_of_normalized_lt
    hnPos hrhoPos hnormalized

end

end BerryEsseen
