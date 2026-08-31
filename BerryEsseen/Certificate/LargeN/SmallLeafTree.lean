import BerryEsseen.Certificate.LargeN.SmallTail
import BerryEsseen.Certificate.LargeN.LeafTree
/-!
# Checked leaf trees for the endpoint-regular large-`n` region

The supplied checker parametrizes `0 < L <= 1/16` by `L = x/16` and
`1 <= r <= 2` by `r = 1 + z`, with `(x,z)` in the unit square.  An untrusted
generator chooses a binary subdivision and one of three quadrature resolutions
at each leaf.  Lean recomputes every endpoint-regular bound in exact dyadic
arithmetic and proves that the leaves cover the whole square.
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

noncomputable def routeBLargeSmallRegionL (x : ℝ) : ℝ := x / 16

noncomputable def routeBLargeSmallRegionR (z : ℝ) : ℝ := 1 + z

def dyadicRouteBLargeSmallRegionL
    (x : DyadicInterval) : DyadicInterval :=
  DyadicInterval.divPoint x 16

def dyadicRouteBLargeSmallRegionR
    (z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add (DyadicInterval.point 1) z

noncomputable section

theorem dyadicRouteBLargeSmallRegionL_contains
    {x : DyadicInterval} {xR : ℝ} (hx : x.Contains xR) :
    (dyadicRouteBLargeSmallRegionL x).Contains
      (routeBLargeSmallRegionL xR) := by
  simpa [dyadicRouteBLargeSmallRegionL, routeBLargeSmallRegionL] using
    dyadicContains_div_point hx 16 (by norm_num)

theorem dyadicRouteBLargeSmallRegionR_contains
    {z : DyadicInterval} {zR : ℝ} (hz : z.Contains zR) :
    (dyadicRouteBLargeSmallRegionR z).Contains
      (routeBLargeSmallRegionR zR) := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  simpa [dyadicRouteBLargeSmallRegionR, routeBLargeSmallRegionR] using
    hone.add hz

end

/-- All exact-integer side conditions needed by one endpoint-regular leaf. -/
def DyadicRouteBLargeSmallFullAdmissible
    (L r : DyadicInterval) (N : ℕ) : Prop :=
  DyadicLargeSmallBoxAdmissible L r ∧
    ∀ i : Fin N,
      DyadicLargeSmallCellAdmissible L r
        (dyadicRouteBLargeSmallYCell N i.1)

instance (L r : DyadicInterval) (N : ℕ) :
    Decidable (DyadicRouteBLargeSmallFullAdmissible L r N) := by
  unfold DyadicRouteBLargeSmallFullAdmissible
  infer_instance

def dyadicRouteBLargeSmallAcceptedAt
    (resolution : DyadicRouteBLargeResolution)
    (x z : DyadicInterval) : Bool :=
  let L := dyadicRouteBLargeSmallRegionL x
  let r := dyadicRouteBLargeSmallRegionR z
  match resolution with
  | .n256 =>
      decide ((dyadicRouteBLargeSmallBound L r 256).hi <
        dyadicRouteBThreshold.lo) &&
        decide (DyadicRouteBLargeSmallFullAdmissible L r 256)
  | .n1024 =>
      decide ((dyadicRouteBLargeSmallBound L r 1024).hi <
        dyadicRouteBThreshold.lo) &&
        decide (DyadicRouteBLargeSmallFullAdmissible L r 1024)
  | .n2048 =>
      decide ((dyadicRouteBLargeSmallBound L r 2048).hi <
        dyadicRouteBThreshold.lo) &&
        decide (DyadicRouteBLargeSmallFullAdmissible L r 2048)

theorem dyadicRouteBLargeSmallAcceptedAt_true_iff
    (resolution : DyadicRouteBLargeResolution)
    (x z : DyadicInterval) :
    dyadicRouteBLargeSmallAcceptedAt resolution x z = true ↔
      let L := dyadicRouteBLargeSmallRegionL x
      let r := dyadicRouteBLargeSmallRegionR z
      match resolution with
      | .n256 =>
          (dyadicRouteBLargeSmallBound L r 256).hi <
              dyadicRouteBThreshold.lo ∧
            DyadicRouteBLargeSmallFullAdmissible L r 256
      | .n1024 =>
          (dyadicRouteBLargeSmallBound L r 1024).hi <
              dyadicRouteBThreshold.lo ∧
            DyadicRouteBLargeSmallFullAdmissible L r 1024
      | .n2048 =>
          (dyadicRouteBLargeSmallBound L r 2048).hi <
              dyadicRouteBThreshold.lo ∧
            DyadicRouteBLargeSmallFullAdmissible L r 2048 := by
  cases resolution <;>
    simp [dyadicRouteBLargeSmallAcceptedAt, Bool.and_eq_true]

def dyadicRouteBLargeSmallVerifyLeafTree :
    DyadicRouteBLargeLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf resolution, x, z =>
      dyadicRouteBLargeSmallAcceptedAt resolution x z
  | .splitX left right, x, z =>
      dyadicRouteBLargeSmallVerifyLeafTree left
          (dyadicRouteBLeftHalf x) z &&
        dyadicRouteBLargeSmallVerifyLeafTree right
          (dyadicRouteBRightHalf x) z
  | .splitZ left right, x, z =>
      dyadicRouteBLargeSmallVerifyLeafTree left
          x (dyadicRouteBLeftHalf z) &&
        dyadicRouteBLargeSmallVerifyLeafTree right
          x (dyadicRouteBRightHalf z)

noncomputable section

theorem routeB_normalizedRouteBU_lt_threshold_of_largeSmallAcceptedAt
    {resolution : DyadicRouteBLargeResolution}
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hL : routeBLargeSmallRegionL xR = routeBSmoothingScale n rho)
    (hr : routeBLargeSmallRegionR zR = routeBDboundR rho eta)
    (haccepted :
      dyadicRouteBLargeSmallAcceptedAt resolution x z = true) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  let L := dyadicRouteBLargeSmallRegionL x
  let r := dyadicRouteBLargeSmallRegionR z
  have hLContains : L.Contains (routeBSmoothingScale n rho) := by
    rw [← hL]
    exact dyadicRouteBLargeSmallRegionL_contains hx
  have hrContains : r.Contains (routeBDboundR rho eta) := by
    rw [← hr]
    exact dyadicRouteBLargeSmallRegionR_contains hz
  have hfinish {N : ℕ} (hN : 0 < N)
      (hbound : (dyadicRouteBLargeSmallBound L r N).hi <
        dyadicRouteBThreshold.lo)
      (hfull : DyadicRouteBLargeSmallFullAdmissible L r N) :
      Real.sqrt (n : ℝ) / rho *
          routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
        (4495 : ℝ) / 10000 := by
    have hreal :=
      routeB_normalizedRouteBU_le_dyadicRouteBLargeSmallBound_upper
        hn hN hrho1 heta0 heta1 hLContains hrContains hfull.1
          (fun i hi => hfull.2 ⟨i, hi⟩)
    exact hreal.trans_lt <|
      (dyadic_upper_lt_lower_of_hi_lt_lo hbound).trans_le
        dyadicRouteBThreshold_contains.1
  have hprop :=
    (dyadicRouteBLargeSmallAcceptedAt_true_iff resolution x z).mp haccepted
  cases resolution with
  | n256 => exact hfinish (by norm_num) hprop.1 hprop.2
  | n1024 => exact hfinish (by norm_num) hprop.1 hprop.2
  | n2048 => exact hfinish (by norm_num) hprop.1 hprop.2

theorem dyadicRouteBLargeSmallVerifyLeafTree_sound
    {tree : DyadicRouteBLargeLeafTree}
    {x z : DyadicInterval}
    (hverify : dyadicRouteBLargeSmallVerifyLeafTree tree x z = true)
    {xR zR : ℝ} (hx : x.Contains xR) (hz : z.Contains zR)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hL : routeBLargeSmallRegionL xR = routeBSmoothingScale n rho)
    (hr : routeBLargeSmallRegionR zR = routeBDboundR rho eta) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  induction tree generalizing x z with
  | leaf resolution =>
      exact routeB_normalizedRouteBU_lt_threshold_of_largeSmallAcceptedAt
        hx hz hn hrho1 heta0 heta1 hL hr hverify
  | splitX left right ihLeft ihRight =>
      have hchildren :
          dyadicRouteBLargeSmallVerifyLeafTree left
                (dyadicRouteBLeftHalf x) z = true ∧
            dyadicRouteBLargeSmallVerifyLeafTree right
                (dyadicRouteBRightHalf x) z = true := by
        simpa [dyadicRouteBLargeSmallVerifyLeafTree, Bool.and_eq_true] using
          hverify
      rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          dyadicRouteBLargeSmallVerifyLeafTree left
                x (dyadicRouteBLeftHalf z) = true ∧
            dyadicRouteBLargeSmallVerifyLeafTree right
                x (dyadicRouteBRightHalf z) = true := by
        simpa [dyadicRouteBLargeSmallVerifyLeafTree, Bool.and_eq_true] using
          hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hx hleft
      · exact ihRight hchildren.2 hx hright

end

def dyadicRouteBLargeSmallLeafTreeCertificate
    (tree : DyadicRouteBLargeLeafTree) : Bool :=
  dyadicRouteBLargeSmallVerifyLeafTree tree
    dyadicRouteBUnitInterval dyadicRouteBUnitInterval

def dyadicRouteBLargeSmallLeafCodeCertificate (code : String) : Bool :=
  match dyadicRouteBLargeLeafTreeOfCode code with
  | some tree => dyadicRouteBLargeSmallLeafTreeCertificate tree
  | none => false

noncomputable section

theorem routeB_normalizedRouteBU_lt_threshold_of_largeSmallLeafCodeCertificate
    {code : String}
    (hcertificate : dyadicRouteBLargeSmallLeafCodeCertificate code = true)
    {xR zR : ℝ} (hx0 : 0 ≤ xR) (hx1 : xR ≤ 1)
    (hz0 : 0 ≤ zR) (hz1 : zR ≤ 1)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hL : routeBLargeSmallRegionL xR = routeBSmoothingScale n rho)
    (hr : routeBLargeSmallRegionR zR = routeBDboundR rho eta) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  unfold dyadicRouteBLargeSmallLeafCodeCertificate at hcertificate
  split at hcertificate
  next tree htree =>
    exact dyadicRouteBLargeSmallVerifyLeafTree_sound hcertificate
      (dyadicRouteBUnitInterval_contains hx0 hx1)
      (dyadicRouteBUnitInterval_contains hz0 hz1)
      hn hrho1 heta0 heta1 hL hr
  next => simp at hcertificate

def routeBLargeSmallX (n : ℕ) (rho : ℝ) : ℝ :=
  16 * routeBSmoothingScale n rho

def routeBLargeSmallZ (rho eta : ℝ) : ℝ := eta / rho

theorem routeBLargeSmallX_nonnegative
    {n : ℕ} (hn : 0 < n) {rho : ℝ} (hrho : 0 < rho) :
    0 ≤ routeBLargeSmallX n rho := by
  unfold routeBLargeSmallX
  positivity [routeBSmoothingScale_pos hn hrho]

theorem routeBLargeSmallX_le_one
    {n : ℕ} {rho : ℝ}
    (hL : routeBSmoothingScale n rho ≤ (1 : ℝ) / 16) :
    routeBLargeSmallX n rho ≤ 1 := by
  unfold routeBLargeSmallX
  nlinarith

theorem routeBLargeSmallZ_nonnegative
    {rho eta : ℝ} (hrho : 1 ≤ rho) (heta : 0 ≤ eta) :
    0 ≤ routeBLargeSmallZ rho eta := by
  unfold routeBLargeSmallZ
  positivity

theorem routeBLargeSmallZ_le_one
    {rho eta : ℝ} (hrho : 1 ≤ rho) (heta : eta ≤ 1) :
    routeBLargeSmallZ rho eta ≤ 1 := by
  unfold routeBLargeSmallZ
  rw [div_le_one (zero_lt_one.trans_le hrho)]
  linarith

theorem routeBLargeSmallL_inverse (L : ℝ) :
    routeBLargeSmallRegionL (16 * L) = L := by
  unfold routeBLargeSmallRegionL
  ring

theorem routeBLargeSmallR_inverse
    {rho eta : ℝ} (hrho : 0 < rho) :
    routeBLargeSmallRegionR (routeBLargeSmallZ rho eta) =
      routeBDboundR rho eta := by
  rw [routeBDboundR_eq_one_add hrho.ne']
  rfl

/-- A checked endpoint-regular code proves the normalized Route B bound for
every actual parameter with `rho / sqrt n <= 1/16`. -/
theorem routeB_normalizedRouteBU_lt_threshold_of_largeSmallCertificate
    {code : String}
    (hcertificate : dyadicRouteBLargeSmallLeafCodeCertificate code = true)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hL : routeBSmoothingScale n rho ≤ (1 : ℝ) / 16) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  apply routeB_normalizedRouteBU_lt_threshold_of_largeSmallLeafCodeCertificate
    hcertificate
  · exact routeBLargeSmallX_nonnegative hnPos hrhoPos
  · exact routeBLargeSmallX_le_one hL
  · exact routeBLargeSmallZ_nonnegative hrho heta0
  · exact routeBLargeSmallZ_le_one hrho heta1
  · exact hn
  · exact hrho
  · exact heta0
  · exact heta1
  · exact routeBLargeSmallL_inverse _
  · exact routeBLargeSmallR_inverse hrhoPos

end

end BerryEsseen
