import BerryEsseen.Certificate.LargeN.LeafTree
/-!
# Checked leaf trees for the direct large-`n` upper region

At the corner `x = 0`, `z = 1`, the real upper-region parameter is exactly
`r = 2`.  Evaluating `1 + z / (10 * L)` with a separately rounded enclosure
of `L = 1/10` gives an artificial upper endpoint slightly above `2`.  The
checker below intersects only that computed upper endpoint with the proved
real constraint `r ≤ 2`; all remaining interval arithmetic, leaf choices, and
the threshold test are unchanged.
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

/-- Intersect the upper endpoint of a dyadic interval with the exact point `2`. -/
def dyadicRouteBLargeCapAtTwo (I : DyadicInterval) : DyadicInterval :=
  ⟨I.lo, min I.hi (DyadicInterval.point 2).lo⟩

theorem dyadicRouteBLargeCapAtTwo_contains
    {I : DyadicInterval} {x : ℝ}
    (hx : I.Contains x) (hxTwo : x ≤ 2) :
    (dyadicRouteBLargeCapAtTwo I).Contains x := by
  by_cases hhi : I.hi ≤ (DyadicInterval.point 2).lo
  · simpa [dyadicRouteBLargeCapAtTwo, min_eq_left hhi] using hx
  · have htwo : (DyadicInterval.point 2).lo ≤ I.hi :=
      le_of_not_ge hhi
    constructor
    · simpa [dyadicRouteBLargeCapAtTwo, DyadicInterval.Contains,
        DyadicInterval.lower] using hx.1
    · change x ≤
        ((min I.hi (DyadicInterval.point 2).lo : ℤ) : ℝ) /
          (dyadicScale : ℝ)
      rw [min_eq_right htwo]
      simpa [DyadicInterval.point, dyadicScale_pos.ne'] using hxTwo

theorem routeBLargeDirectRegionR_upper_le_two
    {x z : ℝ} (hx0 : 0 ≤ x) (hz1 : z ≤ 1) :
    routeBLargeDirectRegionR .upper x z ≤ 2 := by
  have hspan : 0 ≤ (56 : ℝ) / 45 - (1 : ℝ) / 10 := by norm_num
  have hL : (1 : ℝ) / 10 ≤ routeBLargeDirectRegionL .upper x := by
    simp only [routeBLargeDirectRegionL]
    exact le_add_of_nonneg_right (mul_nonneg hx0 hspan)
  have hden : (1 : ℝ) ≤ 10 * routeBLargeDirectRegionL .upper x := by
    nlinarith
  have hdenPos : 0 < 10 * routeBLargeDirectRegionL .upper x :=
    zero_lt_one.trans_le hden
  have hquot : z / (10 * routeBLargeDirectRegionL .upper x) ≤ 1 := by
    rw [div_le_one hdenPos]
    exact hz1.trans hden
  simp only [routeBLargeDirectRegionR]
  linarith

/-- The direct upper-region `r` enclosure, tightened by its exact range bound. -/
def dyadicRouteBLargeUpperDirectRegionR
    (x z : DyadicInterval) : DyadicInterval :=
  dyadicRouteBLargeCapAtTwo
    (dyadicRouteBLargeDirectRegionR .upper x z)

theorem dyadicRouteBLargeUpperDirectRegionR_contains
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    (hx0 : 0 ≤ xR) (hz1 : zR ≤ 1)
    (hLPos : 0 < (dyadicRouteBLargeDirectRegionL .upper x).lo) :
    (dyadicRouteBLargeUpperDirectRegionR x z).Contains
      (routeBLargeDirectRegionR .upper xR zR) := by
  apply dyadicRouteBLargeCapAtTwo_contains
  · exact dyadicRouteBLargeDirectRegionR_contains hx hz hLPos
  · exact routeBLargeDirectRegionR_upper_le_two hx0 hz1

def dyadicRouteBLargeUpperAcceptedAt
    (cache : DyadicRouteBResolutionCache)
    (resolution : DyadicRouteBLargeResolution)
    (x z : DyadicInterval) : Bool :=
  let L := dyadicRouteBLargeDirectRegionL .upper x
  let r := dyadicRouteBLargeUpperDirectRegionR x z
  match resolution with
  | .n256 =>
      dyadicRouteBLargeCachedBoxAccepted cache.cells256 cache.e1 L r
  | .n1024 =>
      dyadicRouteBLargeCachedBoxAccepted cache.cells1024 cache.e1 L r
  | .n2048 =>
      dyadicRouteBLargeCachedBoxAccepted cache.cells2048 cache.e1 L r

def dyadicRouteBLargeUpperVerifyLeafTree
    (cache : DyadicRouteBResolutionCache) :
    DyadicRouteBLargeLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf resolution, x, z =>
      dyadicRouteBLargeUpperAcceptedAt cache resolution x z
  | .splitX left right, x, z =>
      dyadicRouteBLargeUpperVerifyLeafTree cache left
          (dyadicRouteBLeftHalf x) z &&
        dyadicRouteBLargeUpperVerifyLeafTree cache right
          (dyadicRouteBRightHalf x) z
  | .splitZ left right, x, z =>
      dyadicRouteBLargeUpperVerifyLeafTree cache left
          x (dyadicRouteBLeftHalf z) &&
        dyadicRouteBLargeUpperVerifyLeafTree cache right
          x (dyadicRouteBRightHalf z)

theorem routeB_normalizedRouteBU_lt_threshold_of_largeUpperAcceptedAt
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {resolution : DyadicRouteBLargeResolution}
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    (hx0 : 0 ≤ xR) (hz1 : zR ≤ 1)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta)
    (hL : routeBLargeDirectRegionL .upper xR =
      routeBSmoothingScale n rho)
    (hr : routeBLargeDirectRegionR .upper xR zR =
      routeBDboundR rho eta)
    (haccepted :
      dyadicRouteBLargeUpperAcceptedAt cache resolution x z = true) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  let L := dyadicRouteBLargeDirectRegionL .upper x
  let r := dyadicRouteBLargeUpperDirectRegionR x z
  have hLContains : L.Contains (routeBLargeDirectRegionL .upper xR) :=
    dyadicRouteBLargeDirectRegionL_contains hx
  cases resolution with
  | n256 =>
      have hacc :
          dyadicRouteBLargeCachedBoxAccepted cache.cells256 cache.e1 L r = true := by
        simpa [dyadicRouteBLargeUpperAcceptedAt, L, r] using haccepted
      have hprop :=
        (dyadicRouteBLargeCachedBoxAccepted_true_iff
          cache.cells256 cache.e1 L r).mp hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR .upper xR zR) :=
        dyadicRouteBLargeUpperDirectRegionR_contains
          hx hz hx0 hz1 hprop.2.1.LPos
      exact routeB_normalizedRouteBU_lt_threshold_of_largeCachedBoxAccepted
        hcache.cells256 hcache.e1 hn (by norm_num)
        hrho1 heta0 (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n1024 =>
      have hacc :
          dyadicRouteBLargeCachedBoxAccepted cache.cells1024 cache.e1 L r = true := by
        simpa [dyadicRouteBLargeUpperAcceptedAt, L, r] using haccepted
      have hprop :=
        (dyadicRouteBLargeCachedBoxAccepted_true_iff
          cache.cells1024 cache.e1 L r).mp hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR .upper xR zR) :=
        dyadicRouteBLargeUpperDirectRegionR_contains
          hx hz hx0 hz1 hprop.2.1.LPos
      exact routeB_normalizedRouteBU_lt_threshold_of_largeCachedBoxAccepted
        hcache.cells1024 hcache.e1 hn (by norm_num)
        hrho1 heta0 (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n2048 =>
      have hacc :
          dyadicRouteBLargeCachedBoxAccepted cache.cells2048 cache.e1 L r = true := by
        simpa [dyadicRouteBLargeUpperAcceptedAt, L, r] using haccepted
      have hprop :=
        (dyadicRouteBLargeCachedBoxAccepted_true_iff
          cache.cells2048 cache.e1 L r).mp hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR .upper xR zR) :=
        dyadicRouteBLargeUpperDirectRegionR_contains
          hx hz hx0 hz1 hprop.2.1.LPos
      exact routeB_normalizedRouteBU_lt_threshold_of_largeCachedBoxAccepted
        hcache.cells2048 hcache.e1 hn (by norm_num)
        hrho1 heta0 (hL ▸ hLContains) (hr ▸ hrContains) hacc

theorem dyadicRouteBLargeUpperVerifyLeafTree_sound
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {tree : DyadicRouteBLargeLeafTree} {x z : DyadicInterval}
    (hverify :
      dyadicRouteBLargeUpperVerifyLeafTree cache tree x z = true)
    {xR zR : ℝ} (hx : x.Contains xR) (hz : z.Contains zR)
    (hx0 : 0 ≤ xR) (hz1 : zR ≤ 1)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta)
    (hL : routeBLargeDirectRegionL .upper xR =
      routeBSmoothingScale n rho)
    (hr : routeBLargeDirectRegionR .upper xR zR =
      routeBDboundR rho eta) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  induction tree generalizing x z with
  | leaf resolution =>
      exact routeB_normalizedRouteBU_lt_threshold_of_largeUpperAcceptedAt
        hcache hx hz hx0 hz1 hn hrho1 heta0 hL hr hverify
  | splitX left right ihLeft ihRight =>
      have hchildren :
          dyadicRouteBLargeUpperVerifyLeafTree cache left
                (dyadicRouteBLeftHalf x) z = true ∧
            dyadicRouteBLargeUpperVerifyLeafTree cache right
                (dyadicRouteBRightHalf x) z = true := by
        simpa [dyadicRouteBLargeUpperVerifyLeafTree, Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          dyadicRouteBLargeUpperVerifyLeafTree cache left
                x (dyadicRouteBLeftHalf z) = true ∧
            dyadicRouteBLargeUpperVerifyLeafTree cache right
                x (dyadicRouteBRightHalf z) = true := by
        simpa [dyadicRouteBLargeUpperVerifyLeafTree, Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hx hleft
      · exact ihRight hchildren.2 hx hright

def dyadicRouteBLargeUpperLeafTreeCertificate
    (tree : DyadicRouteBLargeLeafTree) : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLargeUpperVerifyLeafTree cache tree
    dyadicRouteBUnitInterval dyadicRouteBUnitInterval

def dyadicRouteBLargeUpperLeafCodeCertificate (code : String) : Bool :=
  match dyadicRouteBLargeLeafTreeOfCode code with
  | some tree => dyadicRouteBLargeUpperLeafTreeCertificate tree
  | none => false

theorem routeB_normalizedRouteBU_lt_threshold_of_largeUpperLeafCodeCertificate
    {code : String}
    (hcertificate :
      dyadicRouteBLargeUpperLeafCodeCertificate code = true)
    {xR zR : ℝ} (hx0 : 0 ≤ xR) (hx1 : xR ≤ 1)
    (hz0 : 0 ≤ zR) (hz1 : zR ≤ 1)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta)
    (hL : routeBLargeDirectRegionL .upper xR =
      routeBSmoothingScale n rho)
    (hr : routeBLargeDirectRegionR .upper xR zR =
      routeBDboundR rho eta) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  unfold dyadicRouteBLargeUpperLeafCodeCertificate at hcertificate
  split at hcertificate
  next tree htree =>
    exact dyadicRouteBLargeUpperVerifyLeafTree_sound
      dyadicRouteBBuildResolutionCache_valid hcertificate
      (dyadicRouteBUnitInterval_contains hx0 hx1)
      (dyadicRouteBUnitInterval_contains hz0 hz1)
      hx0 hz1 hn hrho1 heta0 hL hr
  next => simp at hcertificate

end BerryEsseen
