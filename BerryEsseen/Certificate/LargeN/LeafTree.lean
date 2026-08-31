import BerryEsseen.Certificate.LargeN.Region
import BerryEsseen.Certificate.Finite.CachedCover
/-!
# Checked leaf trees for the direct large-`n` regions

An untrusted generator may choose the split topology and one of the three
supported quadrature resolutions at each leaf.  Lean re-evaluates every leaf
from exact integers and proves that the two child boxes cover their parent.
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

inductive DyadicRouteBLargeResolution where
  | n256
  | n1024
  | n2048
deriving DecidableEq, Repr

inductive DyadicRouteBLargeLeafTree where
  | leaf (resolution : DyadicRouteBLargeResolution)
  | splitX (left right : DyadicRouteBLargeLeafTree)
  | splitZ (left right : DyadicRouteBLargeLeafTree)
deriving DecidableEq, Repr

def dyadicRouteBLargeAcceptedAt
    (cache : DyadicRouteBResolutionCache)
    (resolution : DyadicRouteBLargeResolution)
    (region : DyadicRouteBLargeDirectRegion)
    (x z : DyadicInterval) : Bool :=
  let L := dyadicRouteBLargeDirectRegionL region x
  let r := dyadicRouteBLargeDirectRegionR region x z
  match resolution with
  | .n256 =>
      dyadicRouteBLargeCachedBoxAccepted cache.cells256 cache.e1 L r
  | .n1024 =>
      dyadicRouteBLargeCachedBoxAccepted cache.cells1024 cache.e1 L r
  | .n2048 =>
      dyadicRouteBLargeCachedBoxAccepted cache.cells2048 cache.e1 L r

def dyadicRouteBLargeVerifyLeafTree
    (cache : DyadicRouteBResolutionCache)
    (region : DyadicRouteBLargeDirectRegion) :
    DyadicRouteBLargeLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf resolution, x, z =>
      dyadicRouteBLargeAcceptedAt cache resolution region x z
  | .splitX left right, x, z =>
      dyadicRouteBLargeVerifyLeafTree cache region left
          (dyadicRouteBLeftHalf x) z &&
        dyadicRouteBLargeVerifyLeafTree cache region right
          (dyadicRouteBRightHalf x) z
  | .splitZ left right, x, z =>
      dyadicRouteBLargeVerifyLeafTree cache region left
          x (dyadicRouteBLeftHalf z) &&
        dyadicRouteBLargeVerifyLeafTree cache region right
          x (dyadicRouteBRightHalf z)

noncomputable section

theorem routeB_normalizedRouteBU_lt_threshold_of_largeAcceptedAt
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {resolution : DyadicRouteBLargeResolution}
    {region : DyadicRouteBLargeDirectRegion}
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta)
    (hL : routeBLargeDirectRegionL region xR =
      routeBSmoothingScale n rho)
    (hr : routeBLargeDirectRegionR region xR zR =
      routeBDboundR rho eta)
    (haccepted :
      dyadicRouteBLargeAcceptedAt cache resolution region x z = true) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  let L := dyadicRouteBLargeDirectRegionL region x
  let r := dyadicRouteBLargeDirectRegionR region x z
  have hLContains : L.Contains (routeBLargeDirectRegionL region xR) :=
    dyadicRouteBLargeDirectRegionL_contains hx
  cases resolution with
  | n256 =>
      have hacc :
          dyadicRouteBLargeCachedBoxAccepted cache.cells256 cache.e1 L r = true := by
        simpa [dyadicRouteBLargeAcceptedAt, L, r] using haccepted
      have hprop :=
        (dyadicRouteBLargeCachedBoxAccepted_true_iff
          cache.cells256 cache.e1 L r).mp hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        dyadicRouteBLargeDirectRegionR_contains hx hz hprop.2.1.LPos
      exact routeB_normalizedRouteBU_lt_threshold_of_largeCachedBoxAccepted
        hcache.cells256 hcache.e1 hn (by norm_num)
        hrho1 heta0 (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n1024 =>
      have hacc :
          dyadicRouteBLargeCachedBoxAccepted cache.cells1024 cache.e1 L r = true := by
        simpa [dyadicRouteBLargeAcceptedAt, L, r] using haccepted
      have hprop :=
        (dyadicRouteBLargeCachedBoxAccepted_true_iff
          cache.cells1024 cache.e1 L r).mp hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        dyadicRouteBLargeDirectRegionR_contains hx hz hprop.2.1.LPos
      exact routeB_normalizedRouteBU_lt_threshold_of_largeCachedBoxAccepted
        hcache.cells1024 hcache.e1 hn (by norm_num)
        hrho1 heta0 (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n2048 =>
      have hacc :
          dyadicRouteBLargeCachedBoxAccepted cache.cells2048 cache.e1 L r = true := by
        simpa [dyadicRouteBLargeAcceptedAt, L, r] using haccepted
      have hprop :=
        (dyadicRouteBLargeCachedBoxAccepted_true_iff
          cache.cells2048 cache.e1 L r).mp hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        dyadicRouteBLargeDirectRegionR_contains hx hz hprop.2.1.LPos
      exact routeB_normalizedRouteBU_lt_threshold_of_largeCachedBoxAccepted
        hcache.cells2048 hcache.e1 hn (by norm_num)
        hrho1 heta0 (hL ▸ hLContains) (hr ▸ hrContains) hacc

theorem dyadicRouteBLargeVerifyLeafTree_sound
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {region : DyadicRouteBLargeDirectRegion}
    {tree : DyadicRouteBLargeLeafTree}
    {x z : DyadicInterval}
    (hverify : dyadicRouteBLargeVerifyLeafTree cache region tree x z = true)
    {xR zR : ℝ} (hx : x.Contains xR) (hz : z.Contains zR)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta)
    (hL : routeBLargeDirectRegionL region xR =
      routeBSmoothingScale n rho)
    (hr : routeBLargeDirectRegionR region xR zR =
      routeBDboundR rho eta) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  induction tree generalizing x z with
  | leaf resolution =>
      exact routeB_normalizedRouteBU_lt_threshold_of_largeAcceptedAt
        hcache hx hz hn hrho1 heta0 hL hr hverify
  | splitX left right ihLeft ihRight =>
      have hchildren :
          dyadicRouteBLargeVerifyLeafTree cache region left
                (dyadicRouteBLeftHalf x) z = true ∧
            dyadicRouteBLargeVerifyLeafTree cache region right
                (dyadicRouteBRightHalf x) z = true := by
        simpa [dyadicRouteBLargeVerifyLeafTree, Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          dyadicRouteBLargeVerifyLeafTree cache region left
                x (dyadicRouteBLeftHalf z) = true ∧
            dyadicRouteBLargeVerifyLeafTree cache region right
                x (dyadicRouteBRightHalf z) = true := by
        simpa [dyadicRouteBLargeVerifyLeafTree, Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hx hleft
      · exact ihRight hchildren.2 hx hright

end

def dyadicRouteBLargeLeafTreeCertificate
    (region : DyadicRouteBLargeDirectRegion)
    (tree : DyadicRouteBLargeLeafTree) : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLargeVerifyLeafTree cache region tree
    dyadicRouteBUnitInterval dyadicRouteBUnitInterval

/-! ## Compact prefix-code certificates -/

/-- Prefix format: `0`, `1`, and `2` are leaves at resolutions 256, 1024,
and 2048; `X` and `Z` are binary splits followed by their two subtrees. -/
def dyadicRouteBLargeParseLeafTreeAux :
    ℕ → List Char → Option (DyadicRouteBLargeLeafTree × List Char)
  | 0, _ => none
  | _fuel + 1, '0' :: rest => some (.leaf .n256, rest)
  | _fuel + 1, '1' :: rest => some (.leaf .n1024, rest)
  | _fuel + 1, '2' :: rest => some (.leaf .n2048, rest)
  | fuel + 1, 'X' :: rest => do
      let (left, afterLeft) ← dyadicRouteBLargeParseLeafTreeAux fuel rest
      let (right, afterRight) ← dyadicRouteBLargeParseLeafTreeAux fuel afterLeft
      some (.splitX left right, afterRight)
  | fuel + 1, 'Z' :: rest => do
      let (left, afterLeft) ← dyadicRouteBLargeParseLeafTreeAux fuel rest
      let (right, afterRight) ← dyadicRouteBLargeParseLeafTreeAux fuel afterLeft
      some (.splitZ left right, afterRight)
  | _ + 1, _ => none

def dyadicRouteBLargeLeafTreeOfCode
    (code : String) : Option DyadicRouteBLargeLeafTree :=
  let chars := code.toList
  match dyadicRouteBLargeParseLeafTreeAux chars.length chars with
  | some (tree, []) => some tree
  | _ => none

def dyadicRouteBLargeLeafCodeCertificate
    (region : DyadicRouteBLargeDirectRegion) (code : String) : Bool :=
  match dyadicRouteBLargeLeafTreeOfCode code with
  | some tree => dyadicRouteBLargeLeafTreeCertificate region tree
  | none => false

noncomputable section

theorem routeB_normalizedRouteBU_lt_threshold_of_largeLeafCodeCertificate
    {region : DyadicRouteBLargeDirectRegion} {code : String}
    (hcertificate :
      dyadicRouteBLargeLeafCodeCertificate region code = true)
    {xR zR : ℝ} (hx0 : 0 ≤ xR) (hx1 : xR ≤ 1)
    (hz0 : 0 ≤ zR) (hz1 : zR ≤ 1)
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta)
    (hL : routeBLargeDirectRegionL region xR =
      routeBSmoothingScale n rho)
    (hr : routeBLargeDirectRegionR region xR zR =
      routeBDboundR rho eta) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 := by
  unfold dyadicRouteBLargeLeafCodeCertificate at hcertificate
  split at hcertificate
  next tree htree =>
    exact dyadicRouteBLargeVerifyLeafTree_sound
      dyadicRouteBBuildResolutionCache_valid hcertificate
      (dyadicRouteBUnitInterval_contains hx0 hx1)
      (dyadicRouteBUnitInterval_contains hz0 hz1)
      hn hrho1 heta0 hL hr
  next => simp at hcertificate

end

end BerryEsseen
