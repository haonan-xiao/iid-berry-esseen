import BerryEsseen.Certificate.Finite.CachedCover
/-!
# Explicit leaf trees for finite Route B certificates

The exhaustive search used to discover a cover evaluates every rejected internal node.  A
checked leaf tree records only the split topology and re-evaluates the expensive numerical bound
at its leaves.  Its soundness does not trust the process that produced the tree: each split
covers its complete parent interval and every leaf must pass the existing cached box checker.
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

inductive DyadicRouteBLeafTree where
  | leaf
  | splitRho (left right : DyadicRouteBLeafTree)
  | splitZ (left right : DyadicRouteBLeafTree)
deriving DecidableEq, Repr

/-- Verify a supplied tree.  Unlike exhaustive discovery, this evaluates no internal bound. -/
def dyadicRouteBVerifyLeafTree
    (cache : DyadicRouteBResolutionCache) (n : ℕ) :
    DyadicRouteBLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf, rho, z => dyadicRouteBCachedFiniteBoxAccepted cache n rho z
  | .splitRho left right, rho, z =>
      dyadicRouteBVerifyLeafTree cache n left (dyadicRouteBLeftHalf rho) z &&
        dyadicRouteBVerifyLeafTree cache n right (dyadicRouteBRightHalf rho) z
  | .splitZ left right, rho, z =>
      dyadicRouteBVerifyLeafTree cache n left rho (dyadicRouteBLeftHalf z) &&
        dyadicRouteBVerifyLeafTree cache n right rho (dyadicRouteBRightHalf z)

theorem dyadicRouteBVerifyLeafTree_sound
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {n : ℕ} (hn : 0 < n) {tree : DyadicRouteBLeafTree}
    {rho z : DyadicInterval}
    (hverify : dyadicRouteBVerifyLeafTree cache n tree rho z = true)
    {rhoR zR : ℝ} (hrho : rho.Contains rhoR) (hz : z.Contains zR) :
    Real.sqrt (n : ℝ) / rhoR *
        routeBU routeBKappa routeBTheta n rhoR (routeBDboundR rhoR zR) <
      (4495 : ℝ) / 10000 := by
  induction tree generalizing rho z with
  | leaf =>
      exact routeB_normalizedRouteBU_lt_threshold_of_cachedFiniteBoxAccepted
        hcache hn hverify hrho hz
  | splitRho left right ihLeft ihRight =>
      have hchildren :
          dyadicRouteBVerifyLeafTree cache n left (dyadicRouteBLeftHalf rho) z = true ∧
            dyadicRouteBVerifyLeafTree cache n right (dyadicRouteBRightHalf rho) z = true := by
        simpa [dyadicRouteBVerifyLeafTree, Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hrho with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          dyadicRouteBVerifyLeafTree cache n left rho (dyadicRouteBLeftHalf z) = true ∧
            dyadicRouteBVerifyLeafTree cache n right rho (dyadicRouteBRightHalf z) = true := by
        simpa [dyadicRouteBVerifyLeafTree, Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hrho hleft
      · exact ihRight hchildren.2 hrho hright

def dyadicRouteBLeafTreeCertificate (n : ℕ) (tree : DyadicRouteBLeafTree) : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBVerifyLeafTree cache n tree
    (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ

theorem routeB_normalizedRouteBU_lt_threshold_of_leafTreeCertificate
    {n : ℕ} (hn : 0 < n) {tree : DyadicRouteBLeafTree}
    (hcertificate : dyadicRouteBLeafTreeCertificate n tree = true)
    {rho z : ℝ} (hrhoLower : 1 ≤ rho)
    (hrhoUpper : rho ≤ ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ z) (hzUpper : z ≤ 1) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z) <
      (4495 : ℝ) / 10000 := by
  exact dyadicRouteBVerifyLeafTree_sound
    dyadicRouteBBuildResolutionCache_valid hn hcertificate
    (dyadicRouteBFiniteRootRho_contains hrhoLower hrhoUpper)
    (dyadicRouteBFiniteRootZ_contains hzLower hzUpper)

/-! ## Compact prefix-code certificates -/

/-- Parse a prefix code for a leaf tree.  `L` denotes a leaf, while `R` and `Z` denote
rho- and z-splits followed by the encodings of their left and right subtrees.  The fuel is
decreased on every tree level, so malformed input cannot make the parser diverge. -/
def dyadicRouteBParseLeafTreeAux :
    ℕ → List Char → Option (DyadicRouteBLeafTree × List Char)
  | 0, _ => none
  | _fuel + 1, 'L' :: rest => some (.leaf, rest)
  | fuel + 1, 'R' :: rest => do
      let (left, afterLeft) ← dyadicRouteBParseLeafTreeAux fuel rest
      let (right, afterRight) ← dyadicRouteBParseLeafTreeAux fuel afterLeft
      some (.splitRho left right, afterRight)
  | fuel + 1, 'Z' :: rest => do
      let (left, afterLeft) ← dyadicRouteBParseLeafTreeAux fuel rest
      let (right, afterRight) ← dyadicRouteBParseLeafTreeAux fuel afterLeft
      some (.splitZ left right, afterRight)
  | _ + 1, _ => none

/-- Decode a complete prefix code, rejecting malformed codes and trailing characters. -/
def dyadicRouteBLeafTreeOfCode (code : String) : Option DyadicRouteBLeafTree :=
  let chars := code.toList
  match dyadicRouteBParseLeafTreeAux chars.length chars with
  | some (tree, []) => some tree
  | _ => none

/-- Check a compact prefix code by decoding it and applying the proof-producing leaf verifier. -/
def dyadicRouteBLeafCodeCertificate (n : ℕ) (code : String) : Bool :=
  match dyadicRouteBLeafTreeOfCode code with
  | some tree => dyadicRouteBLeafTreeCertificate n tree
  | none => false

theorem routeB_normalizedRouteBU_lt_threshold_of_leafCodeCertificate
    {n : ℕ} (hn : 0 < n) {code : String}
    (hcertificate : dyadicRouteBLeafCodeCertificate n code = true)
    {rho z : ℝ} (hrhoLower : 1 ≤ rho)
    (hrhoUpper : rho ≤ ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ z) (hzUpper : z ≤ 1) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z) <
      (4495 : ℝ) / 10000 := by
  unfold dyadicRouteBLeafCodeCertificate at hcertificate
  split at hcertificate
  next tree htree =>
    exact routeB_normalizedRouteBU_lt_threshold_of_leafTreeCertificate
      hn hcertificate hrhoLower hrhoUpper hzLower hzUpper
  next => simp at hcertificate

/-! ## Untrusted discovery helper -/

/-- Reproduce the current exhaustive split policy and return its successful leaf tree.  This is
only a certificate generator: the final theorem checks the returned explicit tree with
`dyadicRouteBVerifyLeafTree` and does not rely on this function's correctness. -/
def dyadicRouteBDiscoverLeafTree
    (cache : DyadicRouteBResolutionCache) (n : ℕ) :
    ℕ → DyadicInterval → DyadicInterval → Option DyadicRouteBLeafTree
  | 0, rho, z =>
      if dyadicRouteBCachedFiniteBoxAccepted cache n rho z then
        some .leaf
      else none
  | fuel + 1, rho, z =>
      if dyadicRouteBCachedFiniteBoxAccepted cache n rho z then
        some .leaf
      else if dyadicRouteBSplitRho n rho z then
        match
            dyadicRouteBDiscoverLeafTree cache n fuel (dyadicRouteBLeftHalf rho) z,
            dyadicRouteBDiscoverLeafTree cache n fuel (dyadicRouteBRightHalf rho) z with
        | some left, some right => some (.splitRho left right)
        | _, _ => none
      else
        match
            dyadicRouteBDiscoverLeafTree cache n fuel rho (dyadicRouteBLeftHalf z),
            dyadicRouteBDiscoverLeafTree cache n fuel rho (dyadicRouteBRightHalf z) with
        | some left, some right => some (.splitZ left right)
        | _, _ => none

def dyadicRouteBDiscoverFiniteLeafTree (n : ℕ) : Option DyadicRouteBLeafTree :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBDiscoverLeafTree cache n 30
    (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ

end BerryEsseen
