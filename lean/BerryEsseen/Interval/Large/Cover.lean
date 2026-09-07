import BerryEsseen.Interval.Large.Cache
import BerryEsseen.Interval.Prawitz.LargeNUpperLeafTree

/-!
# Interval / Large / Cover
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000

def certifiedLargeHybridCachedBoxAccepted
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : Bool :=
  if (DyadicInterval.ofRat 19 10).hi ≤ r.lo then
    certifiedLargeDirectCachedBoxAccepted cellCache e1Cache L r
  else
    certifiedLargeOldCachedBoxAccepted cellCache e1Cache L r

theorem certifiedLargeHybridCachedBoxAccepted_LPos
    {N : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache} {L r : DyadicInterval}
    (haccepted : certifiedLargeHybridCachedBoxAccepted
      cellCache e1Cache L r = true) :
    0 < L.lo := by
  by_cases hnew : (DyadicInterval.ofRat 19 10).hi ≤ r.lo
  · have hacc : certifiedLargeDirectCachedBoxAccepted
        cellCache e1Cache L r = true := by
      simpa [certifiedLargeHybridCachedBoxAccepted, hnew] using haccepted
    exact ((certifiedLargeDirectCachedBoxAccepted_true_iff
      cellCache e1Cache L r).mp hacc).2.1.toDyadicLargeBoxAdmissible.LPos
  · have hacc : certifiedLargeOldCachedBoxAccepted
        cellCache e1Cache L r = true := by
      simpa [certifiedLargeHybridCachedBoxAccepted, hnew] using haccepted
    exact ((certifiedLargeOldCachedBoxAccepted_true_iff
      cellCache e1Cache L r).mp hacc).2.1.LPos

noncomputable section

theorem normalizedKolmogorovDistance_lt_044_of_largeHybridCachedBoxAccepted
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {N n : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n
        (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : r.Contains (symmetrizationRatio (P.map (X 0))))
    (haccepted : certifiedLargeHybridCachedBoxAccepted
      cellCache e1Cache L r = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  by_cases hnew : (DyadicInterval.ofRat 19 10).hi ≤ r.lo
  · have hacc : certifiedLargeDirectCachedBoxAccepted
        cellCache e1Cache L r = true := by
      simpa [certifiedLargeHybridCachedBoxAccepted, hnew] using haccepted
    exact normalizedKolmogorovDistance_lt_044_of_largeDirectCachedBoxAccepted
      P X hindep hident hX hmean hsecond hcell he1 hn hN hL hr hacc
  · have hacc : certifiedLargeOldCachedBoxAccepted
        cellCache e1Cache L r = true := by
      simpa [certifiedLargeHybridCachedBoxAccepted, hnew] using haccepted
    exact normalizedKolmogorovDistance_lt_044_of_largeOldCachedBoxAccepted
      P X hindep hident hX hmean hsecond hcell he1 hn hN hL hr hacc

end

def certifiedLargeRegionR
    (region : DyadicRouteBLargeDirectRegion)
    (x z : DyadicInterval) : DyadicInterval :=
  match region with
  | .middle => dyadicRouteBLargeDirectRegionR .middle x z
  | .upper => dyadicRouteBLargeUpperDirectRegionR x z

noncomputable section

theorem certifiedLargeRegionR_contains
    {region : DyadicRouteBLargeDirectRegion}
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    (hx0 : 0 ≤ xR) (hz1 : zR ≤ 1)
    (hLPos : 0 < (dyadicRouteBLargeDirectRegionL region x).lo) :
    (certifiedLargeRegionR region x z).Contains
      (routeBLargeDirectRegionR region xR zR) := by
  cases region with
  | middle =>
      simpa [certifiedLargeRegionR] using
        dyadicRouteBLargeDirectRegionR_contains hx hz hLPos
  | upper =>
      simpa [certifiedLargeRegionR] using
        dyadicRouteBLargeUpperDirectRegionR_contains
          hx hz hx0 hz1 hLPos

end

inductive CertifiedLargeResolution where
  | n256
  | n1024
  | n2048
  | n4096
deriving DecidableEq, Repr

structure CertifiedLargeResolutionCache where
  base : DyadicRouteBResolutionCache
  cells4096 : DyadicRouteBCellCache 4096

def CertifiedLargeResolutionCache.Valid
    (cache : CertifiedLargeResolutionCache) : Prop :=
  cache.base.Valid ∧ cache.cells4096.Valid

def certifiedLargeBuildResolutionCache :
    CertifiedLargeResolutionCache where
  base := dyadicRouteBBuildResolutionCache
  cells4096 := dyadicRouteBBuildCellCache 4096

theorem certifiedLargeBuildResolutionCache_valid :
    certifiedLargeBuildResolutionCache.Valid := by
  exact ⟨dyadicRouteBBuildResolutionCache_valid,
    dyadicRouteBBuildCellCache_valid 4096⟩

def certifiedLargeAcceptedAt
    (cache : CertifiedLargeResolutionCache)
    (resolution : CertifiedLargeResolution)
    (region : DyadicRouteBLargeDirectRegion)
    (x z : DyadicInterval) : Bool :=
  let L := dyadicRouteBLargeDirectRegionL region x
  let r := certifiedLargeRegionR region x z
  match resolution with
  | .n256 => certifiedLargeHybridCachedBoxAccepted
      cache.base.cells256 cache.base.e1 L r
  | .n1024 => certifiedLargeHybridCachedBoxAccepted
      cache.base.cells1024 cache.base.e1 L r
  | .n2048 => certifiedLargeHybridCachedBoxAccepted
      cache.base.cells2048 cache.base.e1 L r
  | .n4096 => certifiedLargeHybridCachedBoxAccepted
      cache.cells4096 cache.base.e1 L r

noncomputable section

theorem normalizedKolmogorovDistance_lt_044_of_largeAcceptedAt
    {cache : CertifiedLargeResolutionCache} (hcache : cache.Valid)
    {resolution : CertifiedLargeResolution}
    {region : DyadicRouteBLargeDirectRegion}
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    (hx0 : 0 ≤ xR) (hz1 : zR ≤ 1)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeDirectRegionL region xR =
      routeBSmoothingScale n
        (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0)))
    (haccepted : certifiedLargeAcceptedAt
      cache resolution region x z = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  let L := dyadicRouteBLargeDirectRegionL region x
  let r := certifiedLargeRegionR region x z
  have hLContains : L.Contains
      (routeBLargeDirectRegionL region xR) :=
    dyadicRouteBLargeDirectRegionL_contains hx
  cases resolution with
  | n256 =>
      have hacc : certifiedLargeHybridCachedBoxAccepted
          cache.base.cells256 cache.base.e1 L r = true := by
        simpa [certifiedLargeAcceptedAt, L, r] using haccepted
      have hLPos : 0 < L.lo :=
        certifiedLargeHybridCachedBoxAccepted_LPos hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        certifiedLargeRegionR_contains hx hz hx0 hz1 hLPos
      exact normalizedKolmogorovDistance_lt_044_of_largeHybridCachedBoxAccepted
        P X hindep hident hX hmean hsecond hcache.1.cells256
          hcache.1.e1 hn (by norm_num)
          (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n1024 =>
      have hacc : certifiedLargeHybridCachedBoxAccepted
          cache.base.cells1024 cache.base.e1 L r = true := by
        simpa [certifiedLargeAcceptedAt, L, r] using haccepted
      have hLPos : 0 < L.lo :=
        certifiedLargeHybridCachedBoxAccepted_LPos hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        certifiedLargeRegionR_contains hx hz hx0 hz1 hLPos
      exact normalizedKolmogorovDistance_lt_044_of_largeHybridCachedBoxAccepted
        P X hindep hident hX hmean hsecond hcache.1.cells1024
          hcache.1.e1 hn (by norm_num)
          (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n2048 =>
      have hacc : certifiedLargeHybridCachedBoxAccepted
          cache.base.cells2048 cache.base.e1 L r = true := by
        simpa [certifiedLargeAcceptedAt, L, r] using haccepted
      have hLPos : 0 < L.lo :=
        certifiedLargeHybridCachedBoxAccepted_LPos hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        certifiedLargeRegionR_contains hx hz hx0 hz1 hLPos
      exact normalizedKolmogorovDistance_lt_044_of_largeHybridCachedBoxAccepted
        P X hindep hident hX hmean hsecond hcache.1.cells2048
          hcache.1.e1 hn (by norm_num)
          (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n4096 =>
      have hacc : certifiedLargeHybridCachedBoxAccepted
          cache.cells4096 cache.base.e1 L r = true := by
        simpa [certifiedLargeAcceptedAt, L, r] using haccepted
      have hLPos : 0 < L.lo :=
        certifiedLargeHybridCachedBoxAccepted_LPos hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        certifiedLargeRegionR_contains hx hz hx0 hz1 hLPos
      exact normalizedKolmogorovDistance_lt_044_of_largeHybridCachedBoxAccepted
        P X hindep hident hX hmean hsecond hcache.2
          hcache.1.e1 hn (by norm_num)
          (hL ▸ hLContains) (hr ▸ hrContains) hacc

end

def certifiedLargeAdaptiveAccepted
    (cache : CertifiedLargeResolutionCache)
    (region : DyadicRouteBLargeDirectRegion)
    (x z : DyadicInterval) : Bool :=
  certifiedLargeAcceptedAt cache .n256 region x z ||
    certifiedLargeAcceptedAt cache .n1024 region x z ||
    certifiedLargeAcceptedAt cache .n2048 region x z ||
    certifiedLargeAcceptedAt cache .n4096 region x z

noncomputable section

theorem normalizedKolmogorovDistance_lt_044_of_largeAdaptiveAccepted
    {cache : CertifiedLargeResolutionCache} (hcache : cache.Valid)
    {region : DyadicRouteBLargeDirectRegion}
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    (hx0 : 0 ≤ xR) (hz1 : zR ≤ 1)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeDirectRegionL region xR =
      routeBSmoothingScale n
        (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0)))
    (haccepted : certifiedLargeAdaptiveAccepted
      cache region x z = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  by_cases h256 : certifiedLargeAcceptedAt
      cache .n256 region x z = true
  · exact normalizedKolmogorovDistance_lt_044_of_largeAcceptedAt
      hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
        hn hL hr h256
  · by_cases h1024 : certifiedLargeAcceptedAt
        cache .n1024 region x z = true
    · exact normalizedKolmogorovDistance_lt_044_of_largeAcceptedAt
        hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
          hn hL hr h1024
    · by_cases h2048 : certifiedLargeAcceptedAt
          cache .n2048 region x z = true
      · exact normalizedKolmogorovDistance_lt_044_of_largeAcceptedAt
          hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
            hn hL hr h2048
      · have h4096 : certifiedLargeAcceptedAt
            cache .n4096 region x z = true := by
          simpa [certifiedLargeAdaptiveAccepted, h256, h1024, h2048]
            using haccepted
        exact normalizedKolmogorovDistance_lt_044_of_largeAcceptedAt
          hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
            hn hL hr h4096

end

def certifiedLargeCoverVerify
    (cache : CertifiedLargeResolutionCache)
    (region : DyadicRouteBLargeDirectRegion) :
    ℕ → DyadicInterval → DyadicInterval → Bool
  | 0, x, z => certifiedLargeAdaptiveAccepted cache region x z
  | fuel + 1, x, z =>
      if certifiedLargeAdaptiveAccepted cache region x z then true
      else if z.hi - z.lo ≤ x.hi - x.lo then
        certifiedLargeCoverVerify cache region fuel
            (dyadicRouteBLeftHalf x) z &&
          certifiedLargeCoverVerify cache region fuel
            (dyadicRouteBRightHalf x) z
      else
        certifiedLargeCoverVerify cache region fuel
            x (dyadicRouteBLeftHalf z) &&
          certifiedLargeCoverVerify cache region fuel
            x (dyadicRouteBRightHalf z)

noncomputable section

theorem certifiedLargeCoverVerify_sound
    {cache : CertifiedLargeResolutionCache} (hcache : cache.Valid)
    {region : DyadicRouteBLargeDirectRegion}
    {fuel : ℕ} {x z : DyadicInterval}
    (hverify : certifiedLargeCoverVerify
      cache region fuel x z = true)
    {xR zR : ℝ} (hx : x.Contains xR) (hz : z.Contains zR)
    (hx0 : 0 ≤ xR) (hz1 : zR ≤ 1)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeDirectRegionL region xR =
      routeBSmoothingScale n
        (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  induction fuel generalizing x z with
  | zero =>
      exact normalizedKolmogorovDistance_lt_044_of_largeAdaptiveAccepted
        hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
          hn hL hr hverify
  | succ fuel ih =>
      by_cases hadaptive :
          certifiedLargeAdaptiveAccepted cache region x z = true
      · exact normalizedKolmogorovDistance_lt_044_of_largeAdaptiveAccepted
          hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
            hn hL hr hadaptive
      · by_cases hwidth : z.hi - z.lo ≤ x.hi - x.lo
        · have hchildren :
              certifiedLargeCoverVerify cache region fuel
                  (dyadicRouteBLeftHalf x) z = true ∧
                certifiedLargeCoverVerify cache region fuel
                  (dyadicRouteBRightHalf x) z = true := by
            simpa [certifiedLargeCoverVerify, hadaptive, hwidth,
              Bool.and_eq_true] using hverify
          rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
          · exact ih hchildren.1 hleft hz
          · exact ih hchildren.2 hright hz
        · have hchildren :
              certifiedLargeCoverVerify cache region fuel
                  x (dyadicRouteBLeftHalf z) = true ∧
                certifiedLargeCoverVerify cache region fuel
                  x (dyadicRouteBRightHalf z) = true := by
            simpa [certifiedLargeCoverVerify, hadaptive, hwidth,
              Bool.and_eq_true] using hverify
          rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
          · exact ih hchildren.1 hx hleft
          · exact ih hchildren.2 hx hright

end

def certifiedLargeVerifyLeafTreeWithRefinement
    (cache : CertifiedLargeResolutionCache)
    (region : DyadicRouteBLargeDirectRegion) (extraFuel : ℕ) :
    DyadicRouteBLargeLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf _, x, z =>
      certifiedLargeCoverVerify cache region extraFuel x z
  | .splitX left right, x, z =>
      certifiedLargeVerifyLeafTreeWithRefinement
          cache region extraFuel left (dyadicRouteBLeftHalf x) z &&
        certifiedLargeVerifyLeafTreeWithRefinement
          cache region extraFuel right (dyadicRouteBRightHalf x) z
  | .splitZ left right, x, z =>
      certifiedLargeVerifyLeafTreeWithRefinement
          cache region extraFuel left x (dyadicRouteBLeftHalf z) &&
        certifiedLargeVerifyLeafTreeWithRefinement
          cache region extraFuel right x (dyadicRouteBRightHalf z)

noncomputable section

theorem certifiedLargeVerifyLeafTreeWithRefinement_sound
    {cache : CertifiedLargeResolutionCache} (hcache : cache.Valid)
    {region : DyadicRouteBLargeDirectRegion} {extraFuel : ℕ}
    {tree : DyadicRouteBLargeLeafTree} {x z : DyadicInterval}
    (hverify : certifiedLargeVerifyLeafTreeWithRefinement
      cache region extraFuel tree x z = true)
    {xR zR : ℝ} (hx : x.Contains xR) (hz : z.Contains zR)
    (hx0 : 0 ≤ xR) (hz1 : zR ≤ 1)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeDirectRegionL region xR =
      routeBSmoothingScale n
        (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  induction tree generalizing x z with
  | leaf resolution =>
      exact certifiedLargeCoverVerify_sound
        hcache hverify hx hz hx0 hz1 P X hindep hident hX hmean hsecond
          hn hL hr
  | splitX left right ihLeft ihRight =>
      have hchildren :
          certifiedLargeVerifyLeafTreeWithRefinement cache region
                extraFuel left (dyadicRouteBLeftHalf x) z = true ∧
            certifiedLargeVerifyLeafTreeWithRefinement cache region
                extraFuel right (dyadicRouteBRightHalf x) z = true := by
        simpa [certifiedLargeVerifyLeafTreeWithRefinement,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          certifiedLargeVerifyLeafTreeWithRefinement cache region
                extraFuel left x (dyadicRouteBLeftHalf z) = true ∧
            certifiedLargeVerifyLeafTreeWithRefinement cache region
                extraFuel right x (dyadicRouteBRightHalf z) = true := by
        simpa [certifiedLargeVerifyLeafTreeWithRefinement,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hx hleft
      · exact ihRight hchildren.2 hx hright

end

def certifiedLargeRefinedLeafTreeCertificate
    (region : DyadicRouteBLargeDirectRegion) (extraFuel : ℕ)
    (tree : DyadicRouteBLargeLeafTree) : Bool :=
  certifiedLargeVerifyLeafTreeWithRefinement
    certifiedLargeBuildResolutionCache region extraFuel tree
      dyadicRouteBUnitInterval dyadicRouteBUnitInterval

def certifiedLargeRefinedLeafCodeCertificate
    (region : DyadicRouteBLargeDirectRegion) (extraFuel : ℕ)
    (code : String) : Bool :=
  match dyadicRouteBLargeLeafTreeOfCode code with
  | some tree =>
      certifiedLargeRefinedLeafTreeCertificate region extraFuel tree
  | none => false

noncomputable section

theorem normalizedKolmogorovDistance_lt_044_of_largeRefinedLeafCodeCertificate
    {region : DyadicRouteBLargeDirectRegion} {extraFuel : ℕ}
    {code : String}
    (hcertificate : certifiedLargeRefinedLeafCodeCertificate
      region extraFuel code = true)
    {xR zR : ℝ} (hx0 : 0 ≤ xR) (hx1 : xR ≤ 1)
    (hz0 : 0 ≤ zR) (hz1 : zR ≤ 1)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeDirectRegionL region xR =
      routeBSmoothingScale n
        (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  unfold certifiedLargeRefinedLeafCodeCertificate at hcertificate
  split at hcertificate
  next tree htree =>
    exact certifiedLargeVerifyLeafTreeWithRefinement_sound
      certifiedLargeBuildResolutionCache_valid hcertificate
      (dyadicRouteBUnitInterval_contains hx0 hx1)
      (dyadicRouteBUnitInterval_contains hz0 hz1)
      hx0 hz1 P X hindep hident hX hmean hsecond hn hL hr
  next => simp at hcertificate

end

end BerryEsseen
