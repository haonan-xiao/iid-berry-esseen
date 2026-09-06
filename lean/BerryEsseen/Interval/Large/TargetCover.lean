import BerryEsseen.Interval.Large.BoxSoundness

/-!
# Interval / Large / Target Cover
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000

def bound4395LargeAcceptedAt
    (cache : CertifiedLargeResolutionCache)
    (resolution : CertifiedLargeResolution)
    (region : DyadicRouteBLargeDirectRegion)
    (x z : DyadicInterval) : Bool :=
  let L := dyadicRouteBLargeDirectRegionL region x
  let r := certifiedLargeRegionR region x z
  match resolution with
  | .n256 => bound4395LargeHybridCachedBoxAccepted
      cache.base.cells256 cache.base.e1 L r
  | .n1024 => bound4395LargeHybridCachedBoxAccepted
      cache.base.cells1024 cache.base.e1 L r
  | .n2048 => bound4395LargeHybridCachedBoxAccepted
      cache.base.cells2048 cache.base.e1 L r
  | .n4096 => bound4395LargeHybridCachedBoxAccepted
      cache.cells4096 cache.base.e1 L r

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_post044LargeAcceptedAt
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
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0)))
    (haccepted : bound4395LargeAcceptedAt
      cache resolution region x z = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  let L := dyadicRouteBLargeDirectRegionL region x
  let r := certifiedLargeRegionR region x z
  have hLContains : L.Contains
      (routeBLargeDirectRegionL region xR) :=
    dyadicRouteBLargeDirectRegionL_contains hx
  cases resolution with
  | n256 =>
      have hacc : bound4395LargeHybridCachedBoxAccepted
          cache.base.cells256 cache.base.e1 L r = true := by
        simpa [bound4395LargeAcceptedAt, L, r] using haccepted
      have hLPos : 0 < L.lo :=
        bound4395LargeHybridCachedBoxAccepted_LPos hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        certifiedLargeRegionR_contains hx hz hx0 hz1 hLPos
      exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeHybridBox
        P X hindep hident hX hmean hsecond hcache.1.cells256
          hcache.1.e1 hn (by norm_num)
          (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n1024 =>
      have hacc : bound4395LargeHybridCachedBoxAccepted
          cache.base.cells1024 cache.base.e1 L r = true := by
        simpa [bound4395LargeAcceptedAt, L, r] using haccepted
      have hLPos : 0 < L.lo :=
        bound4395LargeHybridCachedBoxAccepted_LPos hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        certifiedLargeRegionR_contains hx hz hx0 hz1 hLPos
      exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeHybridBox
        P X hindep hident hX hmean hsecond hcache.1.cells1024
          hcache.1.e1 hn (by norm_num)
          (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n2048 =>
      have hacc : bound4395LargeHybridCachedBoxAccepted
          cache.base.cells2048 cache.base.e1 L r = true := by
        simpa [bound4395LargeAcceptedAt, L, r] using haccepted
      have hLPos : 0 < L.lo :=
        bound4395LargeHybridCachedBoxAccepted_LPos hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        certifiedLargeRegionR_contains hx hz hx0 hz1 hLPos
      exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeHybridBox
        P X hindep hident hX hmean hsecond hcache.1.cells2048
          hcache.1.e1 hn (by norm_num)
          (hL ▸ hLContains) (hr ▸ hrContains) hacc
  | n4096 =>
      have hacc : bound4395LargeHybridCachedBoxAccepted
          cache.cells4096 cache.base.e1 L r = true := by
        simpa [bound4395LargeAcceptedAt, L, r] using haccepted
      have hLPos : 0 < L.lo :=
        bound4395LargeHybridCachedBoxAccepted_LPos hacc
      have hrContains : r.Contains
          (routeBLargeDirectRegionR region xR zR) :=
        certifiedLargeRegionR_contains hx hz hx0 hz1 hLPos
      exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeHybridBox
        P X hindep hident hX hmean hsecond hcache.2
          hcache.1.e1 hn (by norm_num)
          (hL ▸ hLContains) (hr ▸ hrContains) hacc

end

def bound4395LargeAdaptiveAccepted
    (cache : CertifiedLargeResolutionCache)
    (region : DyadicRouteBLargeDirectRegion)
    (x z : DyadicInterval) : Bool :=
  bound4395LargeAcceptedAt cache .n256 region x z ||
    bound4395LargeAcceptedAt cache .n1024 region x z ||
    bound4395LargeAcceptedAt cache .n2048 region x z ||
    bound4395LargeAcceptedAt cache .n4096 region x z

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_post044LargeAdaptive
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
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0)))
    (haccepted : bound4395LargeAdaptiveAccepted cache region x z = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  by_cases h256 : bound4395LargeAcceptedAt cache .n256 region x z = true
  · exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeAcceptedAt
      hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond hn hL hr h256
  · by_cases h1024 :
        bound4395LargeAcceptedAt cache .n1024 region x z = true
    · exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeAcceptedAt
        hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
          hn hL hr h1024
    · by_cases h2048 :
          bound4395LargeAcceptedAt cache .n2048 region x z = true
      · exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeAcceptedAt
          hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
            hn hL hr h2048
      · have h4096 :
            bound4395LargeAcceptedAt cache .n4096 region x z = true := by
          simpa [bound4395LargeAdaptiveAccepted, h256, h1024, h2048]
            using haccepted
        exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeAcceptedAt
          hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
            hn hL hr h4096

end

def bound4395LargeCoverVerify
    (cache : CertifiedLargeResolutionCache)
    (region : DyadicRouteBLargeDirectRegion) :
    ℕ → DyadicInterval → DyadicInterval → Bool
  | 0, x, z => bound4395LargeAdaptiveAccepted cache region x z
  | fuel + 1, x, z =>
      if bound4395LargeAdaptiveAccepted cache region x z then true
      else if z.hi - z.lo ≤ x.hi - x.lo then
        bound4395LargeCoverVerify cache region fuel
            (dyadicRouteBLeftHalf x) z &&
          bound4395LargeCoverVerify cache region fuel
            (dyadicRouteBRightHalf x) z
      else
        bound4395LargeCoverVerify cache region fuel
            x (dyadicRouteBLeftHalf z) &&
          bound4395LargeCoverVerify cache region fuel
            x (dyadicRouteBRightHalf z)

noncomputable section

theorem bound4395LargeCoverVerify_sound
    {cache : CertifiedLargeResolutionCache} (hcache : cache.Valid)
    {region : DyadicRouteBLargeDirectRegion}
    {fuel : ℕ} {x z : DyadicInterval}
    (hverify : bound4395LargeCoverVerify cache region fuel x z = true)
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
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  induction fuel generalizing x z with
  | zero =>
      exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeAdaptive
        hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
          hn hL hr hverify
  | succ fuel ih =>
      by_cases hadaptive :
          bound4395LargeAdaptiveAccepted cache region x z = true
      · exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeAdaptive
          hcache hx hz hx0 hz1 P X hindep hident hX hmean hsecond
            hn hL hr hadaptive
      · by_cases hwidth : z.hi - z.lo ≤ x.hi - x.lo
        · have hchildren :
              bound4395LargeCoverVerify cache region fuel
                  (dyadicRouteBLeftHalf x) z = true ∧
                bound4395LargeCoverVerify cache region fuel
                  (dyadicRouteBRightHalf x) z = true := by
            simpa [bound4395LargeCoverVerify, hadaptive, hwidth,
              Bool.and_eq_true] using hverify
          rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
          · exact ih hchildren.1 hleft hz
          · exact ih hchildren.2 hright hz
        · have hchildren :
              bound4395LargeCoverVerify cache region fuel
                  x (dyadicRouteBLeftHalf z) = true ∧
                bound4395LargeCoverVerify cache region fuel
                  x (dyadicRouteBRightHalf z) = true := by
            simpa [bound4395LargeCoverVerify, hadaptive, hwidth,
              Bool.and_eq_true] using hverify
          rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
          · exact ih hchildren.1 hx hleft
          · exact ih hchildren.2 hx hright

end

def bound4395LargeVerifyLeafTreeWithRefinement
    (cache : CertifiedLargeResolutionCache)
    (region : DyadicRouteBLargeDirectRegion) (extraFuel : ℕ) :
    DyadicRouteBLargeLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf _, x, z =>
      bound4395LargeCoverVerify cache region extraFuel x z
  | .splitX left right, x, z =>
      bound4395LargeVerifyLeafTreeWithRefinement
          cache region extraFuel left (dyadicRouteBLeftHalf x) z &&
        bound4395LargeVerifyLeafTreeWithRefinement
          cache region extraFuel right (dyadicRouteBRightHalf x) z
  | .splitZ left right, x, z =>
      bound4395LargeVerifyLeafTreeWithRefinement
          cache region extraFuel left x (dyadicRouteBLeftHalf z) &&
        bound4395LargeVerifyLeafTreeWithRefinement
          cache region extraFuel right x (dyadicRouteBRightHalf z)

noncomputable section

theorem bound4395LargeVerifyLeafTreeWithRefinement_sound
    {cache : CertifiedLargeResolutionCache} (hcache : cache.Valid)
    {region : DyadicRouteBLargeDirectRegion} {extraFuel : ℕ}
    {tree : DyadicRouteBLargeLeafTree} {x z : DyadicInterval}
    (hverify : bound4395LargeVerifyLeafTreeWithRefinement
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
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  induction tree generalizing x z with
  | leaf resolution =>
      exact bound4395LargeCoverVerify_sound
        hcache hverify hx hz hx0 hz1 P X hindep hident hX hmean hsecond
          hn hL hr
  | splitX left right ihLeft ihRight =>
      have hchildren :
          bound4395LargeVerifyLeafTreeWithRefinement cache region
                extraFuel left (dyadicRouteBLeftHalf x) z = true ∧
            bound4395LargeVerifyLeafTreeWithRefinement cache region
                extraFuel right (dyadicRouteBRightHalf x) z = true := by
        simpa [bound4395LargeVerifyLeafTreeWithRefinement,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          bound4395LargeVerifyLeafTreeWithRefinement cache region
                extraFuel left x (dyadicRouteBLeftHalf z) = true ∧
            bound4395LargeVerifyLeafTreeWithRefinement cache region
                extraFuel right x (dyadicRouteBRightHalf z) = true := by
        simpa [bound4395LargeVerifyLeafTreeWithRefinement,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hx hleft
      · exact ihRight hchildren.2 hx hright

end

def bound4395LargeRefinedLeafTreeCertificate
    (region : DyadicRouteBLargeDirectRegion) (extraFuel : ℕ)
    (tree : DyadicRouteBLargeLeafTree) : Bool :=
  bound4395LargeVerifyLeafTreeWithRefinement
    certifiedLargeBuildResolutionCache region extraFuel tree
      dyadicRouteBUnitInterval dyadicRouteBUnitInterval

def bound4395LargeRefinedLeafCodeCertificate
    (region : DyadicRouteBLargeDirectRegion) (extraFuel : ℕ)
    (code : String) : Bool :=
  match dyadicRouteBLargeLeafTreeOfCode code with
  | some tree =>
      bound4395LargeRefinedLeafTreeCertificate region extraFuel tree
  | none => false

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_post044LargeCode
    {region : DyadicRouteBLargeDirectRegion} {extraFuel : ℕ}
    {code : String}
    (hcertificate : bound4395LargeRefinedLeafCodeCertificate
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
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeDirectRegionR region xR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  unfold bound4395LargeRefinedLeafCodeCertificate at hcertificate
  split at hcertificate
  next tree htree =>
    exact bound4395LargeVerifyLeafTreeWithRefinement_sound
      certifiedLargeBuildResolutionCache_valid hcertificate
      (dyadicRouteBUnitInterval_contains hx0 hx1)
      (dyadicRouteBUnitInterval_contains hz0 hz1)
      hx0 hz1 P X hindep hident hX hmean hsecond hn hL hr
  next => simp at hcertificate

end

end BerryEsseen
