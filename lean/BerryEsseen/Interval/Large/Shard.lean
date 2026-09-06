import BerryEsseen.Interval.Large.TargetCover

/-!
# Interval / Large / Shard
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000

/-- Check one parsed legacy subtree on the explicitly supplied root box and a
shared resolution cache.  The legacy code contributes only its subdivision
topology; every numerical leaf is recomputed by the post-`0.44` checker. -/
def bound4395LargeSubtreeCodeCertificateAtWithCache
    (cache : CertifiedLargeResolutionCache)
    (region : DyadicRouteBLargeDirectRegion) (extraFuel : ℕ)
    (code : String) (xRoot zRoot : DyadicInterval) : Bool :=
  match dyadicRouteBLargeLeafTreeOfCode code with
  | some tree =>
      bound4395LargeVerifyLeafTreeWithRefinement
        cache region extraFuel tree xRoot zRoot
  | none => false

/-- Standalone form used by theorem statements.  Batch modules should bind
`certifiedLargeBuildResolutionCache` once and call the shared-cache form
for every member of the batch. -/
def bound4395LargeSubtreeCodeCertificateAt
    (region : DyadicRouteBLargeDirectRegion) (extraFuel : ℕ)
    (code : String) (xRoot zRoot : DyadicInterval) : Bool :=
  bound4395LargeSubtreeCodeCertificateAtWithCache
    certifiedLargeBuildResolutionCache region extraFuel code xRoot zRoot

/-- Kernel composition for an `X` split.  This combines already established
child Booleans and performs no numerical evaluation of either child. -/
theorem bound4395LargeVerifySplitX_true
    {cache : CertifiedLargeResolutionCache}
    {region : DyadicRouteBLargeDirectRegion} {extraFuel : ℕ}
    {left right : DyadicRouteBLargeLeafTree} {x z : DyadicInterval}
    (hleft : bound4395LargeVerifyLeafTreeWithRefinement
      cache region extraFuel left (dyadicRouteBLeftHalf x) z = true)
    (hright : bound4395LargeVerifyLeafTreeWithRefinement
      cache region extraFuel right (dyadicRouteBRightHalf x) z = true) :
    bound4395LargeVerifyLeafTreeWithRefinement cache region extraFuel
      (.splitX left right) x z = true := by
  simpa [bound4395LargeVerifyLeafTreeWithRefinement, Bool.and_eq_true]
    using And.intro hleft hright

/-- Kernel composition for a `Z` split. -/
theorem bound4395LargeVerifySplitZ_true
    {cache : CertifiedLargeResolutionCache}
    {region : DyadicRouteBLargeDirectRegion} {extraFuel : ℕ}
    {left right : DyadicRouteBLargeLeafTree} {x z : DyadicInterval}
    (hleft : bound4395LargeVerifyLeafTreeWithRefinement
      cache region extraFuel left x (dyadicRouteBLeftHalf z) = true)
    (hright : bound4395LargeVerifyLeafTreeWithRefinement
      cache region extraFuel right x (dyadicRouteBRightHalf z) = true) :
    bound4395LargeVerifyLeafTreeWithRefinement cache region extraFuel
      (.splitZ left right) x z = true := by
  simpa [bound4395LargeVerifyLeafTreeWithRefinement, Bool.and_eq_true]
    using And.intro hleft hright

noncomputable section

/-- Soundness of one independently checkable subtree Boolean.  The caller
must still prove that its closed root box participates in a complete cover. -/
theorem normalizedKolmogorovDistance_lt_879_2000_of_post044LargeSubtreeCode
    {region : DyadicRouteBLargeDirectRegion} {extraFuel : ℕ}
    {code : String} {xRoot zRoot : DyadicInterval}
    (hcertificate : bound4395LargeSubtreeCodeCertificateAt
      region extraFuel code xRoot zRoot = true)
    {xR zR : ℝ} (hx : xRoot.Contains xR) (hz : zRoot.Contains zR)
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
  unfold bound4395LargeSubtreeCodeCertificateAt at hcertificate
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at hcertificate
  split at hcertificate
  next tree htree =>
    exact bound4395LargeVerifyLeafTreeWithRefinement_sound
      certifiedLargeBuildResolutionCache_valid hcertificate
      hx hz hx0 hz1 P X hindep hident hX hmean hsecond hn hL hr
  next => simp at hcertificate

end

end BerryEsseen
