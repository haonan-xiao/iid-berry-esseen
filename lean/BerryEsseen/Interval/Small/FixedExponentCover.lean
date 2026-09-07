import BerryEsseen.Interval.Small.FixedExponentIntegral
import BerryEsseen.Interval.Prawitz.LargeNSmallLeafTree

/-!
# Interval / Small / Fixed Exponent Cover
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000

def certifiedLargeSmallThreshold : DyadicInterval :=
  DyadicInterval.ofRat 44 100

theorem certifiedLargeSmallThreshold_contains :
    certifiedLargeSmallThreshold.Contains (44 / 100 : ℝ) := by
  simpa [certifiedLargeSmallThreshold] using
    DyadicInterval.contains_ofRat 44 (b := 100) (by norm_num)

def CertifiedLargeSmallFullAdmissible
    (L r : DyadicInterval) (N : ℕ) : Prop :=
  CertifiedLargeSmallBoxAdmissible L r ∧
    ∀ i : Fin N,
      CertifiedLargeSmallCellAdmissible L r
        (dyadicRouteBLargeSmallYCell N i.1)

instance (L r : DyadicInterval) (N : ℕ) :
    Decidable (CertifiedLargeSmallFullAdmissible L r N) := by
  unfold CertifiedLargeSmallFullAdmissible
  infer_instance

def certifiedLargeSmallNewBoxAccepted
    (N : ℕ) (L r : DyadicInterval) : Bool :=
  decide ((certifiedLargeSmallBound L r N).hi <
    certifiedLargeSmallThreshold.lo) &&
  decide (CertifiedLargeSmallFullAdmissible L r N)

def certifiedLargeSmallOldBoxAccepted
    (N : ℕ) (L r : DyadicInterval) : Bool :=
  decide ((dyadicRouteBLargeSmallBound L r N).hi <
    certifiedLargeSmallThreshold.lo) &&
  decide (DyadicRouteBLargeSmallFullAdmissible L r N)

def certifiedLargeSmallHybridBoxAccepted
    (N : ℕ) (L r : DyadicInterval) : Bool :=
  if (DyadicInterval.ofRat 19 10).hi ≤ r.lo then
    certifiedLargeSmallNewBoxAccepted N L r
  else
    certifiedLargeSmallOldBoxAccepted N L r

theorem certifiedLargeSmallNewBoxAccepted_true_iff
    (N : ℕ) (L r : DyadicInterval) :
    certifiedLargeSmallNewBoxAccepted N L r = true ↔
      (certifiedLargeSmallBound L r N).hi <
          certifiedLargeSmallThreshold.lo ∧
        CertifiedLargeSmallFullAdmissible L r N := by
  simp [certifiedLargeSmallNewBoxAccepted, Bool.and_eq_true]

theorem certifiedLargeSmallOldBoxAccepted_true_iff
    (N : ℕ) (L r : DyadicInterval) :
    certifiedLargeSmallOldBoxAccepted N L r = true ↔
      (dyadicRouteBLargeSmallBound L r N).hi <
          certifiedLargeSmallThreshold.lo ∧
        DyadicRouteBLargeSmallFullAdmissible L r N := by
  simp [certifiedLargeSmallOldBoxAccepted, Bool.and_eq_true]

noncomputable section

theorem lawNormalizedPrawitzFunctional_lt_044_of_smallNewBoxAccepted
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (haccepted : certifiedLargeSmallNewBoxAccepted N L r = true) :
    lawNormalizedPrawitzFunctional n mu < (44 : ℝ) / 100 := by
  have hprop :=
    (certifiedLargeSmallNewBoxAccepted_true_iff N L r).mp haccepted
  have hreal := lawNormalizedPrawitzFunctional_le_smallBound_upper
    mu hX hmean hsecond hn hN hL hr hprop.2.1
      (fun i hi => hprop.2.2 ⟨i, hi⟩)
  exact hreal.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo hprop.1).trans_le
      certifiedLargeSmallThreshold_contains.1

theorem lawNormalizedPrawitzFunctional_lt_044_of_smallOldBoxAccepted
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (haccepted : certifiedLargeSmallOldBoxAccepted N L r = true) :
    lawNormalizedPrawitzFunctional n mu < (44 : ℝ) / 100 := by
  let rho := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let eta := rho * (rR - 1)
  have hprop :=
    (certifiedLargeSmallOldBoxAccepted_true_iff N L r).mp haccepted
  have hrho1 : 1 ≤ rho := by
    dsimp only [rho]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hrR1 : 1 ≤ rR := by
    dsimp only [rR]
    exact symmetrizationRatio_lower mu hX hmean hsecond
  have hrRUpper : rR ≤ 1 + 1 / rho := by
    dsimp only [rR, rho]
    exact symmetrizationRatio_upper mu hX hmean hsecond
  have heta0 : 0 ≤ eta := by
    dsimp only [eta]
    exact mul_nonneg (zero_le_one.trans hrho1) (sub_nonneg.mpr hrR1)
  have heta1 : eta ≤ 1 := by
    have hdiff : rR - 1 ≤ 1 / rho := by linarith
    have hmul := mul_le_mul_of_nonneg_left hdiff (zero_le_one.trans hrho1)
    have hcancel : rho * (1 / rho) = 1 := by field_simp
    dsimp only [eta]
    linarith
  have hrouteR : routeBDboundR rho eta = rR := by
    simpa only [eta] using routeBDboundR_mul_excess hrhoPos.ne'
  have hrouteBound :=
    refinedRouteB_normalizedRouteBU_le_dyadicRouteBLargeSmallBound_upper
      hn hN hrho1 heta0 heta1
        (by simpa only [rho] using hL)
        (by simpa only [hrouteR] using hr)
        hprop.2.1 (fun i hi => hprop.2.2 ⟨i, hi⟩)
  have h := lawNormalizedPrawitzFunctional_le_routeB
    mu hX hmean hsecond (n := n) (by omega)
  have hbound : lawNormalizedPrawitzFunctional n mu ≤
      (dyadicRouteBLargeSmallBound L r N).upper := by
    exact h.trans <| by
      simpa only [rho, rR, eta, hrouteR] using hrouteBound
  exact hbound.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo hprop.1).trans_le
      certifiedLargeSmallThreshold_contains.1

theorem lawNormalizedPrawitzFunctional_lt_044_of_smallHybridBoxAccepted
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (haccepted : certifiedLargeSmallHybridBoxAccepted N L r = true) :
    lawNormalizedPrawitzFunctional n mu < (44 : ℝ) / 100 := by
  by_cases hnew : (DyadicInterval.ofRat 19 10).hi ≤ r.lo
  · have hacc : certifiedLargeSmallNewBoxAccepted N L r = true := by
      simpa [certifiedLargeSmallHybridBoxAccepted, hnew] using haccepted
    exact lawNormalizedPrawitzFunctional_lt_044_of_smallNewBoxAccepted
      mu hX hmean hsecond hn hN hL hr hacc
  · have hacc : certifiedLargeSmallOldBoxAccepted N L r = true := by
      simpa [certifiedLargeSmallHybridBoxAccepted, hnew] using haccepted
    exact lawNormalizedPrawitzFunctional_lt_044_of_smallOldBoxAccepted
      mu hX hmean hsecond hn hN hL hr hacc

theorem normalizedKolmogorovDistance_lt_044_of_smallHybridBoxAccepted
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : r.Contains (symmetrizationRatio (P.map (X 0))))
    (haccepted : certifiedLargeSmallHybridBoxAccepted N L r = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  let mu := P.map (X 0)
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hKD := normalizedKolmogorovDistance_le_lawNormalizedPrawitzFunctional
    P X hindep hident hX hmean hsecond (n := n) (by omega)
  have hfunctional :=
    lawNormalizedPrawitzFunctional_lt_044_of_smallHybridBoxAccepted
      mu hX hmean hsecond hn hN
        (by simpa only [mu] using hL)
        (by simpa only [mu] using hr) haccepted
  exact hKD.trans_lt <| by simpa only [mu] using hfunctional

end

inductive CertifiedLargeSmallResolution where
  | n256
  | n1024
  | n2048
  | n4096
deriving DecidableEq, Repr

def certifiedLargeSmallAcceptedAt
    (resolution : CertifiedLargeSmallResolution)
    (x z : DyadicInterval) : Bool :=
  let L := dyadicRouteBLargeSmallRegionL x
  let r := dyadicRouteBLargeSmallRegionR z
  match resolution with
  | .n256 => certifiedLargeSmallHybridBoxAccepted 256 L r
  | .n1024 => certifiedLargeSmallHybridBoxAccepted 1024 L r
  | .n2048 => certifiedLargeSmallHybridBoxAccepted 2048 L r
  | .n4096 => certifiedLargeSmallHybridBoxAccepted 4096 L r

noncomputable section

theorem normalizedKolmogorovDistance_lt_044_of_largeSmallAcceptedAt
    {resolution : CertifiedLargeSmallResolution}
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeSmallRegionL xR =
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeSmallRegionR zR =
      symmetrizationRatio (P.map (X 0)))
    (haccepted : certifiedLargeSmallAcceptedAt resolution x z = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  let L := dyadicRouteBLargeSmallRegionL x
  let r := dyadicRouteBLargeSmallRegionR z
  have hLContains : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0)))) := by
    rw [← hL]
    exact dyadicRouteBLargeSmallRegionL_contains hx
  have hrContains : r.Contains
      (symmetrizationRatio (P.map (X 0))) := by
    rw [← hr]
    exact dyadicRouteBLargeSmallRegionR_contains hz
  cases resolution with
  | n256 =>
      exact normalizedKolmogorovDistance_lt_044_of_smallHybridBoxAccepted
        P X hindep hident hX hmean hsecond (n := n) (N := 256)
          hn (by norm_num)
          hLContains hrContains (by
            simpa [certifiedLargeSmallAcceptedAt, L, r] using haccepted)
  | n1024 =>
      exact normalizedKolmogorovDistance_lt_044_of_smallHybridBoxAccepted
        P X hindep hident hX hmean hsecond (n := n) (N := 1024)
          hn (by norm_num)
          hLContains hrContains (by
            simpa [certifiedLargeSmallAcceptedAt, L, r] using haccepted)
  | n2048 =>
      exact normalizedKolmogorovDistance_lt_044_of_smallHybridBoxAccepted
        P X hindep hident hX hmean hsecond (n := n) (N := 2048)
          hn (by norm_num)
          hLContains hrContains (by
            simpa [certifiedLargeSmallAcceptedAt, L, r] using haccepted)
  | n4096 =>
      exact normalizedKolmogorovDistance_lt_044_of_smallHybridBoxAccepted
        P X hindep hident hX hmean hsecond (n := n) (N := 4096)
          hn (by norm_num)
          hLContains hrContains (by
            simpa [certifiedLargeSmallAcceptedAt, L, r] using haccepted)

end


def certifiedLargeSmallAdaptiveAccepted
    (x z : DyadicInterval) : Bool :=
  certifiedLargeSmallAcceptedAt .n256 x z ||
    certifiedLargeSmallAcceptedAt .n1024 x z ||
    certifiedLargeSmallAcceptedAt .n2048 x z ||
    certifiedLargeSmallAcceptedAt .n4096 x z

noncomputable section

theorem normalizedKolmogorovDistance_lt_044_of_largeSmallAdaptiveAccepted
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeSmallRegionL xR =
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeSmallRegionR zR =
      symmetrizationRatio (P.map (X 0)))
    (haccepted : certifiedLargeSmallAdaptiveAccepted x z = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  by_cases h256 : certifiedLargeSmallAcceptedAt .n256 x z = true
  · exact normalizedKolmogorovDistance_lt_044_of_largeSmallAcceptedAt
      hx hz P X hindep hident hX hmean hsecond hn hL hr h256
  · by_cases h1024 : certifiedLargeSmallAcceptedAt .n1024 x z = true
    · exact normalizedKolmogorovDistance_lt_044_of_largeSmallAcceptedAt
        hx hz P X hindep hident hX hmean hsecond hn hL hr h1024
    · by_cases h2048 : certifiedLargeSmallAcceptedAt .n2048 x z = true
      · exact normalizedKolmogorovDistance_lt_044_of_largeSmallAcceptedAt
          hx hz P X hindep hident hX hmean hsecond hn hL hr h2048
      · have h4096 : certifiedLargeSmallAcceptedAt .n4096 x z = true := by
          simpa [certifiedLargeSmallAdaptiveAccepted,
            h256, h1024, h2048] using haccepted
        exact normalizedKolmogorovDistance_lt_044_of_largeSmallAcceptedAt
          hx hz P X hindep hident hX hmean hsecond hn hL hr h4096

end


def certifiedLargeSmallCoverVerify :
    ℕ → DyadicInterval → DyadicInterval → Bool
  | 0, x, z => certifiedLargeSmallAdaptiveAccepted x z
  | fuel + 1, x, z =>
      if certifiedLargeSmallAdaptiveAccepted x z then true
      else if 10 * (z.hi - z.lo) ≤ 9 * (x.hi - x.lo) then
        certifiedLargeSmallCoverVerify fuel
            (dyadicRouteBLeftHalf x) z &&
          certifiedLargeSmallCoverVerify fuel
            (dyadicRouteBRightHalf x) z
      else
        certifiedLargeSmallCoverVerify fuel
            x (dyadicRouteBLeftHalf z) &&
          certifiedLargeSmallCoverVerify fuel
            x (dyadicRouteBRightHalf z)

noncomputable section

theorem certifiedLargeSmallCoverVerify_sound
    {fuel : ℕ} {x z : DyadicInterval}
    (hverify : certifiedLargeSmallCoverVerify fuel x z = true)
    {xR zR : ℝ} (hx : x.Contains xR) (hz : z.Contains zR)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeSmallRegionL xR =
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeSmallRegionR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  induction fuel generalizing x z with
  | zero =>
      exact normalizedKolmogorovDistance_lt_044_of_largeSmallAdaptiveAccepted
        hx hz P X hindep hident hX hmean hsecond hn hL hr hverify
  | succ fuel ih =>
      by_cases hadaptive : certifiedLargeSmallAdaptiveAccepted x z = true
      · exact normalizedKolmogorovDistance_lt_044_of_largeSmallAdaptiveAccepted
          hx hz P X hindep hident hX hmean hsecond hn hL hr hadaptive
      · by_cases hwidth : 10 * (z.hi - z.lo) ≤ 9 * (x.hi - x.lo)
        · have hchildren :
              certifiedLargeSmallCoverVerify fuel
                  (dyadicRouteBLeftHalf x) z = true ∧
                certifiedLargeSmallCoverVerify fuel
                  (dyadicRouteBRightHalf x) z = true := by
            simpa [certifiedLargeSmallCoverVerify, hadaptive, hwidth,
              Bool.and_eq_true] using hverify
          rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
          · exact ih hchildren.1 hleft hz
          · exact ih hchildren.2 hright hz
        · have hchildren :
              certifiedLargeSmallCoverVerify fuel
                  x (dyadicRouteBLeftHalf z) = true ∧
                certifiedLargeSmallCoverVerify fuel
                  x (dyadicRouteBRightHalf z) = true := by
            simpa [certifiedLargeSmallCoverVerify, hadaptive, hwidth,
              Bool.and_eq_true] using hverify
          rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
          · exact ih hchildren.1 hx hleft
          · exact ih hchildren.2 hx hright

end


def certifiedLargeSmallVerifyLeafTreeWithRefinement
    (extraFuel : ℕ) :
    DyadicRouteBLargeLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf _, x, z => certifiedLargeSmallCoverVerify extraFuel x z
  | .splitX left right, x, z =>
      certifiedLargeSmallVerifyLeafTreeWithRefinement
          extraFuel left (dyadicRouteBLeftHalf x) z &&
        certifiedLargeSmallVerifyLeafTreeWithRefinement
          extraFuel right (dyadicRouteBRightHalf x) z
  | .splitZ left right, x, z =>
      certifiedLargeSmallVerifyLeafTreeWithRefinement
          extraFuel left x (dyadicRouteBLeftHalf z) &&
        certifiedLargeSmallVerifyLeafTreeWithRefinement
          extraFuel right x (dyadicRouteBRightHalf z)

noncomputable section

theorem certifiedLargeSmallVerifyLeafTreeWithRefinement_sound
    {extraFuel : ℕ} {tree : DyadicRouteBLargeLeafTree}
    {x z : DyadicInterval}
    (hverify : certifiedLargeSmallVerifyLeafTreeWithRefinement
      extraFuel tree x z = true)
    {xR zR : ℝ} (hx : x.Contains xR) (hz : z.Contains zR)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeSmallRegionL xR =
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeSmallRegionR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  induction tree generalizing x z with
  | leaf resolution =>
      exact certifiedLargeSmallCoverVerify_sound
        hverify hx hz P X hindep hident hX hmean hsecond hn hL hr
  | splitX left right ihLeft ihRight =>
      have hchildren :
          certifiedLargeSmallVerifyLeafTreeWithRefinement extraFuel
                left (dyadicRouteBLeftHalf x) z = true ∧
            certifiedLargeSmallVerifyLeafTreeWithRefinement extraFuel
                right (dyadicRouteBRightHalf x) z = true := by
        simpa [certifiedLargeSmallVerifyLeafTreeWithRefinement,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          certifiedLargeSmallVerifyLeafTreeWithRefinement extraFuel
                left x (dyadicRouteBLeftHalf z) = true ∧
            certifiedLargeSmallVerifyLeafTreeWithRefinement extraFuel
                right x (dyadicRouteBRightHalf z) = true := by
        simpa [certifiedLargeSmallVerifyLeafTreeWithRefinement,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hx hleft
      · exact ihRight hchildren.2 hx hright

end


def certifiedLargeSmallRefinedLeafTreeCertificate
    (extraFuel : ℕ) (tree : DyadicRouteBLargeLeafTree) : Bool :=
  certifiedLargeSmallVerifyLeafTreeWithRefinement extraFuel tree
    dyadicRouteBUnitInterval dyadicRouteBUnitInterval

def certifiedLargeSmallRefinedLeafCodeCertificate
    (extraFuel : ℕ) (code : String) : Bool :=
  match dyadicRouteBLargeLeafTreeOfCode code with
  | some tree => certifiedLargeSmallRefinedLeafTreeCertificate
      extraFuel tree
  | none => false

noncomputable section

theorem normalizedKolmogorovDistance_lt_044_of_largeSmallRefinedLeafCodeCertificate
    {extraFuel : ℕ} {code : String}
    (hcertificate : certifiedLargeSmallRefinedLeafCodeCertificate
      extraFuel code = true)
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
    (hL : routeBLargeSmallRegionL xR =
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeSmallRegionR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  unfold certifiedLargeSmallRefinedLeafCodeCertificate at hcertificate
  split at hcertificate
  next tree htree =>
    exact certifiedLargeSmallVerifyLeafTreeWithRefinement_sound
      hcertificate
      (dyadicRouteBUnitInterval_contains hx0 hx1)
      (dyadicRouteBUnitInterval_contains hz0 hz1)
      P X hindep hident hX hmean hsecond hn hL hr
  next => simp at hcertificate

theorem normalizedKolmogorovDistance_lt_044_of_largeSmallCertificate
    {extraFuel : ℕ} {code : String}
    (hcertificate : certifiedLargeSmallRefinedLeafCodeCertificate
      extraFuel code = true)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hLupper : routeBSmoothingScale n
      (thirdAbsoluteMoment (P.map (X 0))) ≤ (1 : ℝ) / 16) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let eta := rho * (r - 1)
  let xR := routeBLargeSmallX n rho
  let zR := routeBLargeSmallZ rho eta
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrho : 1 ≤ rho := by
    dsimp only [rho, mu]
    exact thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hr : 1 ≤ r := by
    dsimp only [r, mu]
    exact symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond
  have hrUpper : r ≤ 1 + 1 / rho := by
    dsimp only [r, rho, mu]
    exact symmetrizationRatio_upper (P.map (X 0)) hX hmean hsecond
  have heta0 : 0 ≤ eta := by
    dsimp only [eta]
    exact mul_nonneg (zero_le_one.trans hrho) (sub_nonneg.mpr hr)
  have heta1 : eta ≤ 1 := by
    have hdiff : r - 1 ≤ 1 / rho := by linarith
    have hmul := mul_le_mul_of_nonneg_left hdiff (zero_le_one.trans hrho)
    have hcancel : rho * (1 / rho) = 1 := by field_simp
    dsimp only [eta]
    linarith
  have hx0 : 0 ≤ xR := routeBLargeSmallX_nonnegative hnPos hrhoPos
  have hx1 : xR ≤ 1 := by
    dsimp only [xR, rho, mu]
    exact routeBLargeSmallX_le_one hLupper
  have hz0 : 0 ≤ zR := routeBLargeSmallZ_nonnegative hrho heta0
  have hz1 : zR ≤ 1 := routeBLargeSmallZ_le_one hrho heta1
  have hregionL : routeBLargeSmallRegionL xR =
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))) := by
    dsimp only [xR, rho, mu]
    exact routeBLargeSmallL_inverse _
  have hrouteR : routeBDboundR rho eta = r := by
    simpa only [eta] using routeBDboundR_mul_excess hrhoPos.ne'
  have hregionR : routeBLargeSmallRegionR zR =
      symmetrizationRatio (P.map (X 0)) := by
    dsimp only [zR]
    rw [routeBLargeSmallR_inverse hrhoPos, hrouteR]
  exact normalizedKolmogorovDistance_lt_044_of_largeSmallRefinedLeafCodeCertificate
    hcertificate hx0 hx1 hz0 hz1 P X hindep hident hX hmean hsecond
      hn hregionL hregionR

end

end BerryEsseen
