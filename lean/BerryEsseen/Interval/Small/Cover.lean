import BerryEsseen.Smoothing.VariableExponentBoundarySoundness
import BerryEsseen.Interval.Small.FixedExponentCover

/-!
# Interval / Small / Cover
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000

def variableAlphaSmallOldBoxAccepted
    (N : ℕ) (L r : DyadicInterval) : Bool :=
  decide ((dyadicRouteBLargeSmallBound L r N).hi <
    bound4395Threshold.lo) &&
  decide (DyadicRouteBLargeSmallFullAdmissible L r N)

def variableAlphaSmallHybridBoxAccepted
    (N : ℕ) (L r : DyadicInterval) : Bool :=
  if (DyadicInterval.ofRat 19 10).hi ≤ r.lo then
    bound4395VariableAlphaSmallBoxAccepted N L r
  else
    variableAlphaSmallOldBoxAccepted N L r

theorem variableAlphaSmallOldBoxAccepted_true_iff
    (N : ℕ) (L r : DyadicInterval) :
    variableAlphaSmallOldBoxAccepted N L r = true ↔
      (dyadicRouteBLargeSmallBound L r N).hi <
          bound4395Threshold.lo ∧
        DyadicRouteBLargeSmallFullAdmissible L r N := by
  simp [variableAlphaSmallOldBoxAccepted, Bool.and_eq_true]

noncomputable section

theorem lawNormalizedPrawitzFunctional_lt_879_2000_of_variable_old_box
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (haccepted : variableAlphaSmallOldBoxAccepted N L r = true) :
    lawNormalizedPrawitzFunctional n mu < (879 : ℝ) / 2000 := by
  let rho := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let eta := rho * (rR - 1)
  have hprop :=
    (variableAlphaSmallOldBoxAccepted_true_iff N L r).mp haccepted
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
      bound4395Threshold_contains.1

theorem lawNormalizedPrawitzFunctional_lt_879_2000_of_variable_hybrid_box
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (haccepted : variableAlphaSmallHybridBoxAccepted N L r = true) :
    lawNormalizedPrawitzFunctional n mu < (879 : ℝ) / 2000 := by
  by_cases hnew : (DyadicInterval.ofRat 19 10).hi ≤ r.lo
  · have hacc : bound4395VariableAlphaSmallBoxAccepted N L r = true := by
      simpa [variableAlphaSmallHybridBoxAccepted, hnew] using haccepted
    exact lawNormalizedPrawitzFunctional_lt_879_2000_of_variable_box
      mu hX hmean hsecond hn hN hL hr hacc
  · have hacc : variableAlphaSmallOldBoxAccepted N L r = true := by
      simpa [variableAlphaSmallHybridBoxAccepted, hnew] using haccepted
    exact lawNormalizedPrawitzFunctional_lt_879_2000_of_variable_old_box
      mu hX hmean hsecond hn hN hL hr hacc

theorem normalizedKolmogorovDistance_lt_879_2000_of_variable_hybrid_box
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
    (haccepted : variableAlphaSmallHybridBoxAccepted N L r = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  let mu := P.map (X 0)
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hKD := normalizedKolmogorovDistance_le_lawNormalizedPrawitzFunctional
    P X hindep hident hX hmean hsecond (n := n) (by omega)
  have hfunctional :=
    lawNormalizedPrawitzFunctional_lt_879_2000_of_variable_hybrid_box
      mu hX hmean hsecond hn hN
        (by simpa only [mu] using hL)
        (by simpa only [mu] using hr) haccepted
  exact hKD.trans_lt <| by simpa only [mu] using hfunctional

end

inductive VariableAlphaSmallResolution where
  | n256
  | n1024
  | n2048
  | n4096
  | n8192
deriving DecidableEq, Repr

def variableAlphaSmallAcceptedAt
    (resolution : VariableAlphaSmallResolution)
    (x z : DyadicInterval) : Bool :=
  let L := dyadicRouteBLargeSmallRegionL x
  let r := dyadicRouteBLargeSmallRegionR z
  match resolution with
  | .n256 => variableAlphaSmallHybridBoxAccepted 256 L r
  | .n1024 => variableAlphaSmallHybridBoxAccepted 1024 L r
  | .n2048 => variableAlphaSmallHybridBoxAccepted 2048 L r
  | .n4096 => variableAlphaSmallHybridBoxAccepted 4096 L r
  | .n8192 => variableAlphaSmallHybridBoxAccepted 8192 L r

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_variable_smallAcceptedAt
    {resolution : VariableAlphaSmallResolution}
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
    (haccepted : variableAlphaSmallAcceptedAt resolution x z = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
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
      exact normalizedKolmogorovDistance_lt_879_2000_of_variable_hybrid_box
        P X hindep hident hX hmean hsecond (n := n) (N := 256)
          hn (by norm_num) hLContains hrContains (by
            simpa [variableAlphaSmallAcceptedAt, L, r] using haccepted)
  | n1024 =>
      exact normalizedKolmogorovDistance_lt_879_2000_of_variable_hybrid_box
        P X hindep hident hX hmean hsecond (n := n) (N := 1024)
          hn (by norm_num) hLContains hrContains (by
            simpa [variableAlphaSmallAcceptedAt, L, r] using haccepted)
  | n2048 =>
      exact normalizedKolmogorovDistance_lt_879_2000_of_variable_hybrid_box
        P X hindep hident hX hmean hsecond (n := n) (N := 2048)
          hn (by norm_num) hLContains hrContains (by
            simpa [variableAlphaSmallAcceptedAt, L, r] using haccepted)
  | n4096 =>
      exact normalizedKolmogorovDistance_lt_879_2000_of_variable_hybrid_box
        P X hindep hident hX hmean hsecond (n := n) (N := 4096)
          hn (by norm_num) hLContains hrContains (by
            simpa [variableAlphaSmallAcceptedAt, L, r] using haccepted)
  | n8192 =>
      exact normalizedKolmogorovDistance_lt_879_2000_of_variable_hybrid_box
        P X hindep hident hX hmean hsecond (n := n) (N := 8192)
          hn (by norm_num) hLContains hrContains (by
            simpa [variableAlphaSmallAcceptedAt, L, r] using haccepted)

end


def variableAlphaSmallAdaptiveAccepted
    (x z : DyadicInterval) : Bool :=
  variableAlphaSmallAcceptedAt .n256 x z ||
    variableAlphaSmallAcceptedAt .n1024 x z ||
    variableAlphaSmallAcceptedAt .n2048 x z ||
    variableAlphaSmallAcceptedAt .n4096 x z ||
    variableAlphaSmallAcceptedAt .n8192 x z

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_variable_smallAdaptive
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
    (haccepted : variableAlphaSmallAdaptiveAccepted x z = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  by_cases h256 : variableAlphaSmallAcceptedAt .n256 x z = true
  · exact normalizedKolmogorovDistance_lt_879_2000_of_variable_smallAcceptedAt
      hx hz P X hindep hident hX hmean hsecond hn hL hr h256
  · by_cases h1024 : variableAlphaSmallAcceptedAt .n1024 x z = true
    · exact normalizedKolmogorovDistance_lt_879_2000_of_variable_smallAcceptedAt
        hx hz P X hindep hident hX hmean hsecond hn hL hr h1024
    · by_cases h2048 : variableAlphaSmallAcceptedAt .n2048 x z = true
      · exact normalizedKolmogorovDistance_lt_879_2000_of_variable_smallAcceptedAt
          hx hz P X hindep hident hX hmean hsecond hn hL hr h2048
      · by_cases h4096 : variableAlphaSmallAcceptedAt .n4096 x z = true
        · exact normalizedKolmogorovDistance_lt_879_2000_of_variable_smallAcceptedAt
            hx hz P X hindep hident hX hmean hsecond hn hL hr h4096
        · have h8192 :
              variableAlphaSmallAcceptedAt .n8192 x z = true := by
            simpa [variableAlphaSmallAdaptiveAccepted,
              h256, h1024, h2048, h4096] using haccepted
          exact normalizedKolmogorovDistance_lt_879_2000_of_variable_smallAcceptedAt
            hx hz P X hindep hident hX hmean hsecond hn hL hr h8192

end


def variableAlphaSmallCoverVerify :
    ℕ → DyadicInterval → DyadicInterval → Bool
  | 0, x, z => variableAlphaSmallAdaptiveAccepted x z
  | fuel + 1, x, z =>
      if variableAlphaSmallAdaptiveAccepted x z then true
      else if 10 * (z.hi - z.lo) ≤ 9 * (x.hi - x.lo) then
        variableAlphaSmallCoverVerify fuel
            (dyadicRouteBLeftHalf x) z &&
          variableAlphaSmallCoverVerify fuel
            (dyadicRouteBRightHalf x) z
      else
        variableAlphaSmallCoverVerify fuel
            x (dyadicRouteBLeftHalf z) &&
          variableAlphaSmallCoverVerify fuel
            x (dyadicRouteBRightHalf z)

noncomputable section

theorem variableAlphaSmallCoverVerify_sound
    {fuel : ℕ} {x z : DyadicInterval}
    (hverify : variableAlphaSmallCoverVerify fuel x z = true)
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
      (879 : ℝ) / 2000 := by
  induction fuel generalizing x z with
  | zero =>
      exact normalizedKolmogorovDistance_lt_879_2000_of_variable_smallAdaptive
        hx hz P X hindep hident hX hmean hsecond hn hL hr hverify
  | succ fuel ih =>
      by_cases hadaptive : variableAlphaSmallAdaptiveAccepted x z = true
      · exact normalizedKolmogorovDistance_lt_879_2000_of_variable_smallAdaptive
          hx hz P X hindep hident hX hmean hsecond hn hL hr hadaptive
      · by_cases hwidth : 10 * (z.hi - z.lo) ≤ 9 * (x.hi - x.lo)
        · have hchildren :
              variableAlphaSmallCoverVerify fuel
                  (dyadicRouteBLeftHalf x) z = true ∧
                variableAlphaSmallCoverVerify fuel
                  (dyadicRouteBRightHalf x) z = true := by
            simpa [variableAlphaSmallCoverVerify, hadaptive, hwidth,
              Bool.and_eq_true] using hverify
          rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
          · exact ih hchildren.1 hleft hz
          · exact ih hchildren.2 hright hz
        · have hchildren :
              variableAlphaSmallCoverVerify fuel
                  x (dyadicRouteBLeftHalf z) = true ∧
                variableAlphaSmallCoverVerify fuel
                  x (dyadicRouteBRightHalf z) = true := by
            simpa [variableAlphaSmallCoverVerify, hadaptive, hwidth,
              Bool.and_eq_true] using hverify
          rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
          · exact ih hchildren.1 hx hleft
          · exact ih hchildren.2 hx hright

end


def variableAlphaSmallVerifyLeafTreeWithRefinement
    (extraFuel : ℕ) :
    DyadicRouteBLargeLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf _, x, z => variableAlphaSmallCoverVerify extraFuel x z
  | .splitX left right, x, z =>
      variableAlphaSmallVerifyLeafTreeWithRefinement
          extraFuel left (dyadicRouteBLeftHalf x) z &&
        variableAlphaSmallVerifyLeafTreeWithRefinement
          extraFuel right (dyadicRouteBRightHalf x) z
  | .splitZ left right, x, z =>
      variableAlphaSmallVerifyLeafTreeWithRefinement
          extraFuel left x (dyadicRouteBLeftHalf z) &&
        variableAlphaSmallVerifyLeafTreeWithRefinement
          extraFuel right x (dyadicRouteBRightHalf z)

noncomputable section

theorem variableAlphaSmallVerifyLeafTreeWithRefinement_sound
    {extraFuel : ℕ} {tree : DyadicRouteBLargeLeafTree}
    {x z : DyadicInterval}
    (hverify : variableAlphaSmallVerifyLeafTreeWithRefinement
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
      (879 : ℝ) / 2000 := by
  induction tree generalizing x z with
  | leaf resolution =>
      exact variableAlphaSmallCoverVerify_sound
        hverify hx hz P X hindep hident hX hmean hsecond hn hL hr
  | splitX left right ihLeft ihRight =>
      have hchildren :
          variableAlphaSmallVerifyLeafTreeWithRefinement extraFuel
                left (dyadicRouteBLeftHalf x) z = true ∧
            variableAlphaSmallVerifyLeafTreeWithRefinement extraFuel
                right (dyadicRouteBRightHalf x) z = true := by
        simpa [variableAlphaSmallVerifyLeafTreeWithRefinement,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hx with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          variableAlphaSmallVerifyLeafTreeWithRefinement extraFuel
                left x (dyadicRouteBLeftHalf z) = true ∧
            variableAlphaSmallVerifyLeafTreeWithRefinement extraFuel
                right x (dyadicRouteBRightHalf z) = true := by
        simpa [variableAlphaSmallVerifyLeafTreeWithRefinement,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hx hleft
      · exact ihRight hchildren.2 hx hright

end


def variableAlphaSmallRefinedLeafCodeCertificateAt
    (extraFuel : ℕ) (code : String)
    (xRoot zRoot : DyadicInterval) : Bool :=
  match dyadicRouteBLargeLeafTreeOfCode code with
  | some tree => variableAlphaSmallVerifyLeafTreeWithRefinement
      extraFuel tree xRoot zRoot
  | none => false

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_variable_smallCodeAt
    {extraFuel : ℕ} {code : String} {xRoot zRoot : DyadicInterval}
    (hcertificate : variableAlphaSmallRefinedLeafCodeCertificateAt
      extraFuel code xRoot zRoot = true)
    {xR zR : ℝ} (hx : xRoot.Contains xR) (hz : zRoot.Contains zR)
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
      (879 : ℝ) / 2000 := by
  unfold variableAlphaSmallRefinedLeafCodeCertificateAt at hcertificate
  split at hcertificate
  next tree htree =>
    exact variableAlphaSmallVerifyLeafTreeWithRefinement_sound
      hcertificate hx hz P X hindep hident hX hmean hsecond hn hL hr
  next => simp at hcertificate

end

end BerryEsseen
