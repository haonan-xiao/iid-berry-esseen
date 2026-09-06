import BerryEsseen.Interval.Small.IntegralSoundness
import BerryEsseen.Smoothing.VariableExponentBoundary

/-!
# Smoothing / Variable Exponent Boundary Soundness
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

noncomputable section

theorem bound4395VariableAlphaSmallBoxAccepted_true_iff
    (N : ℕ) (L r : DyadicInterval) :
    bound4395VariableAlphaSmallBoxAccepted N L r = true ↔
      (certifiedLargeSmallVariableAlphaBound L r N).hi <
          bound4395Threshold.lo ∧
        CertifiedLargeSmallVariableAlphaFullAdmissible L r N := by
  simp [bound4395VariableAlphaSmallBoxAccepted, Bool.and_eq_true]

theorem lawNormalizedPrawitzFunctional_lt_879_2000_of_variable_box
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (haccepted :
      bound4395VariableAlphaSmallBoxAccepted N L r = true) :
    lawNormalizedPrawitzFunctional n mu < (879 : ℝ) / 2000 := by
  have hprop :=
    (bound4395VariableAlphaSmallBoxAccepted_true_iff N L r).mp haccepted
  have hreal :=
    lawNormalizedPrawitzFunctional_le_variable_smallBound_upper
      mu hX hmean hsecond hn hN hL hr hprop.2.1
        (fun i hi => hprop.2.2 ⟨i, hi⟩)
  exact hreal.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo hprop.1).trans_le
      bound4395Threshold_contains.1

theorem normalizedKolmogorovDistance_lt_879_2000_of_variable_box
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
    (haccepted :
      bound4395VariableAlphaSmallBoxAccepted N L r = true) :
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
    lawNormalizedPrawitzFunctional_lt_879_2000_of_variable_box
      mu hX hmean hsecond hn hN
        (by simpa only [mu] using hL)
        (by simpa only [mu] using hr) haccepted
  exact hKD.trans_lt <| by simpa only [mu] using hfunctional

end

end BerryEsseen
