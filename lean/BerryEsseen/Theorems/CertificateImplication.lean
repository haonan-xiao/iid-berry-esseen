import BerryEsseen.StandardizedSumMoments
import BerryEsseen.Smoothing.UniversalSplit

/-!
# Theorems / Certificate Implication
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory

noncomputable section

theorem iidBerryEsseen879_2000_of_numericalBranch
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    (hNumerical : ∀ {n : ℕ}, 1 ≤ n →
      thirdAbsoluteMoment (P.map (X 0)) ≤
        ((56 : ℝ) / 45) * Real.sqrt (n : ℝ) →
      Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
          kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
        bound4395TargetConstant) :
    IIDBerryEsseen879_2000Conclusion P X
      (thirdAbsoluteMoment (P.map (X 0))) := by
  intro n hn
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
  have hnPos : 0 < n := Nat.zero_lt_of_lt hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hrho : 1 ≤ rho := by
    dsimp only [rho, mu]
    exact thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hX0 : MemLp (X 0) 3 P := by
    have hmap := (memLp_map_measure_iff aestronglyMeasurable_id
      (hident 0).aemeasurable_fst).1 hX
    simpa only [Function.comp_apply, id_eq] using hmap
  have hsourceMean : ∫ omega, X 0 omega ∂P = 0 := by
    rw [← hmean]
    change (∫ omega, X 0 omega ∂P) =
      ∫ x : ℝ, (id : ℝ → ℝ) x ∂P.map (X 0)
    rw [integral_map (hident 0).aemeasurable_fst
      aestronglyMeasurable_id]
    rfl
  have hsourceSecond : ∫ omega, (X 0 omega) ^ 2 ∂P = 1 := by
    rw [← hsecond]
    change (∫ omega, (X 0 omega) ^ 2 ∂P) =
      ∫ x : ℝ, (fun y : ℝ => y ^ 2) x ∂P.map (X 0)
    rw [integral_map (hident 0).aemeasurable_fst (by fun_prop)]
  have hsumMem : MemLp (id : ℝ → ℝ) 2
      (standardizedSumLaw P X n) :=
    memLp_two_id_standardizedSumLaw P X hident hX0 n
  have hsumMean : ∫ x : ℝ, x ∂(standardizedSumLaw P X n) = 0 :=
    integral_id_standardizedSumLaw_eq_zero P X hident hX0 hsourceMean n
  have hsumVar : Var[(id : ℝ → ℝ); standardizedSumLaw P X n] = 1 :=
    variance_id_standardizedSumLaw_eq_one P X hindep hident hX0
      hsourceMean hsourceSecond hn
  unfold HasBerryEsseenBound normalizedRate
  by_cases hcut :
      bound4395UniversalCutoff ≤ rho / Real.sqrt (n : ℝ)
  · have huniversal := bound4395_universal_branch
      (standardizedSumLaw P X n) hsumMem hsumMean hsumVar
        hsqrt hcut
    simpa only [rho, mu] using huniversal
  · have hrhoUpper :
        rho ≤ ((56 : ℝ) / 45) * Real.sqrt (n : ℝ) :=
      (bound4395_complement_inside_routeB hsqrt hcut).le
    have hnormalized := hNumerical hn
      (by simpa only [rho, mu] using hrhoUpper)
    have hfactor : 0 < Real.sqrt (n : ℝ) / rho :=
      div_pos hsqrt hrhoPos
    have hdiv :
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
          bound4395TargetConstant /
            (Real.sqrt (n : ℝ) / rho) :=
      (lt_div_iff₀' hfactor).2 (by
        simpa only [rho, mu] using hnormalized)
    have heq :
        bound4395TargetConstant / (Real.sqrt (n : ℝ) / rho) =
          bound4395TargetConstant * rho / Real.sqrt (n : ℝ) := by
      field_simp
    rw [heq] at hdiv
    exact hdiv.le

end

end BerryEsseen
