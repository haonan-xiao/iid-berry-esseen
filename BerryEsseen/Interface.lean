import BerryEsseen.CharacteristicFunction.Constants
import Mathlib.Probability.CentralLimitTheorem
import StatLean.HypothesisTesting.Bootstrap.Consistency
import StatLean.HypothesisTesting.ForMathlib.BerryEsseen
import StatLean.HypothesisTesting.ForMathlib.EsseenSmoothing

/-!
# Source-faithful probability interface

The final theorem will quantify over a measurable i.i.d. family on an arbitrary probability
space.  This module fixes the normalized sum, its law, the third absolute moment, and the
Kolmogorov distance used in the statement.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace BerryEsseen

noncomputable section

open StatLean.HypothesisTesting

/-- The distribution function of a probability law, written in the form consumed by StatLean's
CDF-level smoothing theorem. -/
def lawCDF (mu : Measure ℝ) (x : ℝ) : ℝ :=
  (mu (Set.Iic x)).toReal

/-- Kolmogorov distance between two probability laws on the real line. -/
def kolmogorovDistance (mu nu : Measure ℝ) : ℝ :=
  supCDFDist (lawCDF mu) (lawCDF nu)

/-- The standard normal law. -/
def standardNormalLaw : Measure ℝ :=
  gaussianReal 0 1

instance instIsProbabilityMeasureStandardNormalLaw : IsProbabilityMeasure standardNormalLaw := by
  unfold standardNormalLaw
  infer_instance

/-- The normalized sum `n^(-1/2) * sum_{k < n} X_k`. -/
def standardizedSum {Omega : Type*} (X : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, X k omega

/-- The law of the normalized sum.  Measurability is an explicit theorem hypothesis at uses of
this definition, so `Measure.map` never supplies an unstated regularity assumption. -/
def standardizedSumLaw {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : ℕ → Omega → ℝ) (n : ℕ) : Measure ℝ :=
  P.map (standardizedSum X n)

/-- The absolute third moment of a real probability law. -/
def thirdAbsoluteMoment (mu : Measure ℝ) : ℝ :=
  ∫ x, |x| ^ 3 ∂mu

/-- The rate `C * rho / sqrt n`, with the source proof's normalization. -/
def normalizedRate (C rho : ℝ) (n : ℕ) : ℝ :=
  C * rho / Real.sqrt (n : ℝ)

/-- A Berry--Esseen conclusion for a specified law, moment parameter, sample size, and constant. -/
def HasBerryEsseenBound (mu : Measure ℝ) (rho : ℝ) (n : ℕ) (C : ℝ) : Prop :=
  kolmogorovDistance mu standardNormalLaw ≤ normalizedRate C rho n

/-- The exact `0.45` conclusion for the normalized i.i.d. sum.  Assumptions on the family are
kept at theorem level rather than hidden inside this definition. -/
def IIDBerryEsseen45Conclusion {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : ℕ → Omega → ℝ) (rho : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → HasBerryEsseenBound (standardizedSumLaw P X n) rho n targetConstant

theorem isCDF_lawCDF (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    IsCDF (lawCDF mu) := by
  simpa only [lawCDF] using isCDF_toReal_measure_Iic mu

theorem isCDF_standardNormalLaw : IsCDF (lawCDF standardNormalLaw) := by
  exact isCDF_lawCDF standardNormalLaw

/-- The supremum statement is equivalent to its pointwise CDF form for probability laws. -/
theorem kolmogorovDistance_le_iff_pointwise
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (C : ℝ) :
    kolmogorovDistance mu nu ≤ C ↔
      ∀ x : ℝ, |lawCDF mu x - lawCDF nu x| ≤ C := by
  constructor
  · intro h x
    exact (le_ciSup (bddAbove_absSub (isCDF_lawCDF mu) (isCDF_lawCDF nu)) x).trans h
  · intro h
    exact ciSup_le h

theorem measurable_standardizedSum {Omega : Type*} [MeasurableSpace Omega]
    {X : ℕ → Omega → ℝ} (hX : ∀ k, Measurable (X k)) (n : ℕ) :
    Measurable (standardizedSum X n) := by
  unfold standardizedSum
  fun_prop

theorem aemeasurable_standardizedSum {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {X : ℕ → Omega → ℝ}
    (hX : ∀ k, AEMeasurable (X k) P) (n : ℕ) :
    AEMeasurable (standardizedSum X n) P := by
  unfold standardizedSum
  exact (Finset.aemeasurable_fun_sum _ fun k _ => hX k).const_mul _

theorem isProbabilityMeasure_standardizedSumLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ) (hX : ∀ k, AEMeasurable (X k) P) (n : ℕ) :
    IsProbabilityMeasure (standardizedSumLaw P X n) := by
  unfold standardizedSumLaw
  exact Measure.isProbabilityMeasure_map (aemeasurable_standardizedSum hX n)

/-- Independence and identical distribution turn the normalized-sum
characteristic function into the `n`-th power used by Route B. -/
theorem charFun_standardizedSumLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (n : ℕ) (t : ℝ) :
    charFun (standardizedSumLaw P X n) t =
      charFun (P.map (X 0)) ((Real.sqrt (n : ℝ))⁻¹ * t) ^ n := by
  simpa only [standardizedSumLaw, standardizedSum] using
    (ProbabilityTheory.charFun_inv_sqrt_mul_sum hindep hident (n := n) (t := t))

theorem integrable_id_standardizedSumLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX0 : MemLp (X 0) 3 P) (n : ℕ) :
    Integrable (id : ℝ → ℝ) (standardizedSumLaw P X n) := by
  have hX : ∀ k, AEMeasurable (X k) P := fun k => (hident k).aemeasurable_fst
  have hsum : Integrable (fun omega => ∑ k ∈ Finset.range n, X k omega) P :=
    integrable_finset_sum _ fun k _ =>
      ((hident k).symm.memLp_snd hX0).integrable (by norm_num)
  unfold standardizedSumLaw
  rw [integrable_map_measure (by fun_prop)
    (aemeasurable_standardizedSum hX n)]
  simpa only [Function.comp_apply, id_eq, standardizedSum] using
    hsum.const_mul (Real.sqrt (n : ℝ))⁻¹

end

end BerryEsseen
