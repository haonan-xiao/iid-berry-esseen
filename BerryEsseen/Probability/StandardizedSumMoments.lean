import BerryEsseen.Assembly
import BerryEsseen.Smoothing.ExplicitSmoothing
/-!
# Mean and variance of the standardized i.i.d. sum

These lemmas discharge the moment hypotheses of the distribution-free branch
for the law of the normalized sum.  They are stated for the same i.i.d.
interface used by the Route B characteristic-function reduction.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace BerryEsseen

noncomputable section

theorem memLp_two_standardizedSum
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX0 : MemLp (X 0) 3 P) (n : ℕ) :
    MemLp (standardizedSum X n) 2 P := by
  have hX2 : ∀ k, MemLp (X k) 2 P := fun k =>
    ((hident k).symm.memLp_snd hX0).mono_exponent (by norm_num)
  have hsum : MemLp (fun omega => ∑ k ∈ Finset.range n, X k omega) 2 P :=
    memLp_finset_sum _ fun k _ => hX2 k
  simpa only [standardizedSum] using
    hsum.const_mul (Real.sqrt (n : ℝ))⁻¹

theorem memLp_two_id_standardizedSumLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX0 : MemLp (X 0) 3 P) (n : ℕ) :
    MemLp (id : ℝ → ℝ) 2 (standardizedSumLaw P X n) := by
  have hXae : ∀ k, AEMeasurable (X k) P :=
    fun k => (hident k).aemeasurable_fst
  unfold standardizedSumLaw
  rw [memLp_map_measure_iff aestronglyMeasurable_id
    (aemeasurable_standardizedSum hXae n)]
  simpa only [Function.comp_apply, id_eq] using
    memLp_two_standardizedSum P X hident hX0 n

theorem integral_standardizedSum_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX0 : MemLp (X 0) 3 P)
    (hmean : ∫ x, X 0 x ∂P = 0) (n : ℕ) :
    ∫ omega, standardizedSum X n omega ∂P = 0 := by
  have hX2 : ∀ k, MemLp (X k) 2 P := fun k =>
    ((hident k).symm.memLp_snd hX0).mono_exponent (by norm_num)
  unfold standardizedSum
  rw [integral_const_mul, integral_finset_sum]
  · simp_rw [(hident _).integral_eq, hmean]
    simp
  · exact fun k _ => (hX2 k).integrable (by norm_num)

theorem integral_id_standardizedSumLaw_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX0 : MemLp (X 0) 3 P)
    (hmean : ∫ x, X 0 x ∂P = 0) (n : ℕ) :
    ∫ x : ℝ, x ∂(standardizedSumLaw P X n) = 0 := by
  have hXae : ∀ k, AEMeasurable (X k) P :=
    fun k => (hident k).aemeasurable_fst
  unfold standardizedSumLaw
  change ∫ x : ℝ, (id : ℝ → ℝ) x ∂Measure.map (standardizedSum X n) P = 0
  rw [integral_map (aemeasurable_standardizedSum hXae n)
    aestronglyMeasurable_id]
  simpa only [Function.comp_apply, id_eq] using
    integral_standardizedSum_eq_zero P X hident hX0 hmean n

theorem variance_standardizedSum_eq_one
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX0 : MemLp (X 0) 3 P)
    (hmean : ∫ x, X 0 x ∂P = 0)
    (hsecond : ∫ x, (X 0 x) ^ 2 ∂P = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    Var[standardizedSum X n; P] = 1 := by
  have hX2 : ∀ k, MemLp (X k) 2 P := fun k =>
    ((hident k).symm.memLp_snd hX0).mono_exponent (by norm_num)
  have hvar0 : Var[X 0; P] = 1 := by
    rw [variance_eq_sub (hX2 0)]
    simp only [Pi.pow_apply, hmean, hsecond]
    norm_num
  have hpairwise : ((↑(Finset.range n) : Set ℕ).Pairwise
      fun i j => X i ⟂ᵢ[P] X j) := by
    intro i _hi j _hj hij
    exact hindep.indepFun hij
  have hsumVar := IndepFun.variance_sum
    (s := Finset.range n) (fun k _ => hX2 k) hpairwise
  have hsumVarOne : Var[(fun omega => ∑ k ∈ Finset.range n, X k omega); P] =
      (n : ℝ) := by
    have hfun : (fun omega => ∑ k ∈ Finset.range n, X k omega) =
        ∑ k ∈ Finset.range n, X k := by
      funext omega
      simp
    rw [hfun]
    rw [hsumVar]
    simp_rw [(hident _).variance_eq, hvar0]
    simp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  unfold standardizedSum
  rw [variance_const_mul, hsumVarOne]
  have hsquare : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnR.le
  field_simp
  exact hsquare.symm

theorem variance_id_standardizedSumLaw_eq_one
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX0 : MemLp (X 0) 3 P)
    (hmean : ∫ x, X 0 x ∂P = 0)
    (hsecond : ∫ x, (X 0 x) ^ 2 ∂P = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    Var[(id : ℝ → ℝ); standardizedSumLaw P X n] = 1 := by
  have hXae : ∀ k, AEMeasurable (X k) P :=
    fun k => (hident k).aemeasurable_fst
  unfold standardizedSumLaw
  rw [variance_map aemeasurable_id
    (aemeasurable_standardizedSum hXae n)]
  simpa only [Function.comp_apply, id_eq] using
    variance_standardizedSum_eq_one P X hindep hident hX0 hmean hsecond hn

/-- The analytic and probabilistic assembly once the scalar Route B numerical
bound has been certified. -/
theorem iidBerryEsseen45_of_certifiedNumericalBound
    (hNumerical : CertifiedNumericalBound
      (routeBU routeBKappa routeBTheta))
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1) :
    IIDBerryEsseen45Conclusion P X (thirdAbsoluteMoment (P.map (X 0))) := by
  intro n hn
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
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
  have hrho : 1 ≤ rho := by
    dsimp only [rho, mu]
    exact thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond
  have hrLower : 1 ≤ r := by
    dsimp only [r, mu]
    exact symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond
  have hrUpper : r ≤ 1 + 1 / rho := by
    dsimp only [r, rho, mu]
    exact symmetrizationRatio_upper (P.map (X 0)) hX hmean hsecond
  have hsumMem : MemLp (id : ℝ → ℝ) 2
      (standardizedSumLaw P X n) :=
    memLp_two_id_standardizedSumLaw P X hident hX0 n
  have hsumMean : ∫ x : ℝ, x ∂(standardizedSumLaw P X n) = 0 :=
    integral_id_standardizedSumLaw_eq_zero P X hident hX0
      hsourceMean n
  have hsumVar : Var[(id : ℝ → ℝ); standardizedSumLaw P X n] = 1 :=
    variance_id_standardizedSumLaw_eq_one P X hindep hident hX0
      hsourceMean hsourceSecond hn
  apply conditional_target_of_numerical_bound
    (standardizedSumLaw P X n) (routeBU routeBKappa routeBTheta)
      hn hrho hrLower hrUpper hNumerical
  · exact universal_kolmogorov_bound
      (standardizedSumLaw P X n) hsumMem hsumMean hsumVar
  · intro _hsmall
    simpa only [rho, r, mu] using
      kolmogorovDistance_standardizedSum_le_exactRouteBU
        P X hindep hident hX hmean hsecond hn

end

end BerryEsseen
