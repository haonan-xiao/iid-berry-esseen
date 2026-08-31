import BerryEsseen.Probability.Analytic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The universal `0.56` branch

This module formalizes the distribution-free branch of Route B.  Its only probabilistic input is
the one-sided Chebyshev--Cantelli estimate for a centered variance-one law.  The standard-normal
comparison then uses the exact density bound already proved in `Analytic.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace BerryEsseen

noncomputable section

open StatLean.HypothesisTesting

/-- The standard normal CDF is Lipschitz with the supremum of its density.  This local proof keeps
the universal branch independent of StatLean's much larger Edgeworth module. -/
theorem standardNormalCDF_sub_le {a b : ℝ} (hab : a ≤ b) :
    lawCDF standardNormalLaw b - lawCDF standardNormalLaw a ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * (b - a) := by
  have hdisj : standardNormalLaw (Set.Iic b) =
      standardNormalLaw (Set.Iic a) + standardNormalLaw (Set.Ioc a b) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hab]
  have hnn : 0 ≤ ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x :=
    integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x
  have hstep : lawCDF standardNormalLaw b - lawCDF standardNormalLaw a =
      ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x := by
    unfold lawCDF
    calc
      (standardNormalLaw (Set.Iic b)).toReal - (standardNormalLaw (Set.Iic a)).toReal
          = (standardNormalLaw (Set.Ioc a b)).toReal := by
            rw [hdisj, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
            ring
      _ = ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x := by
        unfold standardNormalLaw
        rw [gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Ioc a b),
          ENNReal.toReal_ofReal hnn]
  have hbound : ∀ x : ℝ, gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro x
    have hexp : Real.exp (-(x : ℝ) ^ 2 / 2) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : 0 ≤ x ^ 2 / 2 := by positivity
      linarith
    calc
      gaussianPDFReal 0 1 x
          = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
            rw [gaussianPDFReal]
            norm_num
      _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (Real.sqrt (2 * Real.pi))⁻¹ := mul_one _
  rw [hstep]
  calc
    (∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x)
        ≤ ∫ _x in Set.Ioc a b, (Real.sqrt (2 * Real.pi))⁻¹ :=
          setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
            (continuous_const.integrableOn_Ioc) measurableSet_Ioc fun x _ => hbound x
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (b - a) := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_comm]

/-- Symmetry and atomlessness give `Phi(0) = 1/2` for the standard normal law. -/
theorem standardNormalCDF_zero : lawCDF standardNormalLaw 0 = (1 / 2 : ℝ) := by
  let nu : Measure ℝ := standardNormalLaw
  haveI : IsProbabilityMeasure nu := inferInstance
  haveI : NoAtoms nu := by
    dsimp [nu, standardNormalLaw]
    exact noAtoms_gaussianReal one_ne_zero
  have hneg : nu.map (fun x : ℝ => -x) = nu := by
    dsimp [nu, standardNormalLaw]
    simpa using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
  have htail : nu (Set.Ioi 0) = nu (Set.Iio 0) := by
    calc
      nu (Set.Ioi 0) = (nu.map (fun x : ℝ => -x)) (Set.Ioi 0) := by rw [hneg]
      _ = nu ((fun x : ℝ => -x) ⁻¹' Set.Ioi 0) :=
        Measure.map_apply measurable_neg measurableSet_Ioi
      _ = nu (Set.Iio 0) := by
        congr 1
        ext x
        simp
  have hclosed : nu (Set.Iio 0) = nu (Set.Iic 0) := by
    rw [← Set.Iio_union_right]
    rw [measure_union]
    · simp
    · exact Set.disjoint_left.2 (by
        rintro x hx rfl
        exact (lt_irrefl (0 : ℝ)) (by simpa only [Set.mem_Iio] using hx))
    · exact measurableSet_singleton 0
  have hcompl := measureReal_add_measureReal_compl (μ := nu) (s := Set.Iic 0) measurableSet_Iic
  have hreal : nu.real (Set.Ioi 0) = nu.real (Set.Iic 0) := by
    change (nu (Set.Ioi 0)).toReal = (nu (Set.Iic 0)).toReal
    rw [htail, hclosed]
  rw [lawCDF, ← measureReal_def]
  change nu.real (Set.Iic 0) = 1 / 2
  rw [Set.compl_Iic, hreal] at hcompl
  rw [probReal_univ] at hcompl
  linarith

/-- One-sided Chebyshev--Cantelli inequality for a centered variance-one random variable. -/
theorem probReal_ge_le_cantelli
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    {X : Omega → ℝ} (hX : MemLp X 2 P)
    (hmean : ∫ omega, X omega ∂P = 0)
    (hvariance : Var[X; P] = 1)
    {a : ℝ} (ha : 0 < a) :
    P.real {omega | a ≤ X omega} ≤ 1 / (1 + a ^ 2) := by
  let t : ℝ := 1 / a
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hshift : MemLp (fun omega => X omega + t) 2 P := by
    simpa only [Pi.add_apply] using hX.add (memLp_const t)
  have hshiftMean : ∫ omega, X omega + t ∂P = t := by
    change ∫ omega, (X omega + (fun _ : Omega => t) omega) ∂P = t
    rw [integral_add (hX.integrable one_le_two) (integrable_const t), integral_const,
      probReal_univ]
    simp only [one_smul]
    rw [hmean]
    simp
  have hshiftVariance : Var[(fun omega => X omega + t); P] = 1 := by
    calc
      Var[(fun omega => X omega + t); P] = Var[X; P] := by
        simpa only using variance_add_const hX.1 t
      _ = 1 := hvariance
  have hshiftSecond : ∫ omega, (X omega + t) ^ 2 ∂P = 1 + t ^ 2 := by
    have hvarIdentity := variance_eq_sub hshift
    rw [hshiftVariance, hshiftMean] at hvarIdentity
    have hvarIdentity' : 1 = (∫ omega, (X omega + t) ^ 2 ∂P) - t ^ 2 := by
      simpa only [Pi.pow_apply] using hvarIdentity
    linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (ae_of_all P fun omega => sq_nonneg (X omega + t)) hshift.integrable_sq
    ((a + t) ^ 2)
  have hsubset : {omega | a ≤ X omega} ⊆
      {omega | (a + t) ^ 2 ≤ (X omega + t) ^ 2} := by
    intro omega homega
    change a ≤ X omega at homega
    have hat : 0 ≤ a + t := (add_pos ha ht).le
    have hxt : a + t ≤ X omega + t := by linarith [homega]
    have hXnonneg : 0 ≤ X omega + t := hat.trans hxt
    exact (sq_le_sq₀ hat hXnonneg).2 hxt
  have hmono : P.real {omega | a ≤ X omega} ≤
      P.real {omega | (a + t) ^ 2 ≤ (X omega + t) ^ 2} :=
    measureReal_mono hsubset
  have hproduct : (a + t) ^ 2 * P.real {omega | a ≤ X omega} ≤ 1 + t ^ 2 := by
    calc
      (a + t) ^ 2 * P.real {omega | a ≤ X omega}
          ≤ (a + t) ^ 2 * P.real {omega | (a + t) ^ 2 ≤ (X omega + t) ^ 2} :=
            mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
      _ ≤ ∫ omega, (X omega + t) ^ 2 ∂P := hmarkov
      _ = 1 + t ^ 2 := hshiftSecond
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hden : 0 < 1 + a ^ 2 := by positivity
  have hproduct' : ((1 + a ^ 2) ^ 2 * P.real {omega | a ≤ X omega}) / a ^ 2 ≤
      (1 + a ^ 2) / a ^ 2 := by
    dsimp [t] at hproduct
    convert hproduct using 1 <;> field_simp <;> ring
  have hcancelSquare : (1 + a ^ 2) ^ 2 * P.real {omega | a ≤ X omega} ≤
      1 + a ^ 2 := by
    exact (div_le_div_iff_of_pos_right ha2).1 hproduct'
  have hcancel : (1 + a ^ 2) * P.real {omega | a ≤ X omega} ≤ 1 := by
    apply le_of_mul_le_mul_left
    · calc
      (1 + a ^ 2) * ((1 + a ^ 2) * P.real {omega | a ≤ X omega})
          = (1 + a ^ 2) ^ 2 * P.real {omega | a ≤ X omega} := by ring
      _ ≤ 1 + a ^ 2 := hcancelSquare
      _ = (1 + a ^ 2) * 1 := by ring
    · exact hden
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hcancel)

/-- Law-level upper-tail form of Chebyshev--Cantelli. -/
theorem measureReal_Ici_le_cantelli
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 2 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hvariance : Var[(id : ℝ → ℝ); mu] = 1)
    {a : ℝ} (ha : 0 < a) :
    mu.real (Set.Ici a) ≤ 1 / (1 + a ^ 2) := by
  simpa only [id_eq, Set.setOf_mem_eq] using
    probReal_ge_le_cantelli mu hX hmean hvariance ha

/-- Law-level lower-tail form of Chebyshev--Cantelli. -/
theorem measureReal_Iic_neg_le_cantelli
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 2 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hvariance : Var[(id : ℝ → ℝ); mu] = 1)
    {a : ℝ} (ha : 0 < a) :
    mu.real (Set.Iic (-a)) ≤ 1 / (1 + a ^ 2) := by
  have hnegMem : MemLp (fun x : ℝ => -x) 2 mu := by
    simpa only [Pi.neg_apply, id_eq] using hX.neg
  have hnegMean : ∫ x : ℝ, -x ∂mu = 0 := by
    calc
      (∫ x : ℝ, -x ∂mu) = -(∫ x : ℝ, x ∂mu) := by rw [integral_neg]
      _ = 0 := by rw [hmean, neg_zero]
  have hnegVariance : Var[(fun x : ℝ => -x); mu] = 1 := by
    calc
      Var[(fun x : ℝ => -x); mu] = Var[(id : ℝ → ℝ); mu] := by
        simpa only [Pi.neg_apply, id_eq] using variance_neg (X := (id : ℝ → ℝ)) (μ := mu)
      _ = 1 := hvariance
  have htail := probReal_ge_le_cantelli mu hnegMem hnegMean hnegVariance ha
  have hset : {x : ℝ | a ≤ -x} = Set.Iic (-a) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    constructor <;> intro hx <;> linarith
  rw [hset] at htail
  exact htail

theorem lawCDF_nonneg (mu : Measure ℝ) (x : ℝ) : 0 ≤ lawCDF mu x := by
  exact ENNReal.toReal_nonneg

theorem lawCDF_le_one (mu : Measure ℝ) [IsProbabilityMeasure mu] (x : ℝ) :
    lawCDF mu x ≤ 1 := by
  exact measureReal_le_one

theorem lawCDF_add_upperTail (mu : Measure ℝ) [IsProbabilityMeasure mu] (x : ℝ) :
    lawCDF mu x + mu.real (Set.Ioi x) = 1 := by
  have h := measureReal_add_measureReal_compl (μ := mu) (s := Set.Iic x) measurableSet_Iic
  simpa only [lawCDF, Set.compl_Iic, probReal_univ] using h

/-- The normal upper tail stays above its linear density envelope on the positive half-line. -/
theorem standardNormalUpperTail_linear_lower {a : ℝ} (ha : 0 ≤ a) :
    1 / 2 - 2 * a / 5 ≤ 1 - lawCDF standardNormalLaw a := by
  have hLip := standardNormalCDF_sub_le ha
  rw [standardNormalCDF_zero] at hLip
  have hconst : (Real.sqrt (2 * Real.pi))⁻¹ * a ≤ 2 / 5 * a :=
    mul_le_mul_of_nonneg_right inv_sqrt_two_pi_lt_two_fifths.le ha
  linarith

/-- The same linear envelope bounds the standard normal CDF on the negative half-line. -/
theorem standardNormalCDF_neg_linear_lower {a : ℝ} (ha : 0 ≤ a) :
    1 / 2 - 2 * a / 5 ≤ lawCDF standardNormalLaw (-a) := by
  have horder : -a ≤ 0 := by linarith
  have hLip := standardNormalCDF_sub_le horder
  rw [standardNormalCDF_zero] at hLip
  have hconst : (Real.sqrt (2 * Real.pi))⁻¹ * a ≤ 2 / 5 * a :=
    mul_le_mul_of_nonneg_right inv_sqrt_two_pi_lt_two_fifths.le ha
  linarith

theorem one_div_one_add_sq_le_half {a : ℝ} (ha : 1 ≤ a) :
    1 / (1 + a ^ 2) ≤ 1 / 2 := by
  have hden : 0 < 1 + a ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg (a - 1)]

/-- Every centered variance-one law is within `14/25` of the standard normal law in Kolmogorov
distance.  This is the universal branch used when `rho / sqrt n >= 56/45`. -/
theorem universal_kolmogorov_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 2 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hvariance : Var[(id : ℝ → ℝ); mu] = 1) :
    kolmogorovDistance mu standardNormalLaw ≤ universalConstant := by
  apply (kolmogorovDistance_le_iff_pointwise mu standardNormalLaw universalConstant).2
  intro x
  have hhalf : (1 / 2 : ℝ) ≤ universalConstant := by
    norm_num [universalConstant]
  have hFnonneg := lawCDF_nonneg mu x
  have hFle := lawCDF_le_one mu x
  have hPhiNonneg := lawCDF_nonneg standardNormalLaw x
  have hPhiLe := lawCDF_le_one standardNormalLaw x
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · have hPhiHalf : lawCDF standardNormalLaw x ≤ 1 / 2 := by
      have hmono := isCDF_standardNormalLaw.mono hxneg.le
      rw [standardNormalCDF_zero] at hmono
      exact hmono
    have hleft : -universalConstant ≤
        lawCDF mu x - lawCDF standardNormalLaw x := by
      linarith
    let a : ℝ := -x
    have ha : 0 < a := by dsimp [a]; linarith
    have htail := measureReal_Iic_neg_le_cantelli mu hX hmean hvariance ha
    have hFtail : lawCDF mu x ≤ 1 / (1 + a ^ 2) := by
      dsimp [a] at htail ⊢
      simpa only [neg_neg, lawCDF, measureReal_def] using htail
    have hright : lawCDF mu x - lawCDF standardNormalLaw x ≤ universalConstant := by
      by_cases haone : a ≤ 1
      · have hnormal := standardNormalCDF_neg_linear_lower ha.le
        have hnormalX : 1 / 2 - 2 * a / 5 ≤ lawCDF standardNormalLaw x := by
          simpa only [a, neg_neg] using hnormal
        have henv := universalRationalEnvelope_le ha.le haone
        linarith
      · have haone' : 1 ≤ a := le_of_lt (lt_of_not_ge haone)
        have htailHalf := one_div_one_add_sq_le_half haone'
        linarith
    exact (abs_le).2 ⟨hleft, hright⟩
  · subst x
    rw [standardNormalCDF_zero]
    exact (abs_le).2 (by constructor <;> linarith)
  · have hPhiHalf : 1 / 2 ≤ lawCDF standardNormalLaw x := by
      have hmono := isCDF_standardNormalLaw.mono hxpos.le
      rw [standardNormalCDF_zero] at hmono
      exact hmono
    have hright : lawCDF mu x - lawCDF standardNormalLaw x ≤ universalConstant := by
      linarith
    have hmuComplement := lawCDF_add_upperTail mu x
    have htailOpen : mu.real (Set.Ioi x) ≤ 1 / (1 + x ^ 2) := by
      calc
        mu.real (Set.Ioi x) ≤ mu.real (Set.Ici x) :=
          measureReal_mono Set.Ioi_subset_Ici_self
        _ ≤ 1 / (1 + x ^ 2) :=
          measureReal_Ici_le_cantelli mu hX hmean hvariance hxpos
    have hleft : -universalConstant ≤
        lawCDF mu x - lawCDF standardNormalLaw x := by
      by_cases hxone : x ≤ 1
      · have hnormal := standardNormalUpperTail_linear_lower hxpos.le
        have henv := universalRationalEnvelope_le hxpos.le hxone
        linarith
      · have hxone' : 1 ≤ x := le_of_lt (lt_of_not_ge hxone)
        have htailHalf := one_div_one_add_sq_le_half hxone'
        have hnormalTail : 0 ≤ 1 - lawCDF standardNormalLaw x := by linarith
        linarith
    exact (abs_le).2 ⟨hleft, hright⟩

end

end BerryEsseen
