import BerryEsseen.DyadicPrawitzFiniteCache
import Mathlib.Analysis.Calculus.Taylor

namespace BerryEsseen

open Finset Set

noncomputable section

def cosPolynomialReal (x : ℝ) : ℝ :=
  ∑ k ∈ range 17, (-1 : ℝ) ^ k * x ^ (2 * k) / (2 * k).factorial

def sinPolynomialReal (x : ℝ) : ℝ :=
  ∑ k ∈ range 17, (-1 : ℝ) ^ k * x ^ (2 * k + 1) /
    (2 * k + 1).factorial

lemma taylorWithinEval_cos_32_eq
    {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.cos 32 (Icc 0 x) 0 x =
      cosPolynomialReal x := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) x := ⟨le_rfl, hx.le⟩
  rw [taylor_within_apply]
  simp_rw [Real.iteratedDerivWithin_cos_Icc _ hx hzero]
  norm_num [cosPolynomialReal, Finset.sum_range_succ,
    Real.iteratedDeriv_add_one_cos, Real.iteratedDeriv_add_one_sin]
  ring

lemma taylorWithinEval_sin_33_eq
    {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.sin 33 (Icc 0 x) 0 x =
      sinPolynomialReal x := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) x := ⟨le_rfl, hx.le⟩
  rw [taylor_within_apply]
  simp_rw [Real.iteratedDerivWithin_sin_Icc _ hx hzero]
  norm_num [sinPolynomialReal, Finset.sum_range_succ,
    Real.iteratedDeriv_add_one_cos, Real.iteratedDeriv_add_one_sin]
  ring

lemma cos_taylor_remainder_32
    {x : ℝ} (hx0 : 0 ≤ x) :
    |Real.cos x - cosPolynomialReal x| ≤
      x ^ 33 / (33 : ℕ).factorial := by
  by_cases hx : x = 0
  · subst x
    norm_num [cosPolynomialReal, Finset.sum_range_succ]
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    obtain ⟨y, _hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cos) (n := 32) hxpos Real.contDiff_cos.contDiffOn
    rw [taylorWithinEval_cos_32_eq hxpos] at hrem
    rw [hrem]
    have hderiv := Real.abs_iteratedDeriv_cos_le_one 33 y
    have hpow : 0 ≤ x ^ 33 := pow_nonneg hx0 33
    have hfac : (0 : ℝ) < (33 : ℕ).factorial := by positivity
    norm_num only [Nat.reduceAdd, sub_zero, abs_div, abs_mul, abs_pow]
    rw [abs_of_nonneg hx0]
    have hmul : |iteratedDeriv 33 Real.cos y| * x ^ 33 ≤ x ^ 33 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hderiv hpow
    exact div_le_div_of_nonneg_right
      hmul (by positivity)

lemma sin_taylor_remainder_33
    {x : ℝ} (hx0 : 0 ≤ x) :
    |Real.sin x - sinPolynomialReal x| ≤
      x ^ 34 / (34 : ℕ).factorial := by
  by_cases hx : x = 0
  · subst x
    norm_num [sinPolynomialReal, Finset.sum_range_succ]
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    obtain ⟨y, _hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.sin) (n := 33) hxpos Real.contDiff_sin.contDiffOn
    rw [taylorWithinEval_sin_33_eq hxpos] at hrem
    rw [hrem]
    have hderiv := Real.abs_iteratedDeriv_sin_le_one 34 y
    have hpow : 0 ≤ x ^ 34 := pow_nonneg hx0 34
    have hfac : (0 : ℝ) < (34 : ℕ).factorial := by positivity
    norm_num only [Nat.reduceAdd, sub_zero, abs_div, abs_mul, abs_pow]
    rw [abs_of_nonneg hx0]
    have hmul : |iteratedDeriv 34 Real.sin y| * x ^ 34 ≤ x ^ 34 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hderiv hpow
    exact div_le_div_of_nonneg_right
      hmul (by positivity)

def trigAlternatingSign (k : ℕ) : ℤ :=
  if Even k then 1 else -1

lemma trigAlternatingSign_eq (k : ℕ) :
    trigAlternatingSign k = (-1 : ℤ) ^ k := by
  by_cases h : Even k
  · rw [trigAlternatingSign, if_pos h, h.neg_one_pow]
  · have hodd : Odd k := Nat.not_even_iff_odd.mp h
    rw [trigAlternatingSign, if_neg h, hodd.neg_one_pow]

lemma trigAlternatingSign_cast (k : ℕ) :
    (trigAlternatingSign k : ℝ) = (-1 : ℝ) ^ k := by
  rw [trigAlternatingSign_eq]
  push_cast
  rfl

def trigCosHorner (x : DyadicInterval) : DyadicInterval :=
  let y := DyadicInterval.sqr x
  (List.range 17).reverse.foldl
    (fun acc k =>
      DyadicInterval.add
        (DyadicInterval.ofRat (trigAlternatingSign k)
          (Int.ofNat (2 * k).factorial))
        (DyadicInterval.mul y acc))
    (DyadicInterval.point 0)

def trigSinHorner (x : DyadicInterval) : DyadicInterval :=
  let y := DyadicInterval.sqr x
  let quotient := (List.range 17).reverse.foldl
    (fun acc k =>
      DyadicInterval.add
        (DyadicInterval.ofRat (trigAlternatingSign k)
          (Int.ofNat (2 * k + 1).factorial))
        (DyadicInterval.mul y acc))
    (DyadicInterval.point 0)
  DyadicInterval.mul x quotient

def trigCosHornerReal (x : ℝ) : ℝ :=
  let y := x ^ 2
  (List.range 17).reverse.foldl
    (fun acc k =>
      (trigAlternatingSign k : ℝ) /
          ((2 * k).factorial : ℝ) + y * acc)
    0

def trigSinHornerReal (x : ℝ) : ℝ :=
  let y := x ^ 2
  let quotient := (List.range 17).reverse.foldl
    (fun acc k =>
      (trigAlternatingSign k : ℝ) /
          ((2 * k + 1).factorial : ℝ) + y * acc)
    0
  x * quotient

lemma trig_horner_fold_sound
    {y : DyadicInterval} {yR : ℝ} (hy : y.Contains yR)
    (denom : ℕ → ℕ) (hdenom : ∀ k, 0 < denom k) :
    ∀ (ks : List ℕ) (acc : DyadicInterval) (accR : ℝ),
      acc.Contains accR →
      (ks.foldl
        (fun value k =>
          DyadicInterval.add
            (DyadicInterval.ofRat (trigAlternatingSign k)
              (Int.ofNat (denom k)))
            (DyadicInterval.mul y value)) acc).Contains
      (ks.foldl
        (fun value k =>
          (trigAlternatingSign k : ℝ) / ((denom k : ℕ) : ℝ) +
            yR * value) accR) := by
  intro ks
  induction ks with
  | nil =>
      intro acc accR hacc
      exact hacc
  | cons k ks ih =>
      intro acc accR hacc
      have hdenomInt : (0 : ℤ) < Int.ofNat (denom k) := by
        have hcast : (0 : ℤ) < (denom k : ℤ) := by
          exact_mod_cast hdenom k
        exact hcast
      have hcoeff := DyadicInterval.contains_ofRat
        (trigAlternatingSign k) hdenomInt
      exact ih _ _ (hcoeff.add (hy.mul hacc))

lemma trigCosHorner_sound
    {x : DyadicInterval} {xR : ℝ} (hx : x.Contains xR) :
    (trigCosHorner x).Contains (trigCosHornerReal xR) := by
  have hy := hx.sqr hx.ordered
  have hzero : (DyadicInterval.point 0).Contains (0 : ℝ) := by
    simpa using DyadicInterval.contains_point (0 : ℤ)
  simpa [trigCosHorner, trigCosHornerReal] using
    trig_horner_fold_sound hy (fun k => (2 * k).factorial)
      (fun _ => Nat.factorial_pos _) (List.range 17).reverse
      (DyadicInterval.point 0) 0 hzero

lemma trigSinHorner_sound
    {x : DyadicInterval} {xR : ℝ} (hx : x.Contains xR) :
    (trigSinHorner x).Contains (trigSinHornerReal xR) := by
  have hy := hx.sqr hx.ordered
  have hzero : (DyadicInterval.point 0).Contains (0 : ℝ) := by
    simpa using DyadicInterval.contains_point (0 : ℤ)
  have hquot := trig_horner_fold_sound hy
    (fun k => (2 * k + 1).factorial) (fun _ => Nat.factorial_pos _)
    (List.range 17).reverse (DyadicInterval.point 0) 0 hzero
  exact hx.mul (by
    simpa [trigSinHornerReal] using hquot)

lemma trigCosHornerReal_eq (x : ℝ) :
    trigCosHornerReal x = cosPolynomialReal x := by
  unfold trigCosHornerReal cosPolynomialReal
  simp_rw [trigAlternatingSign_cast]
  norm_num [List.range_succ, Finset.sum_range_succ]
  ring

lemma trigSinHornerReal_eq (x : ℝ) :
    trigSinHornerReal x = sinPolynomialReal x := by
  unfold trigSinHornerReal sinPolynomialReal
  simp_rw [trigAlternatingSign_cast]
  norm_num [List.range_succ, Finset.sum_range_succ]
  ring

def trigAbsHull (I : DyadicInterval) : DyadicInterval :=
  ⟨0, max (-I.lo) I.hi⟩

def trigUnitClip (I : DyadicInterval) : DyadicInterval :=
  ⟨max (-dyadicScale) I.lo, min dyadicScale I.hi⟩

def trigTaylorRemainder
    (x : DyadicInterval) (degreePlusOne : ℕ) : DyadicInterval :=
  DyadicInterval.divPoint
    (powi (trigAbsHull x) degreePlusOne)
    (Int.ofNat degreePlusOne.factorial)

def trigSymmetricUpper (I : DyadicInterval) : DyadicInterval :=
  ⟨-I.hi, I.hi⟩

def trigCosAtPoint (x : DyadicInterval) : DyadicInterval :=
  let p := trigCosHorner x
  let rem := trigTaylorRemainder x 33
  trigUnitClip
    (DyadicInterval.add p (trigSymmetricUpper rem))

def trigSinAtPoint (x : DyadicInterval) : DyadicInterval :=
  let p := trigSinHorner x
  let rem := trigTaylorRemainder x 34
  trigUnitClip
    (DyadicInterval.add p (trigSymmetricUpper rem))

lemma trigAbsHull_sound
    {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) :
    (trigAbsHull I).Contains |x| := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  constructor
  · simp [trigAbsHull, DyadicInterval.lower, hscale.ne']
  · have hright : I.upper ≤
        ((max (-I.lo) I.hi : ℤ) : ℝ) / (dyadicScale : ℝ) := by
      unfold DyadicInterval.upper
      apply (div_le_div_iff_of_pos_right hscale).2
      exact_mod_cast le_max_right (-I.lo) I.hi
    have hleft : -I.lower ≤
        ((max (-I.lo) I.hi : ℤ) : ℝ) / (dyadicScale : ℝ) := by
      rw [show -I.lower = ((-I.lo : ℤ) : ℝ) / (dyadicScale : ℝ) by
        unfold DyadicInterval.lower
        push_cast
        ring]
      apply (div_le_div_iff_of_pos_right hscale).2
      exact_mod_cast le_max_left (-I.lo) I.hi
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0]
      exact hx.2.trans hright
    · rw [abs_of_nonpos (le_of_not_ge hx0)]
      exact (neg_le_neg hx.1).trans hleft

lemma trigUnitClip_sound
    {I : DyadicInterval} {x : ℝ} (hx : I.Contains x)
    (hunit : -1 ≤ x ∧ x ≤ 1) :
    (trigUnitClip I).Contains x := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  constructor
  · change ((max (-dyadicScale) I.lo : ℤ) : ℝ) /
      (dyadicScale : ℝ) ≤ x
    rw [div_le_iff₀ hscale, Int.cast_max]
    apply max_le
    · push_cast
      nlinarith
    · exact (div_le_iff₀ hscale).1 hx.1
  · change x ≤ ((min dyadicScale I.hi : ℤ) : ℝ) /
      (dyadicScale : ℝ)
    rw [le_div_iff₀ hscale, Int.cast_min]
    apply le_min
    · push_cast
      nlinarith
    · exact (le_div_iff₀ hscale).1 hx.2

lemma trigSymmetricUpper_sound
    {I : DyadicInterval} {R e : ℝ}
    (hR : I.Contains R) (he : |e| ≤ R) :
    (trigSymmetricUpper I).Contains e := by
  have habs : |e| ≤ I.upper := he.trans hR.2
  have hb := (abs_le).mp habs
  constructor
  · change (((-I.hi : ℤ) : ℝ) / (dyadicScale : ℝ)) ≤ e
    convert hb.1 using 1 <;>
      simp [DyadicInterval.upper] <;> ring
  · simpa [trigSymmetricUpper, DyadicInterval.upper] using hb.2

lemma trigTaylorRemainder_sound
    {I : DyadicInterval} {x : ℝ} (hx : I.Contains x)
    (degreePlusOne : ℕ) :
    (trigTaylorRemainder I degreePlusOne).Contains
      (|x| ^ degreePlusOne / (degreePlusOne.factorial : ℝ)) := by
  have habs := trigAbsHull_sound hx
  have hpow := powi_sound habs degreePlusOne
  let denominator : DyadicInterval :=
    DyadicInterval.point (Int.ofNat degreePlusOne.factorial)
  have hden : denominator.Contains (degreePlusOne.factorial : ℝ) := by
    simpa [denominator] using
      DyadicInterval.contains_point (Int.ofNat degreePlusOne.factorial)
  have hdenPos : 0 < denominator.lo := by
    change 0 < Int.ofNat degreePlusOne.factorial * dyadicScale
    exact mul_pos (by
      have hfac : (0 : ℤ) < (degreePlusOne.factorial : ℕ) := by
        exact_mod_cast Nat.factorial_pos degreePlusOne
      exact hfac) dyadicScale_pos
  rw [trigTaylorRemainder, DyadicInterval.divPoint_eq_div]
  exact hpow.div hden hden.ordered hdenPos

lemma trigCosAtPoint_sound
    {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) (hx0 : 0 ≤ x) :
    (trigCosAtPoint I).Contains (Real.cos x) := by
  have hp := trigCosHorner_sound hx
  rw [trigCosHornerReal_eq] at hp
  have hrem := trigTaylorRemainder_sound hx 33
  rw [abs_of_nonneg hx0] at hrem
  have herror := trigSymmetricUpper_sound hrem
    (cos_taylor_remainder_32 hx0)
  have hsum := hp.add herror
  have hpre : (DyadicInterval.add (trigCosHorner I)
      (trigSymmetricUpper (trigTaylorRemainder I 33))).Contains
      (Real.cos x) := by
    convert hsum using 1 <;> ring
  exact trigUnitClip_sound hpre
    ((abs_le).mp (Real.abs_cos_le_one x))

lemma trigSinAtPoint_sound
    {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) (hx0 : 0 ≤ x) :
    (trigSinAtPoint I).Contains (Real.sin x) := by
  have hp := trigSinHorner_sound hx
  rw [trigSinHornerReal_eq] at hp
  have hrem := trigTaylorRemainder_sound hx 34
  rw [abs_of_nonneg hx0] at hrem
  have herror := trigSymmetricUpper_sound hrem
    (sin_taylor_remainder_33 hx0)
  have hsum := hp.add herror
  have hpre : (DyadicInterval.add (trigSinHorner I)
      (trigSymmetricUpper (trigTaylorRemainder I 34))).Contains
      (Real.sin x) := by
    convert hsum using 1 <;> ring
  exact trigUnitClip_sound hpre
    ((abs_le).mp (Real.abs_sin_le_one x))

def trigMid (I : DyadicInterval) : ℤ :=
  floorDiv (I.lo + I.hi) 2

def trigRadius (I : DyadicInterval) : ℤ :=
  max (trigMid I - I.lo) (I.hi - trigMid I)

def trigSinCos
    (I : DyadicInterval) : DyadicInterval × DyadicInterval :=
  let mid := trigMid I
  let center : DyadicInterval := ⟨mid, mid⟩
  let radius := trigRadius I
  let wiggle : DyadicInterval := ⟨-radius, radius⟩
  (trigUnitClip
      (DyadicInterval.add (trigSinAtPoint center) wiggle),
    trigUnitClip
      (DyadicInterval.add (trigCosAtPoint center) wiggle))

lemma trigMid_mem
    {I : DyadicInterval} (hI : I.Ordered) (hlo : 0 ≤ I.lo) :
    I.lo ≤ trigMid I ∧ trigMid I ≤ I.hi := by
  change I.lo ≤ I.hi at hI
  unfold trigMid floorDiv
  omega

lemma trigCenter_sound
    (I : DyadicInterval) :
    let mid := trigMid I
    (show DyadicInterval from ⟨mid, mid⟩).Contains
      ((mid : ℝ) / (dyadicScale : ℝ)) := by
  intro mid
  exact ⟨le_rfl, le_rfl⟩

lemma trigRadius_sound
    {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) (hlo : 0 ≤ I.lo) :
    |x - (trigMid I : ℝ) / (dyadicScale : ℝ)| ≤
      (trigRadius I : ℝ) / (dyadicScale : ℝ) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hmid := trigMid_mem hx.ordered hlo
  have hleft :
      ((trigMid I - I.lo : ℤ) : ℝ) /
          (dyadicScale : ℝ) ≤
        (trigRadius I : ℝ) / (dyadicScale : ℝ) := by
    apply (div_le_div_iff_of_pos_right hscale).2
    exact_mod_cast le_max_left
      (trigMid I - I.lo) (I.hi - trigMid I)
  have hright :
      ((I.hi - trigMid I : ℤ) : ℝ) /
          (dyadicScale : ℝ) ≤
        (trigRadius I : ℝ) / (dyadicScale : ℝ) := by
    apply (div_le_div_iff_of_pos_right hscale).2
    exact_mod_cast le_max_right
      (trigMid I - I.lo) (I.hi - trigMid I)
  apply (abs_le).2
  constructor
  · have hxlower := hx.1
    unfold DyadicInterval.lower at hxlower
    have hdist :
        (trigMid I : ℝ) / (dyadicScale : ℝ) - x ≤
          ((trigMid I - I.lo : ℤ) : ℝ) /
            (dyadicScale : ℝ) := by
      calc
        (trigMid I : ℝ) / (dyadicScale : ℝ) - x ≤
            (trigMid I : ℝ) / (dyadicScale : ℝ) -
              (I.lo : ℝ) / (dyadicScale : ℝ) :=
          sub_le_sub_left hxlower _
        _ = ((trigMid I - I.lo : ℤ) : ℝ) /
            (dyadicScale : ℝ) := by
          push_cast
          ring
    have hdist' := hdist.trans hleft
    linarith
  · have hxupper := hx.2
    unfold DyadicInterval.upper at hxupper
    have hdist :
        x - (trigMid I : ℝ) / (dyadicScale : ℝ) ≤
          ((I.hi - trigMid I : ℤ) : ℝ) /
            (dyadicScale : ℝ) := by
      calc
        x - (trigMid I : ℝ) / (dyadicScale : ℝ) ≤
            (I.hi : ℝ) / (dyadicScale : ℝ) -
              (trigMid I : ℝ) / (dyadicScale : ℝ) :=
          sub_le_sub_right hxupper _
        _ = ((I.hi - trigMid I : ℤ) : ℝ) /
            (dyadicScale : ℝ) := by
          push_cast
          ring
    exact hdist.trans hright

lemma trigWiggle_sound
    {I : DyadicInterval} {e : ℝ}
    (he : |e| ≤
      (trigRadius I : ℝ) / (dyadicScale : ℝ)) :
    (show DyadicInterval from
      ⟨-trigRadius I, trigRadius I⟩).Contains e := by
  have hb := (abs_le).mp he
  constructor
  · change (((-trigRadius I : ℤ) : ℝ) /
      (dyadicScale : ℝ)) ≤ e
    convert hb.1 using 1 <;> push_cast <;> ring
  · exact hb.2

lemma trigSinCos_sound
    {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) (hlo : 0 ≤ I.lo) :
    (trigSinCos I).1.Contains (Real.sin x) ∧
      (trigSinCos I).2.Contains (Real.cos x) := by
  let mid := trigMid I
  let center : DyadicInterval := ⟨mid, mid⟩
  let midR : ℝ := (mid : ℝ) / (dyadicScale : ℝ)
  let radius := trigRadius I
  let wiggle : DyadicInterval := ⟨-radius, radius⟩
  have hcenter : center.Contains midR := by
    exact ⟨le_rfl, le_rfl⟩
  have hmidNonneg : 0 ≤ midR := by
    have hmidlo := (trigMid_mem hx.ordered hlo).1
    have hmid0 : 0 ≤ mid := hlo.trans hmidlo
    exact div_nonneg (by exact_mod_cast hmid0) (by
      exact_mod_cast dyadicScale_pos.le)
  have hradius := trigRadius_sound hx hlo
  have hsinDiff : |Real.sin x - Real.sin midR| ≤
      (radius : ℝ) / (dyadicScale : ℝ) :=
    (Real.abs_sin_sub_sin_le x midR).trans (by
      simpa only [midR, mid, radius] using hradius)
  have hcosDiff : |Real.cos x - Real.cos midR| ≤
      (radius : ℝ) / (dyadicScale : ℝ) :=
    (Real.abs_cos_sub_cos_le x midR).trans (by
      simpa only [midR, mid, radius] using hradius)
  have hwiggleSin : wiggle.Contains (Real.sin x - Real.sin midR) := by
    simpa only [wiggle, radius] using
      trigWiggle_sound (I := I) hsinDiff
  have hwiggleCos : wiggle.Contains (Real.cos x - Real.cos midR) := by
    simpa only [wiggle, radius] using
      trigWiggle_sound (I := I) hcosDiff
  have hsinCenter := trigSinAtPoint_sound hcenter hmidNonneg
  have hcosCenter := trigCosAtPoint_sound hcenter hmidNonneg
  have hsinPre := hsinCenter.add hwiggleSin
  have hcosPre := hcosCenter.add hwiggleCos
  constructor
  · have hsinPre' :
        (DyadicInterval.add (trigSinAtPoint center) wiggle).Contains
          (Real.sin x) := by
      convert hsinPre using 1 <;> ring
    simpa only [trigSinCos, mid, center, radius, wiggle] using
      trigUnitClip_sound hsinPre'
        ((abs_le).mp (Real.abs_sin_le_one x))
  · have hcosPre' :
        (DyadicInterval.add (trigCosAtPoint center) wiggle).Contains
          (Real.cos x) := by
      convert hcosPre using 1 <;> ring
    simpa only [trigSinCos, mid, center, radius, wiggle] using
      trigUnitClip_sound hcosPre'
        ((abs_le).mp (Real.abs_cos_le_one x))

end

end BerryEsseen
