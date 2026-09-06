import BerryEsseen.DyadicPrawitzFiniteCache

/-!
# Characteristic Functions / Component Bounds
-/

namespace BerryEsseen

open DyadicInterval

def upperHull (hi : ℤ) : DyadicInterval :=
  ⟨0, max 0 hi⟩

/-- `d = 1-E|X|` is at most both `1-1/rho` and `1-z`, where
`z=rho*(r-1)`. -/
def dUpper (rho z : DyadicInterval) : DyadicInterval :=
  let oneMinusInvRho := DyadicInterval.sub (DyadicInterval.point 1)
    (DyadicInterval.div (DyadicInterval.point 1) rho)
  let oneMinusZ := DyadicInterval.sub (DyadicInterval.point 1) z
  upperHull (min oneMinusInvRho.hi oneMinusZ.hi)

def absHull (I : DyadicInterval) : DyadicInterval :=
  ⟨0, max (-I.lo) I.hi⟩

/-- The real-part interval used inside `cellEnvelope`, factored out so
that its arithmetic soundness can be reviewed independently of quadrature. -/
def realInterval
    (rho d u sinU cosU : DyadicInterval) : DyadicInterval :=
  let u2 := DyadicInterval.sqr u
  let u3 := powi u 3
  let realRadius := DyadicInterval.mul d
    (DyadicInterval.add
      (absHull (DyadicInterval.mul u sinU)) u2)
  let realTaylorLow := DyadicInterval.sub cosU realRadius
  let realTaylorHigh := DyadicInterval.add cosU realRadius
  let realQuadratic := DyadicInterval.sub (DyadicInterval.point 1)
    (DyadicInterval.divPoint u2 2)
  let realCubicUpper := DyadicInterval.add realQuadratic
    (DyadicInterval.mul checkerKappaUpper (DyadicInterval.mul rho u3))
  ⟨max (-dyadicScale) (max realTaylorLow.lo realQuadratic.lo),
    min dyadicScale (min realTaylorHigh.hi realCubicUpper.hi)⟩

/-- The imaginary-part half-width used inside `cellEnvelope`, again
factored out from the quadrature layer. -/
def imagInterval
    (rho z d u sinU cosU : DyadicInterval) : DyadicInterval :=
  let u2 := DyadicInterval.sqr u
  let u3 := powi u 3
  let sqrtTwoD := DyadicInterval.sqrt (DyadicInterval.mulPoint 2 d)
  let imagTaylor := DyadicInterval.add
    (DyadicInterval.mul sqrtTwoD
      (absHull
        (DyadicInterval.sub sinU (DyadicInterval.mul u cosU))))
    (DyadicInterval.mul d u2)
  let circleScale := DyadicInterval.sqrt
    (DyadicInterval.maxZero
      (DyadicInterval.sub (DyadicInterval.sqr rho) (DyadicInterval.sqr z)))
  let imagCircle := DyadicInterval.divPoint
    (DyadicInterval.mul u3 circleScale) 6
  upperHull (min imagTaylor.hi imagCircle.hi)

def rectangularEnvelope
    (real imag : DyadicInterval) : DyadicInterval :=
  DyadicInterval.sqrt
    (DyadicInterval.add
      (DyadicInterval.sqr (absHull real))
      (DyadicInterval.sqr imag))

def errorToCosEnvelope
    (real realRadius imag cosU : DyadicInterval) : DyadicInterval :=
  let intersectedRealError :=
    absHull (DyadicInterval.sub real cosU)
  let realError := upperHull
    (min realRadius.hi intersectedRealError.hi)
  DyadicInterval.sqrt
    (DyadicInterval.add
      (DyadicInterval.sqr realError) (DyadicInterval.sqr imag))

def rademacherDifferenceIntervals
    (n : ℕ) (f errorToCos cosU cosAbs normalN : DyadicInterval) :
    DyadicInterval :=
  let powerBase := dyadicCellNonnegativeHull f cosAbs
  let comparison := DyadicInterval.mulPoint (Int.ofNat n)
    (DyadicInterval.mul errorToCos (powi powerBase (n - 1)))
  let remainder := absHull
    (DyadicInterval.sub (powi cosU n) normalN)
  DyadicInterval.add comparison remainder

def minModulusEnvelope
    (routeA rectangular : DyadicInterval) : DyadicInterval :=
  upperHull
    (min dyadicScale (min routeA.hi rectangular.hi))

def normalOne (u : DyadicInterval) : DyadicInterval :=
  dyadicExpNeg
    (DyadicInterval.divPoint (DyadicInterval.sqr u) 2)

def normalN (n : ℕ) (u : DyadicInterval) : DyadicInterval :=
  let normalArg := DyadicInterval.divPoint (DyadicInterval.sqr u) 2
  dyadicExpNeg
    (DyadicInterval.mulPoint (Int.ofNat n) normalArg)

noncomputable section

lemma upperHull_sound
    {hi : ℤ} {x : ℝ} (hx0 : 0 ≤ x)
    (hxhi : x ≤ (hi : ℝ) / (dyadicScale : ℝ)) :
    (upperHull hi).Contains x := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  constructor
  · simpa [upperHull, DyadicInterval.lower] using hx0
  · change x ≤ ((max 0 hi : ℤ) : ℝ) / (dyadicScale : ℝ)
    apply hxhi.trans
    apply (div_le_div_iff_of_pos_right hscale).2
    exact_mod_cast le_max_right 0 hi

/-- The exact outward-rounded implementation of `dbar` contains every
nonnegative `d` satisfying the two analytic moment constraints. -/
theorem dUpper_sound
    {rho z : DyadicInterval} {rhoR zR d : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hrhoLo : 0 < rho.lo) (hd0 : 0 ≤ d)
    (hdRho : d ≤ 1 - 1 / rhoR) (hdZ : d ≤ 1 - zR) :
    (dUpper rho z).Contains d := by
  let oneMinusInvRho := DyadicInterval.sub (DyadicInterval.point 1)
    (DyadicInterval.div (DyadicInterval.point 1) rho)
  let oneMinusZ := DyadicInterval.sub (DyadicInterval.point 1) z
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hinv : (DyadicInterval.div (DyadicInterval.point 1) rho).Contains
      (1 / rhoR) := by
    simpa only [one_div] using hone.div hrho hrho.ordered hrhoLo
  have hRho : oneMinusInvRho.Contains (1 - 1 / rhoR) := by
    simpa only [oneMinusInvRho] using hone.sub hinv
  have hZ : oneMinusZ.Contains (1 - zR) := by
    simpa only [oneMinusZ] using hone.sub hz
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hRhoScaled : d * (dyadicScale : ℝ) ≤
      (oneMinusInvRho.hi : ℝ) := by
    exact (le_div_iff₀ hscale).1 (hdRho.trans hRho.2)
  have hZScaled : d * (dyadicScale : ℝ) ≤
      (oneMinusZ.hi : ℝ) := by
    exact (le_div_iff₀ hscale).1 (hdZ.trans hZ.2)
  have hmin : d ≤
      ((min oneMinusInvRho.hi oneMinusZ.hi : ℤ) : ℝ) /
        (dyadicScale : ℝ) := by
    apply (le_div_iff₀ hscale).2
    rw [Int.cast_min]
    exact le_min hRhoScaled hZScaled
  simpa only [dUpper, oneMinusInvRho, oneMinusZ] using
    upperHull_sound hd0 hmin

lemma absHull_sound
    {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) :
    (absHull I).Contains |x| := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  constructor
  · simp [absHull, DyadicInterval.lower, hscale.ne']
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

/-- Arithmetic soundness of the real-part intersection.  The hypotheses are
exactly the three analytic enclosures later supplied by the characteristic
function argument, plus the universal `|Re f| ≤ 1`. -/
theorem realInterval_sound
    {rho d u sinU cosU : DyadicInterval}
    {rhoR dR uR reR : ℝ}
    (hrho : rho.Contains rhoR) (hd : d.Contains dR)
    (hu : u.Contains uR)
    (hsin : sinU.Contains (Real.sin uR))
    (hcos : cosU.Contains (Real.cos uR))
    (hunit : -1 ≤ reR ∧ reR ≤ 1)
    (htaylor : |reR - Real.cos uR| ≤
      dR * (|uR * Real.sin uR| + uR ^ 2))
    (hquadratic : 1 - uR ^ 2 / 2 ≤ reR)
    (hcubic : reR ≤ 1 - uR ^ 2 / 2 +
      routeBKappaUpper * rhoR * uR ^ 3) :
    (realInterval rho d u sinU cosU).Contains reR := by
  let u2 := DyadicInterval.sqr u
  let u3 := powi u 3
  let realRadius := DyadicInterval.mul d
    (DyadicInterval.add
      (absHull (DyadicInterval.mul u sinU)) u2)
  let realTaylorLow := DyadicInterval.sub cosU realRadius
  let realTaylorHigh := DyadicInterval.add cosU realRadius
  let realQuadratic := DyadicInterval.sub (DyadicInterval.point 1)
    (DyadicInterval.divPoint u2 2)
  let realCubicUpper := DyadicInterval.add realQuadratic
    (DyadicInterval.mul checkerKappaUpper (DyadicInterval.mul rho u3))
  have hu2 : u2.Contains (uR ^ 2) := by
    simpa only [u2] using hu.sqr hu.ordered
  have hu3 : u3.Contains (uR ^ 3) := by
    simpa only [u3] using powi_sound hu 3
  have huSin : (DyadicInterval.mul u sinU).Contains
      (uR * Real.sin uR) := hu.mul hsin
  have habsUSin := absHull_sound huSin
  have hsum : (DyadicInterval.add
      (absHull (DyadicInterval.mul u sinU)) u2).Contains
      (|uR * Real.sin uR| + uR ^ 2) := habsUSin.add hu2
  have hradius : realRadius.Contains
      (dR * (|uR * Real.sin uR| + uR ^ 2)) := by
    simpa only [realRadius] using hd.mul hsum
  have hlow : realTaylorLow.Contains
      (Real.cos uR - dR * (|uR * Real.sin uR| + uR ^ 2)) := by
    simpa only [realTaylorLow] using hcos.sub hradius
  have hhigh : realTaylorHigh.Contains
      (Real.cos uR + dR * (|uR * Real.sin uR| + uR ^ 2)) := by
    simpa only [realTaylorHigh] using hcos.add hradius
  have hhalf : (DyadicInterval.divPoint u2 2).Contains (uR ^ 2 / 2) := by
    rw [DyadicInterval.divPoint_eq_div]
    exact dyadicContains_div_point hu2 2 (by norm_num)
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hquad : realQuadratic.Contains (1 - uR ^ 2 / 2) := by
    simpa only [realQuadratic] using hone.sub hhalf
  have hkappa := checkerKappaUpper_contains
  have hcubicTerm :
      (DyadicInterval.mul checkerKappaUpper
        (DyadicInterval.mul rho u3)).Contains
      (routeBKappaUpper * (rhoR * uR ^ 3)) :=
    hkappa.mul (hrho.mul hu3)
  have hcubicI : realCubicUpper.Contains
      (1 - uR ^ 2 / 2 + routeBKappaUpper * rhoR * uR ^ 3) := by
    have := hquad.add hcubicTerm
    convert this using 1 <;> ring
  have htaylorBounds := (abs_le).1 htaylor
  have hlowRe : realTaylorLow.lower ≤ reR := by
    apply hlow.1.trans
    linarith
  have hhighRe : reR ≤ realTaylorHigh.upper := by
    apply le_trans _ hhigh.2
    linarith
  have hquadRe : realQuadratic.lower ≤ reR :=
    hquad.1.trans hquadratic
  have hcubicRe : reR ≤ realCubicUpper.upper :=
    hcubic.trans hcubicI.2
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  change
    ((max (-dyadicScale)
      (max realTaylorLow.lo realQuadratic.lo) : ℤ) : ℝ) /
        (dyadicScale : ℝ) ≤ reR ∧
      reR ≤ ((min dyadicScale
        (min realTaylorHigh.hi realCubicUpper.hi) : ℤ) : ℝ) /
          (dyadicScale : ℝ)
  constructor
  · apply (div_le_iff₀ hscale).2
    rw [Int.cast_max, Int.cast_max]
    apply max_le
    · push_cast
      simpa using (mul_le_mul_of_nonneg_right hunit.1 hscale.le)
    · apply max_le
      · exact (div_le_iff₀ hscale).1 hlowRe
      · exact (div_le_iff₀ hscale).1 hquadRe
  · apply (le_div_iff₀ hscale).2
    rw [Int.cast_min, Int.cast_min]
    apply le_min
    · push_cast
      simpa using (mul_le_mul_of_nonneg_right hunit.2 hscale.le)
    · apply le_min
      · exact (le_div_iff₀ hscale).1 hhighRe
      · exact (le_div_iff₀ hscale).1 hcubicRe

/-- Arithmetic soundness of the minimum of the radial Taylor and sine-circle
imaginary-part bounds. -/
theorem imagInterval_sound
    {rho z d u sinU cosU : DyadicInterval}
    {rhoR zR dR uR imR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hd : d.Contains dR) (hu : u.Contains uR)
    (hsin : sinU.Contains (Real.sin uR))
    (hcos : cosU.Contains (Real.cos uR))
    (hdLo : 0 ≤ d.lo) (hd0 : 0 ≤ dR)
    (hrad : 0 ≤ rhoR ^ 2 - zR ^ 2)
    (htaylor : |imR| ≤
      Real.sqrt (2 * dR) * |Real.sin uR - uR * Real.cos uR| +
        dR * uR ^ 2)
    (hcircle : |imR| ≤
      uR ^ 3 * Real.sqrt (rhoR ^ 2 - zR ^ 2) / 6) :
    (imagInterval rho z d u sinU cosU).Contains |imR| := by
  let u2 := DyadicInterval.sqr u
  let u3 := powi u 3
  let twoD := DyadicInterval.mulPoint 2 d
  let sqrtTwoD := DyadicInterval.sqrt twoD
  let imagTaylor := DyadicInterval.add
    (DyadicInterval.mul sqrtTwoD
      (absHull
        (DyadicInterval.sub sinU (DyadicInterval.mul u cosU))))
    (DyadicInterval.mul d u2)
  let radicand := DyadicInterval.sub
    (DyadicInterval.sqr rho) (DyadicInterval.sqr z)
  let nonnegativeRadicand := DyadicInterval.maxZero radicand
  let circleScale := DyadicInterval.sqrt nonnegativeRadicand
  let imagCircle := DyadicInterval.divPoint
    (DyadicInterval.mul u3 circleScale) 6
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have htwoD : twoD.Contains (2 * dR) := by
    simpa only [twoD, DyadicInterval.mulPoint_eq_mul] using htwo.mul hd
  have htwoDLo : 0 ≤ twoD.lo := by
    have hfast : 0 ≤ (2 : ℤ) ∧ d.lo ≤ d.hi :=
      ⟨by norm_num, hd.ordered⟩
    change 0 ≤ (DyadicInterval.mulPoint 2 d).lo
    rw [DyadicInterval.mulPoint]
    rw [if_pos hfast]
    exact mul_nonneg (by norm_num) hdLo
  have hsqrtTwoD : sqrtTwoD.Contains (Real.sqrt (2 * dR)) := by
    simpa only [sqrtTwoD] using htwoD.sqrt htwoD.ordered htwoDLo
  have hu2 : u2.Contains (uR ^ 2) := by
    simpa only [u2] using hu.sqr hu.ordered
  have hu3 : u3.Contains (uR ^ 3) := by
    simpa only [u3] using powi_sound hu 3
  have huCos := hu.mul hcos
  have hdiff :
      (DyadicInterval.sub sinU (DyadicInterval.mul u cosU)).Contains
        (Real.sin uR - uR * Real.cos uR) := hsin.sub huCos
  have habsDiff := absHull_sound hdiff
  have hfirst := hsqrtTwoD.mul habsDiff
  have hsecond := hd.mul hu2
  have himagTaylor : imagTaylor.Contains
      (Real.sqrt (2 * dR) * |Real.sin uR - uR * Real.cos uR| +
        dR * uR ^ 2) := by
    simpa only [imagTaylor] using hfirst.add hsecond
  have hrho2 := hrho.sqr hrho.ordered
  have hz2 := hz.sqr hz.ordered
  have hradI : radicand.Contains (rhoR ^ 2 - zR ^ 2) := by
    simpa only [radicand] using hrho2.sub hz2
  have hnonnegativeRadicand : nonnegativeRadicand.Contains
      (rhoR ^ 2 - zR ^ 2) := by
    have := hradI.maxZero
    simpa only [nonnegativeRadicand, max_eq_right hrad] using this
  have hnonnegativeLo : 0 ≤ nonnegativeRadicand.lo := by
    simp [nonnegativeRadicand, DyadicInterval.maxZero]
  have hcircleScale : circleScale.Contains
      (Real.sqrt (rhoR ^ 2 - zR ^ 2)) := by
    simpa only [circleScale] using hnonnegativeRadicand.sqrt
      hnonnegativeRadicand.ordered hnonnegativeLo
  have hcircleProduct := hu3.mul hcircleScale
  have himagCircle : imagCircle.Contains
      (uR ^ 3 * Real.sqrt (rhoR ^ 2 - zR ^ 2) / 6) := by
    rw [show imagCircle = DyadicInterval.div
      (DyadicInterval.mul u3 circleScale) (DyadicInterval.point 6) by
      simp only [imagCircle, DyadicInterval.divPoint_eq_div]]
    exact dyadicContains_div_point hcircleProduct 6 (by norm_num)
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hTaylorScaled : |imR| * (dyadicScale : ℝ) ≤
      (imagTaylor.hi : ℝ) :=
    (le_div_iff₀ hscale).1 (htaylor.trans himagTaylor.2)
  have hCircleScaled : |imR| * (dyadicScale : ℝ) ≤
      (imagCircle.hi : ℝ) :=
    (le_div_iff₀ hscale).1 (hcircle.trans himagCircle.2)
  have hmin : |imR| ≤
      ((min imagTaylor.hi imagCircle.hi : ℤ) : ℝ) /
        (dyadicScale : ℝ) := by
    apply (le_div_iff₀ hscale).2
    rw [Int.cast_min]
    exact le_min hTaylorScaled hCircleScaled
  simpa only [imagInterval, u2, u3, twoD, sqrtTwoD,
    imagTaylor, radicand, nonnegativeRadicand, circleScale, imagCircle] using
    upperHull_sound (abs_nonneg imR) hmin

lemma sqr_lo_nonneg (I : DyadicInterval) :
    0 ≤ (DyadicInterval.sqr I).lo := by
  unfold DyadicInterval.sqr
  split_ifs
  · norm_num
  · apply Int.ediv_nonneg
    · exact mul_self_nonneg _
    · exact dyadicScale_pos.le

/-- The rectangular real/imaginary interval encloses the Euclidean modulus. -/
theorem rectangularEnvelope_sound
    {real imag : DyadicInterval} {reR imR : ℝ}
    (hreal : real.Contains reR) (himag : imag.Contains |imR|) :
    (rectangularEnvelope real imag).Contains
      (Real.sqrt (reR ^ 2 + imR ^ 2)) := by
  have habsReal := absHull_sound hreal
  have hrealSq := habsReal.sqr habsReal.ordered
  have himagSq := himag.sqr himag.ordered
  have hsum : (DyadicInterval.add
      (DyadicInterval.sqr (absHull real))
      (DyadicInterval.sqr imag)).Contains
      (reR ^ 2 + imR ^ 2) := by
    convert hrealSq.add himagSq using 1 <;> simp [sq_abs]
  have hsumLo : 0 ≤ (DyadicInterval.add
      (DyadicInterval.sqr (absHull real))
      (DyadicInterval.sqr imag)).lo := by
    simp only [DyadicInterval.add]
    exact add_nonneg (sqr_lo_nonneg _) (sqr_lo_nonneg _)
  simpa only [rectangularEnvelope] using
    hsum.sqrt hsum.ordered hsumLo

/-- The checker takes the smaller of the direct Taylor radius and the radius
obtained after intersecting the real interval, then combines it with the
imaginary half-width. -/
theorem errorToCosEnvelope_sound
    {real realRadius imag cosU : DyadicInterval} {reR imR uR radiusR : ℝ}
    (hreal : real.Contains reR)
    (hcos : cosU.Contains (Real.cos uR))
    (hradius : realRadius.Contains radiusR)
    (himag : imag.Contains |imR|)
    (herrorRadius : |reR - Real.cos uR| ≤ radiusR) :
    (errorToCosEnvelope real realRadius imag cosU).Contains
      (Real.sqrt ((reR - Real.cos uR) ^ 2 + imR ^ 2)) := by
  let intersectedRealError :=
    absHull (DyadicInterval.sub real cosU)
  let realError := upperHull
    (min realRadius.hi intersectedRealError.hi)
  have hdiff := hreal.sub hcos
  have hintersection : intersectedRealError.Contains
      |reR - Real.cos uR| := by
    simpa only [intersectedRealError] using absHull_sound hdiff
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hRadiusScaled : |reR - Real.cos uR| * (dyadicScale : ℝ) ≤
      (realRadius.hi : ℝ) :=
    (le_div_iff₀ hscale).1 (herrorRadius.trans hradius.2)
  have hIntersectionScaled :
      |reR - Real.cos uR| * (dyadicScale : ℝ) ≤
        (intersectedRealError.hi : ℝ) :=
    (le_div_iff₀ hscale).1 hintersection.2
  have hmin : |reR - Real.cos uR| ≤
      ((min realRadius.hi intersectedRealError.hi : ℤ) : ℝ) /
        (dyadicScale : ℝ) := by
    apply (le_div_iff₀ hscale).2
    rw [Int.cast_min]
    exact le_min hRadiusScaled hIntersectionScaled
  have hrealError : realError.Contains |reR - Real.cos uR| := by
    simpa only [realError] using
      upperHull_sound (abs_nonneg _) hmin
  have hrealErrorSq := hrealError.sqr hrealError.ordered
  have himagSq := himag.sqr himag.ordered
  have hsum : (DyadicInterval.add
      (DyadicInterval.sqr realError) (DyadicInterval.sqr imag)).Contains
      ((reR - Real.cos uR) ^ 2 + imR ^ 2) := by
    convert hrealErrorSq.add himagSq using 1 <;> simp [sq_abs]
  have hsumLo : 0 ≤ (DyadicInterval.add
      (DyadicInterval.sqr realError) (DyadicInterval.sqr imag)).lo := by
    simp only [DyadicInterval.add]
    exact add_nonneg (sqr_lo_nonneg _) (sqr_lo_nonneg _)
  simpa only [errorToCosEnvelope, intersectedRealError, realError] using
    hsum.sqrt hsum.ordered hsumLo

/-- Telescoping through the exact Rademacher reference `cos u`. -/
theorem rademacher_power_difference_le
    {a : ℂ} {c g : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ‖a ^ n - (g : ℂ)‖ ≤
      (n : ℝ) * ‖a - (c : ℂ)‖ * max ‖a‖ |c| ^ (n - 1) +
        |c ^ n - g| := by
  have ha : ‖a‖ ≤ max ‖a‖ |c| := le_max_left _ _
  have hc : ‖(c : ℂ)‖ ≤ max ‖a‖ |c| := by
    simpa using (le_max_right ‖a‖ |c|)
  have hpow := norm_pow_sub_pow_le_nat hn ha hc
  have hrealNorm : ‖(c : ℂ) ^ n - (g : ℂ)‖ = |c ^ n - g| := by
    calc
      ‖(c : ℂ) ^ n - (g : ℂ)‖ =
          ‖((c ^ n - g : ℝ) : ℂ)‖ := by
        rw [Complex.ofReal_sub, Complex.ofReal_pow]
      _ = ‖c ^ n - g‖ := Complex.norm_real _
      _ = |c ^ n - g| := Real.norm_eq_abs _
  calc
    ‖a ^ n - (g : ℂ)‖ ≤
        ‖a ^ n - (c : ℂ) ^ n‖ + ‖(c : ℂ) ^ n - (g : ℂ)‖ := by
      exact norm_sub_le_norm_sub_add_norm_sub
        (a ^ n) ((c : ℂ) ^ n) (g : ℂ)
    _ ≤ (n : ℝ) * ‖a - (c : ℂ)‖ * max ‖a‖ |c| ^ (n - 1) +
        ‖(c : ℂ) ^ n - (g : ℂ)‖ := add_le_add hpow le_rfl
    _ = (n : ℝ) * ‖a - (c : ℂ)‖ * max ‖a‖ |c| ^ (n - 1) +
        |c ^ n - g| := by rw [hrealNorm]

/-- Outward-rounded arithmetic for the Rademacher-reference branch. -/
theorem rademacherDifferenceIntervals_sound
    {n : ℕ} {f errorToCos cosU cosAbs normalN : DyadicInterval}
    {fR errorR uR normalR : ℝ}
    (hf : f.Contains fR) (herror : errorToCos.Contains errorR)
    (hcos : cosU.Contains (Real.cos uR))
    (hcosAbs : cosAbs.Contains |Real.cos uR|)
    (hnormal : normalN.Contains normalR)
    (hf0 : 0 ≤ fR) (herror0 : 0 ≤ errorR) :
    (rademacherDifferenceIntervals
      n f errorToCos cosU cosAbs normalN).Contains
      ((n : ℝ) * errorR * max fR |Real.cos uR| ^ (n - 1) +
        |Real.cos uR ^ n - normalR|) := by
  let powerBase := dyadicCellNonnegativeHull f cosAbs
  let comparison := DyadicInterval.mulPoint (Int.ofNat n)
    (DyadicInterval.mul errorToCos (powi powerBase (n - 1)))
  let remainder := absHull
    (DyadicInterval.sub (powi cosU n) normalN)
  have hbase : powerBase.Contains (max fR |Real.cos uR|) := by
    simpa only [powerBase] using
      dyadicCellNonnegativeHull_contains hf hcosAbs hf0 (abs_nonneg _)
  have hbasePow := powi_sound hbase (n - 1)
  have herrorPower := herror.mul hbasePow
  have hnPoint : (DyadicInterval.point (Int.ofNat n)).Contains (n : ℝ) := by
    simpa using DyadicInterval.contains_point (Int.ofNat n)
  have hcomparison : comparison.Contains
      ((n : ℝ) * errorR * max fR |Real.cos uR| ^ (n - 1)) := by
    simpa only [comparison, DyadicInterval.mulPoint_eq_mul,
      mul_assoc] using hnPoint.mul herrorPower
  have hcosPow := powi_sound hcos n
  have hdifference := hcosPow.sub hnormal
  have hremainder : remainder.Contains
      |Real.cos uR ^ n - normalR| := by
    simpa only [remainder] using absHull_sound hdifference
  simpa only [rademacherDifferenceIntervals, powerBase,
    comparison, remainder] using hcomparison.add hremainder

/-- The exact interval branch upper-bounds the true complex power difference
whenever its component intervals enclose the characteristic function,
one-step Rademacher error, and Gaussian reference. -/
theorem rademacherDifferenceIntervals_upper
    {n : ℕ} (hn : 1 ≤ n)
    {f errorToCos cosU cosAbs normalN : DyadicInterval}
    {a : ℂ} {uR normalR : ℝ}
    (hf : f.Contains ‖a‖)
    (herror : errorToCos.Contains ‖a - (Real.cos uR : ℂ)‖)
    (hcos : cosU.Contains (Real.cos uR))
    (hcosAbs : cosAbs.Contains |Real.cos uR|)
    (hnormal : normalN.Contains normalR) :
    ‖a ^ n - (normalR : ℂ)‖ ≤
      (rademacherDifferenceIntervals
        n f errorToCos cosU cosAbs normalN).upper := by
  have hinterval := rademacherDifferenceIntervals_sound (n := n)
    hf herror hcos hcosAbs hnormal (norm_nonneg _) (norm_nonneg _)
  exact (rademacher_power_difference_le hn).trans hinterval.2

/-- Soundness of the three-way minimum `min(1, routeA, rectangular)`. -/
theorem minModulusEnvelope_sound
    {routeA rectangular : DyadicInterval} {x a b : ℝ}
    (ha : routeA.Contains a) (hb : rectangular.Contains b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxa : x ≤ a) (hxb : x ≤ b) :
    (minModulusEnvelope routeA rectangular).Contains x := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hOneScaled : x * (dyadicScale : ℝ) ≤ (dyadicScale : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hx1 hscale.le
  have hAScaled : x * (dyadicScale : ℝ) ≤ (routeA.hi : ℝ) :=
    (le_div_iff₀ hscale).1 (hxa.trans ha.2)
  have hBScaled : x * (dyadicScale : ℝ) ≤ (rectangular.hi : ℝ) :=
    (le_div_iff₀ hscale).1 (hxb.trans hb.2)
  have hmin : x ≤
      ((min dyadicScale (min routeA.hi rectangular.hi) : ℤ) : ℝ) /
        (dyadicScale : ℝ) := by
    apply (le_div_iff₀ hscale).2
    rw [Int.cast_min, Int.cast_min]
    exact le_min hOneScaled (le_min hAScaled hBScaled)
  simpa only [minModulusEnvelope] using
    upperHull_sound hx0 hmin

lemma divPoint_lo_nonneg
    {I : DyadicInterval} (hI : I.Ordered) (hlo : 0 ≤ I.lo)
    {k : ℤ} (hk : 0 < k) :
    0 ≤ (DyadicInterval.divPoint I k).lo := by
  unfold DyadicInterval.divPoint
  rw [if_pos ⟨hI, hk⟩]
  unfold floorDiv
  exact Int.ediv_nonneg hlo hk.le

lemma mulPoint_lo_nonneg
    {I : DyadicInterval} (hI : I.Ordered) (hlo : 0 ≤ I.lo)
    {k : ℤ} (hk : 0 ≤ k) :
    0 ≤ (DyadicInterval.mulPoint k I).lo := by
  unfold DyadicInterval.mulPoint
  rw [if_pos ⟨hk, hI⟩]
  exact mul_nonneg hk hlo

theorem normalOne_sound
    {u : DyadicInterval} {uR : ℝ} (hu : u.Contains uR) :
    (normalOne u).Contains (Real.exp (-(uR ^ 2 / 2))) := by
  let u2 := DyadicInterval.sqr u
  let arg := DyadicInterval.divPoint u2 2
  have hu2 : u2.Contains (uR ^ 2) := by
    simpa only [u2] using hu.sqr hu.ordered
  have harg : arg.Contains (uR ^ 2 / 2) := by
    rw [show arg = DyadicInterval.div u2 (DyadicInterval.point 2) by
      simp only [arg, DyadicInterval.divPoint_eq_div]]
    exact dyadicContains_div_point hu2 2 (by norm_num)
  have hargLo : 0 ≤ arg.lo :=
    divPoint_lo_nonneg hu2.ordered (sqr_lo_nonneg u) (by norm_num)
  simpa only [normalOne, u2, arg] using
    dyadicExpNeg_sound harg hargLo

theorem normalN_sound
    {n : ℕ} {u : DyadicInterval} {uR : ℝ} (hu : u.Contains uR) :
    (normalN n u).Contains
      (Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))) := by
  let u2 := DyadicInterval.sqr u
  let arg := DyadicInterval.divPoint u2 2
  let narg := DyadicInterval.mulPoint (Int.ofNat n) arg
  have hu2 : u2.Contains (uR ^ 2) := by
    simpa only [u2] using hu.sqr hu.ordered
  have harg : arg.Contains (uR ^ 2 / 2) := by
    rw [show arg = DyadicInterval.div u2 (DyadicInterval.point 2) by
      simp only [arg, DyadicInterval.divPoint_eq_div]]
    exact dyadicContains_div_point hu2 2 (by norm_num)
  have hn : (DyadicInterval.point (Int.ofNat n)).Contains (n : ℝ) := by
    simpa using DyadicInterval.contains_point (Int.ofNat n)
  have hnarg : narg.Contains ((n : ℝ) * (uR ^ 2 / 2)) := by
    simpa only [narg, DyadicInterval.mulPoint_eq_mul] using hn.mul harg
  have hargLo : 0 ≤ arg.lo :=
    divPoint_lo_nonneg hu2.ordered (sqr_lo_nonneg u) (by norm_num)
  have hnargLo : 0 ≤ narg.lo :=
    mulPoint_lo_nonneg harg.ordered hargLo (by simp)
  simpa only [normalN, u2, arg, narg] using
    dyadicExpNeg_sound hnarg hnargLo

end

end BerryEsseen
