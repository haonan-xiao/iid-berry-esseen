import BerryEsseen.CharacteristicFunction.BreakpointNumerics
/-!
# Exact dyadic interval arithmetic

This module defines the precision-48 fixed-point interval kernel used by the Route B numerical
certificate.  Rational conversion, addition, negation, subtraction, multiplication, division,
squaring, maximum with zero, and nonnegative square root use exact integer arithmetic with
outward floor/ceiling rounding.  Each public operation is accompanied by a real-semantics
containment theorem; division, squaring, and square root match the corresponding operations in
the supplied exact C++ verifier.
-/

namespace BerryEsseen

def cornerMin (a b c d : ℝ) : ℝ :=
  min (min (a * c) (a * d)) (min (b * c) (b * d))

def cornerMax (a b c d : ℝ) : ℝ :=
  max (max (a * c) (a * d)) (max (b * c) (b * d))

theorem mul_mem_cornerBounds {a b c d x y : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x * y ∈ Set.Icc (cornerMin a b c d) (cornerMax a b c d) := by
  have hlo_ac : cornerMin a b c d ≤ a * c :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hlo_ad : cornerMin a b c d ≤ a * d :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hlo_bc : cornerMin a b c d ≤ b * c :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hlo_bd : cornerMin a b c d ≤ b * d :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hac_hi : a * c ≤ cornerMax a b c d :=
    (le_max_left _ _).trans (le_max_left _ _)
  have had_hi : a * d ≤ cornerMax a b c d :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hbc_hi : b * c ≤ cornerMax a b c d :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hbd_hi : b * d ≤ cornerMax a b c d :=
    (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · by_cases hx0 : 0 ≤ x
    · by_cases hy0 : 0 ≤ y
      · by_cases ha0 : 0 ≤ a
        · by_cases hc0 : 0 ≤ c
          · exact hlo_ac.trans (mul_le_mul hx.1 hy.1 hc0 hx0)
          · have hc : c ≤ 0 := le_of_not_ge hc0
            have hb0 : 0 ≤ b := hx0.trans hx.2
            exact hlo_bc.trans ((mul_nonpos_of_nonneg_of_nonpos hb0 hc).trans
              (mul_nonneg hx0 hy0))
        · have ha : a ≤ 0 := le_of_not_ge ha0
          have hd0 : 0 ≤ d := hy0.trans hy.2
          exact hlo_ad.trans ((mul_nonpos_of_nonpos_of_nonneg ha hd0).trans
            (mul_nonneg hx0 hy0))
      · have hyneg : y ≤ 0 := le_of_not_ge hy0
        have hc : c ≤ 0 := hy.1.trans hyneg
        have hb0 : 0 ≤ b := hx0.trans hx.2
        refine hlo_bc.trans ?_
        calc
          b * c ≤ x * c := mul_le_mul_of_nonpos_right hx.2 hc
          _ ≤ x * y := mul_le_mul_of_nonneg_left hy.1 hx0
    · have hxneg : x ≤ 0 := le_of_not_ge hx0
      by_cases hy0 : 0 ≤ y
      · have ha : a ≤ 0 := hx.1.trans hxneg
        have hd0 : 0 ≤ d := hy0.trans hy.2
        refine hlo_ad.trans ?_
        calc
          a * d ≤ x * d := mul_le_mul_of_nonneg_right hx.1 hd0
          _ ≤ x * y := mul_le_mul_of_nonpos_left hy.2 hxneg
      · have hyneg : y ≤ 0 := le_of_not_ge hy0
        by_cases hb0 : 0 ≤ b
        · have hc : c ≤ 0 := hy.1.trans hyneg
          exact hlo_bc.trans ((mul_nonpos_of_nonneg_of_nonpos hb0 hc).trans
            (mul_nonneg_of_nonpos_of_nonpos hxneg hyneg))
        · have hb : b ≤ 0 := le_of_not_ge hb0
          by_cases hd0 : 0 ≤ d
          · have ha : a ≤ 0 := hx.1.trans hxneg
            exact hlo_ad.trans ((mul_nonpos_of_nonpos_of_nonneg ha hd0).trans
              (mul_nonneg_of_nonpos_of_nonpos hxneg hyneg))
          · have hd : d ≤ 0 := le_of_not_ge hd0
            refine hlo_bd.trans ?_
            calc
              b * d ≤ x * d := mul_le_mul_of_nonpos_right hx.2 hd
              _ ≤ x * y := mul_le_mul_of_nonpos_left hy.2 hxneg
  · by_cases hx0 : 0 ≤ x
    · by_cases hy0 : 0 ≤ y
      · refine le_trans ?_ hbd_hi
        calc
          x * y ≤ b * y := mul_le_mul_of_nonneg_right hx.2 hy0
          _ ≤ b * d := mul_le_mul_of_nonneg_left hy.2 (hx0.trans hx.2)
      · have hyneg : y ≤ 0 := le_of_not_ge hy0
        by_cases ha0 : 0 ≤ a
        · by_cases hd0 : 0 ≤ d
          · have hb0 : 0 ≤ b := hx0.trans hx.2
            exact (mul_nonpos_of_nonneg_of_nonpos hx0 hyneg).trans
              ((mul_nonneg hb0 hd0).trans hbd_hi)
          · have hd : d ≤ 0 := le_of_not_ge hd0
            refine le_trans ?_ had_hi
            calc
              x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 hyneg
              _ ≤ a * d := mul_le_mul_of_nonneg_left hy.2 ha0
        · have ha : a ≤ 0 := le_of_not_ge ha0
          have hc : c ≤ 0 := hy.1.trans hyneg
          exact (mul_nonpos_of_nonneg_of_nonpos hx0 hyneg).trans
            ((mul_nonneg_of_nonpos_of_nonpos ha hc).trans hac_hi)
    · have hxneg : x ≤ 0 := le_of_not_ge hx0
      by_cases hy0 : 0 ≤ y
      · by_cases hc0 : 0 ≤ c
        · by_cases hb0 : 0 ≤ b
          · have hd0 : 0 ≤ d := hy0.trans hy.2
            exact (mul_nonpos_of_nonpos_of_nonneg hxneg hy0).trans
              ((mul_nonneg hb0 hd0).trans hbd_hi)
          · have hb : b ≤ 0 := le_of_not_ge hb0
            refine le_trans ?_ hbc_hi
            calc
              x * y ≤ b * y := mul_le_mul_of_nonneg_right hx.2 hy0
              _ ≤ b * c := mul_le_mul_of_nonpos_left hy.1 hb
        · have hc : c ≤ 0 := le_of_not_ge hc0
          have ha : a ≤ 0 := hx.1.trans hxneg
          exact (mul_nonpos_of_nonpos_of_nonneg hxneg hy0).trans
            ((mul_nonneg_of_nonpos_of_nonpos ha hc).trans hac_hi)
      · have hyneg : y ≤ 0 := le_of_not_ge hy0
        refine le_trans ?_ hac_hi
        calc
          x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 hyneg
          _ ≤ a * c := mul_le_mul_of_nonpos_left hy.1 (hx.1.trans hxneg)

def floorDiv (a b : ℤ) : ℤ := a / b

def ceilDiv (a b : ℤ) : ℤ := -((-a) / b)

theorem floorDiv_mul_le (a : ℤ) {b : ℤ} (hb : 0 < b) :
    floorDiv a b * b ≤ a := by
  exact Int.ediv_mul_le a hb.ne'

theorem le_ceilDiv_mul (a : ℤ) {b : ℤ} (hb : 0 < b) :
    a ≤ ceilDiv a b * b := by
  have h := Int.ediv_mul_le (-a) hb.ne'
  calc
    a = -(-a) := by ring
    _ ≤ -(((-a) / b) * b) := neg_le_neg h
    _ = ceilDiv a b * b := by unfold ceilDiv; ring

theorem floorDiv_cast_le_div (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (floorDiv a b : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  norm_cast
  exact floorDiv_mul_le a hb

theorem div_le_ceilDiv_cast (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (ceilDiv a b : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  norm_cast
  exact le_ceilDiv_mul a hb

def dyadicPrecision : ℕ := 48

def dyadicScale : ℤ := 2 ^ dyadicPrecision

theorem dyadicScale_pos : 0 < dyadicScale := by
  norm_num [dyadicScale, dyadicPrecision]

structure DyadicInterval where
  lo : ℤ
  hi : ℤ
deriving DecidableEq, Repr

namespace DyadicInterval

noncomputable def lower (I : DyadicInterval) : ℝ := (I.lo : ℝ) / (dyadicScale : ℝ)

noncomputable def upper (I : DyadicInterval) : ℝ := (I.hi : ℝ) / (dyadicScale : ℝ)

def Contains (I : DyadicInterval) (x : ℝ) : Prop := x ∈ Set.Icc I.lower I.upper

def Ordered (I : DyadicInterval) : Prop := I.lo ≤ I.hi

def point (a : ℤ) : DyadicInterval := ⟨a * dyadicScale, a * dyadicScale⟩

def ofRat (a b : ℤ) : DyadicInterval :=
  ⟨floorDiv (a * dyadicScale) b, ceilDiv (a * dyadicScale) b⟩

def add (I J : DyadicInterval) : DyadicInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : DyadicInterval) : DyadicInterval := ⟨-I.hi, -I.lo⟩

def sub (I J : DyadicInterval) : DyadicInterval := add I (neg J)

def cornerMinInt (I J : DyadicInterval) : ℤ :=
  min (min (I.lo * J.lo) (I.lo * J.hi))
    (min (I.hi * J.lo) (I.hi * J.hi))

def cornerMaxInt (I J : DyadicInterval) : ℤ :=
  max (max (I.lo * J.lo) (I.lo * J.hi))
    (max (I.hi * J.lo) (I.hi * J.hi))

def mulGeneric (I J : DyadicInterval) : DyadicInterval :=
  ⟨floorDiv (cornerMinInt I J) dyadicScale,
    ceilDiv (cornerMaxInt I J) dyadicScale⟩

/-- Exact multiplication with a two-corner fast path for ordered nonnegative intervals. -/
def mul (I J : DyadicInterval) : DyadicInterval :=
  if 0 ≤ I.lo ∧ I.lo ≤ I.hi ∧ 0 ≤ J.lo ∧ J.lo ≤ J.hi then
    ⟨floorDiv (I.lo * J.lo) dyadicScale,
      ceilDiv (I.hi * J.hi) dyadicScale⟩
  else
    mulGeneric I J

@[simp] theorem mul_eq_generic (I J : DyadicInterval) : mul I J = mulGeneric I J := by
  unfold mul
  split
  · next h =>
      rcases h with ⟨hIlo, hIord, hJlo, hJord⟩
      have hIhi : 0 ≤ I.hi := hIlo.trans hIord
      have hJhi : 0 ≤ J.hi := hJlo.trans hJord
      have hll_lh : I.lo * J.lo ≤ I.lo * J.hi :=
        mul_le_mul_of_nonneg_left hJord hIlo
      have hll_hl : I.lo * J.lo ≤ I.hi * J.lo :=
        mul_le_mul_of_nonneg_right hIord hJlo
      have hhl_hh : I.hi * J.lo ≤ I.hi * J.hi :=
        mul_le_mul_of_nonneg_left hJord hIhi
      have hlh_hh : I.lo * J.hi ≤ I.hi * J.hi :=
        mul_le_mul_of_nonneg_right hIord hJhi
      have hmin : cornerMinInt I J = I.lo * J.lo := by
        unfold cornerMinInt
        rw [min_eq_left hll_lh, min_eq_left hhl_hh, min_eq_left hll_hl]
      have hmax : cornerMaxInt I J = I.hi * J.hi := by
        unfold cornerMaxInt
        rw [max_eq_right hll_lh, max_eq_right hhl_hh, max_eq_right hlh_hh]
      unfold mulGeneric
      rw [hmin, hmax]
  · rfl

theorem floorDiv_mul_scale_exact (a : ℤ) :
    floorDiv (a * dyadicScale) dyadicScale = a := by
  unfold floorDiv
  simpa [mul_comm] using Int.mul_ediv_cancel_left a dyadicScale_pos.ne'

theorem ceilDiv_mul_scale_exact (a : ℤ) :
    ceilDiv (a * dyadicScale) dyadicScale = a := by
  unfold ceilDiv
  rw [show -(a * dyadicScale) = dyadicScale * (-a) by ring]
  rw [Int.mul_ediv_cancel_left (-a) dyadicScale_pos.ne']
  ring

/-- Exact multiplication by an integer point.  The ordered nonnegative branch cancels the
fixed-point scale before evaluation; all other inputs use the canonical interval product. -/
def mulPoint (k : ℤ) (I : DyadicInterval) : DyadicInterval :=
  if 0 ≤ k ∧ I.lo ≤ I.hi then
    ⟨k * I.lo, k * I.hi⟩
  else
    mul (point k) I

@[simp] theorem mulPoint_eq_mul (k : ℤ) (I : DyadicInterval) :
    mulPoint k I = mul (point k) I := by
  unfold mulPoint
  split
  · next h =>
      rcases h with ⟨hk, hI⟩
      rw [mul_eq_generic]
      unfold mulGeneric cornerMinInt cornerMaxInt
      simp only [point]
      have hlo : k * dyadicScale * I.lo ≤ k * dyadicScale * I.hi :=
        mul_le_mul_of_nonneg_left hI (mul_nonneg hk dyadicScale_pos.le)
      rw [min_eq_left hlo, max_eq_right hlo, max_self]
      simp only [min_self]
      rw [show k * dyadicScale * I.lo = (k * I.lo) * dyadicScale by ring,
        show k * dyadicScale * I.hi = (k * I.hi) * dyadicScale by ring,
        floorDiv_mul_scale_exact, ceilDiv_mul_scale_exact]
  · rfl

def inv (I : DyadicInterval) : DyadicInterval :=
  ⟨floorDiv (dyadicScale * dyadicScale) I.hi,
    ceilDiv (dyadicScale * dyadicScale) I.lo⟩

def quotientMinInt (I J : DyadicInterval) : ℤ :=
  min
    (min (floorDiv (I.lo * dyadicScale) J.lo)
      (floorDiv (I.lo * dyadicScale) J.hi))
    (min (floorDiv (I.hi * dyadicScale) J.lo)
      (floorDiv (I.hi * dyadicScale) J.hi))

def quotientMaxInt (I J : DyadicInterval) : ℤ :=
  max
    (max (ceilDiv (I.lo * dyadicScale) J.lo)
      (ceilDiv (I.lo * dyadicScale) J.hi))
    (max (ceilDiv (I.hi * dyadicScale) J.lo)
      (ceilDiv (I.hi * dyadicScale) J.hi))

/-- For a nonnegative numerator, floor division is antitone in a positive denominator. -/
theorem floorDiv_anti_denominator
    {a c d : ℤ} (ha : 0 ≤ a) (hc : 0 < c) (hcd : c ≤ d) :
    floorDiv a d ≤ floorDiv a c := by
  unfold floorDiv
  apply (Int.le_ediv_iff_mul_le hc).2
  have hd : 0 < d := hc.trans_le hcd
  calc
    (a / d) * c ≤ (a / d) * d :=
      mul_le_mul_of_nonneg_left hcd (Int.ediv_nonneg ha hd.le)
    _ ≤ a := Int.ediv_mul_le a hd.ne'

theorem ceilDiv_le_iff_le_mul {a b q : ℤ} (hb : 0 < b) :
    ceilDiv a b ≤ q ↔ a ≤ q * b := by
  unfold ceilDiv
  constructor
  · intro h
    have hneg : -q ≤ (-a) / b := by omega
    have hmul := (Int.le_ediv_iff_mul_le hb).1 hneg
    calc
      a = -(-a) := by ring
      _ ≤ -((-q) * b) := neg_le_neg hmul
      _ = q * b := by ring
  · intro h
    have hmul : (-q) * b ≤ -a := by
      calc
        (-q) * b = -(q * b) := by ring
        _ ≤ -a := neg_le_neg h
    have hneg := (Int.le_ediv_iff_mul_le hb).2 hmul
    omega

theorem ceilDiv_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ ceilDiv a b := by
  unfold ceilDiv
  exact neg_nonneg.mpr
    (Int.ediv_nonpos_of_nonpos_of_neg (neg_nonpos.mpr ha) hb)

theorem ceilDiv_mono_numerator
    {a c b : ℤ} (hac : a ≤ c) (hb : 0 < b) :
    ceilDiv a b ≤ ceilDiv c b := by
  apply (ceilDiv_le_iff_le_mul hb).2
  exact hac.trans (le_ceilDiv_mul c hb)

theorem ceilDiv_anti_denominator
    {a c d : ℤ} (ha : 0 ≤ a) (hc : 0 < c) (hcd : c ≤ d) :
    ceilDiv a d ≤ ceilDiv a c := by
  have hd : 0 < d := hc.trans_le hcd
  apply (ceilDiv_le_iff_le_mul hd).2
  calc
    a ≤ ceilDiv a c * c := le_ceilDiv_mul a hc
    _ ≤ ceilDiv a c * d :=
      mul_le_mul_of_nonneg_left hcd (ceilDiv_nonneg ha hc)

def divGeneric (I J : DyadicInterval) : DyadicInterval :=
  ⟨quotientMinInt I J, quotientMaxInt I J⟩

/-- Four-corner outward-rounded division with an exact two-corner fast path for ordered
nonnegative numerators and ordered positive denominators. -/
def div (I J : DyadicInterval) : DyadicInterval :=
  if 0 ≤ I.lo ∧ I.lo ≤ I.hi ∧ 0 < J.lo ∧ J.lo ≤ J.hi then
    ⟨floorDiv (I.lo * dyadicScale) J.hi,
      ceilDiv (I.hi * dyadicScale) J.lo⟩
  else
    divGeneric I J

@[simp] theorem div_eq_generic (I J : DyadicInterval) : div I J = divGeneric I J := by
  unfold div
  split
  · next h =>
      rcases h with ⟨hIlo, hIord, hJlo, hJord⟩
      have hscale : 0 < dyadicScale := dyadicScale_pos
      have hloNum : 0 ≤ I.lo * dyadicScale := mul_nonneg hIlo hscale.le
      have hhiNum : 0 ≤ I.hi * dyadicScale :=
        mul_nonneg (hIlo.trans hIord) hscale.le
      have hnum : I.lo * dyadicScale ≤ I.hi * dyadicScale :=
        mul_le_mul_of_nonneg_right hIord hscale.le
      have hfloorDen := floorDiv_anti_denominator hloNum hJlo hJord
      have hfloorNumHi :
          floorDiv (I.lo * dyadicScale) J.hi ≤
            floorDiv (I.hi * dyadicScale) J.hi := by
        unfold floorDiv
        exact Int.ediv_le_ediv (hJlo.trans_le hJord) hnum
      have hmin : quotientMinInt I J =
          floorDiv (I.lo * dyadicScale) J.hi := by
        unfold quotientMinInt
        rw [min_eq_right hfloorDen, min_eq_right
          (floorDiv_anti_denominator hhiNum hJlo hJord),
          min_eq_left hfloorNumHi]
      have hceilNum :
          ceilDiv (I.lo * dyadicScale) J.lo ≤
            ceilDiv (I.hi * dyadicScale) J.lo :=
        ceilDiv_mono_numerator hnum hJlo
      have hceilDenLo := ceilDiv_anti_denominator hloNum hJlo hJord
      have hceilDenHi := ceilDiv_anti_denominator hhiNum hJlo hJord
      have hmax : quotientMaxInt I J =
          ceilDiv (I.hi * dyadicScale) J.lo := by
        unfold quotientMaxInt
        rw [max_eq_left hceilDenLo, max_eq_left hceilDenHi,
          max_eq_right hceilNum]
      unfold divGeneric
      rw [hmin, hmax]
  · rfl

theorem floorDiv_mul_scale_cancel (a k : ℤ) :
    floorDiv (a * dyadicScale) (k * dyadicScale) = floorDiv a k := by
  unfold floorDiv
  exact Int.mul_ediv_mul_of_pos_left a k dyadicScale_pos

theorem ceilDiv_mul_scale_cancel (a k : ℤ) :
    ceilDiv (a * dyadicScale) (k * dyadicScale) = ceilDiv a k := by
  unfold ceilDiv
  rw [show -(a * dyadicScale) = (-a) * dyadicScale by ring]
  rw [Int.mul_ediv_mul_of_pos_left (-a) k dyadicScale_pos]

/-- Exact division by an integer point.  For an ordered interval and a positive divisor this
cancels the fixed-point scale before Euclidean division; the fallback is canonical `div`. -/
def divPoint (I : DyadicInterval) (k : ℤ) : DyadicInterval :=
  if I.lo ≤ I.hi ∧ 0 < k then
    ⟨floorDiv I.lo k, ceilDiv I.hi k⟩
  else
    div I (point k)

@[simp] theorem divPoint_eq_div (I : DyadicInterval) (k : ℤ) :
    divPoint I k = div I (point k) := by
  unfold divPoint
  split
  · next h =>
      rcases h with ⟨hI, hk⟩
      rw [div_eq_generic]
      unfold divGeneric quotientMinInt quotientMaxInt
      simp only [point]
      rw [floorDiv_mul_scale_cancel I.lo k,
        floorDiv_mul_scale_cancel I.hi k,
        ceilDiv_mul_scale_cancel I.lo k,
        ceilDiv_mul_scale_cancel I.hi k]
      have hfloor : floorDiv I.lo k ≤ floorDiv I.hi k := by
        unfold floorDiv
        exact Int.ediv_le_ediv hk hI
      have hceil : ceilDiv I.lo k ≤ ceilDiv I.hi k :=
        ceilDiv_mono_numerator hI hk
      rw [min_self, min_self, min_eq_left hfloor,
        max_self, max_self, max_eq_right hceil]
  · rfl

def squareAbsMaxInt (I : DyadicInterval) : ℤ := max (-I.lo) I.hi

def squareAbsMinInt (I : DyadicInterval) : ℤ := min (-I.lo) I.hi

/-- Sign-aware outward-rounded square, matching the exact certificate checker. -/
def sqr (I : DyadicInterval) : DyadicInterval :=
  let hi := ceilDiv (squareAbsMaxInt I * squareAbsMaxInt I) dyadicScale
  if I.lo ≤ 0 ∧ 0 ≤ I.hi then ⟨0, hi⟩
  else
    ⟨floorDiv (squareAbsMinInt I * squareAbsMinInt I) dyadicScale, hi⟩

def maxZero (I : DyadicInterval) : DyadicInterval :=
  ⟨max 0 I.lo, max 0 I.hi⟩

/-- Outward-rounded division by two, used by the exponential range reduction. -/
def half (I : DyadicInterval) : DyadicInterval :=
  ⟨floorDiv I.lo 2, ceilDiv I.hi 2⟩

def sqrtUpperNat (n : ℕ) : ℕ :=
  let r := Nat.sqrt n
  if r * r = n then r else r + 1

def sqrt (I : DyadicInterval) : DyadicInterval :=
  ⟨Int.ofNat (Nat.sqrt (Int.toNat (I.lo * dyadicScale))),
    Int.ofNat (sqrtUpperNat (Int.toNat (I.hi * dyadicScale)))⟩

theorem le_sqrtUpperNat_sq (n : ℕ) :
    n ≤ sqrtUpperNat n * sqrtUpperNat n := by
  by_cases h : Nat.sqrt n * Nat.sqrt n = n
  · simp [sqrtUpperNat, h]
  · simpa [sqrtUpperNat, h, Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt n).le

theorem contains_point (a : ℤ) : (point a).Contains (a : ℝ) := by
  constructor <;> simp [lower, upper, point, dyadicScale_pos.ne']

theorem contains_ofRat (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (ofRat a b).Contains ((a : ℝ) / (b : ℝ)) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hlo := floorDiv_cast_le_div (a * dyadicScale) hb
  have hhi := div_le_ceilDiv_cast (a * dyadicScale) hb
  constructor
  · dsimp only [Contains, lower, ofRat]
    rw [div_le_iff₀ hscale]
    calc
      (floorDiv (a * dyadicScale) b : ℝ) ≤
          ((a * dyadicScale : ℤ) : ℝ) / (b : ℝ) := hlo
      _ = (a : ℝ) / (b : ℝ) * (dyadicScale : ℝ) := by
        push_cast
        ring
  · dsimp only [Contains, upper, ofRat]
    rw [le_div_iff₀ hscale]
    calc
      (a : ℝ) / (b : ℝ) * (dyadicScale : ℝ) =
          ((a * dyadicScale : ℤ) : ℝ) / (b : ℝ) := by
        push_cast
        ring
      _ ≤ (ceilDiv (a * dyadicScale) b : ℝ) := hhi

theorem Contains.ordered {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) : I.Ordered := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hreal : (I.lo : ℝ) ≤ (I.hi : ℝ) := by
    exact (div_le_div_iff_of_pos_right hscale).1 (hx.1.trans hx.2)
  exact_mod_cast hreal

theorem contains_lower {I : DyadicInterval} (hI : I.Ordered) : I.Contains I.lower := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  exact ⟨le_rfl, (div_le_div_iff_of_pos_right hscale).2 (by exact_mod_cast hI)⟩

theorem contains_upper {I : DyadicInterval} (hI : I.Ordered) : I.Contains I.upper := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  exact ⟨(div_le_div_iff_of_pos_right hscale).2 (by exact_mod_cast hI), le_rfl⟩

theorem Contains.add {I J : DyadicInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  constructor
  · simpa only [lower, DyadicInterval.add, Int.cast_add, add_div] using
      add_le_add hx.1 hy.1
  · simpa only [upper, DyadicInterval.add, Int.cast_add, add_div] using
      add_le_add hx.2 hy.2

theorem Contains.neg {I : DyadicInterval} {x : ℝ}
    (hx : I.Contains x) : (neg I).Contains (-x) := by
  constructor
  · simpa only [lower, upper, DyadicInterval.neg, Int.cast_neg, neg_div] using
      neg_le_neg hx.2
  · simpa only [lower, upper, DyadicInterval.neg, Int.cast_neg, neg_div] using
      neg_le_neg hx.1

theorem Contains.sub {I J : DyadicInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (sub I J).Contains (x - y) := by
  simpa only [sub, sub_eq_add_neg] using hx.add hy.neg

theorem floorDiv_scaled_product_le {m p q : ℤ} (hm : m ≤ p * q) :
    (floorDiv m dyadicScale : ℝ) / (dyadicScale : ℝ) ≤
      ((p : ℝ) / (dyadicScale : ℝ)) * ((q : ℝ) / (dyadicScale : ℝ)) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hf := floorDiv_cast_le_div m dyadicScale_pos
  calc
    (floorDiv m dyadicScale : ℝ) / (dyadicScale : ℝ) ≤
        ((m : ℝ) / (dyadicScale : ℝ)) / (dyadicScale : ℝ) :=
      (div_le_div_iff_of_pos_right hscale).2 hf
    _ = (m : ℝ) / ((dyadicScale : ℝ) * (dyadicScale : ℝ)) := by ring
    _ ≤ ((p * q : ℤ) : ℝ) / ((dyadicScale : ℝ) * (dyadicScale : ℝ)) := by
      apply (div_le_div_iff_of_pos_right (mul_pos hscale hscale)).2
      exact_mod_cast hm
    _ = ((p : ℝ) / (dyadicScale : ℝ)) * ((q : ℝ) / (dyadicScale : ℝ)) := by
      push_cast
      ring

theorem scaled_product_le_ceilDiv {m p q : ℤ} (hm : p * q ≤ m) :
    ((p : ℝ) / (dyadicScale : ℝ)) * ((q : ℝ) / (dyadicScale : ℝ)) ≤
      (ceilDiv m dyadicScale : ℝ) / (dyadicScale : ℝ) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hc := div_le_ceilDiv_cast m dyadicScale_pos
  calc
    ((p : ℝ) / (dyadicScale : ℝ)) * ((q : ℝ) / (dyadicScale : ℝ)) =
        ((p * q : ℤ) : ℝ) / ((dyadicScale : ℝ) * (dyadicScale : ℝ)) := by
      push_cast
      ring
    _ ≤ (m : ℝ) / ((dyadicScale : ℝ) * (dyadicScale : ℝ)) := by
      apply (div_le_div_iff_of_pos_right (mul_pos hscale hscale)).2
      exact_mod_cast hm
    _ = ((m : ℝ) / (dyadicScale : ℝ)) / (dyadicScale : ℝ) := by ring
    _ ≤ (ceilDiv m dyadicScale : ℝ) / (dyadicScale : ℝ) :=
      (div_le_div_iff_of_pos_right hscale).2 hc

theorem floorDiv_scaled_quotient_le {p q : ℤ} (hq : 0 < q) :
    (floorDiv (p * dyadicScale) q : ℝ) / (dyadicScale : ℝ) ≤
      (p : ℝ) / (q : ℝ) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hqReal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hround := floorDiv_cast_le_div (p * dyadicScale) hq
  calc
    (floorDiv (p * dyadicScale) q : ℝ) / (dyadicScale : ℝ) ≤
        (((p * dyadicScale : ℤ) : ℝ) / (q : ℝ)) /
          (dyadicScale : ℝ) :=
      (div_le_div_iff_of_pos_right hscale).2 hround
    _ = (p : ℝ) / (q : ℝ) := by
      push_cast
      field_simp [hscale.ne', hqReal.ne']

theorem quotient_le_ceilDiv_scaled {p q : ℤ} (hq : 0 < q) :
    (p : ℝ) / (q : ℝ) ≤
      (ceilDiv (p * dyadicScale) q : ℝ) / (dyadicScale : ℝ) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hqReal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hround := div_le_ceilDiv_cast (p * dyadicScale) hq
  calc
    (p : ℝ) / (q : ℝ) =
        (((p * dyadicScale : ℤ) : ℝ) / (q : ℝ)) /
          (dyadicScale : ℝ) := by
      push_cast
      field_simp [hscale.ne', hqReal.ne']
    _ ≤ (ceilDiv (p * dyadicScale) q : ℝ) / (dyadicScale : ℝ) :=
      (div_le_div_iff_of_pos_right hscale).2 hround

theorem scaled_mul_inv_scaled (p : ℤ) {q : ℤ} (hq : q ≠ 0) :
    ((p : ℝ) / (dyadicScale : ℝ)) *
        (((q : ℝ) / (dyadicScale : ℝ))⁻¹) =
      (p : ℝ) / (q : ℝ) := by
  have hscale : (dyadicScale : ℝ) ≠ 0 := by exact_mod_cast dyadicScale_pos.ne'
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  field_simp [hscale, hqReal]

theorem div_lower_le_cornerMin (I J : DyadicInterval)
    (hloPos : 0 < J.lo) (hordered : J.Ordered) :
    (DyadicInterval.div I J).lower ≤
      cornerMin I.lower I.upper J.upper⁻¹ J.lower⁻¹ := by
  have hhiPos : 0 < J.hi := hloPos.trans_le hordered
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  rw [div_eq_generic]
  change (quotientMinInt I J : ℝ) / (dyadicScale : ℝ) ≤
    cornerMin I.lower I.upper J.upper⁻¹ J.lower⁻¹
  unfold cornerMin
  refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
  · calc
      (quotientMinInt I J : ℝ) / (dyadicScale : ℝ) ≤
          (floorDiv (I.lo * dyadicScale) J.hi : ℝ) /
            (dyadicScale : ℝ) := by
        apply (div_le_div_iff_of_pos_right hscale).2
        exact_mod_cast
          (min_le_of_left_le (min_le_right
            (floorDiv (I.lo * dyadicScale) J.lo)
            (floorDiv (I.lo * dyadicScale) J.hi)) :
            quotientMinInt I J ≤ floorDiv (I.lo * dyadicScale) J.hi)
      _ ≤ (I.lo : ℝ) / (J.hi : ℝ) := floorDiv_scaled_quotient_le hhiPos
      _ = I.lower * J.upper⁻¹ := by
        exact (scaled_mul_inv_scaled I.lo hhiPos.ne').symm
  · calc
      (quotientMinInt I J : ℝ) / (dyadicScale : ℝ) ≤
          (floorDiv (I.lo * dyadicScale) J.lo : ℝ) /
            (dyadicScale : ℝ) := by
        apply (div_le_div_iff_of_pos_right hscale).2
        exact_mod_cast
          (min_le_of_left_le (min_le_left
            (floorDiv (I.lo * dyadicScale) J.lo)
            (floorDiv (I.lo * dyadicScale) J.hi)) :
            quotientMinInt I J ≤ floorDiv (I.lo * dyadicScale) J.lo)
      _ ≤ (I.lo : ℝ) / (J.lo : ℝ) := floorDiv_scaled_quotient_le hloPos
      _ = I.lower * J.lower⁻¹ := by
        exact (scaled_mul_inv_scaled I.lo hloPos.ne').symm
  · calc
      (quotientMinInt I J : ℝ) / (dyadicScale : ℝ) ≤
          (floorDiv (I.hi * dyadicScale) J.hi : ℝ) /
            (dyadicScale : ℝ) := by
        apply (div_le_div_iff_of_pos_right hscale).2
        exact_mod_cast
          (min_le_of_right_le (min_le_right
            (floorDiv (I.hi * dyadicScale) J.lo)
            (floorDiv (I.hi * dyadicScale) J.hi)) :
            quotientMinInt I J ≤ floorDiv (I.hi * dyadicScale) J.hi)
      _ ≤ (I.hi : ℝ) / (J.hi : ℝ) := floorDiv_scaled_quotient_le hhiPos
      _ = I.upper * J.upper⁻¹ := by
        exact (scaled_mul_inv_scaled I.hi hhiPos.ne').symm
  · calc
      (quotientMinInt I J : ℝ) / (dyadicScale : ℝ) ≤
          (floorDiv (I.hi * dyadicScale) J.lo : ℝ) /
            (dyadicScale : ℝ) := by
        apply (div_le_div_iff_of_pos_right hscale).2
        exact_mod_cast
          (min_le_of_right_le (min_le_left
            (floorDiv (I.hi * dyadicScale) J.lo)
            (floorDiv (I.hi * dyadicScale) J.hi)) :
            quotientMinInt I J ≤ floorDiv (I.hi * dyadicScale) J.lo)
      _ ≤ (I.hi : ℝ) / (J.lo : ℝ) := floorDiv_scaled_quotient_le hloPos
      _ = I.upper * J.lower⁻¹ := by
        exact (scaled_mul_inv_scaled I.hi hloPos.ne').symm

theorem cornerMax_le_div_upper (I J : DyadicInterval)
    (hloPos : 0 < J.lo) (hordered : J.Ordered) :
    cornerMax I.lower I.upper J.upper⁻¹ J.lower⁻¹ ≤
      (DyadicInterval.div I J).upper := by
  have hhiPos : 0 < J.hi := hloPos.trans_le hordered
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  rw [div_eq_generic]
  change cornerMax I.lower I.upper J.upper⁻¹ J.lower⁻¹ ≤
    (quotientMaxInt I J : ℝ) / (dyadicScale : ℝ)
  unfold cornerMax
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · calc
      I.lower * J.upper⁻¹ = (I.lo : ℝ) / (J.hi : ℝ) :=
        scaled_mul_inv_scaled I.lo hhiPos.ne'
      _ ≤ (ceilDiv (I.lo * dyadicScale) J.hi : ℝ) /
            (dyadicScale : ℝ) := quotient_le_ceilDiv_scaled hhiPos
      _ ≤ (quotientMaxInt I J : ℝ) / (dyadicScale : ℝ) := by
        apply (div_le_div_iff_of_pos_right hscale).2
        exact_mod_cast
          (le_max_of_le_left (le_max_right
            (ceilDiv (I.lo * dyadicScale) J.lo)
            (ceilDiv (I.lo * dyadicScale) J.hi)) :
            ceilDiv (I.lo * dyadicScale) J.hi ≤ quotientMaxInt I J)
  · calc
      I.lower * J.lower⁻¹ = (I.lo : ℝ) / (J.lo : ℝ) :=
        scaled_mul_inv_scaled I.lo hloPos.ne'
      _ ≤ (ceilDiv (I.lo * dyadicScale) J.lo : ℝ) /
            (dyadicScale : ℝ) := quotient_le_ceilDiv_scaled hloPos
      _ ≤ (quotientMaxInt I J : ℝ) / (dyadicScale : ℝ) := by
        apply (div_le_div_iff_of_pos_right hscale).2
        exact_mod_cast
          (le_max_of_le_left (le_max_left
            (ceilDiv (I.lo * dyadicScale) J.lo)
            (ceilDiv (I.lo * dyadicScale) J.hi)) :
            ceilDiv (I.lo * dyadicScale) J.lo ≤ quotientMaxInt I J)
  · calc
      I.upper * J.upper⁻¹ = (I.hi : ℝ) / (J.hi : ℝ) :=
        scaled_mul_inv_scaled I.hi hhiPos.ne'
      _ ≤ (ceilDiv (I.hi * dyadicScale) J.hi : ℝ) /
            (dyadicScale : ℝ) := quotient_le_ceilDiv_scaled hhiPos
      _ ≤ (quotientMaxInt I J : ℝ) / (dyadicScale : ℝ) := by
        apply (div_le_div_iff_of_pos_right hscale).2
        exact_mod_cast
          (le_max_of_le_right (le_max_right
            (ceilDiv (I.hi * dyadicScale) J.lo)
            (ceilDiv (I.hi * dyadicScale) J.hi)) :
            ceilDiv (I.hi * dyadicScale) J.hi ≤ quotientMaxInt I J)
  · calc
      I.upper * J.lower⁻¹ = (I.hi : ℝ) / (J.lo : ℝ) :=
        scaled_mul_inv_scaled I.hi hloPos.ne'
      _ ≤ (ceilDiv (I.hi * dyadicScale) J.lo : ℝ) /
            (dyadicScale : ℝ) := quotient_le_ceilDiv_scaled hloPos
      _ ≤ (quotientMaxInt I J : ℝ) / (dyadicScale : ℝ) := by
        apply (div_le_div_iff_of_pos_right hscale).2
        exact_mod_cast
          (le_max_of_le_right (le_max_left
            (ceilDiv (I.hi * dyadicScale) J.lo)
            (ceilDiv (I.hi * dyadicScale) J.hi)) :
            ceilDiv (I.hi * dyadicScale) J.lo ≤ quotientMaxInt I J)

theorem mul_lower_le_cornerMin (I J : DyadicInterval) :
    (mul I J).lower ≤ cornerMin I.lower I.upper J.lower J.upper := by
  rw [mul_eq_generic]
  change (floorDiv (cornerMinInt I J) dyadicScale : ℝ) / (dyadicScale : ℝ) ≤
    cornerMin I.lower I.upper J.lower J.upper
  unfold cornerMin lower upper
  refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
  · exact floorDiv_scaled_product_le (m := cornerMinInt I J) (p := I.lo) (q := J.lo)
      (min_le_of_left_le (min_le_left _ _))
  · exact floorDiv_scaled_product_le (m := cornerMinInt I J) (p := I.lo) (q := J.hi)
      (min_le_of_left_le (min_le_right _ _))
  · exact floorDiv_scaled_product_le (m := cornerMinInt I J) (p := I.hi) (q := J.lo)
      (min_le_of_right_le (min_le_left _ _))
  · exact floorDiv_scaled_product_le (m := cornerMinInt I J) (p := I.hi) (q := J.hi)
      (min_le_of_right_le (min_le_right _ _))

theorem cornerMax_le_mul_upper (I J : DyadicInterval) :
    cornerMax I.lower I.upper J.lower J.upper ≤ (mul I J).upper := by
  rw [mul_eq_generic]
  change cornerMax I.lower I.upper J.lower J.upper ≤
    (ceilDiv (cornerMaxInt I J) dyadicScale : ℝ) / (dyadicScale : ℝ)
  unfold cornerMax lower upper
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · exact scaled_product_le_ceilDiv (m := cornerMaxInt I J) (p := I.lo) (q := J.lo)
      (le_max_of_le_left (le_max_left _ _))
  · exact scaled_product_le_ceilDiv (m := cornerMaxInt I J) (p := I.lo) (q := J.hi)
      (le_max_of_le_left (le_max_right _ _))
  · exact scaled_product_le_ceilDiv (m := cornerMaxInt I J) (p := I.hi) (q := J.lo)
      (le_max_of_le_right (le_max_left _ _))
  · exact scaled_product_le_ceilDiv (m := cornerMaxInt I J) (p := I.hi) (q := J.hi)
      (le_max_of_le_right (le_max_right _ _))

theorem Contains.mul {I J : DyadicInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (DyadicInterval.mul I J).Contains (x * y) := by
  have hcorner := mul_mem_cornerBounds hx hy
  exact ⟨(mul_lower_le_cornerMin I J).trans hcorner.1,
    hcorner.2.trans (cornerMax_le_mul_upper I J)⟩

theorem Contains.inv {I : DyadicInterval} {x : ℝ}
    (hordered : I.Ordered) (hloPos : 0 < I.lo) (hx : I.Contains x) :
    (DyadicInterval.inv I).Contains x⁻¹ := by
  have hhiPos : 0 < I.hi := lt_of_lt_of_le hloPos hordered
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hlowerPos : 0 < I.lower := div_pos (by exact_mod_cast hloPos) hscale
  have hupperPos : 0 < I.upper := div_pos (by exact_mod_cast hhiPos) hscale
  have hxPos : 0 < x := hlowerPos.trans_le hx.1
  have hloRat := (contains_ofRat dyadicScale hhiPos).1
  have hhiRat := (contains_ofRat dyadicScale hloPos).2
  constructor
  · have hendpoint : (DyadicInterval.inv I).lower ≤ I.upper⁻¹ := by
      calc
        (DyadicInterval.inv I).lower =
            (ofRat dyadicScale I.hi).lower := by
          rfl
        _ ≤ (dyadicScale : ℝ) / (I.hi : ℝ) := hloRat
        _ = I.upper⁻¹ := by
          unfold upper
          field_simp
    exact hendpoint.trans ((inv_le_inv₀ hupperPos hxPos).2 hx.2)
  · have hactual : x⁻¹ ≤ I.lower⁻¹ := (inv_le_inv₀ hxPos hlowerPos).2 hx.1
    have hendpoint : I.lower⁻¹ ≤ (DyadicInterval.inv I).upper := by
      calc
        I.lower⁻¹ = (dyadicScale : ℝ) / (I.lo : ℝ) := by
          unfold lower
          field_simp
        _ ≤ (ofRat dyadicScale I.lo).upper := hhiRat
        _ = (DyadicInterval.inv I).upper := by rfl
    exact hactual.trans hendpoint

theorem Contains.div {I J : DyadicInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y)
    (hordered : J.Ordered) (hloPos : 0 < J.lo) :
    (DyadicInterval.div I J).Contains (x / y) := by
  have hhiPos : 0 < J.hi := hloPos.trans_le hordered
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hlowerPos : 0 < J.lower := div_pos (by exact_mod_cast hloPos) hscale
  have hupperPos : 0 < J.upper := div_pos (by exact_mod_cast hhiPos) hscale
  have hyPos : 0 < y := hlowerPos.trans_le hy.1
  have hyInv : y⁻¹ ∈ Set.Icc J.upper⁻¹ J.lower⁻¹ :=
    ⟨(inv_le_inv₀ hupperPos hyPos).2 hy.2,
      (inv_le_inv₀ hyPos hlowerPos).2 hy.1⟩
  have hcorner := mul_mem_cornerBounds hx hyInv
  constructor
  · simpa only [div_eq_mul_inv] using
      (div_lower_le_cornerMin I J hloPos hordered).trans hcorner.1
  · simpa only [div_eq_mul_inv] using
      hcorner.2.trans (cornerMax_le_div_upper I J hloPos hordered)

theorem Contains.sqr {I : DyadicInterval} {x : ℝ}
    (hordered : I.Ordered) (hx : I.Contains x) :
    (DyadicInterval.sqr I).Contains (x ^ 2) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  let m : ℤ := squareAbsMaxInt I
  have hupperM : I.upper ≤ (m : ℝ) / (dyadicScale : ℝ) := by
    apply (div_le_div_iff_of_pos_right hscale).2
    exact_mod_cast (le_max_right (-I.lo) I.hi)
  have hnegLowerM : -I.lower ≤ (m : ℝ) / (dyadicScale : ℝ) := by
    rw [show -I.lower = ((-I.lo : ℤ) : ℝ) / (dyadicScale : ℝ) by
      unfold lower
      push_cast
      ring]
    apply (div_le_div_iff_of_pos_right hscale).2
    exact_mod_cast (le_max_left (-I.lo) I.hi)
  have hminusMLeX : -((m : ℝ) / (dyadicScale : ℝ)) ≤ x := by
    have : -x ≤ (m : ℝ) / (dyadicScale : ℝ) :=
      (neg_le_neg hx.1).trans hnegLowerM
    linarith
  have hxLeM : x ≤ (m : ℝ) / (dyadicScale : ℝ) := hx.2.trans hupperM
  have hxSqLeMSq : x ^ 2 ≤ ((m : ℝ) / (dyadicScale : ℝ)) ^ 2 :=
    sq_le_sq' hminusMLeX hxLeM
  have hMSqRound :
      ((m : ℝ) / (dyadicScale : ℝ)) ^ 2 ≤
        (ceilDiv (m * m) dyadicScale : ℝ) / (dyadicScale : ℝ) := by
    simpa only [pow_two] using
      (scaled_product_le_ceilDiv (m := m * m) (p := m) (q := m) le_rfl)
  have hsqrUpper : x ^ 2 ≤
      (ceilDiv (squareAbsMaxInt I * squareAbsMaxInt I) dyadicScale : ℝ) /
        (dyadicScale : ℝ) := by
    simpa only [m] using hxSqLeMSq.trans hMSqRound
  by_cases hcross : I.lo ≤ 0 ∧ 0 ≤ I.hi
  · constructor
    · simpa [DyadicInterval.sqr, hcross, lower] using (sq_nonneg x)
    · simpa [DyadicInterval.sqr, hcross, upper] using hsqrUpper
  · by_cases hloPos : 0 < I.lo
    · have hhiPos : 0 < I.hi := hloPos.trans_le hordered
      have hmin : squareAbsMinInt I = -I.lo := by
        unfold squareAbsMinInt
        rw [min_eq_left]
        linarith
      have hround :
          (floorDiv
              (squareAbsMinInt I * squareAbsMinInt I) dyadicScale : ℝ) /
              (dyadicScale : ℝ) ≤ I.lower ^ 2 := by
        calc
          (floorDiv
              (squareAbsMinInt I * squareAbsMinInt I) dyadicScale : ℝ) /
                (dyadicScale : ℝ) ≤
              ((squareAbsMinInt I : ℝ) / (dyadicScale : ℝ)) *
                ((squareAbsMinInt I : ℝ) / (dyadicScale : ℝ)) :=
            floorDiv_scaled_product_le le_rfl
          _ = I.lower ^ 2 := by
            rw [hmin]
            unfold lower
            push_cast
            ring
      have hlowerNonneg : 0 ≤ I.lower :=
        (div_nonneg (by exact_mod_cast hloPos.le) hscale.le)
      have hxNonneg : 0 ≤ x := hlowerNonneg.trans hx.1
      have hlowerSq : I.lower ^ 2 ≤ x ^ 2 :=
        (sq_le_sq₀ hlowerNonneg hxNonneg).2 hx.1
      constructor
      · simpa [DyadicInterval.sqr, hcross, lower] using hround.trans hlowerSq
      · simpa [DyadicInterval.sqr, hcross, upper] using hsqrUpper
    · have hloNonpos : I.lo ≤ 0 := le_of_not_gt hloPos
      have hhiNeg : I.hi < 0 := by
        exact lt_of_not_ge (fun hhiNonneg => hcross ⟨hloNonpos, hhiNonneg⟩)
      have hmin : squareAbsMinInt I = I.hi := by
        unfold squareAbsMinInt
        rw [min_eq_right]
        linarith
      have hround :
          (floorDiv
              (squareAbsMinInt I * squareAbsMinInt I) dyadicScale : ℝ) /
              (dyadicScale : ℝ) ≤ I.upper ^ 2 := by
        calc
          (floorDiv
              (squareAbsMinInt I * squareAbsMinInt I) dyadicScale : ℝ) /
                (dyadicScale : ℝ) ≤
              ((squareAbsMinInt I : ℝ) / (dyadicScale : ℝ)) *
                ((squareAbsMinInt I : ℝ) / (dyadicScale : ℝ)) :=
            floorDiv_scaled_product_le le_rfl
          _ = I.upper ^ 2 := by
            rw [hmin]
            unfold upper
            ring
      have hupperNonpos : I.upper ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hhiNeg.le) hscale.le
      have hxNonpos : x ≤ 0 := hx.2.trans hupperNonpos
      have hupperSq : I.upper ^ 2 ≤ x ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonpos hupperNonpos, abs_of_nonpos hxNonpos] using
          neg_le_neg hx.2
      constructor
      · simpa [DyadicInterval.sqr, hcross, lower] using hround.trans hupperSq
      · simpa [DyadicInterval.sqr, hcross, upper] using hsqrUpper

theorem Contains.maxZero {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) :
    (DyadicInterval.maxZero I).Contains (max 0 x) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  constructor
  · change ((max 0 I.lo : ℤ) : ℝ) / (dyadicScale : ℝ) ≤ max 0 x
    rw [Int.cast_max, Int.cast_zero, ← max_div_div_right hscale.le, zero_div]
    exact max_le_max le_rfl hx.1
  · change max 0 x ≤ ((max 0 I.hi : ℤ) : ℝ) / (dyadicScale : ℝ)
    rw [Int.cast_max, Int.cast_zero, ← max_div_div_right hscale.le, zero_div]
    exact max_le_max le_rfl hx.2

theorem Contains.half {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) :
    (DyadicInterval.half I).Contains (x / 2) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hloRound := floorDiv_cast_le_div I.lo (by norm_num : (0 : ℤ) < 2)
  have hhiRound := div_le_ceilDiv_cast I.hi (by norm_num : (0 : ℤ) < 2)
  constructor
  · change (floorDiv I.lo 2 : ℝ) / (dyadicScale : ℝ) ≤ x / 2
    calc
      (floorDiv I.lo 2 : ℝ) / (dyadicScale : ℝ) ≤
          ((I.lo : ℝ) / 2) / (dyadicScale : ℝ) :=
        (div_le_div_iff_of_pos_right hscale).2 hloRound
      _ = I.lower / 2 := by
        unfold lower
        ring
      _ ≤ x / 2 := by linarith [hx.1]
  · change x / 2 ≤ (ceilDiv I.hi 2 : ℝ) / (dyadicScale : ℝ)
    calc
      x / 2 ≤ I.upper / 2 := by linarith [hx.2]
      _ = ((I.hi : ℝ) / 2) / (dyadicScale : ℝ) := by
        unfold upper
        ring
      _ ≤ (ceilDiv I.hi 2 : ℝ) / (dyadicScale : ℝ) :=
        (div_le_div_iff_of_pos_right hscale).2 hhiRound

theorem Contains.sqrt {I : DyadicInterval} {x : ℝ}
    (hordered : I.Ordered) (hlo : 0 ≤ I.lo) (hx : I.Contains x) :
    (DyadicInterval.sqrt I).Contains (Real.sqrt x) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hscaleInt : (0 : ℤ) ≤ dyadicScale := dyadicScale_pos.le
  have hhi : 0 ≤ I.hi := hlo.trans hordered
  have hloMul : 0 ≤ I.lo * dyadicScale := mul_nonneg hlo hscaleInt
  have hhiMul : 0 ≤ I.hi * dyadicScale := mul_nonneg hhi hscaleInt
  let nlo : ℕ := Int.toNat (I.lo * dyadicScale)
  let nhi : ℕ := Int.toNat (I.hi * dyadicScale)
  have hnloCast : (nlo : ℝ) = (I.lo : ℝ) * (dyadicScale : ℝ) := by
    have hnloInt : (nlo : ℤ) = I.lo * dyadicScale := by
      exact Int.toNat_of_nonneg hloMul
    exact_mod_cast hnloInt
  have hnhiCast : (nhi : ℝ) = (I.hi : ℝ) * (dyadicScale : ℝ) := by
    have hnhiInt : (nhi : ℤ) = I.hi * dyadicScale := by
      exact Int.toNat_of_nonneg hhiMul
    exact_mod_cast hnhiInt
  have hloNat := Nat.sqrt_le nlo
  have hloReal :
      (Nat.sqrt nlo : ℝ) * (Nat.sqrt nlo : ℝ) ≤
        (I.lo : ℝ) * (dyadicScale : ℝ) := by
    have : (Nat.sqrt nlo : ℝ) * (Nat.sqrt nlo : ℝ) ≤ (nlo : ℝ) := by
      exact_mod_cast hloNat
    simpa only [hnloCast] using this
  have hhiNat := le_sqrtUpperNat_sq nhi
  have hhiReal :
      (I.hi : ℝ) * (dyadicScale : ℝ) ≤
        (sqrtUpperNat nhi : ℝ) * (sqrtUpperNat nhi : ℝ) := by
    have : (nhi : ℝ) ≤
        (sqrtUpperNat nhi : ℝ) * (sqrtUpperNat nhi : ℝ) := by
      exact_mod_cast hhiNat
    simpa only [hnhiCast] using this
  constructor
  · change
      (Nat.sqrt nlo : ℝ) / (dyadicScale : ℝ) ≤ Real.sqrt x
    apply Real.le_sqrt_of_sq_le
    calc
      ((Nat.sqrt nlo : ℝ) / (dyadicScale : ℝ)) ^ 2 =
          ((Nat.sqrt nlo : ℝ) * (Nat.sqrt nlo : ℝ)) /
            ((dyadicScale : ℝ) * (dyadicScale : ℝ)) := by ring
      _ ≤ ((I.lo : ℝ) * (dyadicScale : ℝ)) /
            ((dyadicScale : ℝ) * (dyadicScale : ℝ)) :=
        (div_le_div_iff_of_pos_right (mul_pos hscale hscale)).2 hloReal
      _ = I.lower := by
        unfold lower
        field_simp [hscale.ne']
      _ ≤ x := hx.1
  · change Real.sqrt x ≤
      (sqrtUpperNat nhi : ℝ) / (dyadicScale : ℝ)
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        x ≤ I.upper := hx.2
        _ = ((I.hi : ℝ) * (dyadicScale : ℝ)) /
              ((dyadicScale : ℝ) * (dyadicScale : ℝ)) := by
          unfold upper
          field_simp [hscale.ne']
        _ ≤ ((sqrtUpperNat nhi : ℝ) * (sqrtUpperNat nhi : ℝ)) /
              ((dyadicScale : ℝ) * (dyadicScale : ℝ)) :=
          (div_le_div_iff_of_pos_right (mul_pos hscale hscale)).2 hhiReal
        _ = ((sqrtUpperNat nhi : ℝ) / (dyadicScale : ℝ)) ^ 2 := by ring

end DyadicInterval

end BerryEsseen
