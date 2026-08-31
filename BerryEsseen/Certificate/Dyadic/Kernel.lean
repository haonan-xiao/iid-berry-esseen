import BerryEsseen.Certificate.Dyadic.Cotangent
import BerryEsseen.Smoothing.PrawitzKernelEnvelopes
/-!
# Verifier-matching dyadic Prawitz-kernel envelopes

This module implements the exact checker's `k0up`, `kd2up`, and `kh2up` expressions with the
same outward-rounded operation order.  Its soundness theorems connect their upper endpoints to
the real Prawitz-kernel norms needed by the three Route B Darboux integrals.
-/

namespace BerryEsseen

open DyadicInterval

def dyadicPrawitzK0Upper (t : DyadicInterval) : DyadicInterval :=
  let x := DyadicInterval.mul checkerPi t
  let a := DyadicInterval.mul x (DyadicInterval.sub (DyadicInterval.point 1) t)
  let dl := dyadicCotGapLower x
  let du := dyadicCotGapUpper t
  let rad := DyadicInterval.sub
    (DyadicInterval.add (DyadicInterval.point 1)
      (DyadicInterval.mul (DyadicInterval.sqr a)
        (DyadicInterval.add (DyadicInterval.point 1) (DyadicInterval.sqr du))))
    (DyadicInterval.mul (DyadicInterval.point 2) (DyadicInterval.mul a dl))
  DyadicInterval.div (DyadicInterval.sqrt (DyadicInterval.maxZero rad))
    (DyadicInterval.mul (DyadicInterval.point 2) checkerPi)

def dyadicPrawitzKD2Upper (t : DyadicInterval) : DyadicInterval :=
  let du := dyadicCotGapUpper t
  DyadicInterval.mul (DyadicInterval.sub (DyadicInterval.point 1) t)
    (DyadicInterval.add (DyadicInterval.point 1)
      (DyadicInterval.div (DyadicInterval.sqr du) (DyadicInterval.point 2)))

def dyadicPrawitzKH2Upper (t : DyadicInterval) : DyadicInterval :=
  let u := DyadicInterval.sub (DyadicInterval.point 1) t
  let du := dyadicCotGapUpper u
  DyadicInterval.mul u
    (DyadicInterval.sqrt
      (DyadicInterval.add (DyadicInterval.point 1) (DyadicInterval.sqr du)))

theorem dyadicPrawitzK0Upper_sound {t : DyadicInterval} {s : ℝ}
    (ht : t.Contains s)
    (hCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr t))).lo) :
    (dyadicPrawitzK0Upper t).Contains (prawitzK0Envelope s) := by
  let x := DyadicInterval.mul checkerPi t
  let a := DyadicInterval.mul x (DyadicInterval.sub (DyadicInterval.point 1) t)
  let dl := dyadicCotGapLower x
  let du := dyadicCotGapUpper t
  let rad := DyadicInterval.sub
    (DyadicInterval.add (DyadicInterval.point 1)
      (DyadicInterval.mul (DyadicInterval.sqr a)
        (DyadicInterval.add (DyadicInterval.point 1) (DyadicInterval.sqr du))))
    (DyadicInterval.mul (DyadicInterval.point 2) (DyadicInterval.mul a dl))
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hx : x.Contains (Real.pi * s) := checkerPi_contains_pi.mul ht
  have honeSub : (DyadicInterval.sub (DyadicInterval.point 1) t).Contains (1 - s) :=
    hone.sub ht
  have ha : a.Contains ((Real.pi * s) * (1 - s)) := hx.mul honeSub
  have hdl : dl.Contains (prawitzCotGapLower (Real.pi * s)) :=
    dyadicCotGapLower_sound hx
  have hdu : du.Contains (prawitzCotGapUpperAt s) :=
    dyadicCotGapUpper_sound ht hCotDenom
  have ha2 := ha.sqr ha.ordered
  have hdu2 := hdu.sqr hdu.ordered
  have hrad : rad.Contains
      (1 + ((Real.pi * s) * (1 - s)) ^ 2 *
          (1 + prawitzCotGapUpperAt s ^ 2) -
        2 * (((Real.pi * s) * (1 - s)) * prawitzCotGapLower (Real.pi * s))) :=
    (hone.add (ha2.mul (hone.add hdu2))).sub (htwo.mul (ha.mul hdl))
  have hmax := hrad.maxZero
  have hmaxLo : 0 ≤ (DyadicInterval.maxZero rad).lo := by
    simp [DyadicInterval.maxZero]
  have hsqrt := hmax.sqrt hmax.ordered hmaxLo
  have hden := htwo.mul checkerPi_contains_pi
  have hdenPos : 0 < (DyadicInterval.mul (DyadicInterval.point 2) checkerPi).lo := by
    norm_num [DyadicInterval.mul, DyadicInterval.point, checkerPi, cornerMinInt,
      floorDiv, dyadicScale, dyadicPrecision]
  have hquot := hsqrt.div hden hden.ordered hdenPos
  change (dyadicPrawitzK0Upper t).Contains (prawitzK0Envelope s)
  simp only [dyadicPrawitzK0Upper]
  convert hquot using 1
  unfold prawitzK0Envelope
  ring_nf
  rw [max_comm]
  ring

theorem dyadicPrawitzKD2Upper_sound {t : DyadicInterval} {s : ℝ}
    (ht : t.Contains s)
    (hCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr t))).lo) :
    (dyadicPrawitzKD2Upper t).Contains (prawitzKD2Envelope s) := by
  let du := dyadicCotGapUpper t
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hdu : du.Contains (prawitzCotGapUpperAt s) :=
    dyadicCotGapUpper_sound ht hCotDenom
  have hdu2 := hdu.sqr hdu.ordered
  have htwoPos : 0 < (DyadicInterval.point 2).lo := by
    norm_num [DyadicInterval.point, dyadicScale, dyadicPrecision]
  have hhalf := hdu2.div htwo htwo.ordered htwoPos
  have hresult := (hone.sub ht).mul (hone.add hhalf)
  change (dyadicPrawitzKD2Upper t).Contains (prawitzKD2Envelope s)
  simp only [dyadicPrawitzKD2Upper]
  convert hresult using 1

theorem dyadicPrawitzKH2Upper_sound {t : DyadicInterval} {s : ℝ}
    (ht : t.Contains s)
    (hCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1) t)))).lo) :
    (dyadicPrawitzKH2Upper t).Contains (prawitzKH2Envelope s) := by
  let u := DyadicInterval.sub (DyadicInterval.point 1) t
  let du := dyadicCotGapUpper u
  let rad := DyadicInterval.add (DyadicInterval.point 1) (DyadicInterval.sqr du)
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hu : u.Contains (1 - s) := hone.sub ht
  have hdu : du.Contains (prawitzCotGapUpperAt (1 - s)) :=
    dyadicCotGapUpper_sound hu hCotDenom
  have hdu2 := hdu.sqr hdu.ordered
  have hrad : rad.Contains (1 + prawitzCotGapUpperAt (1 - s) ^ 2) :=
    hone.add hdu2
  have hradLo : 0 ≤ rad.lo := by
    dsimp only [rad, DyadicInterval.add, DyadicInterval.point]
    have hsqrLo : 0 ≤ (DyadicInterval.sqr du).lo := by
      unfold DyadicInterval.sqr
      split_ifs
      · norm_num
      · apply Int.ediv_nonneg
        · exact mul_self_nonneg _
        · exact dyadicScale_pos.le
    dsimp only [dyadicScale, dyadicPrecision]
    omega
  have hsqrt := hrad.sqrt hrad.ordered hradLo
  have hresult := hu.mul hsqrt
  change (dyadicPrawitzKH2Upper t).Contains (prawitzKH2Envelope s)
  simp only [dyadicPrawitzKH2Upper]
  convert hresult using 1

theorem t_mul_norm_prawitzKernel_le_dyadicPrawitzK0Upper_upper
    {t : DyadicInterval} {s : ℝ}
    (ht : t.Contains s) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr t))).lo) :
    s * ‖prawitzKernel s‖ ≤ (dyadicPrawitzK0Upper t).upper := by
  exact (t_mul_norm_prawitzKernel_le_K0Envelope hs0 hs1).trans
    (dyadicPrawitzK0Upper_sound ht hCotDenom).2

theorem two_mul_norm_prawitzKernelCorrection_le_dyadicPrawitzKD2Upper_upper
    {t : DyadicInterval} {s : ℝ}
    (ht : t.Contains s) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr t))).lo) :
    2 * ‖prawitzKernelCorrection s‖ ≤ (dyadicPrawitzKD2Upper t).upper := by
  exact (two_mul_norm_prawitzKernelCorrection_le_KD2Envelope hs0 hs1).trans
    (dyadicPrawitzKD2Upper_sound ht hCotDenom).2

theorem two_mul_norm_prawitzKernel_le_dyadicPrawitzKH2Upper_upper
    {t : DyadicInterval} {s : ℝ}
    (ht : t.Contains s) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1) t)))).lo) :
    2 * ‖prawitzKernel s‖ ≤ (dyadicPrawitzKH2Upper t).upper := by
  exact (two_mul_norm_prawitzKernel_le_KH2Envelope hs0 hs1).trans
    (dyadicPrawitzKH2Upper_sound ht hCotDenom).2

end BerryEsseen
