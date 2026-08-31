import BerryEsseen.Smoothing.PrawitzLargeNSmall
/-!
# Real cell semantics for the endpoint-regular large-`n` evaluator

The exact checker replaces the parameter-dependent exponent by a cellwise
lower bound and the kernel/disk factors by cellwise upper bounds.  These
definitions isolate those replacements before any dyadic arithmetic is used.
-/

namespace BerryEsseen

noncomputable section

def routeBLargeSmallLowCellQ (r y ql : ℝ) : ℝ :=
  max (((2 * Real.pi * y) ^ 2 * ql) / r ^ 2) 0

def routeBLargeSmallHighCellQ (r y qc : ℝ) : ℝ :=
  max (((2 * Real.pi * y) ^ 2 * qc) / r ^ 2) 0

def routeBLargeSmallCellF1
    (r y k0 q D : ℝ) : ℝ :=
  (8 * Real.pi ^ 2 / r ^ 3) * y ^ 2 * (2 * Real.pi * k0) * D *
    Real.exp (-routeBLargeNAlpha * q)

def routeBLargeSmallCellF3
    (r y kd2 : ℝ) : ℝ :=
  kd2 * Real.exp (-((2 * Real.pi * y) ^ 2 / (2 * r ^ 2)))

def routeBLargeSmallCellF2
    (kh2 q : ℝ) : ℝ :=
  kh2 * Real.exp (-q)

lemma prawitzK0Envelope_nonneg_of_mem
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ prawitzK0Envelope t := by
  exact (mul_nonneg ht0 (norm_nonneg _)).trans
    (t_mul_norm_prawitzKernel_le_K0Envelope ht0 ht1)

lemma prawitzKD2Envelope_nonneg_of_mem
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ prawitzKD2Envelope t := by
  exact (mul_nonneg (by norm_num) (norm_nonneg _)).trans
    (two_mul_norm_prawitzKernelCorrection_le_KD2Envelope ht0 ht1)

lemma prawitzKH2Envelope_nonneg_of_mem
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ prawitzKH2Envelope t := by
  exact (mul_nonneg (by norm_num) (norm_nonneg _)).trans
    (two_mul_norm_prawitzKernel_le_KH2Envelope ht0 ht1)

theorem routeBLargeSmallF1_le_cell
    {L r y k0 q D : ℝ}
    (hr : 0 < r) (hy0 : 0 ≤ y)
    (ht0 : 0 ≤ L * y) (ht1 : L * y < 1)
    (hk0 : prawitzK0Envelope (L * y) ≤ k0)
    (hq0 : 0 ≤ q) (hq : q ≤ routeBLargeSmallLowQ L r y)
    (hD : routeBDiskStar r (2 * Real.pi * L * y / r) ≤ D) :
    routeBLargeSmallF1 L r y ≤
      routeBLargeSmallCellF1 r y k0 q D := by
  have hk00 : 0 ≤ k0 :=
    (prawitzK0Envelope_nonneg_of_mem ht0 ht1).trans hk0
  have hD0 : 0 ≤ D :=
    (routeBDiskStar_nonneg _ _).trans hD
  have hDstar0 : 0 ≤
      routeBDiskStar r (2 * Real.pi * L * y / r) :=
    routeBDiskStar_nonneg _ _
  have hscale0 : 0 ≤ 8 * Real.pi ^ 2 / r ^ 3 * y ^ 2 := by positivity
  have hexp :
      Real.exp (-routeBLargeNAlpha * routeBLargeSmallLowQ L r y) ≤
        Real.exp (-routeBLargeNAlpha * q) :=
    Real.exp_le_exp.mpr (by
      have ha := routeBLargeNAlpha_nonneg
      nlinarith)
  have hexp0 : 0 ≤ Real.exp
      (-routeBLargeNAlpha * routeBLargeSmallLowQ L r y) :=
    (Real.exp_pos _).le
  have hcellExp0 : 0 ≤ Real.exp (-routeBLargeNAlpha * q) :=
    (Real.exp_pos _).le
  unfold routeBLargeSmallF1 routeBLargeSmallCellF1
  calc
    8 * Real.pi ^ 2 / r ^ 3 * y ^ 2 *
          (2 * Real.pi * prawitzK0Envelope (L * y)) *
          routeBDiskStar r (2 * Real.pi * L * y / r) *
          Real.exp (-routeBLargeNAlpha * routeBLargeSmallLowQ L r y) ≤
        8 * Real.pi ^ 2 / r ^ 3 * y ^ 2 * (2 * Real.pi * k0) *
          routeBDiskStar r (2 * Real.pi * L * y / r) *
          Real.exp (-routeBLargeNAlpha * routeBLargeSmallLowQ L r y) := by
      have hkfactor : 2 * Real.pi * prawitzK0Envelope (L * y) ≤
          2 * Real.pi * k0 :=
        mul_le_mul_of_nonneg_left hk0 (by positivity)
      have h1 := mul_le_mul_of_nonneg_left hkfactor hscale0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h1 hDstar0) hexp0
    _ ≤ 8 * Real.pi ^ 2 / r ^ 3 * y ^ 2 * (2 * Real.pi * k0) * D *
          Real.exp (-routeBLargeNAlpha * routeBLargeSmallLowQ L r y) := by
      have hprefix0 : 0 ≤
          8 * Real.pi ^ 2 / r ^ 3 * y ^ 2 * (2 * Real.pi * k0) :=
        mul_nonneg hscale0 (mul_nonneg (by positivity) hk00)
      have h1 := mul_le_mul_of_nonneg_left hD hprefix0
      exact mul_le_mul_of_nonneg_right h1 hexp0
    _ ≤ 8 * Real.pi ^ 2 / r ^ 3 * y ^ 2 * (2 * Real.pi * k0) * D *
          Real.exp (-routeBLargeNAlpha * q) := by
      exact mul_le_mul_of_nonneg_left hexp
        (mul_nonneg
          (mul_nonneg hscale0 (mul_nonneg (by positivity) hk00)) hD0)

theorem routeBLargeSmallF3_le_cell
    {L r y kd2 : ℝ}
    (ht0 : 0 ≤ L * y) (ht1 : L * y < 1)
    (hkd2 : prawitzKD2Envelope (L * y) ≤ kd2) :
    routeBLargeSmallF3 L r y ≤ routeBLargeSmallCellF3 r y kd2 := by
  unfold routeBLargeSmallF3 routeBLargeSmallCellF3
  exact mul_le_mul_of_nonneg_right hkd2 (Real.exp_pos _).le

theorem routeBLargeSmallF2_le_cell
    {L r y kh2 q : ℝ}
    (ht0 : 0 < 1 - L * y) (ht1 : 1 - L * y ≤ 1)
    (hkh2 : prawitzKH2Envelope (1 - L * y) ≤ kh2)
    (hq0 : 0 ≤ q) (hq : q ≤ routeBLargeSmallHighQ L r y) :
    routeBLargeSmallF2 L r y ≤ routeBLargeSmallCellF2 kh2 q := by
  have hkh20 : 0 ≤ kh2 :=
    (prawitzKH2Envelope_nonneg_of_mem ht0 ht1).trans hkh2
  have hexp : Real.exp (-routeBLargeSmallHighQ L r y) ≤ Real.exp (-q) :=
    Real.exp_le_exp.mpr (neg_le_neg hq)
  unfold routeBLargeSmallF2 routeBLargeSmallCellF2
  calc
    prawitzKH2Envelope (1 - L * y) *
          Real.exp (-routeBLargeSmallHighQ L r y) ≤
        kh2 * Real.exp (-routeBLargeSmallHighQ L r y) :=
      mul_le_mul_of_nonneg_right hkh2 (Real.exp_pos _).le
    _ ≤ kh2 * Real.exp (-q) := mul_le_mul_of_nonneg_left hexp hkh20

end

end BerryEsseen
