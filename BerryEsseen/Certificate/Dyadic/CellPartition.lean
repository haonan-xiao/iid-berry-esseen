import BerryEsseen.Certificate.Dyadic.Darboux
import BerryEsseen.Certificate.Finite.Cell
import BerryEsseen.Certificate.Dyadic.HQLower
/-!
# Verifier-matching equal-width Prawitz cells

This module transcribes the exact checker's `cells` and `cached_cells` routines.  It separates
the ideal real equal-width partition from the outward-rounded dyadic endpoints, proves that
every real subinterval is covered by the corresponding checker cell, and connects the cell's
kernel and minorant fields to their analytic meanings.
-/

namespace BerryEsseen

open DyadicInterval

noncomputable def routeBEqualPartitionPoint (a b : ℝ) (N k : ℕ) : ℝ :=
  a + (k : ℝ) * ((b - a) / (N : ℝ))

def dyadicPrawitzCellStep
    (aa bb : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.div (DyadicInterval.sub bb aa)
    (DyadicInterval.point (Int.ofNat N))

def dyadicPrawitzCellLeft
    (aa bb : DyadicInterval) (N i : ℕ) : DyadicInterval :=
  DyadicInterval.add aa
    (DyadicInterval.mul (DyadicInterval.point (Int.ofNat i))
      (dyadicPrawitzCellStep aa bb N))

def dyadicPrawitzCellRight
    (aa bb : DyadicInterval) (N i : ℕ) : DyadicInterval :=
  if i = N - 1 then bb
  else DyadicInterval.add (dyadicPrawitzCellLeft aa bb N i)
    (dyadicPrawitzCellStep aa bb N)

def dyadicPrawitzCellRange
    (aa bb : DyadicInterval) (N i : ℕ) : DyadicInterval :=
  ⟨(dyadicPrawitzCellLeft aa bb N i).lo,
    (dyadicPrawitzCellRight aa bb N i).hi⟩

def dyadicPrawitzCellRawWidth
    (aa bb : DyadicInterval) (N i : ℕ) : DyadicInterval :=
  DyadicInterval.sub (dyadicPrawitzCellRight aa bb N i)
    (dyadicPrawitzCellLeft aa bb N i)

/-- Exact transcription of one iteration of the checker's `cells` routine. -/
def dyadicPrawitzCellAt
    (aa bb : DyadicInterval) (N : ℕ) (low : Bool) (i : ℕ) :
    DyadicPrawitzCell :=
  let t := dyadicPrawitzCellRange aa bb N i
  {
    t := t
    wid := dyadicPrawitzCellRawWidth aa bb N i
    k0 := if low then dyadicPrawitzK0Upper t else DyadicInterval.point 0
    kd2 := if low then dyadicPrawitzKD2Upper t else DyadicInterval.point 0
    kh2 := if low then DyadicInterval.point 0 else dyadicPrawitzKH2Upper t
    hq := dyadicPrawitzHQLower t
    v := DyadicInterval.mul
      (DyadicInterval.mul (DyadicInterval.point 2) checkerPi) t
  }

def dyadicRouteBSplit : DyadicInterval := DyadicInterval.ofRat 19 50

def dyadicRouteBLowCell (N i : ℕ) : DyadicPrawitzCell :=
  dyadicPrawitzCellAt (DyadicInterval.point 0) dyadicRouteBSplit N true i

def dyadicRouteBHighCell (N i : ℕ) : DyadicPrawitzCell :=
  dyadicPrawitzCellAt dyadicRouteBSplit (DyadicInterval.point 1) N false i

noncomputable section

theorem routeBEqualPartitionPoint_zero (a b : ℝ) (N : ℕ) :
    routeBEqualPartitionPoint a b N 0 = a := by
  simp [routeBEqualPartitionPoint]

theorem routeBEqualPartitionPoint_succ (a b : ℝ) (N k : ℕ) :
    routeBEqualPartitionPoint a b N (k + 1) =
      routeBEqualPartitionPoint a b N k + (b - a) / (N : ℝ) := by
  unfold routeBEqualPartitionPoint
  push_cast
  ring

theorem routeBEqualPartitionPoint_at_N
    {a b : ℝ} {N : ℕ} (hN : 0 < N) :
    routeBEqualPartitionPoint a b N N = b := by
  unfold routeBEqualPartitionPoint
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hN0]
  ring

theorem routeBEqualPartitionPoint_mono
    {a b : ℝ} {N k l : ℕ} (hab : a ≤ b) (hN : 0 < N) (hkl : k ≤ l) :
    routeBEqualPartitionPoint a b N k ≤
      routeBEqualPartitionPoint a b N l := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hstep : 0 ≤ (b - a) / (N : ℝ) :=
    div_nonneg (sub_nonneg.mpr hab) hNR.le
  unfold routeBEqualPartitionPoint
  gcongr

theorem routeBEqualPartitionPoint_mem_Icc
    {a b : ℝ} {N k : ℕ} (hab : a ≤ b) (hN : 0 < N) (hk : k ≤ N) :
    routeBEqualPartitionPoint a b N k ∈ Set.Icc a b := by
  constructor
  · simpa only [routeBEqualPartitionPoint_zero] using
      routeBEqualPartitionPoint_mono hab hN (Nat.zero_le k)
  · calc
      routeBEqualPartitionPoint a b N k ≤
          routeBEqualPartitionPoint a b N N :=
        routeBEqualPartitionPoint_mono hab hN hk
      _ = b := routeBEqualPartitionPoint_at_N hN

theorem dyadicPrawitzCellStep_sound
    {aa bb : DyadicInterval} {a b : ℝ} {N : ℕ}
    (haa : aa.Contains a) (hbb : bb.Contains b) (hN : 0 < N) :
    (dyadicPrawitzCellStep aa bb N).Contains ((b - a) / (N : ℝ)) := by
  have hden : (DyadicInterval.point (Int.ofNat N)).Contains (N : ℝ) := by
    simpa using DyadicInterval.contains_point (Int.ofNat N)
  have hdenLo : 0 < (DyadicInterval.point (Int.ofNat N)).lo := by
    dsimp only [DyadicInterval.point]
    have hNInt : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
    exact mul_pos hNInt dyadicScale_pos
  exact (hbb.sub haa).div hden hden.ordered hdenLo

theorem dyadicPrawitzCellLeft_sound
    {aa bb : DyadicInterval} {a b : ℝ} {N i : ℕ}
    (haa : aa.Contains a) (hbb : bb.Contains b) (hN : 0 < N) :
    (dyadicPrawitzCellLeft aa bb N i).Contains
      (routeBEqualPartitionPoint a b N i) := by
  have hi : (DyadicInterval.point (Int.ofNat i)).Contains (i : ℝ) := by
    simpa using DyadicInterval.contains_point (Int.ofNat i)
  have hstep := dyadicPrawitzCellStep_sound haa hbb hN
  simpa [dyadicPrawitzCellLeft, routeBEqualPartitionPoint] using haa.add (hi.mul hstep)

theorem dyadicPrawitzCellRight_sound
    {aa bb : DyadicInterval} {a b : ℝ} {N i : ℕ}
    (haa : aa.Contains a) (hbb : bb.Contains b) (hN : 0 < N) (hi : i < N) :
    (dyadicPrawitzCellRight aa bb N i).Contains
      (routeBEqualPartitionPoint a b N (i + 1)) := by
  by_cases hlast : i = N - 1
  · rw [dyadicPrawitzCellRight, if_pos hlast]
    have hiN : i + 1 = N := by omega
    rw [hiN, routeBEqualPartitionPoint_at_N hN]
    exact hbb
  · rw [dyadicPrawitzCellRight, if_neg hlast]
    have hleft := dyadicPrawitzCellLeft_sound haa hbb hN (i := i)
    have hstep := dyadicPrawitzCellStep_sound haa hbb hN
    simpa [routeBEqualPartitionPoint_succ] using hleft.add hstep

theorem dyadicPrawitzCellRange_contains
    {aa bb : DyadicInterval} {a b x : ℝ} {N i : ℕ}
    (haa : aa.Contains a) (hbb : bb.Contains b) (hN : 0 < N) (hi : i < N)
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint a b N i)
      (routeBEqualPartitionPoint a b N (i + 1))) :
    (dyadicPrawitzCellRange aa bb N i).Contains x := by
  have hleft := dyadicPrawitzCellLeft_sound haa hbb hN (i := i)
  have hright := dyadicPrawitzCellRight_sound haa hbb hN hi
  exact ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩

theorem dyadicPrawitzCellRawWidth_sound
    {aa bb : DyadicInterval} {a b : ℝ} {N i : ℕ}
    (haa : aa.Contains a) (hbb : bb.Contains b) (hN : 0 < N) (hi : i < N) :
    (dyadicPrawitzCellRawWidth aa bb N i).Contains
      (routeBEqualPartitionPoint a b N (i + 1) -
        routeBEqualPartitionPoint a b N i) := by
  exact (dyadicPrawitzCellRight_sound haa hbb hN hi).sub
    (dyadicPrawitzCellLeft_sound haa hbb hN)

theorem dyadicPrawitzCellAt_t_contains
    {aa bb : DyadicInterval} {a b x : ℝ} {N i : ℕ} {low : Bool}
    (haa : aa.Contains a) (hbb : bb.Contains b) (hN : 0 < N) (hi : i < N)
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint a b N i)
      (routeBEqualPartitionPoint a b N (i + 1))) :
    (dyadicPrawitzCellAt aa bb N low i).t.Contains x := by
  simpa [dyadicPrawitzCellAt] using
    dyadicPrawitzCellRange_contains haa hbb hN hi hx

theorem dyadicPrawitzCellAt_wid_contains
    {aa bb : DyadicInterval} {a b : ℝ} {N i : ℕ} {low : Bool}
    (haa : aa.Contains a) (hbb : bb.Contains b) (hN : 0 < N) (hi : i < N) :
    (dyadicPrawitzCellAt aa bb N low i).wid.Contains
      (routeBEqualPartitionPoint a b N (i + 1) -
        routeBEqualPartitionPoint a b N i) := by
  simpa [dyadicPrawitzCellAt] using
    dyadicPrawitzCellRawWidth_sound haa hbb hN hi

theorem dyadicPrawitzCellAt_v_contains
    {aa bb : DyadicInterval} {N i : ℕ} {low : Bool} {x : ℝ}
    (ht : (dyadicPrawitzCellAt aa bb N low i).t.Contains x) :
    (dyadicPrawitzCellAt aa bb N low i).v.Contains (routeBCellV x) := by
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  simpa [dyadicPrawitzCellAt, routeBCellV] using
    (htwo.mul checkerPi_contains_pi).mul ht

theorem dyadicPrawitzLowCell_k0_sound
    {aa bb : DyadicInterval} {N i : ℕ} {x : ℝ}
    (ht : (dyadicPrawitzCellAt aa bb N true i).t.Contains x)
    (hCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr (dyadicPrawitzCellAt aa bb N true i).t))).lo) :
    (dyadicPrawitzCellAt aa bb N true i).k0.Contains (prawitzK0Envelope x) := by
  simpa [dyadicPrawitzCellAt] using dyadicPrawitzK0Upper_sound ht hCotDenom

theorem dyadicPrawitzLowCell_kd2_sound
    {aa bb : DyadicInterval} {N i : ℕ} {x : ℝ}
    (ht : (dyadicPrawitzCellAt aa bb N true i).t.Contains x)
    (hCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr (dyadicPrawitzCellAt aa bb N true i).t))).lo) :
    (dyadicPrawitzCellAt aa bb N true i).kd2.Contains (prawitzKD2Envelope x) := by
  simpa [dyadicPrawitzCellAt] using dyadicPrawitzKD2Upper_sound ht hCotDenom

theorem dyadicPrawitzHighCell_kh2_sound
    {aa bb : DyadicInterval} {N i : ℕ} {x : ℝ}
    (ht : (dyadicPrawitzCellAt aa bb N false i).t.Contains x)
    (hCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1)
          (dyadicPrawitzCellAt aa bb N false i).t)))).lo) :
    (dyadicPrawitzCellAt aa bb N false i).kh2.Contains (prawitzKH2Envelope x) := by
  simpa [dyadicPrawitzCellAt] using dyadicPrawitzKH2Upper_sound ht hCotDenom

theorem dyadicPrawitzCellAt_hq_lower_le
    {aa bb : DyadicInterval} {N i : ℕ} {low : Bool} {x : ℝ}
    (ht : (dyadicPrawitzCellAt aa bb N low i).t.Contains x)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (dyadicPrawitzCellAt aa bb N low i).hq.lower ≤
      routeBCellV x ^ 2 * routeBMinorant routeBKappa routeBTheta (routeBCellV x) := by
  simpa [dyadicPrawitzCellAt, routeBCellV] using
    dyadicPrawitzHQLower_lower_le ht hx0 hx1

theorem dyadicRouteBSplit_contains :
    dyadicRouteBSplit.Contains prawitzSplit := by
  convert DyadicInterval.contains_ofRat 19 (b := 50) (by norm_num) using 1

theorem dyadicRouteBLowCell_t_contains
    {N i : ℕ} {x : ℝ} (hN : 0 < N) (hi : i < N)
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint 0 prawitzSplit N i)
      (routeBEqualPartitionPoint 0 prawitzSplit N (i + 1))) :
    (dyadicRouteBLowCell N i).t.Contains x := by
  have hzero : (DyadicInterval.point 0).Contains (0 : ℝ) := by
    simpa using DyadicInterval.contains_point (0 : ℤ)
  simpa [dyadicRouteBLowCell] using
    dyadicPrawitzCellAt_t_contains
      (low := true) hzero dyadicRouteBSplit_contains hN hi hx

theorem dyadicRouteBHighCell_t_contains
    {N i : ℕ} {x : ℝ} (hN : 0 < N) (hi : i < N)
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint prawitzSplit 1 N i)
      (routeBEqualPartitionPoint prawitzSplit 1 N (i + 1))) :
    (dyadicRouteBHighCell N i).t.Contains x := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  simpa [dyadicRouteBHighCell] using
    dyadicPrawitzCellAt_t_contains
      (low := false) dyadicRouteBSplit_contains hone hN hi hx

theorem dyadicRouteBLowCell_wid_contains
    {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    (dyadicRouteBLowCell N i).wid.Contains
      (routeBEqualPartitionPoint 0 prawitzSplit N (i + 1) -
        routeBEqualPartitionPoint 0 prawitzSplit N i) := by
  have hzero : (DyadicInterval.point 0).Contains (0 : ℝ) := by
    simpa using DyadicInterval.contains_point (0 : ℤ)
  simpa [dyadicRouteBLowCell] using
    dyadicPrawitzCellAt_wid_contains
      (low := true) hzero dyadicRouteBSplit_contains hN hi

theorem dyadicRouteBHighCell_wid_contains
    {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    (dyadicRouteBHighCell N i).wid.Contains
      (routeBEqualPartitionPoint prawitzSplit 1 N (i + 1) -
        routeBEqualPartitionPoint prawitzSplit 1 N i) := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  simpa [dyadicRouteBHighCell] using
    dyadicPrawitzCellAt_wid_contains
      (low := false) dyadicRouteBSplit_contains hone hN hi

end

end BerryEsseen
