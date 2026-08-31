import BerryEsseen.Certificate.Dyadic.GaussianTail
import Mathlib.Data.Vector.Basic
import Batteries.Data.Vector.Lemmas

/-!
# Shared Prawitz cell cache

The supplied checker constructs the parameter-independent quadrature cells once at each
resolution and reuses them for every parameter box.  This module gives the same sharing to the
Lean evaluator.  The cached sums preserve the order of the original `intervalNatSum`, and the
main equality theorem proves that a valid cache computes exactly the already-verified canonical
finite bound.
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

/-- A fixed-size pair of low- and high-frequency cell arrays. -/
structure DyadicRouteBCellCache (N : ℕ) where
  low : Vector DyadicPrawitzCell N
  high : Vector DyadicPrawitzCell N

/-- Build the canonical cells once.  `Vector.ofFn` is represented by an array at runtime. -/
def dyadicRouteBBuildCellCache (N : ℕ) : DyadicRouteBCellCache N where
  low := Vector.ofFn (fun i => dyadicRouteBLowCell N i.1)
  high := Vector.ofFn (fun i => dyadicRouteBHighCell N i.1)

structure DyadicRouteBCellCache.Valid
    {N : ℕ} (cache : DyadicRouteBCellCache N) : Prop where
  low : ∀ i : Fin N, cache.low.get i = dyadicRouteBLowCell N i.1
  high : ∀ i : Fin N, cache.high.get i = dyadicRouteBHighCell N i.1

theorem dyadicRouteBBuildCellCache_valid (N : ℕ) :
    (dyadicRouteBBuildCellCache N).Valid := by
  constructor <;> intro i <;>
    simp [dyadicRouteBBuildCellCache, Vector.get_ofFn]

/-- A dependent finite sum with exactly the same left-to-right addition order as
`intervalNatSum`. -/
def intervalFinSum : {N : ℕ} → (Fin N → DyadicInterval) → DyadicInterval
  | 0, _ => DyadicInterval.point 0
  | N + 1, F =>
      DyadicInterval.add
        (intervalFinSum (fun i : Fin N => F i.castSucc))
        (F (Fin.last N))

theorem intervalFinSum_eq_intervalNatSum
    {N : ℕ} {F : Fin N → DyadicInterval} {G : ℕ → DyadicInterval}
    (h : ∀ i : Fin N, F i = G i.1) :
    intervalFinSum F = intervalNatSum G N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [intervalFinSum, intervalNatSum]
      congr 1
      · apply ih
        intro i
        exact h i.castSucc
      · exact h (Fin.last N)

/-! ## Shared `E1up` table -/

/-- One parameter-independent entry in the checker's 769-point `E1up` table. -/
structure DyadicRouteBE1CacheEntry where
  grid : DyadicInterval
  exp : DyadicInterval

/-- The checker constructs the values `expneg(j / 32)` once and reuses them.  We additionally
cache the exact dyadic grid values, which are parameter-independent as well. -/
structure DyadicRouteBE1Cache where
  entries : Vector DyadicRouteBE1CacheEntry (routeBE1NY + 1)

def dyadicRouteBBuildE1Cache : DyadicRouteBE1Cache where
  entries := Vector.ofFn (fun j =>
    { grid := dyadicE1Grid j.1, exp := dyadicE1Exp j.1 })

structure DyadicRouteBE1Cache.Valid (cache : DyadicRouteBE1Cache) : Prop where
  grid : ∀ j : Fin (routeBE1NY + 1),
    (cache.entries.get j).grid = dyadicE1Grid j.1
  exp : ∀ j : Fin (routeBE1NY + 1),
    (cache.entries.get j).exp = dyadicE1Exp j.1

theorem dyadicRouteBBuildE1Cache_valid :
    dyadicRouteBBuildE1Cache.Valid := by
  constructor <;> intro j <;>
    simp [dyadicRouteBBuildE1Cache, Vector.get_ofFn]

def dyadicRouteBCachedE1Term
    (cache : DyadicRouteBE1Cache) (xx : DyadicInterval)
    (j : Fin (routeBE1NY + 1)) : DyadicInterval :=
  let entry := cache.entries.get j
  let f := DyadicInterval.div entry.exp (DyadicInterval.add xx entry.grid)
  if j.1 = 0 ∨ j.1 = routeBE1NY then
    DyadicInterval.divPoint f 2
  else f

def dyadicRouteBCachedE1Sum
    (cache : DyadicRouteBE1Cache) (xx : DyadicInterval) : DyadicInterval :=
  intervalFinSum (dyadicRouteBCachedE1Term cache xx)

def dyadicRouteBCachedE1Trapezoid
    (cache : DyadicRouteBE1Cache) (xx : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul routeBE1Dy (dyadicRouteBCachedE1Sum cache xx)

def dyadicRouteBCachedE1Tail
    (cache : DyadicRouteBE1Cache) (xx : DyadicInterval) : DyadicInterval :=
  let last : Fin (routeBE1NY + 1) := ⟨routeBE1NY, Nat.lt_succ_self routeBE1NY⟩
  DyadicInterval.div (cache.entries.get last).exp
    (DyadicInterval.add xx (DyadicInterval.point 24))

def dyadicRouteBCachedE1Up
    (cache : DyadicRouteBE1Cache) (x : DyadicInterval) : DyadicInterval :=
  let xx := dyadicLowerPoint x
  let integ := DyadicInterval.add
    (dyadicRouteBCachedE1Trapezoid cache xx)
    (dyadicRouteBCachedE1Tail cache xx)
  DyadicInterval.mul (dyadicExpNeg xx) integ

theorem dyadicRouteBCachedE1Term_eq
    {cache : DyadicRouteBE1Cache} (hcache : cache.Valid)
    (xx : DyadicInterval) (j : Fin (routeBE1NY + 1)) :
    dyadicRouteBCachedE1Term cache xx j = dyadicE1Term xx j.1 := by
  rw [dyadicRouteBCachedE1Term, dyadicE1Term, hcache.grid j, hcache.exp j]
  simp only [DyadicInterval.divPoint_eq_div]

theorem dyadicRouteBCachedE1Sum_eq
    {cache : DyadicRouteBE1Cache} (hcache : cache.Valid)
    (xx : DyadicInterval) :
    dyadicRouteBCachedE1Sum cache xx = dyadicE1Sum xx := by
  unfold dyadicRouteBCachedE1Sum dyadicE1Sum
  apply intervalFinSum_eq_intervalNatSum
  exact dyadicRouteBCachedE1Term_eq hcache xx

theorem dyadicRouteBCachedE1Tail_eq
    {cache : DyadicRouteBE1Cache} (hcache : cache.Valid)
    (xx : DyadicInterval) :
    dyadicRouteBCachedE1Tail cache xx = dyadicE1Tail xx := by
  rw [dyadicRouteBCachedE1Tail, dyadicE1Tail]
  exact congrArg
    (fun e => DyadicInterval.div e
      (DyadicInterval.add xx (DyadicInterval.point 24)))
    (hcache.exp ⟨routeBE1NY, Nat.lt_succ_self routeBE1NY⟩)

theorem dyadicRouteBCachedE1Up_eq
    {cache : DyadicRouteBE1Cache} (hcache : cache.Valid)
    (x : DyadicInterval) :
    dyadicRouteBCachedE1Up cache x = dyadicE1Up x := by
  rw [dyadicRouteBCachedE1Up, dyadicE1Up,
    dyadicRouteBCachedE1Trapezoid, dyadicE1Trapezoid,
    dyadicRouteBCachedE1Sum_eq hcache,
    dyadicRouteBCachedE1Tail_eq hcache]

/-- Box-dependent quantities shared by every quadrature cell, matching the local variables at
the start of the checker's `finite_bound`. -/
structure DyadicRouteBBoxState where
  sn : DyadicInterval
  p : DyadicInterval
  w : DyadicInterval
  w2 : DyadicInterval
  snP : DyadicInterval
  twoSnP : DyadicInterval
  prefactor : DyadicInterval
  w3 : DyadicInterval
  p2 : DyadicInterval
  twoW2 : DyadicInterval
  fourW : DyadicInterval
  w2Over36 : DyadicInterval
  wpOver18 : DyadicInterval
  wOver18 : DyadicInterval
  a : DyadicInterval
  kappaUpperSq : DyadicInterval

def dyadicRouteBBuildBoxState
    (n : ℕ) (rho z : DyadicInterval) : DyadicRouteBBoxState :=
  let w := dyadicCellW rho z
  let p := dyadicCellP rho
  let w2 := DyadicInterval.sqr w
  let wp := DyadicInterval.mul w p
  let sn := dyadicCellSqrtN n
  {
    sn := sn
    p := p
    w := w
    w2 := w2
    snP := DyadicInterval.mul sn p
    twoSnP := DyadicInterval.mul
      (DyadicInterval.mulPoint 2 sn) p
    prefactor := DyadicInterval.mulPoint (Int.ofNat (2 * n)) sn
    w3 := powi w 3
    p2 := DyadicInterval.sqr p
    twoW2 := DyadicInterval.mulPoint 2 w2
    fourW := DyadicInterval.mulPoint 4 w
    w2Over36 := DyadicInterval.divPoint w2 36
    wpOver18 := DyadicInterval.divPoint wp 18
    wOver18 := DyadicInterval.divPoint w 18
    a := DyadicInterval.divPoint
      (DyadicInterval.sub wp (DyadicInterval.point 1)) 6
    kappaUpperSq := DyadicInterval.sqr checkerKappaUpper
  }

/-- `Dbound` with every box-dependent intermediate supplied by `DyadicRouteBBoxState`. -/
def dyadicRouteBDboundFromBoxState
    (state : DyadicRouteBBoxState) (v : DyadicInterval) : DyadicInterval :=
  let y := DyadicInterval.div (DyadicInterval.sqr v) state.twoW2
  let C := DyadicInterval.mul
    (DyadicInterval.div v state.fourW) (hfunInterval y)
  let C2 := DyadicInterval.sqr C
  let common := DyadicInterval.mul
    (DyadicInterval.sub C2 state.w2Over36) state.p2
  let V0 := DyadicInterval.add common state.wpOver18
  let Va := DyadicInterval.add
    (DyadicInterval.add (DyadicInterval.ofRat 1 36)
      (DyadicInterval.mul
        (DyadicInterval.sub C2
          (DyadicInterval.divPoint (DyadicInterval.mul C state.w) 3)) state.p2))
    (DyadicInterval.divPoint (DyadicInterval.mul C state.p) 3)
  let Vk := DyadicInterval.add
    (DyadicInterval.add state.kappaUpperSq common)
    (DyadicInterval.mul
      (DyadicInterval.sub state.wOver18
        (DyadicInterval.mulPoint 2 (DyadicInterval.mul checkerKappaLower C))) state.p)
  let hi :=
    if state.a.hi ≤ checkerKappaLower.lo then max V0.hi Va.hi
    else if checkerKappaUpper.hi ≤ state.a.lo then max V0.hi Vk.hi
    else max (max V0.hi Va.hi) Vk.hi
  DyadicInterval.sqrt (dyadicUpperHull hi)

theorem dyadicRouteBDboundFromBoxState_eq
    (n : ℕ) (rho z v : DyadicInterval) :
    dyadicRouteBDboundFromBoxState (dyadicRouteBBuildBoxState n rho z) v =
      dyadicPrawitzDboundShared rho z v := by
  rfl

/-- Let-shared transcription of one low-frequency loop body. -/
def dyadicRouteBSharedLowCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let A2 := DyadicInterval.maxZero
      (DyadicInterval.sub (DyadicInterval.point 1)
      (DyadicInterval.div
        (DyadicInterval.mulPoint 2 (dyadicCellLowerPoint c.hq))
        state.w2))
  let A := DyadicInterval.sqrt A2
  let B := dyadicExpNeg
    (DyadicInterval.div (DyadicInterval.sqr c.v)
      state.twoW2)
  let M := powi A n
  let NN := dyadicExpNeg
    (DyadicInterval.div
      (DyadicInterval.mulPoint (Int.ofNat n) (DyadicInterval.sqr c.v))
      state.twoW2)
  let H := powi (dyadicCellNonnegativeHull A B) (n - 1)
  let D := dyadicRouteBDboundFromBoxState state c.v
  let withKernel := DyadicInterval.mul state.prefactor c.k0
  let frequency := DyadicInterval.mul (DyadicInterval.sqr c.t) dyadicCellTwoPiCubed
  let withFrequency := DyadicInterval.mul withKernel frequency
  let diskScale := DyadicInterval.div D state.w3
  let telescoping := DyadicInterval.mul
    (DyadicInterval.mul withFrequency diskScale) H
  let trivial :=
    if 0 < c.t.lo then
      DyadicInterval.mul
        state.twoSnP
        (DyadicInterval.mul c.k0
          (DyadicInterval.div (DyadicInterval.add M NN) c.t))
    else dyadicCellHuge
  let f1 : DyadicInterval := ⟨0, min telescoping.hi trivial.hi⟩
  let f3 := DyadicInterval.mul
    state.snP (DyadicInterval.mul c.kd2 NN)
  DyadicInterval.add f1 f3

/-- Let-shared transcription of one high-frequency loop body. -/
def dyadicRouteBSharedHighCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let A2 := DyadicInterval.maxZero
      (DyadicInterval.sub (DyadicInterval.point 1)
      (DyadicInterval.div
        (DyadicInterval.mulPoint 2 (dyadicCellLowerPoint c.hq))
        state.w2))
  let A := DyadicInterval.sqrt A2
  let M := powi A n
  DyadicInterval.mul
    state.snP (DyadicInterval.mul c.kh2 M)

theorem dyadicRouteBSharedLowCellValue_eq
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    dyadicRouteBSharedLowCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c =
      dyadicLowCellValue n rho z c := by
  unfold dyadicRouteBSharedLowCellValue
  rw [dyadicRouteBDboundFromBoxState_eq, dyadicPrawitzDboundShared_eq]
  simp only [dyadicRouteBBuildBoxState, DyadicInterval.mulPoint_eq_mul]
  rfl

theorem dyadicRouteBSharedHighCellValue_eq
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    dyadicRouteBSharedHighCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c =
      dyadicHighCellValue n rho z c := by
  simp only [dyadicRouteBSharedHighCellValue, dyadicRouteBBuildBoxState,
    DyadicInterval.mulPoint_eq_mul]
  rfl

def dyadicRouteBCachedLowSum
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  let state := dyadicRouteBBuildBoxState n rho z
  intervalFinSum (fun i =>
    let c := cache.low.get i
    DyadicInterval.mul c.wid
      (dyadicRouteBSharedLowCellValue state n rho z c))

def dyadicRouteBCachedHighSum
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  let state := dyadicRouteBBuildBoxState n rho z
  intervalFinSum (fun i =>
    let c := cache.high.get i
    DyadicInterval.mul c.wid
      (dyadicRouteBSharedHighCellValue state n rho z c))

def dyadicRouteBCachedFiniteBound
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBCachedLowSum cache n rho z)
    (dyadicRouteBCachedHighSum cache n rho z)

/-- The Gaussian-tail term using the shared `E1up` table. -/
def dyadicRouteBCachedTailValue
    (cache : DyadicRouteBE1Cache)
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul
    (DyadicInterval.mul (dyadicCellSqrtN n) (dyadicCellP rho))
    (DyadicInterval.div
      (dyadicRouteBCachedE1Up cache (dyadicRouteBTailX n rho z))
      dyadicRouteBTwoPi)

/-- Add a once-computed tail value to one cached finite quadrature. -/
def dyadicRouteBCachedFullBoundUsingTail
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z tail : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBCachedFiniteBound cache n rho z) tail

def dyadicRouteBCachedFullBound
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBCachedFiniteBound cache n rho z)
    (dyadicRouteBTailValue n rho z)

theorem dyadicRouteBCachedLowSum_eq
    {N n : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    (rho z : DyadicInterval) :
    dyadicRouteBCachedLowSum cache n rho z =
      dyadicRouteBLowSum n rho z N := by
  unfold dyadicRouteBCachedLowSum dyadicRouteBLowSum
  apply intervalFinSum_eq_intervalNatSum
  intro i
  rw [hcache.low i]
  dsimp only
  rw [dyadicRouteBSharedLowCellValue_eq]

theorem dyadicRouteBCachedHighSum_eq
    {N n : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    (rho z : DyadicInterval) :
    dyadicRouteBCachedHighSum cache n rho z =
      dyadicRouteBHighSum n rho z N := by
  unfold dyadicRouteBCachedHighSum dyadicRouteBHighSum
  apply intervalFinSum_eq_intervalNatSum
  intro i
  rw [hcache.high i]
  dsimp only
  rw [dyadicRouteBSharedHighCellValue_eq]

theorem dyadicRouteBCachedFiniteBound_eq
    {N n : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    (rho z : DyadicInterval) :
    dyadicRouteBCachedFiniteBound cache n rho z =
      dyadicRouteBFiniteBound n rho z N := by
  rw [dyadicRouteBCachedFiniteBound, dyadicRouteBFiniteBound,
    dyadicRouteBCachedLowSum_eq hcache,
    dyadicRouteBCachedHighSum_eq hcache]

theorem dyadicRouteBCachedTailValue_eq
    {cache : DyadicRouteBE1Cache} (hcache : cache.Valid)
    (n : ℕ) (rho z : DyadicInterval) :
    dyadicRouteBCachedTailValue cache n rho z =
      dyadicRouteBTailValue n rho z := by
  rw [dyadicRouteBCachedTailValue, dyadicRouteBTailValue,
    dyadicRouteBCachedE1Up_eq hcache]

theorem dyadicRouteBCachedFullBoundUsingTail_eq
    {N n : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (rho z : DyadicInterval) :
    dyadicRouteBCachedFullBoundUsingTail cellCache n rho z
        (dyadicRouteBCachedTailValue e1Cache n rho z) =
      dyadicRouteBFullBound n rho z N := by
  rw [dyadicRouteBCachedFullBoundUsingTail, dyadicRouteBFullBound,
    dyadicRouteBCachedFiniteBound_eq hcell,
    dyadicRouteBCachedTailValue_eq he1]

theorem dyadicRouteBCachedFullBound_eq
    {N n : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    (rho z : DyadicInterval) :
    dyadicRouteBCachedFullBound cache n rho z =
      dyadicRouteBFullBound n rho z N := by
  rw [dyadicRouteBCachedFullBound, dyadicRouteBFullBound,
    dyadicRouteBCachedFiniteBound_eq hcache]

/-- Side conditions evaluated against the shared cell arrays. -/
def DyadicRouteBCachedFullAdmissible
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : Prop :=
  DyadicRouteBBoxAdmissible rho z ∧
    DyadicRouteBTailAdmissible n rho z ∧
    (∀ i : Fin N,
      DyadicLowCellAdmissible n rho z (cache.low.get i)) ∧
    (∀ i : Fin N,
      DyadicHighCellAdmissible n rho z (cache.high.get i))

instance {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) :
    Decidable (DyadicRouteBCachedFullAdmissible cache n rho z) := by
  unfold DyadicRouteBCachedFullAdmissible
  infer_instance

theorem DyadicRouteBCachedFullAdmissible.toCanonical
    {N n : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    {rho z : DyadicInterval}
    (h : DyadicRouteBCachedFullAdmissible cache n rho z) :
    DyadicRouteBFullAdmissible n N rho z := by
  rcases h with ⟨hbox, htail, hlow, hhigh⟩
  refine ⟨hbox, htail, ?_, ?_⟩
  · intro i
    rw [← hcache.low i]
    exact hlow i
  · intro i
    rw [← hcache.high i]
    exact hhigh i

end BerryEsseen
