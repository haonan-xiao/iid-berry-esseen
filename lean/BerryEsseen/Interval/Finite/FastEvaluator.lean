import BerryEsseen.Interval.Finite.AdaptiveFullCover

/-!
# Interval / Finite / Fast Evaluator
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

def fastTelescopingWithEnvelope
    (state : DyadicRouteBBoxState) (n : ℕ) (c : DyadicPrawitzCell)
    (env : CertifiedCellEnvelope) : DyadicInterval :=
  let H := powi (dyadicCellNonnegativeHull env.f env.normalOne) (n - 1)
  let D := dyadicRouteBDboundFromBoxState state c.v
  let withKernel := DyadicInterval.mul state.prefactor c.k0
  let frequency := DyadicInterval.mul (DyadicInterval.sqr c.t)
    dyadicCellTwoPiCubed
  let withFrequency := DyadicInterval.mul withKernel frequency
  let diskScale := DyadicInterval.div D state.w3
  DyadicInterval.mul (DyadicInterval.mul withFrequency diskScale) H

def fastLowCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let env := certifiedCellEnvelope n rho z c
  let telescoping := fastTelescopingWithEnvelope state n c env
  let trivial :=
    if 0 < c.t.lo then
      DyadicInterval.mul state.twoSnP
        (DyadicInterval.mul c.k0
          (DyadicInterval.div (DyadicInterval.add (powi env.f n) env.normalN) c.t))
    else dyadicCellHuge
  let rademacher :=
    if 0 < c.t.lo then
      DyadicInterval.mul state.twoSnP
        (DyadicInterval.mul c.k0
          (DyadicInterval.div (certifiedRademacherDifference n env) c.t))
    else dyadicCellHuge
  let f1 : DyadicInterval :=
    ⟨0, min telescoping.hi (min trivial.hi rademacher.hi)⟩
  DyadicInterval.add f1
    (DyadicInterval.mul state.snP (DyadicInterval.mul c.kd2 env.normalN))

theorem fastLowCellValue_eq
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    fastLowCellValue state n rho z c =
      certifiedSharedLowCellValue state n rho z c := by
  rfl

def fastHighCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  -- The high-frequency value uses only f, not the Gaussian/remainder fields.
  let u := DyadicInterval.div c.v (dyadicCellW rho z)
  let trig := trigSinCos u
  let d := dUpper rho z
  let real := realInterval rho d u trig.1 trig.2
  let imag := imagInterval rho z d u trig.1 trig.2
  let rectangular := rectangularEnvelope real imag
  let f := minModulusEnvelope (dyadicCellA rho z c) rectangular
  DyadicInterval.mul state.snP (DyadicInterval.mul c.kh2 (powi f n))

theorem fastHighCellValue_eq
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    fastHighCellValue state n rho z c =
      certifiedSharedHighCellValue state n rho z c := by
  rfl

def FastLowCellAdmissible
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : Prop :=
  let state := dyadicRouteBBuildBoxState n rho z
  DyadicLowCellAdmissible n rho z c ∧
    0 ≤ (DyadicInterval.div c.v (dyadicCellW rho z)).lo ∧
    (¬ 0 < c.t.lo →
      (fastTelescopingWithEnvelope state n c
        (certifiedCellEnvelope n rho z c)).hi ≤ dyadicCellHuge.hi) ∧
    (let value := fastLowCellValue state n rho z c
     value.lo ≤ value.hi)

instance (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    Decidable (FastLowCellAdmissible n rho z c) := by
  unfold FastLowCellAdmissible
  infer_instance

theorem fastLowCellAdmissible_iff
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    FastLowCellAdmissible n rho z c ↔
      CertifiedLowCellAdmissible n rho z c := by
  constructor
  · rintro ⟨hb, hf, hh, hv⟩
    exact ⟨hb, hf, hh, hv⟩
  · intro h
    exact ⟨h.base, h.frequencyNonnegative, h.hugeFallback, h.valueOrdered⟩

def FastHighCellAdmissible
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : Prop :=
  let state := dyadicRouteBBuildBoxState n rho z
  DyadicHighCellAdmissible n rho z c ∧
    0 ≤ (DyadicInterval.div c.v (dyadicCellW rho z)).lo ∧
    (let value := fastHighCellValue state n rho z c
     value.lo ≤ value.hi)

instance (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    Decidable (FastHighCellAdmissible n rho z c) := by
  unfold FastHighCellAdmissible
  infer_instance

theorem fastHighCellAdmissible_iff
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    FastHighCellAdmissible n rho z c ↔
      CertifiedHighCellAdmissible n rho z c := by
  constructor
  · rintro ⟨hb, hf, hv⟩
    exact ⟨hb, hf, hv⟩
  · intro h
    exact ⟨h.base, h.frequencyNonnegative, h.valueOrdered⟩

def FastCachedFullAdmissible
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : Prop :=
  DyadicRouteBBoxAdmissible rho z ∧
    DyadicRouteBTailAdmissible n rho z ∧
    (∀ i : Fin N, FastLowCellAdmissible n rho z (cache.low.get i)) ∧
    (∀ i : Fin N, FastHighCellAdmissible n rho z (cache.high.get i))

instance {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) :
    Decidable (FastCachedFullAdmissible cache n rho z) := by
  unfold FastCachedFullAdmissible
  infer_instance

theorem fastCachedFullAdmissible_eq
    {N : ℕ} (cache : DyadicRouteBCellCache N) (n : ℕ)
    (rho z : DyadicInterval) :
    FastCachedFullAdmissible cache n rho z =
      CertifiedCachedFullAdmissible cache n rho z := by
  apply propext
  simp only [FastCachedFullAdmissible, CertifiedCachedFullAdmissible,
    fastLowCellAdmissible_iff, fastHighCellAdmissible_iff]

def fastCachedLowSum
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) : DyadicInterval :=
  intervalFinSum (fun i =>
    let c := cache.low.get i
    DyadicInterval.mul c.wid (fastLowCellValue state n rho z c))

def fastCachedHighSum
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) : DyadicInterval :=
  intervalFinSum (fun i =>
    let c := cache.high.get i
    DyadicInterval.mul c.wid
      (fastHighCellValue state n rho z c))

def fastCachedFullBoundUsingTail
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z tail : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add
    (DyadicInterval.add (fastCachedLowSum cache state n rho z)
      (fastCachedHighSum cache state n rho z)) tail

def fastCachedFullBound
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (e1 : DyadicRouteBE1Cache) (n : ℕ)
    (rho z : DyadicInterval) : DyadicInterval :=
  let state := dyadicRouteBBuildBoxState n rho z
  let tail := dyadicRouteBCachedTailValue e1 n rho z
  fastCachedFullBoundUsingTail cache state n rho z tail

theorem fastCachedFullBoundUsingTail_eq
    {N : ℕ} (cache : DyadicRouteBCellCache N) (n : ℕ)
    (rho z tail : DyadicInterval) :
    fastCachedFullBoundUsingTail cache
        (dyadicRouteBBuildBoxState n rho z) n rho z tail =
      certifiedCachedFullBoundUsingTail cache n rho z tail := by
  rfl

theorem fastCachedFullBound_eq
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (e1 : DyadicRouteBE1Cache) (n : ℕ) (rho z : DyadicInterval) :
    fastCachedFullBound cache e1 n rho z =
      certifiedCachedFullBound cache e1 n rho z := by
  rfl

def fastFiniteAcceptedAtUsingTail
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z tail : DyadicInterval) : Bool :=
  let bound := fastCachedFullBoundUsingTail cache state n rho z tail
  decide (bound.hi < bound4395FiniteThreshold.lo) &&
    decide (FastCachedFullAdmissible cache n rho z)

def fastFiniteTargetAwareAccepted
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) : Bool :=
  let state := dyadicRouteBBuildBoxState n rho z
  let tail := dyadicRouteBCachedTailValue cache.e1 n rho z
  fastFiniteAcceptedAtUsingTail cache.cells256 state n rho z tail ||
    fastFiniteAcceptedAtUsingTail cache.cells1024 state n rho z tail ||
    fastFiniteAcceptedAtUsingTail cache.cells2048 state n rho z tail

theorem fastFiniteTargetAwareAccepted_eq
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) :
    fastFiniteTargetAwareAccepted cache n rho z =
      bound4395FiniteTargetAwareAccepted cache n rho z := by
  have bool_ext (a b : Bool) (h : a = true ↔ b = true) : a = b := by
    cases a <;> cases b <;> simp_all
  apply bool_ext
  simp only [fastFiniteTargetAwareAccepted,
    bound4395FiniteTargetAwareAccepted, fastFiniteAcceptedAtUsingTail,
    bound4395FiniteAcceptedAt, certifiedCachedFullBound,
    fastCachedFullBoundUsingTail_eq, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, fastCachedFullAdmissible_eq]

#print axioms fastLowCellValue_eq
#print axioms fastHighCellValue_eq
#print axioms fastLowCellAdmissible_iff
#print axioms fastHighCellAdmissible_iff
#print axioms fastCachedFullAdmissible_eq
#print axioms fastCachedFullBound_eq
#print axioms fastFiniteTargetAwareAccepted_eq

end BerryEsseen
