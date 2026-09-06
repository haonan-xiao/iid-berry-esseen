import BerryEsseen.Interval.Large.Shard

/-!
# Certificates / Large / Middle Fuel5Shard Batch02Native Check
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def bound4395LargeMiddleFuel5Shard04Code : String := "ZXZXZ11Z11XZ2X11Z2X11ZXZ11Z11XZ2X11Z1X11XZXZX22XZ22Z22ZX22XZ22Z22XZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22XZ22Z12ZX22XZ12Z12XZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22"

def bound4395LargeMiddleFuel5Shard04Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard04Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard08Code : String := "XZXZ00Z00XZ01Z01ZXZ00Z00XZ01Z01"

def bound4395LargeMiddleFuel5Shard08Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard08Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard12Code : String := "XZXZ01Z00XZ1X11Z1X11ZXZ00Z00XZ1X11Z1X11"

def bound4395LargeMiddleFuel5Shard12Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard12Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard14Code : String := "XZXZX22XZ12Z12ZX22XZ12Z12XZXZX22XZ12Z12ZX22XZ12Z12XZXZ22Z22XZX22XZ22Z22ZX22XZ22Z22ZXZ22Z22XZX22XZ22Z22ZX22XZ22Z22ZXZX22XZ12Z12ZX22XZ12Z12XZXZ22Z22XZX22XZ22Z22ZX22XZ22Z22ZXZ22Z22XZX22XZ22Z22ZX22XZ22Z22ZXZX22XZ12Z12ZX22XZ12Z12XZXZX22XZ12Z12ZX22XZ12Z12XZXZ22Z22XZX22XZ22Z22ZX22XZ22Z22ZXZ22Z2X22XZX22XZ22Z22ZX22XZ22Z22ZXZX22XZ12Z12ZX22XZ12Z12XZXZ2X22Z2X22XZX22XZ22Z22ZX22XZ22Z22ZXZ2X22Z2X22XZX22XZ22Z22ZX22XZ22Z22"

def bound4395LargeMiddleFuel5Shard14Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard14Code).getD (.leaf .n256)

def Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate : Bool :=
  let cache := certifiedLargeBuildResolutionCache
  bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard04Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard08Code (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard12Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard14Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))))))

theorem Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate_checked :
    Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate = true := by
  native_decide

theorem bound4395LargeMiddleFuel5Shard04Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard04Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard04Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard08Code (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard12Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard14Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate_checked
  exact hparts.1

theorem bound4395LargeMiddleFuel5Shard04Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard04Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard04Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard04Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard08Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard08Code (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard04Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard08Code (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard12Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard14Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate_checked
  exact hparts.2.1

theorem bound4395LargeMiddleFuel5Shard08Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard08Tree (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true := by
  have h := bound4395LargeMiddleFuel5Shard08Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard08Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard12Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard12Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard04Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard08Code (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard12Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard14Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate_checked
  exact hparts.2.2.1

theorem bound4395LargeMiddleFuel5Shard12Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard12Tree (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard12Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard12Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard14Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard14Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard04Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard08Code (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard12Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard14Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch02NativeCheckCertificate_checked
  exact hparts.2.2.2

theorem bound4395LargeMiddleFuel5Shard14Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard14Tree (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
  have h := bound4395LargeMiddleFuel5Shard14Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard14Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

end BerryEsseen
