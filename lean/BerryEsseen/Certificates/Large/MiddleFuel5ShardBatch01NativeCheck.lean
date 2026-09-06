import BerryEsseen.Interval.Large.Shard

/-!
# Certificates / Large / Middle Fuel5Shard Batch01Native Check
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def bound4395LargeMiddleFuel5Shard01Code : String := "XZXZ00Z00XZ1X11Z1X11ZXZ00Z00XZ12Z01"

def bound4395LargeMiddleFuel5Shard01Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard01Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard06Code : String := "ZXZXZ11Z11XZ1X11Z1X11ZXZ11Z11XZ1X11Z1X11XZXZX22XZ12Z12ZX22XZ12Z12XZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22XZ12Z12ZX22XZ12Z12XZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22"

def bound4395LargeMiddleFuel5Shard06Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard06Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard16Code : String := "XZXZX22XZ12Z12ZX22XZ12Z12XZXZX22XZ12Z12ZX22XZ12Z12XZXZ2X22Z2X22XZX22XZ22Z22ZX22XZ22Z22ZXZ2X22Z2X22XZX22XZ22Z22ZX22XZ22Z22ZXZX22XZ12Z12ZX22XZ12Z12XZXZ2X22Z2X22XZX22XZ22Z22ZX22XZ22Z22ZXZ2X22Z2X22XZX22XZ22Z22ZX22XZ22Z22ZXZX22XZ12Z12ZXZ11Z11XZ12Z12XZXZX22XZ12Z12ZX22XZ22Z22XZXZ2X22Z2X22XZX22XZ22Z22ZX22XZ22Z22ZXZ2X22Z2X22XZX22XZ22Z22ZX22XZ22Z22ZXZX22XZ22Z22ZX22XZ22Z22XZXZ2X22Z2X22XZX2Z22XZ22Z22ZXZ22Z22XZ22Z22ZXZ2X22Z2X22XZXZ22Z22XZ22Z22ZXZ22Z22XZ22Z22"

def bound4395LargeMiddleFuel5Shard16Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard16Code).getD (.leaf .n256)

def Bound4395LargeMiddleFuel5ShardBatch01NativeCheckCertificate : Bool :=
  let cache := certifiedLargeBuildResolutionCache
  bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard01Code (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard06Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard16Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))))))

theorem Bound4395LargeMiddleFuel5ShardBatch01NativeCheckCertificate_checked :
    Bound4395LargeMiddleFuel5ShardBatch01NativeCheckCertificate = true := by
  native_decide

theorem bound4395LargeMiddleFuel5Shard01Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard01Code (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard01Code (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard06Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard16Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch01NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch01NativeCheckCertificate_checked
  exact hparts.1

theorem bound4395LargeMiddleFuel5Shard01Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard01Tree (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true := by
  have h := bound4395LargeMiddleFuel5Shard01Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard01Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard06Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard06Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard01Code (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard06Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard16Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch01NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch01NativeCheckCertificate_checked
  exact hparts.2.1

theorem bound4395LargeMiddleFuel5Shard06Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard06Tree (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard06Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard06Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard16Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard16Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard01Code (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard06Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard16Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch01NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch01NativeCheckCertificate_checked
  exact hparts.2.2

theorem bound4395LargeMiddleFuel5Shard16Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard16Tree (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
  have h := bound4395LargeMiddleFuel5Shard16Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard16Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

end BerryEsseen
