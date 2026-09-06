import BerryEsseen.Interval.Large.Shard

/-!
# Certificates / Large / Middle Fuel5Shard Batch03Native Check
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def bound4395LargeMiddleFuel5Shard03Code : String := "ZXZXZ11Z11XZ2X11Z2X11ZXZ11Z11XZ2X11Z2X11XZXZX22XZ22Z22ZX22XZ22Z22XZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22XZ22Z22ZX22XZ22Z22XZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22"

def bound4395LargeMiddleFuel5Shard03Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard03Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard05Code : String := "XZXZ01Z01XZ1X11Z1X11ZXZ01Z01XZ1X11Z1X11"

def bound4395LargeMiddleFuel5Shard05Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard05Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard11Code : String := "ZXZXZ11Z11XZ1X11Z1X11ZXZ11Z11XZ1X11Z1X11XZXZX22XZ12Z12ZX22XZ12Z12XZXZX22XZ12Z12ZX22XZ12Z12XZXZ22Z22XZX22X22ZX22X22ZXZ22Z22XZX22X22ZX22X22ZXZX22XZ12Z12ZX22XZ12Z12XZXZ22Z22XZX22X22ZX22X22ZXZ22Z22XZX22X22ZX22X22ZXZX22XZ12Z12ZX22XZ12Z12XZXZX22XZ12Z12ZX22XZ12Z12XZXZ22Z22XZX22X22ZX22X22ZXZ22Z22XZX22X22ZX22X2Z22ZXZX22XZ12Z12ZX22XZ12Z12XZXZ22Z22XZX22XZ22Z22ZX22XZ22Z22ZXZ22Z22XZX22XZ22Z22ZX22XZ22Z22"

def bound4395LargeMiddleFuel5Shard11Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard11Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard13Code : String := "XZXZ11Z11XZ1X11Z1X11ZXZ11Z11XZ1X11Z1X11"

def bound4395LargeMiddleFuel5Shard13Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard13Code).getD (.leaf .n256)

def Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate : Bool :=
  let cache := certifiedLargeBuildResolutionCache
  bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard03Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard05Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard11Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard13Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))))))

theorem Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate_checked :
    Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate = true := by
  native_decide

theorem bound4395LargeMiddleFuel5Shard03Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard03Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard03Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard05Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard11Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard13Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate_checked
  exact hparts.1

theorem bound4395LargeMiddleFuel5Shard03Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard03Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard03Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard03Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard05Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard05Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard03Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard05Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard11Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard13Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate_checked
  exact hparts.2.1

theorem bound4395LargeMiddleFuel5Shard05Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard05Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard05Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard05Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard11Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard11Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard03Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard05Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard11Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard13Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate_checked
  exact hparts.2.2.1

theorem bound4395LargeMiddleFuel5Shard11Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard11Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard11Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard11Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard13Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard13Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard03Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard05Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard11Code (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard13Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch03NativeCheckCertificate_checked
  exact hparts.2.2.2

theorem bound4395LargeMiddleFuel5Shard13Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard13Tree (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
  have h := bound4395LargeMiddleFuel5Shard13Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard13Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

end BerryEsseen
