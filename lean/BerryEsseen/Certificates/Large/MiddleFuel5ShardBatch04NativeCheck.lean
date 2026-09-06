import BerryEsseen.Interval.Large.Shard

/-!
# Certificates / Large / Middle Fuel5Shard Batch04Native Check
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def bound4395LargeMiddleFuel5Shard02Code : String := "XZXZ01Z01XZ2X11Z1X11ZXZ01Z01XZ1X11Z1X11"

def bound4395LargeMiddleFuel5Shard02Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard02Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard07Code : String := "ZXZXZ11Z11XZ1X11Z1X11ZXZ11Z11XZ1X11Z1X11XZXZX22XZ12Z12ZX22XZ12Z12XZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22X22ZX22X22XZXZ22Z22XZ2X22Z2X22ZXZ22Z22XZ2X22Z2X22ZXZX22XZ12Z12ZX22XZ12Z12XZXZX22X22ZX22X22XZXZ22Z22XZX22X22ZX22X22ZXZ22Z22XZX22X22ZX22X22ZXZX22X22ZX22X22XZXZ22Z22XZX22X22ZX22X22ZXZ22Z22XZX22X22ZX22X22"

def bound4395LargeMiddleFuel5Shard07Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard07Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard09Code : String := "XZXZ01Z01XZ1X11Z1X11ZXZ01Z01XZ1X11Z1X11"

def bound4395LargeMiddleFuel5Shard09Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard09Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard10Code : String := "ZXZXZ11Z11XZ1X11Z1X11ZXZ11Z11XZ1X11Z1X11XZXZX22XZ12Z12ZX22XZ12Z12XZXZX22X22ZX22X22XZXZ22Z22XZX22X22ZX22X22ZXZ22Z22XZX22X22ZX22X22ZXZX22X22ZX22X22XZXZ22Z22XZX22X22ZX22X22ZXZ22Z22XZX22X22ZX22X22ZXZX22XZ12Z12ZX22XZ12Z12XZXZX22X22ZX22X22XZXZ22Z22XZX22X22ZX22X22ZXZ22Z22XZX22X22ZX22X22ZXZX22XZ12Z12ZX22XZ12Z12XZXZ22Z22XZX22X22ZX22X22ZXZ22Z22XZX22X22ZX22X22"

def bound4395LargeMiddleFuel5Shard10Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard10Code).getD (.leaf .n256)

def bound4395LargeMiddleFuel5Shard15Code : String := "XZXZ11Z11XZ1X11Z1X11ZXZ11Z11XZ1X11Z1X11"

def bound4395LargeMiddleFuel5Shard15Tree : DyadicRouteBLargeLeafTree :=
  (dyadicRouteBLargeLeafTreeOfCode bound4395LargeMiddleFuel5Shard15Code).getD (.leaf .n256)

def Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate : Bool :=
  let cache := certifiedLargeBuildResolutionCache
  bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard02Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard07Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard09Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard10Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) &&
    (bound4395LargeSubtreeCodeCertificateAtWithCache cache .middle 5
      bound4395LargeMiddleFuel5Shard15Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))))))))

theorem Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate_checked :
    Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate = true := by
  native_decide

theorem bound4395LargeMiddleFuel5Shard02Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard02Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard02Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard07Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard09Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard10Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard15Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate_checked
  exact hparts.1

theorem bound4395LargeMiddleFuel5Shard02Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard02Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard02Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard02Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard07Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard07Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard02Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard07Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard09Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard10Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard15Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate_checked
  exact hparts.2.1

theorem bound4395LargeMiddleFuel5Shard07Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard07Tree (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard07Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard07Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard09Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard09Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard02Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard07Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard09Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard10Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard15Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate_checked
  exact hparts.2.2.1

theorem bound4395LargeMiddleFuel5Shard09Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard09Tree (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard09Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard09Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard10Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard10Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard02Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard07Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard09Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard10Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard15Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate_checked
  exact hparts.2.2.2.1

theorem bound4395LargeMiddleFuel5Shard10Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard10Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true := by
  have h := bound4395LargeMiddleFuel5Shard10Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard10Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

theorem bound4395LargeMiddleFuel5Shard15Certificate_checked :
    bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard15Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
  have hparts :
      bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard02Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard07Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard09Code (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard10Code (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval))) = true ∧
        bound4395LargeSubtreeCodeCertificateAt .middle 5
      bound4395LargeMiddleFuel5Shard15Code (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
    simpa only [Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate,
      bound4395LargeSubtreeCodeCertificateAt,
      Bool.and_eq_true] using Bound4395LargeMiddleFuel5ShardBatch04NativeCheckCertificate_checked
  exact hparts.2.2.2.2

theorem bound4395LargeMiddleFuel5Shard15Verify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5Shard15Tree (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBUnitInterval)))) = true := by
  have h := bound4395LargeMiddleFuel5Shard15Certificate_checked
  unfold bound4395LargeSubtreeCodeCertificateAt at h
  unfold bound4395LargeSubtreeCodeCertificateAtWithCache at h
  unfold bound4395LargeMiddleFuel5Shard15Tree
  split at h
  next tree htree => simpa [htree] using h
  next => simp at h

end BerryEsseen
