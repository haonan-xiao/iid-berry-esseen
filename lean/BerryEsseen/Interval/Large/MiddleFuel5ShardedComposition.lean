import BerryEsseen.Certificates.Large.MiddleFuel5ShardBatch01NativeCheck
import BerryEsseen.Certificates.Large.MiddleFuel5ShardBatch02NativeCheck
import BerryEsseen.Certificates.Large.MiddleFuel5ShardBatch03NativeCheck
import BerryEsseen.Certificates.Large.MiddleFuel5ShardBatch04NativeCheck
import BerryEsseen.Certificates.Large.Parameters

/-!
# Interval / Large / Middle Fuel5Sharded Composition
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def bound4395LargeMiddleFuel5ShardedCoverTree : DyadicRouteBLargeLeafTree :=
  (.splitX
    (.splitZ
      bound4395LargeMiddleFuel5Shard01Tree
      (.splitX
        (.splitZ
          bound4395LargeMiddleFuel5Shard02Tree
          (.splitX
            bound4395LargeMiddleFuel5Shard03Tree
            bound4395LargeMiddleFuel5Shard04Tree))
        (.splitZ
          bound4395LargeMiddleFuel5Shard05Tree
          (.splitX
            bound4395LargeMiddleFuel5Shard06Tree
            bound4395LargeMiddleFuel5Shard07Tree))))
    (.splitZ
      bound4395LargeMiddleFuel5Shard08Tree
      (.splitX
        (.splitZ
          bound4395LargeMiddleFuel5Shard09Tree
          (.splitX
            bound4395LargeMiddleFuel5Shard10Tree
            bound4395LargeMiddleFuel5Shard11Tree))
        (.splitZ
          bound4395LargeMiddleFuel5Shard12Tree
          (.splitX
            (.splitZ
              bound4395LargeMiddleFuel5Shard13Tree
              bound4395LargeMiddleFuel5Shard14Tree)
            (.splitZ
              bound4395LargeMiddleFuel5Shard15Tree
              bound4395LargeMiddleFuel5Shard16Tree))))))

theorem bound4395LargeMiddleFuel5ShardedFullCodeParsed :
    dyadicRouteBLargeLeafTreeOfCode oldLargeMiddleCodeValue =
      some bound4395LargeMiddleFuel5ShardedCoverTree := by
  native_decide

theorem bound4395LargeMiddleFuel5ShardedCoverVerify_checked :
    bound4395LargeVerifyLeafTreeWithRefinement
      certifiedLargeBuildResolutionCache .middle 5
      bound4395LargeMiddleFuel5ShardedCoverTree dyadicRouteBUnitInterval
        dyadicRouteBUnitInterval = true := by
  exact (bound4395LargeVerifySplitX_true
    (bound4395LargeVerifySplitZ_true
      bound4395LargeMiddleFuel5Shard01Verify_checked
      (bound4395LargeVerifySplitX_true
        (bound4395LargeVerifySplitZ_true
          bound4395LargeMiddleFuel5Shard02Verify_checked
          (bound4395LargeVerifySplitX_true
            bound4395LargeMiddleFuel5Shard03Verify_checked
            bound4395LargeMiddleFuel5Shard04Verify_checked))
        (bound4395LargeVerifySplitZ_true
          bound4395LargeMiddleFuel5Shard05Verify_checked
          (bound4395LargeVerifySplitX_true
            bound4395LargeMiddleFuel5Shard06Verify_checked
            bound4395LargeMiddleFuel5Shard07Verify_checked))))
    (bound4395LargeVerifySplitZ_true
      bound4395LargeMiddleFuel5Shard08Verify_checked
      (bound4395LargeVerifySplitX_true
        (bound4395LargeVerifySplitZ_true
          bound4395LargeMiddleFuel5Shard09Verify_checked
          (bound4395LargeVerifySplitX_true
            bound4395LargeMiddleFuel5Shard10Verify_checked
            bound4395LargeMiddleFuel5Shard11Verify_checked))
        (bound4395LargeVerifySplitZ_true
          bound4395LargeMiddleFuel5Shard12Verify_checked
          (bound4395LargeVerifySplitX_true
            (bound4395LargeVerifySplitZ_true
              bound4395LargeMiddleFuel5Shard13Verify_checked
              bound4395LargeMiddleFuel5Shard14Verify_checked)
            (bound4395LargeVerifySplitZ_true
              bound4395LargeMiddleFuel5Shard15Verify_checked
              bound4395LargeMiddleFuel5Shard16Verify_checked))))))

theorem bound4395LargeMiddleFuel5ShardedFullCertificate_checked :
    bound4395LargeRefinedLeafCodeCertificate
      .middle 5 oldLargeMiddleCodeValue = true := by
  unfold bound4395LargeRefinedLeafCodeCertificate
  rw [bound4395LargeMiddleFuel5ShardedFullCodeParsed]
  simpa [bound4395LargeRefinedLeafTreeCertificate] using
    bound4395LargeMiddleFuel5ShardedCoverVerify_checked

end BerryEsseen
