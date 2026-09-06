import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN29Shard0002Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZZRZLLLRZRLLRLLLZRZRLLRLLLRZRLLRLLRLLZRLLRLL").getD .leaf

theorem finiteN29Shard0002_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 29 5
        finiteN29Shard0002Tree (dyadicRouteBRightHalf (dyadicRouteBFiniteRootRho 29)) (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
