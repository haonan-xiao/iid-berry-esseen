import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN71Shard0013Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLRLLRZRLLRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLRZLLLRZRLLRLLZRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLRZLRLLLRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLRZRLLRLLZRLLRLLRZRLLRZLLLZRLLRLL").getD .leaf

theorem finiteN71Shard0013_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 71 5
        finiteN71Shard0013Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 71))))) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
