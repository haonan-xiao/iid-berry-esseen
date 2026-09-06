import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN68Shard0009Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRLLRLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRZLLLRZLRLLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRZRLLRLLLRZRLLRLLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN68Shard0009_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 68 5
        finiteN68Shard0009Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 68))))) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
