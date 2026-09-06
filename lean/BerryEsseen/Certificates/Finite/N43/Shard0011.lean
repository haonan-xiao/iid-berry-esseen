import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN43Shard0011Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRZLLLRLLRZRZRLLRLLLRZRLLRLLLRLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLLRZRLLRLLLRLLRZRZRLLRLLLRZRLLRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN43Shard0011_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 43 5
        finiteN43Shard0011Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 43))))) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
