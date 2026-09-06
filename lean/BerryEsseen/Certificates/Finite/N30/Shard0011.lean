import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN30Shard0011Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZLLLRZLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZRZRZRLLRLLLRZRLLRLLRLLZRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRLLRLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRZRLLRZLLLZRLLRLLRZRZLRLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN30Shard0011_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 30 5
        finiteN30Shard0011Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 30))))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
