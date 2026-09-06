import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN08Shard0011Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZLLLRZRLLRLLZLRLLZRLLRZLLZLLRZRZRLLRLLZRLLRLLRZRLLRZLLLZRLLRLLZRZRLLRLLZLRLLRZRLLRLLZRLLRLLZRZRLLRLLZRLLRLLRZRZLRLLZLLRZRLLRLLZRLLRLLZRZLLLRZLRLLZLL").getD .leaf

theorem finiteN08Shard0011_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 8 6
        finiteN08Shard0011Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 8)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
