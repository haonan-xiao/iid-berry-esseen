import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN26Shard0002Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRZRLLRLLRLLRZRLLRLLRLLRZLRLLLRZRZRLLRLLRLLRZRZLLLRZLRLLLRLLRZRLLRLLZLLRZRLLRLLZRLLRLLRZRZRZRZRLLRLLLRZRLLRLLLRLLRZRZRLLRLLRLLRZRLLRLLRLLRLLRZRLLRLLZLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLRZLLLRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLRZRLLRLLZRLLRLLRZRLLRZLLLZRLLRLL").getD .leaf

theorem finiteN26Shard0002_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 26 5
        finiteN26Shard0002Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 26))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
