import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN06Shard0002Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRZLLLRLLRZRZLRLLLRZRLLRLLRLLRZLLZLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLZLRLLRZRZRLLRLLRLLRZRLLRZLLLRZLLLRZRLLRLLZRLLRLLZRZRLLRLLRLLRZRZLLLRZLRLLRLLRZLLZLLRZZRZLLLRZLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLZRZLLZLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN06Shard0002_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 6 6
        finiteN06Shard0002Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 6))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
