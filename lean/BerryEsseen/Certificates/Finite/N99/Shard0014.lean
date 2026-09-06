import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN99Shard0014Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRLLRZLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN99Shard0014_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 99 5
        finiteN99Shard0014Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 99))))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
