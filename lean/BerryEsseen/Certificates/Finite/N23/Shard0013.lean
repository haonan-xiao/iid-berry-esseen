import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN23Shard0013Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLLRZRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLRZZRLLRLLZRLLRLLZRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLRZZRLLRZLLLZRZLRLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN23Shard0013_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 23 5
        finiteN23Shard0013Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 23)))))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
