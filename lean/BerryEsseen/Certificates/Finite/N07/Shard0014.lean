import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN07Shard0014Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZZRZRLLRLLRLLRZRZLLLRZRLLRLLZLRLLRZLZLLZLLZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZZLRLLZRLLRLLZRLLRLLRZRZRLLRLLZRLLRLLRZRLLRZLLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLZRZRLLRZLLLZRLLRLLRZRZLZLRLLZLRLLRZZRLLRLLZRLLRLLZRLLRLLZRZLLZLLRZZLLZRLLRLLZLRLL").getD .leaf

theorem finiteN07Shard0014_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 7 6
        finiteN07Shard0014Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 7)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
