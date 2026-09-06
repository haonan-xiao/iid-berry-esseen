import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN05Shard0001Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRLLZLRLLRZRLLRLLZRLLRLLRZLZLRLLZLLRZRZRLLRZLRLLLZRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRLLRZLLLRZZRLLRLLZRLLRLLZRLLRLLRZRZLLLRZZLLZRLLRLLZLRLLZRLLRZLLL").getD .leaf

theorem finiteN05Shard0001_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 5 6
        finiteN05Shard0001Tree (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 5)) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
