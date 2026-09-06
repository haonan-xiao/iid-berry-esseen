import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN10Shard0000Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRZLLLZRLLRLLRZRZLLLRZRLLRLLLZRLLRLLZRZRLLRLLLRZRLLRLLZLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLZRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRZLLLRZLRLLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRZRLLRLLZRLLRLLRZRZLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN10Shard0000_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 10 6
        finiteN10Shard0000Tree (dyadicRouteBFiniteRootRho 10) (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
