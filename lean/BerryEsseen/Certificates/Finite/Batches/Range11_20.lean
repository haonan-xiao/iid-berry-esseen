import BerryEsseen.Interval.Finite.AdaptiveFullCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem bound4395FiniteTargetAwareBatch11_20_checked :
    ∀ n : Fin 21, 11 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 5 = true := by
  native_decide

end BerryEsseen
