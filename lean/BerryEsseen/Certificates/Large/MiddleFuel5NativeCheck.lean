import BerryEsseen.Interval.Large.MiddleFuel5ShardedComposition

/-!
# Certificates / Large / Middle Fuel5Native Check
-/

namespace BerryEsseen

theorem bound4395LargeMiddleFuel5ConcreteCertificate_checked :
    bound4395LargeRefinedLeafCodeCertificate
      .middle 5 oldLargeMiddleCodeValue = true := by
  exact bound4395LargeMiddleFuel5ShardedFullCertificate_checked

end BerryEsseen
