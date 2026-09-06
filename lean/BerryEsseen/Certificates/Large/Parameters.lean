import BerryEsseen.Interval.Large.TargetCover
import BerryEsseen.Certificates.Data.BaselinePartitions

/-!
# Certificates / Large / Parameters
-/

namespace BerryEsseen

def bound4395LargeMiddleConcreteCertificate : Bool :=
  bound4395LargeRefinedLeafCodeCertificate
    .middle 4 oldLargeMiddleCodeValue

def bound4395LargeUpperConcreteCertificate : Bool :=
  bound4395LargeRefinedLeafCodeCertificate
    .upper 4 oldLargeUpperCodeValue

end BerryEsseen
