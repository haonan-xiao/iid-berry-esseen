import BerryEsseen.Certificates.Large.Parameters

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem bound4395LargeUpperFuel8ConcreteCertificate_checked :
    bound4395LargeRefinedLeafCodeCertificate
      .upper 8 oldLargeUpperCodeValue = true := by
  native_decide

end BerryEsseen
