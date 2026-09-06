import BerryEsseen.Certificates.Small.Parameters

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem variableAlphaSmallLowerConcreteCertificate_checked :
    variableAlphaSmallLowerConcreteCertificate = true := by
  native_decide

end BerryEsseen
