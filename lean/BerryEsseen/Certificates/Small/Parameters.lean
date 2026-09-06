import BerryEsseen.Interval.Small.SplitCover
import BerryEsseen.Certificates.Data.BaselinePartitions

/-!
# Certificates / Small / Parameters
-/

namespace BerryEsseen

def variableAlphaSmallLowerConcreteCertificate : Bool :=
  variableAlphaSmallRefinedLeafCodeCertificateAt
    4 oldLargeSmallCodeValue dyadicRouteBUnitInterval
      certifiedLargeSmallLowerRootZ

def variableAlphaSmallUpperConcreteCertificate : Bool :=
  variableAlphaSmallRefinedLeafCodeCertificateAt
    8 oldLargeSmallCodeValue dyadicRouteBUnitInterval
      certifiedLargeSmallUpperRootZ

end BerryEsseen
