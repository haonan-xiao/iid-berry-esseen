import BerryEsseen.Interval.Small.FixedExponentSplitCover
import BerryEsseen.Interval.Large.Cover

/-!
# Certificates / Data / Baseline Partitions
-/

namespace BerryEsseen

def extractConcreteLeafCode (source marker : String) : Option String :=
  match source.splitOn marker with
  | _before :: after :: _ =>
      match after.toList.dropWhile (fun c => c != '\"') with
      | '\"' :: code => some (String.ofList (code.takeWhile (fun c => c != '\"')))
      | _ => none
  | _ => none

def oldLargeSmallSource : String :=
  include_str "../../DyadicPrawitzLargeNLeafCertificateSmall.lean"

def oldLargeMiddleSource : String :=
  include_str "../../DyadicPrawitzLargeNLeafCertificateMiddle.lean"

def oldLargeUpperSource : String :=
  include_str "../../DyadicPrawitzLargeNLeafCertificateUpper.lean"

def oldLargeSmallCode : Option String :=
  extractConcreteLeafCode oldLargeSmallSource
    "def routeBLargeSmallLeafCode : String :="

def oldLargeMiddleCode : Option String :=
  extractConcreteLeafCode oldLargeMiddleSource
    "def routeBLargeMiddleLeafCode : String :="

def oldLargeUpperCode : Option String :=
  extractConcreteLeafCode oldLargeUpperSource
    "def routeBLargeUpperLeafCode : String :="

def oldLargeSmallCodeValue : String :=
  oldLargeSmallCode.getD ""

def oldLargeMiddleCodeValue : String :=
  oldLargeMiddleCode.getD ""

def oldLargeUpperCodeValue : String :=
  oldLargeUpperCode.getD ""

def largeSmallLowerConcreteCertificate : Bool :=
  certifiedLargeSmallRefinedLeafCodeCertificateAt
    4 oldLargeSmallCodeValue dyadicRouteBUnitInterval
      certifiedLargeSmallLowerRootZ

def largeSmallUpperConcreteCertificate : Bool :=
  certifiedLargeSmallRefinedLeafCodeCertificateAt
    8 oldLargeSmallCodeValue dyadicRouteBUnitInterval
      certifiedLargeSmallUpperRootZ

def largeMiddleConcreteCertificate : Bool :=
  certifiedLargeRefinedLeafCodeCertificate
    .middle 4 oldLargeMiddleCodeValue

def largeUpperConcreteCertificate : Bool :=
  certifiedLargeRefinedLeafCodeCertificate
    .upper 4 oldLargeUpperCodeValue

end BerryEsseen
