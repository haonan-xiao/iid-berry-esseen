import BerryEsseen.Certificates.Finite.N10.Shard0000
import BerryEsseen.Certificates.Finite.N10.Shard0001
import BerryEsseen.Certificates.Finite.N10.Shard0002
import BerryEsseen.Certificates.Finite.N10.Shard0003
import BerryEsseen.Certificates.Finite.N10.Shard0004
import BerryEsseen.Certificates.Finite.N10.Shard0005
import BerryEsseen.Certificates.Finite.N10.Shard0006
import BerryEsseen.Certificates.Finite.N10.Shard0007
import BerryEsseen.Certificates.Finite.N10.Shard0008
import BerryEsseen.Certificates.Finite.N10.Shard0009
import BerryEsseen.Certificates.Finite.N10.Shard0010
import BerryEsseen.Certificates.Finite.N10.Shard0011
import BerryEsseen.Certificates.Finite.N10.Shard0012
import BerryEsseen.Certificates.Finite.N10.Shard0013
import BerryEsseen.Certificates.Finite.N10.Shard0014
import BerryEsseen.Certificates.Finite.N10.Shard0015

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN10Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN10Shard0000Tree (.splitRho (.splitZ finiteN10Shard0001Tree (.splitRho (.splitZ (.splitRho finiteN10Shard0002Tree finiteN10Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN10Shard0004Tree finiteN10Shard0005Tree) finiteN10Shard0006Tree) (.splitRho (.splitZ (.splitRho finiteN10Shard0007Tree finiteN10Shard0008Tree) (.splitRho (.splitZ finiteN10Shard0009Tree finiteN10Shard0010Tree) finiteN10Shard0011Tree)) finiteN10Shard0012Tree)) finiteN10Shard0013Tree)) finiteN10Shard0014Tree)) finiteN10Shard0015Tree))

theorem finiteN10_parsed :
    (certifiedOldLeafCode 10).bind dyadicRouteBLeafTreeOfCode =
      some finiteN10Tree := by
  native_decide

theorem finiteN10_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 10 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN10_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN10Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN10Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN10Shard0002_checked finiteN10Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN10Shard0004_checked finiteN10Shard0005_checked) finiteN10Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN10Shard0007_checked finiteN10Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN10Shard0009_checked finiteN10Shard0010_checked) finiteN10Shard0011_checked)) finiteN10Shard0012_checked)) finiteN10Shard0013_checked)) finiteN10Shard0014_checked)) finiteN10Shard0015_checked))

end BerryEsseen
