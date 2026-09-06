import BerryEsseen.Certificates.Finite.N21.Shard0000
import BerryEsseen.Certificates.Finite.N21.Shard0001
import BerryEsseen.Certificates.Finite.N21.Shard0002
import BerryEsseen.Certificates.Finite.N21.Shard0003
import BerryEsseen.Certificates.Finite.N21.Shard0004
import BerryEsseen.Certificates.Finite.N21.Shard0005
import BerryEsseen.Certificates.Finite.N21.Shard0006
import BerryEsseen.Certificates.Finite.N21.Shard0007
import BerryEsseen.Certificates.Finite.N21.Shard0008
import BerryEsseen.Certificates.Finite.N21.Shard0009
import BerryEsseen.Certificates.Finite.N21.Shard0010
import BerryEsseen.Certificates.Finite.N21.Shard0011
import BerryEsseen.Certificates.Finite.N21.Shard0012
import BerryEsseen.Certificates.Finite.N21.Shard0013
import BerryEsseen.Certificates.Finite.N21.Shard0014
import BerryEsseen.Certificates.Finite.N21.Shard0015
import BerryEsseen.Certificates.Finite.N21.Shard0016

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN21Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho finiteN21Shard0000Tree finiteN21Shard0001Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN21Shard0002Tree finiteN21Shard0003Tree) finiteN21Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN21Shard0005Tree finiteN21Shard0006Tree) finiteN21Shard0007Tree) (.splitRho (.splitZ (.splitRho finiteN21Shard0008Tree finiteN21Shard0009Tree) (.splitRho (.splitZ finiteN21Shard0010Tree (.splitRho finiteN21Shard0011Tree finiteN21Shard0012Tree)) finiteN21Shard0013Tree)) finiteN21Shard0014Tree)) finiteN21Shard0015Tree)) finiteN21Shard0016Tree))

theorem finiteN21_parsed :
    (certifiedOldLeafCode 21).bind dyadicRouteBLeafTreeOfCode =
      some finiteN21Tree := by
  native_decide

theorem finiteN21_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 21 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN21_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN21Shard0000_checked finiteN21Shard0001_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN21Shard0002_checked finiteN21Shard0003_checked) finiteN21Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN21Shard0005_checked finiteN21Shard0006_checked) finiteN21Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN21Shard0008_checked finiteN21Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN21Shard0010_checked (bound4395FiniteVerifySplitRho_true finiteN21Shard0011_checked finiteN21Shard0012_checked)) finiteN21Shard0013_checked)) finiteN21Shard0014_checked)) finiteN21Shard0015_checked)) finiteN21Shard0016_checked))

end BerryEsseen
