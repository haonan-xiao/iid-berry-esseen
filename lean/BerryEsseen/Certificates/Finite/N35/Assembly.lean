import BerryEsseen.Certificates.Finite.N35.Shard0000
import BerryEsseen.Certificates.Finite.N35.Shard0001
import BerryEsseen.Certificates.Finite.N35.Shard0002
import BerryEsseen.Certificates.Finite.N35.Shard0003
import BerryEsseen.Certificates.Finite.N35.Shard0004
import BerryEsseen.Certificates.Finite.N35.Shard0005
import BerryEsseen.Certificates.Finite.N35.Shard0006
import BerryEsseen.Certificates.Finite.N35.Shard0007
import BerryEsseen.Certificates.Finite.N35.Shard0008
import BerryEsseen.Certificates.Finite.N35.Shard0009
import BerryEsseen.Certificates.Finite.N35.Shard0010
import BerryEsseen.Certificates.Finite.N35.Shard0011
import BerryEsseen.Certificates.Finite.N35.Shard0012
import BerryEsseen.Certificates.Finite.N35.Shard0013
import BerryEsseen.Certificates.Finite.N35.Shard0014
import BerryEsseen.Certificates.Finite.N35.Shard0015
import BerryEsseen.Certificates.Finite.N35.Shard0016
import BerryEsseen.Certificates.Finite.N35.Shard0017
import BerryEsseen.Certificates.Finite.N35.Shard0018
import BerryEsseen.Certificates.Finite.N35.Shard0019
import BerryEsseen.Certificates.Finite.N35.Shard0020
import BerryEsseen.Certificates.Finite.N35.Shard0021

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN35Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN35Shard0000Tree finiteN35Shard0001Tree) finiteN35Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN35Shard0003Tree finiteN35Shard0004Tree) finiteN35Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN35Shard0006Tree (.splitRho finiteN35Shard0007Tree finiteN35Shard0008Tree)) finiteN35Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN35Shard0010Tree finiteN35Shard0011Tree) finiteN35Shard0012Tree) (.splitRho (.splitZ (.splitRho finiteN35Shard0013Tree finiteN35Shard0014Tree) (.splitRho (.splitZ finiteN35Shard0015Tree finiteN35Shard0016Tree) finiteN35Shard0017Tree)) finiteN35Shard0018Tree)) finiteN35Shard0019Tree)) finiteN35Shard0020Tree)) finiteN35Shard0021Tree))

theorem finiteN35_parsed :
    (certifiedOldLeafCode 35).bind dyadicRouteBLeafTreeOfCode =
      some finiteN35Tree := by
  native_decide

theorem finiteN35_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 35 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN35_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN35Shard0000_checked finiteN35Shard0001_checked) finiteN35Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN35Shard0003_checked finiteN35Shard0004_checked) finiteN35Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN35Shard0006_checked (bound4395FiniteVerifySplitRho_true finiteN35Shard0007_checked finiteN35Shard0008_checked)) finiteN35Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN35Shard0010_checked finiteN35Shard0011_checked) finiteN35Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN35Shard0013_checked finiteN35Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN35Shard0015_checked finiteN35Shard0016_checked) finiteN35Shard0017_checked)) finiteN35Shard0018_checked)) finiteN35Shard0019_checked)) finiteN35Shard0020_checked)) finiteN35Shard0021_checked))

end BerryEsseen
