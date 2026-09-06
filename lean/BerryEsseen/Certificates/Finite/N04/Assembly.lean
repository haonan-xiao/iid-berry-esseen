import BerryEsseen.Certificates.Finite.N04.Shard0000
import BerryEsseen.Certificates.Finite.N04.Shard0001
import BerryEsseen.Certificates.Finite.N04.Shard0002
import BerryEsseen.Certificates.Finite.N04.Shard0003
import BerryEsseen.Certificates.Finite.N04.Shard0004
import BerryEsseen.Certificates.Finite.N04.Shard0005
import BerryEsseen.Certificates.Finite.N04.Shard0006
import BerryEsseen.Certificates.Finite.N04.Shard0007
import BerryEsseen.Certificates.Finite.N04.Shard0008
import BerryEsseen.Certificates.Finite.N04.Shard0009
import BerryEsseen.Certificates.Finite.N04.Shard0010
import BerryEsseen.Certificates.Finite.N04.Shard0011
import BerryEsseen.Certificates.Finite.N04.Shard0012
import BerryEsseen.Certificates.Finite.N04.Shard0013
import BerryEsseen.Certificates.Finite.N04.Shard0014
import BerryEsseen.Certificates.Finite.N04.Shard0015
import BerryEsseen.Certificates.Finite.N04.Shard0016
import BerryEsseen.Certificates.Finite.N04.Shard0017
import BerryEsseen.Certificates.Finite.N04.Shard0018
import BerryEsseen.Certificates.Finite.N04.Shard0019
import BerryEsseen.Certificates.Finite.N04.Shard0020
import BerryEsseen.Certificates.Finite.N04.Shard0021
import BerryEsseen.Certificates.Finite.N04.Shard0022
import BerryEsseen.Certificates.Finite.N04.Shard0023

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN04Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN04Shard0000Tree (.splitRho (.splitZ finiteN04Shard0001Tree (.splitRho (.splitZ finiteN04Shard0002Tree (.splitRho (.splitZ (.splitRho finiteN04Shard0003Tree finiteN04Shard0004Tree) (.splitRho (.splitZ (.splitRho finiteN04Shard0005Tree finiteN04Shard0006Tree) (.splitRho (.splitZ (.splitRho finiteN04Shard0007Tree finiteN04Shard0008Tree) (.splitRho (.splitZ finiteN04Shard0009Tree (.splitRho finiteN04Shard0010Tree finiteN04Shard0011Tree)) (.splitZ finiteN04Shard0012Tree finiteN04Shard0013Tree))) (.splitRho (.splitZ finiteN04Shard0014Tree finiteN04Shard0015Tree) finiteN04Shard0016Tree))) (.splitZ finiteN04Shard0017Tree (.splitRho finiteN04Shard0018Tree finiteN04Shard0019Tree)))) (.splitRho finiteN04Shard0020Tree finiteN04Shard0021Tree))) finiteN04Shard0022Tree)) finiteN04Shard0023Tree))

theorem finiteN04_parsed :
    (certifiedOldLeafCode 4).bind dyadicRouteBLeafTreeOfCode =
      some finiteN04Tree := by
  native_decide

theorem finiteN04_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 4 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN04_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN04Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN04Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN04Shard0002_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN04Shard0003_checked finiteN04Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN04Shard0005_checked finiteN04Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN04Shard0007_checked finiteN04Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN04Shard0009_checked (bound4395FiniteVerifySplitRho_true finiteN04Shard0010_checked finiteN04Shard0011_checked)) (bound4395FiniteVerifySplitZ_true finiteN04Shard0012_checked finiteN04Shard0013_checked))) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN04Shard0014_checked finiteN04Shard0015_checked) finiteN04Shard0016_checked))) (bound4395FiniteVerifySplitZ_true finiteN04Shard0017_checked (bound4395FiniteVerifySplitRho_true finiteN04Shard0018_checked finiteN04Shard0019_checked)))) (bound4395FiniteVerifySplitRho_true finiteN04Shard0020_checked finiteN04Shard0021_checked))) finiteN04Shard0022_checked)) finiteN04Shard0023_checked))

end BerryEsseen
