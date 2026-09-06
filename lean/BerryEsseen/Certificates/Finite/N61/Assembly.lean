import BerryEsseen.Certificates.Finite.N61.Shard0000
import BerryEsseen.Certificates.Finite.N61.Shard0001
import BerryEsseen.Certificates.Finite.N61.Shard0002
import BerryEsseen.Certificates.Finite.N61.Shard0003
import BerryEsseen.Certificates.Finite.N61.Shard0004
import BerryEsseen.Certificates.Finite.N61.Shard0005
import BerryEsseen.Certificates.Finite.N61.Shard0006
import BerryEsseen.Certificates.Finite.N61.Shard0007
import BerryEsseen.Certificates.Finite.N61.Shard0008
import BerryEsseen.Certificates.Finite.N61.Shard0009
import BerryEsseen.Certificates.Finite.N61.Shard0010
import BerryEsseen.Certificates.Finite.N61.Shard0011
import BerryEsseen.Certificates.Finite.N61.Shard0012
import BerryEsseen.Certificates.Finite.N61.Shard0013
import BerryEsseen.Certificates.Finite.N61.Shard0014
import BerryEsseen.Certificates.Finite.N61.Shard0015
import BerryEsseen.Certificates.Finite.N61.Shard0016
import BerryEsseen.Certificates.Finite.N61.Shard0017
import BerryEsseen.Certificates.Finite.N61.Shard0018
import BerryEsseen.Certificates.Finite.N61.Shard0019
import BerryEsseen.Certificates.Finite.N61.Shard0020
import BerryEsseen.Certificates.Finite.N61.Shard0021
import BerryEsseen.Certificates.Finite.N61.Shard0022
import BerryEsseen.Certificates.Finite.N61.Shard0023
import BerryEsseen.Certificates.Finite.N61.Shard0024
import BerryEsseen.Certificates.Finite.N61.Shard0025
import BerryEsseen.Certificates.Finite.N61.Shard0026
import BerryEsseen.Certificates.Finite.N61.Shard0027
import BerryEsseen.Certificates.Finite.N61.Shard0028
import BerryEsseen.Certificates.Finite.N61.Shard0029
import BerryEsseen.Certificates.Finite.N61.Shard0030

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN61Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN61Shard0000Tree (.splitRho (.splitZ finiteN61Shard0001Tree finiteN61Shard0002Tree) finiteN61Shard0003Tree)) finiteN61Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN61Shard0005Tree (.splitRho (.splitZ finiteN61Shard0006Tree finiteN61Shard0007Tree) finiteN61Shard0008Tree)) finiteN61Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN61Shard0010Tree finiteN61Shard0011Tree) (.splitRho (.splitZ finiteN61Shard0012Tree finiteN61Shard0013Tree) finiteN61Shard0014Tree)) finiteN61Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN61Shard0016Tree (.splitRho (.splitZ finiteN61Shard0017Tree finiteN61Shard0018Tree) finiteN61Shard0019Tree)) finiteN61Shard0020Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN61Shard0021Tree finiteN61Shard0022Tree) finiteN61Shard0023Tree) (.splitRho (.splitZ finiteN61Shard0024Tree finiteN61Shard0025Tree) finiteN61Shard0026Tree)) finiteN61Shard0027Tree)) finiteN61Shard0028Tree)) finiteN61Shard0029Tree)) finiteN61Shard0030Tree))

theorem finiteN61_parsed :
    (certifiedOldLeafCode 61).bind dyadicRouteBLeafTreeOfCode =
      some finiteN61Tree := by
  native_decide

theorem finiteN61_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 61 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN61_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN61Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN61Shard0001_checked finiteN61Shard0002_checked) finiteN61Shard0003_checked)) finiteN61Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN61Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN61Shard0006_checked finiteN61Shard0007_checked) finiteN61Shard0008_checked)) finiteN61Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN61Shard0010_checked finiteN61Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN61Shard0012_checked finiteN61Shard0013_checked) finiteN61Shard0014_checked)) finiteN61Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN61Shard0016_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN61Shard0017_checked finiteN61Shard0018_checked) finiteN61Shard0019_checked)) finiteN61Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN61Shard0021_checked finiteN61Shard0022_checked) finiteN61Shard0023_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN61Shard0024_checked finiteN61Shard0025_checked) finiteN61Shard0026_checked)) finiteN61Shard0027_checked)) finiteN61Shard0028_checked)) finiteN61Shard0029_checked)) finiteN61Shard0030_checked))

end BerryEsseen
