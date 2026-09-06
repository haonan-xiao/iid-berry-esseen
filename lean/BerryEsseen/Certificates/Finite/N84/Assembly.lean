import BerryEsseen.Certificates.Finite.N84.Shard0000
import BerryEsseen.Certificates.Finite.N84.Shard0001
import BerryEsseen.Certificates.Finite.N84.Shard0002
import BerryEsseen.Certificates.Finite.N84.Shard0003
import BerryEsseen.Certificates.Finite.N84.Shard0004
import BerryEsseen.Certificates.Finite.N84.Shard0005
import BerryEsseen.Certificates.Finite.N84.Shard0006
import BerryEsseen.Certificates.Finite.N84.Shard0007
import BerryEsseen.Certificates.Finite.N84.Shard0008
import BerryEsseen.Certificates.Finite.N84.Shard0009
import BerryEsseen.Certificates.Finite.N84.Shard0010
import BerryEsseen.Certificates.Finite.N84.Shard0011
import BerryEsseen.Certificates.Finite.N84.Shard0012
import BerryEsseen.Certificates.Finite.N84.Shard0013
import BerryEsseen.Certificates.Finite.N84.Shard0014
import BerryEsseen.Certificates.Finite.N84.Shard0015
import BerryEsseen.Certificates.Finite.N84.Shard0016
import BerryEsseen.Certificates.Finite.N84.Shard0017
import BerryEsseen.Certificates.Finite.N84.Shard0018
import BerryEsseen.Certificates.Finite.N84.Shard0019
import BerryEsseen.Certificates.Finite.N84.Shard0020
import BerryEsseen.Certificates.Finite.N84.Shard0021
import BerryEsseen.Certificates.Finite.N84.Shard0022
import BerryEsseen.Certificates.Finite.N84.Shard0023
import BerryEsseen.Certificates.Finite.N84.Shard0024
import BerryEsseen.Certificates.Finite.N84.Shard0025
import BerryEsseen.Certificates.Finite.N84.Shard0026
import BerryEsseen.Certificates.Finite.N84.Shard0027
import BerryEsseen.Certificates.Finite.N84.Shard0028
import BerryEsseen.Certificates.Finite.N84.Shard0029
import BerryEsseen.Certificates.Finite.N84.Shard0030

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN84Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN84Shard0000Tree (.splitRho (.splitZ finiteN84Shard0001Tree finiteN84Shard0002Tree) finiteN84Shard0003Tree)) finiteN84Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN84Shard0005Tree (.splitRho (.splitZ finiteN84Shard0006Tree finiteN84Shard0007Tree) finiteN84Shard0008Tree)) finiteN84Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN84Shard0010Tree finiteN84Shard0011Tree) (.splitRho (.splitZ finiteN84Shard0012Tree finiteN84Shard0013Tree) finiteN84Shard0014Tree)) finiteN84Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN84Shard0016Tree (.splitRho (.splitZ finiteN84Shard0017Tree finiteN84Shard0018Tree) finiteN84Shard0019Tree)) finiteN84Shard0020Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN84Shard0021Tree finiteN84Shard0022Tree) finiteN84Shard0023Tree) (.splitRho (.splitZ finiteN84Shard0024Tree finiteN84Shard0025Tree) finiteN84Shard0026Tree)) finiteN84Shard0027Tree)) finiteN84Shard0028Tree)) finiteN84Shard0029Tree)) finiteN84Shard0030Tree))

theorem finiteN84_parsed :
    (certifiedOldLeafCode 84).bind dyadicRouteBLeafTreeOfCode =
      some finiteN84Tree := by
  native_decide

theorem finiteN84_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 84 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN84_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN84Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN84Shard0001_checked finiteN84Shard0002_checked) finiteN84Shard0003_checked)) finiteN84Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN84Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN84Shard0006_checked finiteN84Shard0007_checked) finiteN84Shard0008_checked)) finiteN84Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN84Shard0010_checked finiteN84Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN84Shard0012_checked finiteN84Shard0013_checked) finiteN84Shard0014_checked)) finiteN84Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN84Shard0016_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN84Shard0017_checked finiteN84Shard0018_checked) finiteN84Shard0019_checked)) finiteN84Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN84Shard0021_checked finiteN84Shard0022_checked) finiteN84Shard0023_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN84Shard0024_checked finiteN84Shard0025_checked) finiteN84Shard0026_checked)) finiteN84Shard0027_checked)) finiteN84Shard0028_checked)) finiteN84Shard0029_checked)) finiteN84Shard0030_checked))

end BerryEsseen
