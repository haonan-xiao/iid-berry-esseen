import BerryEsseen.Certificates.Finite.N69.Shard0000
import BerryEsseen.Certificates.Finite.N69.Shard0001
import BerryEsseen.Certificates.Finite.N69.Shard0002
import BerryEsseen.Certificates.Finite.N69.Shard0003
import BerryEsseen.Certificates.Finite.N69.Shard0004
import BerryEsseen.Certificates.Finite.N69.Shard0005
import BerryEsseen.Certificates.Finite.N69.Shard0006
import BerryEsseen.Certificates.Finite.N69.Shard0007
import BerryEsseen.Certificates.Finite.N69.Shard0008
import BerryEsseen.Certificates.Finite.N69.Shard0009
import BerryEsseen.Certificates.Finite.N69.Shard0010
import BerryEsseen.Certificates.Finite.N69.Shard0011
import BerryEsseen.Certificates.Finite.N69.Shard0012
import BerryEsseen.Certificates.Finite.N69.Shard0013
import BerryEsseen.Certificates.Finite.N69.Shard0014
import BerryEsseen.Certificates.Finite.N69.Shard0015
import BerryEsseen.Certificates.Finite.N69.Shard0016
import BerryEsseen.Certificates.Finite.N69.Shard0017
import BerryEsseen.Certificates.Finite.N69.Shard0018
import BerryEsseen.Certificates.Finite.N69.Shard0019
import BerryEsseen.Certificates.Finite.N69.Shard0020
import BerryEsseen.Certificates.Finite.N69.Shard0021
import BerryEsseen.Certificates.Finite.N69.Shard0022
import BerryEsseen.Certificates.Finite.N69.Shard0023
import BerryEsseen.Certificates.Finite.N69.Shard0024
import BerryEsseen.Certificates.Finite.N69.Shard0025
import BerryEsseen.Certificates.Finite.N69.Shard0026
import BerryEsseen.Certificates.Finite.N69.Shard0027
import BerryEsseen.Certificates.Finite.N69.Shard0028
import BerryEsseen.Certificates.Finite.N69.Shard0029
import BerryEsseen.Certificates.Finite.N69.Shard0030

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN69Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN69Shard0000Tree (.splitRho (.splitZ finiteN69Shard0001Tree finiteN69Shard0002Tree) finiteN69Shard0003Tree)) finiteN69Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN69Shard0005Tree (.splitRho (.splitZ finiteN69Shard0006Tree finiteN69Shard0007Tree) finiteN69Shard0008Tree)) finiteN69Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN69Shard0010Tree (.splitRho (.splitZ finiteN69Shard0011Tree finiteN69Shard0012Tree) finiteN69Shard0013Tree)) finiteN69Shard0014Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN69Shard0015Tree (.splitRho (.splitZ finiteN69Shard0016Tree finiteN69Shard0017Tree) finiteN69Shard0018Tree)) finiteN69Shard0019Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN69Shard0020Tree finiteN69Shard0021Tree) finiteN69Shard0022Tree) (.splitRho (.splitZ finiteN69Shard0023Tree (.splitRho finiteN69Shard0024Tree finiteN69Shard0025Tree)) finiteN69Shard0026Tree)) finiteN69Shard0027Tree)) finiteN69Shard0028Tree)) finiteN69Shard0029Tree)) finiteN69Shard0030Tree))

theorem finiteN69_parsed :
    (certifiedOldLeafCode 69).bind dyadicRouteBLeafTreeOfCode =
      some finiteN69Tree := by
  native_decide

theorem finiteN69_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 69 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN69_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0001_checked finiteN69Shard0002_checked) finiteN69Shard0003_checked)) finiteN69Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0006_checked finiteN69Shard0007_checked) finiteN69Shard0008_checked)) finiteN69Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0010_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0011_checked finiteN69Shard0012_checked) finiteN69Shard0013_checked)) finiteN69Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0015_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0016_checked finiteN69Shard0017_checked) finiteN69Shard0018_checked)) finiteN69Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0020_checked finiteN69Shard0021_checked) finiteN69Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN69Shard0023_checked (bound4395FiniteVerifySplitRho_true finiteN69Shard0024_checked finiteN69Shard0025_checked)) finiteN69Shard0026_checked)) finiteN69Shard0027_checked)) finiteN69Shard0028_checked)) finiteN69Shard0029_checked)) finiteN69Shard0030_checked))

end BerryEsseen
