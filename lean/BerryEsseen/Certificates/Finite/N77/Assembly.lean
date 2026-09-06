import BerryEsseen.Certificates.Finite.N77.Shard0000
import BerryEsseen.Certificates.Finite.N77.Shard0001
import BerryEsseen.Certificates.Finite.N77.Shard0002
import BerryEsseen.Certificates.Finite.N77.Shard0003
import BerryEsseen.Certificates.Finite.N77.Shard0004
import BerryEsseen.Certificates.Finite.N77.Shard0005
import BerryEsseen.Certificates.Finite.N77.Shard0006
import BerryEsseen.Certificates.Finite.N77.Shard0007
import BerryEsseen.Certificates.Finite.N77.Shard0008
import BerryEsseen.Certificates.Finite.N77.Shard0009
import BerryEsseen.Certificates.Finite.N77.Shard0010
import BerryEsseen.Certificates.Finite.N77.Shard0011
import BerryEsseen.Certificates.Finite.N77.Shard0012
import BerryEsseen.Certificates.Finite.N77.Shard0013
import BerryEsseen.Certificates.Finite.N77.Shard0014
import BerryEsseen.Certificates.Finite.N77.Shard0015
import BerryEsseen.Certificates.Finite.N77.Shard0016
import BerryEsseen.Certificates.Finite.N77.Shard0017
import BerryEsseen.Certificates.Finite.N77.Shard0018
import BerryEsseen.Certificates.Finite.N77.Shard0019
import BerryEsseen.Certificates.Finite.N77.Shard0020
import BerryEsseen.Certificates.Finite.N77.Shard0021
import BerryEsseen.Certificates.Finite.N77.Shard0022
import BerryEsseen.Certificates.Finite.N77.Shard0023
import BerryEsseen.Certificates.Finite.N77.Shard0024
import BerryEsseen.Certificates.Finite.N77.Shard0025
import BerryEsseen.Certificates.Finite.N77.Shard0026
import BerryEsseen.Certificates.Finite.N77.Shard0027
import BerryEsseen.Certificates.Finite.N77.Shard0028
import BerryEsseen.Certificates.Finite.N77.Shard0029
import BerryEsseen.Certificates.Finite.N77.Shard0030

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN77Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN77Shard0000Tree finiteN77Shard0001Tree) finiteN77Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN77Shard0003Tree (.splitRho (.splitZ finiteN77Shard0004Tree finiteN77Shard0005Tree) finiteN77Shard0006Tree)) finiteN77Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN77Shard0008Tree (.splitRho (.splitZ finiteN77Shard0009Tree finiteN77Shard0010Tree) finiteN77Shard0011Tree)) finiteN77Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN77Shard0013Tree (.splitRho (.splitZ finiteN77Shard0014Tree finiteN77Shard0015Tree) finiteN77Shard0016Tree)) finiteN77Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN77Shard0018Tree finiteN77Shard0019Tree) finiteN77Shard0020Tree) (.splitRho (.splitZ (.splitRho finiteN77Shard0021Tree finiteN77Shard0022Tree) (.splitRho (.splitZ finiteN77Shard0023Tree finiteN77Shard0024Tree) finiteN77Shard0025Tree)) finiteN77Shard0026Tree)) finiteN77Shard0027Tree)) finiteN77Shard0028Tree)) finiteN77Shard0029Tree)) finiteN77Shard0030Tree))

theorem finiteN77_parsed :
    (certifiedOldLeafCode 77).bind dyadicRouteBLeafTreeOfCode =
      some finiteN77Tree := by
  native_decide

theorem finiteN77_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 77 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN77_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN77Shard0000_checked finiteN77Shard0001_checked) finiteN77Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN77Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN77Shard0004_checked finiteN77Shard0005_checked) finiteN77Shard0006_checked)) finiteN77Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN77Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN77Shard0009_checked finiteN77Shard0010_checked) finiteN77Shard0011_checked)) finiteN77Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN77Shard0013_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN77Shard0014_checked finiteN77Shard0015_checked) finiteN77Shard0016_checked)) finiteN77Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN77Shard0018_checked finiteN77Shard0019_checked) finiteN77Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN77Shard0021_checked finiteN77Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN77Shard0023_checked finiteN77Shard0024_checked) finiteN77Shard0025_checked)) finiteN77Shard0026_checked)) finiteN77Shard0027_checked)) finiteN77Shard0028_checked)) finiteN77Shard0029_checked)) finiteN77Shard0030_checked))

end BerryEsseen
