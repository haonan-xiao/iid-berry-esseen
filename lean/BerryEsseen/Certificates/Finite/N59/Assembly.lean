import BerryEsseen.Certificates.Finite.N59.Shard0000
import BerryEsseen.Certificates.Finite.N59.Shard0001
import BerryEsseen.Certificates.Finite.N59.Shard0002
import BerryEsseen.Certificates.Finite.N59.Shard0003
import BerryEsseen.Certificates.Finite.N59.Shard0004
import BerryEsseen.Certificates.Finite.N59.Shard0005
import BerryEsseen.Certificates.Finite.N59.Shard0006
import BerryEsseen.Certificates.Finite.N59.Shard0007
import BerryEsseen.Certificates.Finite.N59.Shard0008
import BerryEsseen.Certificates.Finite.N59.Shard0009
import BerryEsseen.Certificates.Finite.N59.Shard0010
import BerryEsseen.Certificates.Finite.N59.Shard0011
import BerryEsseen.Certificates.Finite.N59.Shard0012
import BerryEsseen.Certificates.Finite.N59.Shard0013
import BerryEsseen.Certificates.Finite.N59.Shard0014
import BerryEsseen.Certificates.Finite.N59.Shard0015
import BerryEsseen.Certificates.Finite.N59.Shard0016
import BerryEsseen.Certificates.Finite.N59.Shard0017
import BerryEsseen.Certificates.Finite.N59.Shard0018
import BerryEsseen.Certificates.Finite.N59.Shard0019
import BerryEsseen.Certificates.Finite.N59.Shard0020
import BerryEsseen.Certificates.Finite.N59.Shard0021
import BerryEsseen.Certificates.Finite.N59.Shard0022
import BerryEsseen.Certificates.Finite.N59.Shard0023
import BerryEsseen.Certificates.Finite.N59.Shard0024
import BerryEsseen.Certificates.Finite.N59.Shard0025
import BerryEsseen.Certificates.Finite.N59.Shard0026
import BerryEsseen.Certificates.Finite.N59.Shard0027

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN59Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN59Shard0000Tree (.splitRho finiteN59Shard0001Tree finiteN59Shard0002Tree)) finiteN59Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN59Shard0004Tree (.splitRho (.splitZ finiteN59Shard0005Tree finiteN59Shard0006Tree) finiteN59Shard0007Tree)) finiteN59Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN59Shard0009Tree (.splitRho (.splitZ finiteN59Shard0010Tree finiteN59Shard0011Tree) finiteN59Shard0012Tree)) finiteN59Shard0013Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN59Shard0014Tree (.splitRho finiteN59Shard0015Tree finiteN59Shard0016Tree)) finiteN59Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN59Shard0018Tree finiteN59Shard0019Tree) finiteN59Shard0020Tree) (.splitRho (.splitZ finiteN59Shard0021Tree finiteN59Shard0022Tree) finiteN59Shard0023Tree)) finiteN59Shard0024Tree)) finiteN59Shard0025Tree)) finiteN59Shard0026Tree)) finiteN59Shard0027Tree))

theorem finiteN59_parsed :
    (certifiedOldLeafCode 59).bind dyadicRouteBLeafTreeOfCode =
      some finiteN59Tree := by
  native_decide

theorem finiteN59_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 59 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN59_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN59Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN59Shard0001_checked finiteN59Shard0002_checked)) finiteN59Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN59Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN59Shard0005_checked finiteN59Shard0006_checked) finiteN59Shard0007_checked)) finiteN59Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN59Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN59Shard0010_checked finiteN59Shard0011_checked) finiteN59Shard0012_checked)) finiteN59Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN59Shard0014_checked (bound4395FiniteVerifySplitRho_true finiteN59Shard0015_checked finiteN59Shard0016_checked)) finiteN59Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN59Shard0018_checked finiteN59Shard0019_checked) finiteN59Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN59Shard0021_checked finiteN59Shard0022_checked) finiteN59Shard0023_checked)) finiteN59Shard0024_checked)) finiteN59Shard0025_checked)) finiteN59Shard0026_checked)) finiteN59Shard0027_checked))

end BerryEsseen
