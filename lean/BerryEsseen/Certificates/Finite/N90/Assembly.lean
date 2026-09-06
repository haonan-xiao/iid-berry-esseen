import BerryEsseen.Certificates.Finite.N90.Shard0000
import BerryEsseen.Certificates.Finite.N90.Shard0001
import BerryEsseen.Certificates.Finite.N90.Shard0002
import BerryEsseen.Certificates.Finite.N90.Shard0003
import BerryEsseen.Certificates.Finite.N90.Shard0004
import BerryEsseen.Certificates.Finite.N90.Shard0005
import BerryEsseen.Certificates.Finite.N90.Shard0006
import BerryEsseen.Certificates.Finite.N90.Shard0007
import BerryEsseen.Certificates.Finite.N90.Shard0008
import BerryEsseen.Certificates.Finite.N90.Shard0009
import BerryEsseen.Certificates.Finite.N90.Shard0010
import BerryEsseen.Certificates.Finite.N90.Shard0011
import BerryEsseen.Certificates.Finite.N90.Shard0012
import BerryEsseen.Certificates.Finite.N90.Shard0013
import BerryEsseen.Certificates.Finite.N90.Shard0014
import BerryEsseen.Certificates.Finite.N90.Shard0015
import BerryEsseen.Certificates.Finite.N90.Shard0016
import BerryEsseen.Certificates.Finite.N90.Shard0017
import BerryEsseen.Certificates.Finite.N90.Shard0018
import BerryEsseen.Certificates.Finite.N90.Shard0019
import BerryEsseen.Certificates.Finite.N90.Shard0020
import BerryEsseen.Certificates.Finite.N90.Shard0021
import BerryEsseen.Certificates.Finite.N90.Shard0022
import BerryEsseen.Certificates.Finite.N90.Shard0023
import BerryEsseen.Certificates.Finite.N90.Shard0024
import BerryEsseen.Certificates.Finite.N90.Shard0025
import BerryEsseen.Certificates.Finite.N90.Shard0026
import BerryEsseen.Certificates.Finite.N90.Shard0027
import BerryEsseen.Certificates.Finite.N90.Shard0028
import BerryEsseen.Certificates.Finite.N90.Shard0029
import BerryEsseen.Certificates.Finite.N90.Shard0030
import BerryEsseen.Certificates.Finite.N90.Shard0031
import BerryEsseen.Certificates.Finite.N90.Shard0032
import BerryEsseen.Certificates.Finite.N90.Shard0033
import BerryEsseen.Certificates.Finite.N90.Shard0034
import BerryEsseen.Certificates.Finite.N90.Shard0035
import BerryEsseen.Certificates.Finite.N90.Shard0036

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN90Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN90Shard0000Tree (.splitRho (.splitZ finiteN90Shard0001Tree finiteN90Shard0002Tree) finiteN90Shard0003Tree)) finiteN90Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN90Shard0005Tree (.splitRho (.splitZ finiteN90Shard0006Tree finiteN90Shard0007Tree) finiteN90Shard0008Tree)) finiteN90Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN90Shard0010Tree finiteN90Shard0011Tree) finiteN90Shard0012Tree) (.splitRho (.splitZ finiteN90Shard0013Tree finiteN90Shard0014Tree) finiteN90Shard0015Tree)) finiteN90Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN90Shard0017Tree (.splitRho (.splitZ finiteN90Shard0018Tree finiteN90Shard0019Tree) finiteN90Shard0020Tree)) finiteN90Shard0021Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN90Shard0022Tree (.splitRho finiteN90Shard0023Tree finiteN90Shard0024Tree)) finiteN90Shard0025Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN90Shard0026Tree finiteN90Shard0027Tree) finiteN90Shard0028Tree) (.splitRho (.splitZ finiteN90Shard0029Tree finiteN90Shard0030Tree) finiteN90Shard0031Tree)) finiteN90Shard0032Tree)) finiteN90Shard0033Tree)) finiteN90Shard0034Tree)) finiteN90Shard0035Tree)) finiteN90Shard0036Tree))

theorem finiteN90_parsed :
    (certifiedOldLeafCode 90).bind dyadicRouteBLeafTreeOfCode =
      some finiteN90Tree := by
  native_decide

theorem finiteN90_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 90 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN90_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0001_checked finiteN90Shard0002_checked) finiteN90Shard0003_checked)) finiteN90Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0006_checked finiteN90Shard0007_checked) finiteN90Shard0008_checked)) finiteN90Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0010_checked finiteN90Shard0011_checked) finiteN90Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0013_checked finiteN90Shard0014_checked) finiteN90Shard0015_checked)) finiteN90Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0017_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0018_checked finiteN90Shard0019_checked) finiteN90Shard0020_checked)) finiteN90Shard0021_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0022_checked (bound4395FiniteVerifySplitRho_true finiteN90Shard0023_checked finiteN90Shard0024_checked)) finiteN90Shard0025_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0026_checked finiteN90Shard0027_checked) finiteN90Shard0028_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN90Shard0029_checked finiteN90Shard0030_checked) finiteN90Shard0031_checked)) finiteN90Shard0032_checked)) finiteN90Shard0033_checked)) finiteN90Shard0034_checked)) finiteN90Shard0035_checked)) finiteN90Shard0036_checked))

end BerryEsseen
