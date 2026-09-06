import BerryEsseen.Certificates.Finite.N95.Shard0000
import BerryEsseen.Certificates.Finite.N95.Shard0001
import BerryEsseen.Certificates.Finite.N95.Shard0002
import BerryEsseen.Certificates.Finite.N95.Shard0003
import BerryEsseen.Certificates.Finite.N95.Shard0004
import BerryEsseen.Certificates.Finite.N95.Shard0005
import BerryEsseen.Certificates.Finite.N95.Shard0006
import BerryEsseen.Certificates.Finite.N95.Shard0007
import BerryEsseen.Certificates.Finite.N95.Shard0008
import BerryEsseen.Certificates.Finite.N95.Shard0009
import BerryEsseen.Certificates.Finite.N95.Shard0010
import BerryEsseen.Certificates.Finite.N95.Shard0011
import BerryEsseen.Certificates.Finite.N95.Shard0012
import BerryEsseen.Certificates.Finite.N95.Shard0013
import BerryEsseen.Certificates.Finite.N95.Shard0014
import BerryEsseen.Certificates.Finite.N95.Shard0015
import BerryEsseen.Certificates.Finite.N95.Shard0016
import BerryEsseen.Certificates.Finite.N95.Shard0017
import BerryEsseen.Certificates.Finite.N95.Shard0018
import BerryEsseen.Certificates.Finite.N95.Shard0019
import BerryEsseen.Certificates.Finite.N95.Shard0020
import BerryEsseen.Certificates.Finite.N95.Shard0021
import BerryEsseen.Certificates.Finite.N95.Shard0022
import BerryEsseen.Certificates.Finite.N95.Shard0023
import BerryEsseen.Certificates.Finite.N95.Shard0024
import BerryEsseen.Certificates.Finite.N95.Shard0025
import BerryEsseen.Certificates.Finite.N95.Shard0026
import BerryEsseen.Certificates.Finite.N95.Shard0027
import BerryEsseen.Certificates.Finite.N95.Shard0028
import BerryEsseen.Certificates.Finite.N95.Shard0029
import BerryEsseen.Certificates.Finite.N95.Shard0030
import BerryEsseen.Certificates.Finite.N95.Shard0031
import BerryEsseen.Certificates.Finite.N95.Shard0032
import BerryEsseen.Certificates.Finite.N95.Shard0033
import BerryEsseen.Certificates.Finite.N95.Shard0034
import BerryEsseen.Certificates.Finite.N95.Shard0035
import BerryEsseen.Certificates.Finite.N95.Shard0036

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN95Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN95Shard0000Tree (.splitRho (.splitZ finiteN95Shard0001Tree finiteN95Shard0002Tree) finiteN95Shard0003Tree)) finiteN95Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN95Shard0005Tree (.splitRho (.splitZ finiteN95Shard0006Tree finiteN95Shard0007Tree) finiteN95Shard0008Tree)) finiteN95Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN95Shard0010Tree finiteN95Shard0011Tree) finiteN95Shard0012Tree) (.splitRho (.splitZ finiteN95Shard0013Tree finiteN95Shard0014Tree) finiteN95Shard0015Tree)) finiteN95Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN95Shard0017Tree finiteN95Shard0018Tree) (.splitRho (.splitZ finiteN95Shard0019Tree finiteN95Shard0020Tree) finiteN95Shard0021Tree)) finiteN95Shard0022Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN95Shard0023Tree (.splitRho finiteN95Shard0024Tree finiteN95Shard0025Tree)) finiteN95Shard0026Tree) (.splitRho (.splitZ (.splitRho finiteN95Shard0027Tree finiteN95Shard0028Tree) (.splitRho (.splitZ finiteN95Shard0029Tree finiteN95Shard0030Tree) finiteN95Shard0031Tree)) finiteN95Shard0032Tree)) finiteN95Shard0033Tree)) finiteN95Shard0034Tree)) finiteN95Shard0035Tree)) finiteN95Shard0036Tree))

theorem finiteN95_parsed :
    (certifiedOldLeafCode 95).bind dyadicRouteBLeafTreeOfCode =
      some finiteN95Tree := by
  native_decide

theorem finiteN95_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 95 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN95_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN95Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN95Shard0001_checked finiteN95Shard0002_checked) finiteN95Shard0003_checked)) finiteN95Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN95Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN95Shard0006_checked finiteN95Shard0007_checked) finiteN95Shard0008_checked)) finiteN95Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN95Shard0010_checked finiteN95Shard0011_checked) finiteN95Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN95Shard0013_checked finiteN95Shard0014_checked) finiteN95Shard0015_checked)) finiteN95Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN95Shard0017_checked finiteN95Shard0018_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN95Shard0019_checked finiteN95Shard0020_checked) finiteN95Shard0021_checked)) finiteN95Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN95Shard0023_checked (bound4395FiniteVerifySplitRho_true finiteN95Shard0024_checked finiteN95Shard0025_checked)) finiteN95Shard0026_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN95Shard0027_checked finiteN95Shard0028_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN95Shard0029_checked finiteN95Shard0030_checked) finiteN95Shard0031_checked)) finiteN95Shard0032_checked)) finiteN95Shard0033_checked)) finiteN95Shard0034_checked)) finiteN95Shard0035_checked)) finiteN95Shard0036_checked))

end BerryEsseen
