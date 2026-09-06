import BerryEsseen.Certificates.Finite.N89.Shard0000
import BerryEsseen.Certificates.Finite.N89.Shard0001
import BerryEsseen.Certificates.Finite.N89.Shard0002
import BerryEsseen.Certificates.Finite.N89.Shard0003
import BerryEsseen.Certificates.Finite.N89.Shard0004
import BerryEsseen.Certificates.Finite.N89.Shard0005
import BerryEsseen.Certificates.Finite.N89.Shard0006
import BerryEsseen.Certificates.Finite.N89.Shard0007
import BerryEsseen.Certificates.Finite.N89.Shard0008
import BerryEsseen.Certificates.Finite.N89.Shard0009
import BerryEsseen.Certificates.Finite.N89.Shard0010
import BerryEsseen.Certificates.Finite.N89.Shard0011
import BerryEsseen.Certificates.Finite.N89.Shard0012
import BerryEsseen.Certificates.Finite.N89.Shard0013
import BerryEsseen.Certificates.Finite.N89.Shard0014
import BerryEsseen.Certificates.Finite.N89.Shard0015
import BerryEsseen.Certificates.Finite.N89.Shard0016
import BerryEsseen.Certificates.Finite.N89.Shard0017
import BerryEsseen.Certificates.Finite.N89.Shard0018
import BerryEsseen.Certificates.Finite.N89.Shard0019
import BerryEsseen.Certificates.Finite.N89.Shard0020
import BerryEsseen.Certificates.Finite.N89.Shard0021
import BerryEsseen.Certificates.Finite.N89.Shard0022
import BerryEsseen.Certificates.Finite.N89.Shard0023
import BerryEsseen.Certificates.Finite.N89.Shard0024
import BerryEsseen.Certificates.Finite.N89.Shard0025
import BerryEsseen.Certificates.Finite.N89.Shard0026
import BerryEsseen.Certificates.Finite.N89.Shard0027
import BerryEsseen.Certificates.Finite.N89.Shard0028
import BerryEsseen.Certificates.Finite.N89.Shard0029
import BerryEsseen.Certificates.Finite.N89.Shard0030
import BerryEsseen.Certificates.Finite.N89.Shard0031
import BerryEsseen.Certificates.Finite.N89.Shard0032
import BerryEsseen.Certificates.Finite.N89.Shard0033
import BerryEsseen.Certificates.Finite.N89.Shard0034
import BerryEsseen.Certificates.Finite.N89.Shard0035
import BerryEsseen.Certificates.Finite.N89.Shard0036
import BerryEsseen.Certificates.Finite.N89.Shard0037

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN89Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN89Shard0000Tree (.splitRho (.splitZ finiteN89Shard0001Tree finiteN89Shard0002Tree) finiteN89Shard0003Tree)) finiteN89Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN89Shard0005Tree (.splitRho (.splitZ finiteN89Shard0006Tree finiteN89Shard0007Tree) finiteN89Shard0008Tree)) finiteN89Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN89Shard0010Tree finiteN89Shard0011Tree) finiteN89Shard0012Tree) (.splitRho (.splitZ finiteN89Shard0013Tree finiteN89Shard0014Tree) finiteN89Shard0015Tree)) finiteN89Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN89Shard0017Tree finiteN89Shard0018Tree) (.splitRho (.splitZ finiteN89Shard0019Tree finiteN89Shard0020Tree) finiteN89Shard0021Tree)) finiteN89Shard0022Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN89Shard0023Tree (.splitRho finiteN89Shard0024Tree finiteN89Shard0025Tree)) finiteN89Shard0026Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN89Shard0027Tree finiteN89Shard0028Tree) finiteN89Shard0029Tree) (.splitRho (.splitZ finiteN89Shard0030Tree finiteN89Shard0031Tree) finiteN89Shard0032Tree)) finiteN89Shard0033Tree)) finiteN89Shard0034Tree)) finiteN89Shard0035Tree)) finiteN89Shard0036Tree)) finiteN89Shard0037Tree))

theorem finiteN89_parsed :
    (certifiedOldLeafCode 89).bind dyadicRouteBLeafTreeOfCode =
      some finiteN89Tree := by
  native_decide

theorem finiteN89_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 89 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN89_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0001_checked finiteN89Shard0002_checked) finiteN89Shard0003_checked)) finiteN89Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0006_checked finiteN89Shard0007_checked) finiteN89Shard0008_checked)) finiteN89Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0010_checked finiteN89Shard0011_checked) finiteN89Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0013_checked finiteN89Shard0014_checked) finiteN89Shard0015_checked)) finiteN89Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN89Shard0017_checked finiteN89Shard0018_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0019_checked finiteN89Shard0020_checked) finiteN89Shard0021_checked)) finiteN89Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0023_checked (bound4395FiniteVerifySplitRho_true finiteN89Shard0024_checked finiteN89Shard0025_checked)) finiteN89Shard0026_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0027_checked finiteN89Shard0028_checked) finiteN89Shard0029_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN89Shard0030_checked finiteN89Shard0031_checked) finiteN89Shard0032_checked)) finiteN89Shard0033_checked)) finiteN89Shard0034_checked)) finiteN89Shard0035_checked)) finiteN89Shard0036_checked)) finiteN89Shard0037_checked))

end BerryEsseen
