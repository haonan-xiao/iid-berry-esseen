import BerryEsseen.Certificates.Finite.N97.Shard0000
import BerryEsseen.Certificates.Finite.N97.Shard0001
import BerryEsseen.Certificates.Finite.N97.Shard0002
import BerryEsseen.Certificates.Finite.N97.Shard0003
import BerryEsseen.Certificates.Finite.N97.Shard0004
import BerryEsseen.Certificates.Finite.N97.Shard0005
import BerryEsseen.Certificates.Finite.N97.Shard0006
import BerryEsseen.Certificates.Finite.N97.Shard0007
import BerryEsseen.Certificates.Finite.N97.Shard0008
import BerryEsseen.Certificates.Finite.N97.Shard0009
import BerryEsseen.Certificates.Finite.N97.Shard0010
import BerryEsseen.Certificates.Finite.N97.Shard0011
import BerryEsseen.Certificates.Finite.N97.Shard0012
import BerryEsseen.Certificates.Finite.N97.Shard0013
import BerryEsseen.Certificates.Finite.N97.Shard0014
import BerryEsseen.Certificates.Finite.N97.Shard0015
import BerryEsseen.Certificates.Finite.N97.Shard0016
import BerryEsseen.Certificates.Finite.N97.Shard0017
import BerryEsseen.Certificates.Finite.N97.Shard0018
import BerryEsseen.Certificates.Finite.N97.Shard0019
import BerryEsseen.Certificates.Finite.N97.Shard0020
import BerryEsseen.Certificates.Finite.N97.Shard0021
import BerryEsseen.Certificates.Finite.N97.Shard0022
import BerryEsseen.Certificates.Finite.N97.Shard0023
import BerryEsseen.Certificates.Finite.N97.Shard0024
import BerryEsseen.Certificates.Finite.N97.Shard0025
import BerryEsseen.Certificates.Finite.N97.Shard0026
import BerryEsseen.Certificates.Finite.N97.Shard0027
import BerryEsseen.Certificates.Finite.N97.Shard0028
import BerryEsseen.Certificates.Finite.N97.Shard0029
import BerryEsseen.Certificates.Finite.N97.Shard0030
import BerryEsseen.Certificates.Finite.N97.Shard0031
import BerryEsseen.Certificates.Finite.N97.Shard0032
import BerryEsseen.Certificates.Finite.N97.Shard0033
import BerryEsseen.Certificates.Finite.N97.Shard0034
import BerryEsseen.Certificates.Finite.N97.Shard0035
import BerryEsseen.Certificates.Finite.N97.Shard0036
import BerryEsseen.Certificates.Finite.N97.Shard0037
import BerryEsseen.Certificates.Finite.N97.Shard0038
import BerryEsseen.Certificates.Finite.N97.Shard0039
import BerryEsseen.Certificates.Finite.N97.Shard0040
import BerryEsseen.Certificates.Finite.N97.Shard0041

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN97Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN97Shard0000Tree (.splitRho (.splitZ finiteN97Shard0001Tree finiteN97Shard0002Tree) finiteN97Shard0003Tree)) finiteN97Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN97Shard0005Tree (.splitRho (.splitZ finiteN97Shard0006Tree finiteN97Shard0007Tree) finiteN97Shard0008Tree)) finiteN97Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN97Shard0010Tree finiteN97Shard0011Tree) finiteN97Shard0012Tree) (.splitRho (.splitZ finiteN97Shard0013Tree (.splitRho finiteN97Shard0014Tree finiteN97Shard0015Tree)) finiteN97Shard0016Tree)) finiteN97Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN97Shard0018Tree finiteN97Shard0019Tree) finiteN97Shard0020Tree) (.splitRho (.splitZ finiteN97Shard0021Tree finiteN97Shard0022Tree) finiteN97Shard0023Tree)) finiteN97Shard0024Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN97Shard0025Tree finiteN97Shard0026Tree) (.splitRho (.splitZ finiteN97Shard0027Tree finiteN97Shard0028Tree) finiteN97Shard0029Tree)) finiteN97Shard0030Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN97Shard0031Tree finiteN97Shard0032Tree) finiteN97Shard0033Tree) (.splitRho (.splitZ finiteN97Shard0034Tree finiteN97Shard0035Tree) finiteN97Shard0036Tree)) finiteN97Shard0037Tree)) finiteN97Shard0038Tree)) finiteN97Shard0039Tree)) finiteN97Shard0040Tree)) finiteN97Shard0041Tree))

theorem finiteN97_parsed :
    (certifiedOldLeafCode 97).bind dyadicRouteBLeafTreeOfCode =
      some finiteN97Tree := by
  native_decide

theorem finiteN97_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 97 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN97_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0001_checked finiteN97Shard0002_checked) finiteN97Shard0003_checked)) finiteN97Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0006_checked finiteN97Shard0007_checked) finiteN97Shard0008_checked)) finiteN97Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0010_checked finiteN97Shard0011_checked) finiteN97Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0013_checked (bound4395FiniteVerifySplitRho_true finiteN97Shard0014_checked finiteN97Shard0015_checked)) finiteN97Shard0016_checked)) finiteN97Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0018_checked finiteN97Shard0019_checked) finiteN97Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0021_checked finiteN97Shard0022_checked) finiteN97Shard0023_checked)) finiteN97Shard0024_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN97Shard0025_checked finiteN97Shard0026_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0027_checked finiteN97Shard0028_checked) finiteN97Shard0029_checked)) finiteN97Shard0030_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0031_checked finiteN97Shard0032_checked) finiteN97Shard0033_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN97Shard0034_checked finiteN97Shard0035_checked) finiteN97Shard0036_checked)) finiteN97Shard0037_checked)) finiteN97Shard0038_checked)) finiteN97Shard0039_checked)) finiteN97Shard0040_checked)) finiteN97Shard0041_checked))

end BerryEsseen
