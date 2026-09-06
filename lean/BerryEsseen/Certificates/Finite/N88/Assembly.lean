import BerryEsseen.Certificates.Finite.N88.Shard0000
import BerryEsseen.Certificates.Finite.N88.Shard0001
import BerryEsseen.Certificates.Finite.N88.Shard0002
import BerryEsseen.Certificates.Finite.N88.Shard0003
import BerryEsseen.Certificates.Finite.N88.Shard0004
import BerryEsseen.Certificates.Finite.N88.Shard0005
import BerryEsseen.Certificates.Finite.N88.Shard0006
import BerryEsseen.Certificates.Finite.N88.Shard0007
import BerryEsseen.Certificates.Finite.N88.Shard0008
import BerryEsseen.Certificates.Finite.N88.Shard0009
import BerryEsseen.Certificates.Finite.N88.Shard0010
import BerryEsseen.Certificates.Finite.N88.Shard0011
import BerryEsseen.Certificates.Finite.N88.Shard0012
import BerryEsseen.Certificates.Finite.N88.Shard0013
import BerryEsseen.Certificates.Finite.N88.Shard0014
import BerryEsseen.Certificates.Finite.N88.Shard0015
import BerryEsseen.Certificates.Finite.N88.Shard0016
import BerryEsseen.Certificates.Finite.N88.Shard0017
import BerryEsseen.Certificates.Finite.N88.Shard0018
import BerryEsseen.Certificates.Finite.N88.Shard0019
import BerryEsseen.Certificates.Finite.N88.Shard0020
import BerryEsseen.Certificates.Finite.N88.Shard0021
import BerryEsseen.Certificates.Finite.N88.Shard0022
import BerryEsseen.Certificates.Finite.N88.Shard0023
import BerryEsseen.Certificates.Finite.N88.Shard0024
import BerryEsseen.Certificates.Finite.N88.Shard0025
import BerryEsseen.Certificates.Finite.N88.Shard0026
import BerryEsseen.Certificates.Finite.N88.Shard0027
import BerryEsseen.Certificates.Finite.N88.Shard0028
import BerryEsseen.Certificates.Finite.N88.Shard0029
import BerryEsseen.Certificates.Finite.N88.Shard0030
import BerryEsseen.Certificates.Finite.N88.Shard0031
import BerryEsseen.Certificates.Finite.N88.Shard0032
import BerryEsseen.Certificates.Finite.N88.Shard0033
import BerryEsseen.Certificates.Finite.N88.Shard0034
import BerryEsseen.Certificates.Finite.N88.Shard0035
import BerryEsseen.Certificates.Finite.N88.Shard0036
import BerryEsseen.Certificates.Finite.N88.Shard0037

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN88Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN88Shard0000Tree (.splitRho (.splitZ finiteN88Shard0001Tree finiteN88Shard0002Tree) finiteN88Shard0003Tree)) finiteN88Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN88Shard0005Tree (.splitRho (.splitZ finiteN88Shard0006Tree finiteN88Shard0007Tree) finiteN88Shard0008Tree)) finiteN88Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN88Shard0010Tree finiteN88Shard0011Tree) finiteN88Shard0012Tree) (.splitRho (.splitZ finiteN88Shard0013Tree finiteN88Shard0014Tree) finiteN88Shard0015Tree)) finiteN88Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN88Shard0017Tree finiteN88Shard0018Tree) (.splitRho (.splitZ finiteN88Shard0019Tree finiteN88Shard0020Tree) finiteN88Shard0021Tree)) finiteN88Shard0022Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN88Shard0023Tree (.splitRho finiteN88Shard0024Tree finiteN88Shard0025Tree)) finiteN88Shard0026Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN88Shard0027Tree finiteN88Shard0028Tree) finiteN88Shard0029Tree) (.splitRho (.splitZ finiteN88Shard0030Tree finiteN88Shard0031Tree) finiteN88Shard0032Tree)) finiteN88Shard0033Tree)) finiteN88Shard0034Tree)) finiteN88Shard0035Tree)) finiteN88Shard0036Tree)) finiteN88Shard0037Tree))

theorem finiteN88_parsed :
    (certifiedOldLeafCode 88).bind dyadicRouteBLeafTreeOfCode =
      some finiteN88Tree := by
  native_decide

theorem finiteN88_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 88 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN88_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0001_checked finiteN88Shard0002_checked) finiteN88Shard0003_checked)) finiteN88Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0006_checked finiteN88Shard0007_checked) finiteN88Shard0008_checked)) finiteN88Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0010_checked finiteN88Shard0011_checked) finiteN88Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0013_checked finiteN88Shard0014_checked) finiteN88Shard0015_checked)) finiteN88Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN88Shard0017_checked finiteN88Shard0018_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0019_checked finiteN88Shard0020_checked) finiteN88Shard0021_checked)) finiteN88Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0023_checked (bound4395FiniteVerifySplitRho_true finiteN88Shard0024_checked finiteN88Shard0025_checked)) finiteN88Shard0026_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0027_checked finiteN88Shard0028_checked) finiteN88Shard0029_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN88Shard0030_checked finiteN88Shard0031_checked) finiteN88Shard0032_checked)) finiteN88Shard0033_checked)) finiteN88Shard0034_checked)) finiteN88Shard0035_checked)) finiteN88Shard0036_checked)) finiteN88Shard0037_checked))

end BerryEsseen
