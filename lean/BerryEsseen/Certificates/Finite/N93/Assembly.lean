import BerryEsseen.Certificates.Finite.N93.Shard0000
import BerryEsseen.Certificates.Finite.N93.Shard0001
import BerryEsseen.Certificates.Finite.N93.Shard0002
import BerryEsseen.Certificates.Finite.N93.Shard0003
import BerryEsseen.Certificates.Finite.N93.Shard0004
import BerryEsseen.Certificates.Finite.N93.Shard0005
import BerryEsseen.Certificates.Finite.N93.Shard0006
import BerryEsseen.Certificates.Finite.N93.Shard0007
import BerryEsseen.Certificates.Finite.N93.Shard0008
import BerryEsseen.Certificates.Finite.N93.Shard0009
import BerryEsseen.Certificates.Finite.N93.Shard0010
import BerryEsseen.Certificates.Finite.N93.Shard0011
import BerryEsseen.Certificates.Finite.N93.Shard0012
import BerryEsseen.Certificates.Finite.N93.Shard0013
import BerryEsseen.Certificates.Finite.N93.Shard0014
import BerryEsseen.Certificates.Finite.N93.Shard0015
import BerryEsseen.Certificates.Finite.N93.Shard0016
import BerryEsseen.Certificates.Finite.N93.Shard0017
import BerryEsseen.Certificates.Finite.N93.Shard0018
import BerryEsseen.Certificates.Finite.N93.Shard0019
import BerryEsseen.Certificates.Finite.N93.Shard0020
import BerryEsseen.Certificates.Finite.N93.Shard0021
import BerryEsseen.Certificates.Finite.N93.Shard0022
import BerryEsseen.Certificates.Finite.N93.Shard0023
import BerryEsseen.Certificates.Finite.N93.Shard0024
import BerryEsseen.Certificates.Finite.N93.Shard0025
import BerryEsseen.Certificates.Finite.N93.Shard0026
import BerryEsseen.Certificates.Finite.N93.Shard0027
import BerryEsseen.Certificates.Finite.N93.Shard0028
import BerryEsseen.Certificates.Finite.N93.Shard0029
import BerryEsseen.Certificates.Finite.N93.Shard0030
import BerryEsseen.Certificates.Finite.N93.Shard0031
import BerryEsseen.Certificates.Finite.N93.Shard0032
import BerryEsseen.Certificates.Finite.N93.Shard0033
import BerryEsseen.Certificates.Finite.N93.Shard0034
import BerryEsseen.Certificates.Finite.N93.Shard0035
import BerryEsseen.Certificates.Finite.N93.Shard0036

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN93Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN93Shard0000Tree (.splitRho (.splitZ finiteN93Shard0001Tree finiteN93Shard0002Tree) finiteN93Shard0003Tree)) finiteN93Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN93Shard0005Tree (.splitRho (.splitZ finiteN93Shard0006Tree finiteN93Shard0007Tree) finiteN93Shard0008Tree)) finiteN93Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN93Shard0010Tree finiteN93Shard0011Tree) finiteN93Shard0012Tree) (.splitRho (.splitZ finiteN93Shard0013Tree finiteN93Shard0014Tree) finiteN93Shard0015Tree)) finiteN93Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN93Shard0017Tree finiteN93Shard0018Tree) finiteN93Shard0019Tree) (.splitRho (.splitZ finiteN93Shard0020Tree finiteN93Shard0021Tree) finiteN93Shard0022Tree)) finiteN93Shard0023Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN93Shard0024Tree (.splitRho finiteN93Shard0025Tree finiteN93Shard0026Tree)) finiteN93Shard0027Tree) (.splitRho (.splitZ (.splitRho finiteN93Shard0028Tree finiteN93Shard0029Tree) (.splitRho finiteN93Shard0030Tree finiteN93Shard0031Tree)) finiteN93Shard0032Tree)) finiteN93Shard0033Tree)) finiteN93Shard0034Tree)) finiteN93Shard0035Tree)) finiteN93Shard0036Tree))

theorem finiteN93_parsed :
    (certifiedOldLeafCode 93).bind dyadicRouteBLeafTreeOfCode =
      some finiteN93Tree := by
  native_decide

theorem finiteN93_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 93 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN93_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN93Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN93Shard0001_checked finiteN93Shard0002_checked) finiteN93Shard0003_checked)) finiteN93Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN93Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN93Shard0006_checked finiteN93Shard0007_checked) finiteN93Shard0008_checked)) finiteN93Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN93Shard0010_checked finiteN93Shard0011_checked) finiteN93Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN93Shard0013_checked finiteN93Shard0014_checked) finiteN93Shard0015_checked)) finiteN93Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN93Shard0017_checked finiteN93Shard0018_checked) finiteN93Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN93Shard0020_checked finiteN93Shard0021_checked) finiteN93Shard0022_checked)) finiteN93Shard0023_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN93Shard0024_checked (bound4395FiniteVerifySplitRho_true finiteN93Shard0025_checked finiteN93Shard0026_checked)) finiteN93Shard0027_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN93Shard0028_checked finiteN93Shard0029_checked) (bound4395FiniteVerifySplitRho_true finiteN93Shard0030_checked finiteN93Shard0031_checked)) finiteN93Shard0032_checked)) finiteN93Shard0033_checked)) finiteN93Shard0034_checked)) finiteN93Shard0035_checked)) finiteN93Shard0036_checked))

end BerryEsseen
