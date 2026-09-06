import BerryEsseen.Certificates.Finite.N92.Shard0000
import BerryEsseen.Certificates.Finite.N92.Shard0001
import BerryEsseen.Certificates.Finite.N92.Shard0002
import BerryEsseen.Certificates.Finite.N92.Shard0003
import BerryEsseen.Certificates.Finite.N92.Shard0004
import BerryEsseen.Certificates.Finite.N92.Shard0005
import BerryEsseen.Certificates.Finite.N92.Shard0006
import BerryEsseen.Certificates.Finite.N92.Shard0007
import BerryEsseen.Certificates.Finite.N92.Shard0008
import BerryEsseen.Certificates.Finite.N92.Shard0009
import BerryEsseen.Certificates.Finite.N92.Shard0010
import BerryEsseen.Certificates.Finite.N92.Shard0011
import BerryEsseen.Certificates.Finite.N92.Shard0012
import BerryEsseen.Certificates.Finite.N92.Shard0013
import BerryEsseen.Certificates.Finite.N92.Shard0014
import BerryEsseen.Certificates.Finite.N92.Shard0015
import BerryEsseen.Certificates.Finite.N92.Shard0016
import BerryEsseen.Certificates.Finite.N92.Shard0017
import BerryEsseen.Certificates.Finite.N92.Shard0018
import BerryEsseen.Certificates.Finite.N92.Shard0019
import BerryEsseen.Certificates.Finite.N92.Shard0020
import BerryEsseen.Certificates.Finite.N92.Shard0021
import BerryEsseen.Certificates.Finite.N92.Shard0022
import BerryEsseen.Certificates.Finite.N92.Shard0023
import BerryEsseen.Certificates.Finite.N92.Shard0024
import BerryEsseen.Certificates.Finite.N92.Shard0025
import BerryEsseen.Certificates.Finite.N92.Shard0026
import BerryEsseen.Certificates.Finite.N92.Shard0027
import BerryEsseen.Certificates.Finite.N92.Shard0028
import BerryEsseen.Certificates.Finite.N92.Shard0029
import BerryEsseen.Certificates.Finite.N92.Shard0030
import BerryEsseen.Certificates.Finite.N92.Shard0031
import BerryEsseen.Certificates.Finite.N92.Shard0032
import BerryEsseen.Certificates.Finite.N92.Shard0033
import BerryEsseen.Certificates.Finite.N92.Shard0034

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN92Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN92Shard0000Tree (.splitRho (.splitZ finiteN92Shard0001Tree finiteN92Shard0002Tree) finiteN92Shard0003Tree)) finiteN92Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN92Shard0005Tree (.splitRho (.splitZ finiteN92Shard0006Tree finiteN92Shard0007Tree) finiteN92Shard0008Tree)) finiteN92Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN92Shard0010Tree finiteN92Shard0011Tree) finiteN92Shard0012Tree) (.splitRho (.splitZ finiteN92Shard0013Tree finiteN92Shard0014Tree) finiteN92Shard0015Tree)) finiteN92Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN92Shard0017Tree finiteN92Shard0018Tree) (.splitRho (.splitZ finiteN92Shard0019Tree finiteN92Shard0020Tree) finiteN92Shard0021Tree)) finiteN92Shard0022Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN92Shard0023Tree finiteN92Shard0024Tree) finiteN92Shard0025Tree) (.splitRho (.splitZ (.splitRho finiteN92Shard0026Tree finiteN92Shard0027Tree) (.splitRho finiteN92Shard0028Tree finiteN92Shard0029Tree)) finiteN92Shard0030Tree)) finiteN92Shard0031Tree)) finiteN92Shard0032Tree)) finiteN92Shard0033Tree)) finiteN92Shard0034Tree))

theorem finiteN92_parsed :
    (certifiedOldLeafCode 92).bind dyadicRouteBLeafTreeOfCode =
      some finiteN92Tree := by
  native_decide

theorem finiteN92_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 92 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN92_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN92Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN92Shard0001_checked finiteN92Shard0002_checked) finiteN92Shard0003_checked)) finiteN92Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN92Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN92Shard0006_checked finiteN92Shard0007_checked) finiteN92Shard0008_checked)) finiteN92Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN92Shard0010_checked finiteN92Shard0011_checked) finiteN92Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN92Shard0013_checked finiteN92Shard0014_checked) finiteN92Shard0015_checked)) finiteN92Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN92Shard0017_checked finiteN92Shard0018_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN92Shard0019_checked finiteN92Shard0020_checked) finiteN92Shard0021_checked)) finiteN92Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN92Shard0023_checked finiteN92Shard0024_checked) finiteN92Shard0025_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN92Shard0026_checked finiteN92Shard0027_checked) (bound4395FiniteVerifySplitRho_true finiteN92Shard0028_checked finiteN92Shard0029_checked)) finiteN92Shard0030_checked)) finiteN92Shard0031_checked)) finiteN92Shard0032_checked)) finiteN92Shard0033_checked)) finiteN92Shard0034_checked))

end BerryEsseen
