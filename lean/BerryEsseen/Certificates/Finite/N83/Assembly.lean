import BerryEsseen.Certificates.Finite.N83.Shard0000
import BerryEsseen.Certificates.Finite.N83.Shard0001
import BerryEsseen.Certificates.Finite.N83.Shard0002
import BerryEsseen.Certificates.Finite.N83.Shard0003
import BerryEsseen.Certificates.Finite.N83.Shard0004
import BerryEsseen.Certificates.Finite.N83.Shard0005
import BerryEsseen.Certificates.Finite.N83.Shard0006
import BerryEsseen.Certificates.Finite.N83.Shard0007
import BerryEsseen.Certificates.Finite.N83.Shard0008
import BerryEsseen.Certificates.Finite.N83.Shard0009
import BerryEsseen.Certificates.Finite.N83.Shard0010
import BerryEsseen.Certificates.Finite.N83.Shard0011
import BerryEsseen.Certificates.Finite.N83.Shard0012
import BerryEsseen.Certificates.Finite.N83.Shard0013
import BerryEsseen.Certificates.Finite.N83.Shard0014
import BerryEsseen.Certificates.Finite.N83.Shard0015
import BerryEsseen.Certificates.Finite.N83.Shard0016
import BerryEsseen.Certificates.Finite.N83.Shard0017
import BerryEsseen.Certificates.Finite.N83.Shard0018
import BerryEsseen.Certificates.Finite.N83.Shard0019
import BerryEsseen.Certificates.Finite.N83.Shard0020
import BerryEsseen.Certificates.Finite.N83.Shard0021
import BerryEsseen.Certificates.Finite.N83.Shard0022
import BerryEsseen.Certificates.Finite.N83.Shard0023
import BerryEsseen.Certificates.Finite.N83.Shard0024
import BerryEsseen.Certificates.Finite.N83.Shard0025
import BerryEsseen.Certificates.Finite.N83.Shard0026
import BerryEsseen.Certificates.Finite.N83.Shard0027
import BerryEsseen.Certificates.Finite.N83.Shard0028
import BerryEsseen.Certificates.Finite.N83.Shard0029
import BerryEsseen.Certificates.Finite.N83.Shard0030
import BerryEsseen.Certificates.Finite.N83.Shard0031
import BerryEsseen.Certificates.Finite.N83.Shard0032

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN83Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN83Shard0000Tree (.splitRho finiteN83Shard0001Tree finiteN83Shard0002Tree)) finiteN83Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN83Shard0004Tree (.splitRho (.splitZ finiteN83Shard0005Tree finiteN83Shard0006Tree) finiteN83Shard0007Tree)) finiteN83Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN83Shard0009Tree (.splitRho (.splitZ finiteN83Shard0010Tree finiteN83Shard0011Tree) finiteN83Shard0012Tree)) finiteN83Shard0013Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN83Shard0014Tree finiteN83Shard0015Tree) (.splitRho (.splitZ finiteN83Shard0016Tree finiteN83Shard0017Tree) finiteN83Shard0018Tree)) finiteN83Shard0019Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN83Shard0020Tree finiteN83Shard0021Tree) finiteN83Shard0022Tree) (.splitRho (.splitZ (.splitRho finiteN83Shard0023Tree finiteN83Shard0024Tree) (.splitRho (.splitZ finiteN83Shard0025Tree finiteN83Shard0026Tree) finiteN83Shard0027Tree)) finiteN83Shard0028Tree)) finiteN83Shard0029Tree)) finiteN83Shard0030Tree)) finiteN83Shard0031Tree)) finiteN83Shard0032Tree))

theorem finiteN83_parsed :
    (certifiedOldLeafCode 83).bind dyadicRouteBLeafTreeOfCode =
      some finiteN83Tree := by
  native_decide

theorem finiteN83_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 83 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN83_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN83Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN83Shard0001_checked finiteN83Shard0002_checked)) finiteN83Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN83Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN83Shard0005_checked finiteN83Shard0006_checked) finiteN83Shard0007_checked)) finiteN83Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN83Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN83Shard0010_checked finiteN83Shard0011_checked) finiteN83Shard0012_checked)) finiteN83Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN83Shard0014_checked finiteN83Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN83Shard0016_checked finiteN83Shard0017_checked) finiteN83Shard0018_checked)) finiteN83Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN83Shard0020_checked finiteN83Shard0021_checked) finiteN83Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN83Shard0023_checked finiteN83Shard0024_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN83Shard0025_checked finiteN83Shard0026_checked) finiteN83Shard0027_checked)) finiteN83Shard0028_checked)) finiteN83Shard0029_checked)) finiteN83Shard0030_checked)) finiteN83Shard0031_checked)) finiteN83Shard0032_checked))

end BerryEsseen
