import BerryEsseen.Certificates.Finite.N94.Shard0000
import BerryEsseen.Certificates.Finite.N94.Shard0001
import BerryEsseen.Certificates.Finite.N94.Shard0002
import BerryEsseen.Certificates.Finite.N94.Shard0003
import BerryEsseen.Certificates.Finite.N94.Shard0004
import BerryEsseen.Certificates.Finite.N94.Shard0005
import BerryEsseen.Certificates.Finite.N94.Shard0006
import BerryEsseen.Certificates.Finite.N94.Shard0007
import BerryEsseen.Certificates.Finite.N94.Shard0008
import BerryEsseen.Certificates.Finite.N94.Shard0009
import BerryEsseen.Certificates.Finite.N94.Shard0010
import BerryEsseen.Certificates.Finite.N94.Shard0011
import BerryEsseen.Certificates.Finite.N94.Shard0012
import BerryEsseen.Certificates.Finite.N94.Shard0013
import BerryEsseen.Certificates.Finite.N94.Shard0014
import BerryEsseen.Certificates.Finite.N94.Shard0015
import BerryEsseen.Certificates.Finite.N94.Shard0016
import BerryEsseen.Certificates.Finite.N94.Shard0017
import BerryEsseen.Certificates.Finite.N94.Shard0018
import BerryEsseen.Certificates.Finite.N94.Shard0019
import BerryEsseen.Certificates.Finite.N94.Shard0020
import BerryEsseen.Certificates.Finite.N94.Shard0021
import BerryEsseen.Certificates.Finite.N94.Shard0022
import BerryEsseen.Certificates.Finite.N94.Shard0023
import BerryEsseen.Certificates.Finite.N94.Shard0024
import BerryEsseen.Certificates.Finite.N94.Shard0025
import BerryEsseen.Certificates.Finite.N94.Shard0026
import BerryEsseen.Certificates.Finite.N94.Shard0027
import BerryEsseen.Certificates.Finite.N94.Shard0028
import BerryEsseen.Certificates.Finite.N94.Shard0029
import BerryEsseen.Certificates.Finite.N94.Shard0030
import BerryEsseen.Certificates.Finite.N94.Shard0031
import BerryEsseen.Certificates.Finite.N94.Shard0032

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN94Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN94Shard0000Tree (.splitRho (.splitZ finiteN94Shard0001Tree finiteN94Shard0002Tree) finiteN94Shard0003Tree)) finiteN94Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN94Shard0005Tree (.splitRho (.splitZ finiteN94Shard0006Tree finiteN94Shard0007Tree) finiteN94Shard0008Tree)) finiteN94Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN94Shard0010Tree (.splitRho (.splitZ finiteN94Shard0011Tree finiteN94Shard0012Tree) finiteN94Shard0013Tree)) finiteN94Shard0014Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN94Shard0015Tree (.splitRho (.splitZ finiteN94Shard0016Tree finiteN94Shard0017Tree) finiteN94Shard0018Tree)) finiteN94Shard0019Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN94Shard0020Tree finiteN94Shard0021Tree) finiteN94Shard0022Tree) (.splitRho (.splitZ (.splitRho finiteN94Shard0023Tree finiteN94Shard0024Tree) (.splitRho (.splitZ finiteN94Shard0025Tree finiteN94Shard0026Tree) finiteN94Shard0027Tree)) finiteN94Shard0028Tree)) finiteN94Shard0029Tree)) finiteN94Shard0030Tree)) finiteN94Shard0031Tree)) finiteN94Shard0032Tree))

theorem finiteN94_parsed :
    (certifiedOldLeafCode 94).bind dyadicRouteBLeafTreeOfCode =
      some finiteN94Tree := by
  native_decide

theorem finiteN94_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 94 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN94_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0001_checked finiteN94Shard0002_checked) finiteN94Shard0003_checked)) finiteN94Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0006_checked finiteN94Shard0007_checked) finiteN94Shard0008_checked)) finiteN94Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0010_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0011_checked finiteN94Shard0012_checked) finiteN94Shard0013_checked)) finiteN94Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0015_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0016_checked finiteN94Shard0017_checked) finiteN94Shard0018_checked)) finiteN94Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0020_checked finiteN94Shard0021_checked) finiteN94Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN94Shard0023_checked finiteN94Shard0024_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN94Shard0025_checked finiteN94Shard0026_checked) finiteN94Shard0027_checked)) finiteN94Shard0028_checked)) finiteN94Shard0029_checked)) finiteN94Shard0030_checked)) finiteN94Shard0031_checked)) finiteN94Shard0032_checked))

end BerryEsseen
