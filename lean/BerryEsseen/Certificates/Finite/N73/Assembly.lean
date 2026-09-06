import BerryEsseen.Certificates.Finite.N73.Shard0000
import BerryEsseen.Certificates.Finite.N73.Shard0001
import BerryEsseen.Certificates.Finite.N73.Shard0002
import BerryEsseen.Certificates.Finite.N73.Shard0003
import BerryEsseen.Certificates.Finite.N73.Shard0004
import BerryEsseen.Certificates.Finite.N73.Shard0005
import BerryEsseen.Certificates.Finite.N73.Shard0006
import BerryEsseen.Certificates.Finite.N73.Shard0007
import BerryEsseen.Certificates.Finite.N73.Shard0008
import BerryEsseen.Certificates.Finite.N73.Shard0009
import BerryEsseen.Certificates.Finite.N73.Shard0010
import BerryEsseen.Certificates.Finite.N73.Shard0011
import BerryEsseen.Certificates.Finite.N73.Shard0012
import BerryEsseen.Certificates.Finite.N73.Shard0013
import BerryEsseen.Certificates.Finite.N73.Shard0014
import BerryEsseen.Certificates.Finite.N73.Shard0015
import BerryEsseen.Certificates.Finite.N73.Shard0016
import BerryEsseen.Certificates.Finite.N73.Shard0017
import BerryEsseen.Certificates.Finite.N73.Shard0018
import BerryEsseen.Certificates.Finite.N73.Shard0019
import BerryEsseen.Certificates.Finite.N73.Shard0020
import BerryEsseen.Certificates.Finite.N73.Shard0021
import BerryEsseen.Certificates.Finite.N73.Shard0022
import BerryEsseen.Certificates.Finite.N73.Shard0023
import BerryEsseen.Certificates.Finite.N73.Shard0024
import BerryEsseen.Certificates.Finite.N73.Shard0025
import BerryEsseen.Certificates.Finite.N73.Shard0026
import BerryEsseen.Certificates.Finite.N73.Shard0027
import BerryEsseen.Certificates.Finite.N73.Shard0028
import BerryEsseen.Certificates.Finite.N73.Shard0029
import BerryEsseen.Certificates.Finite.N73.Shard0030

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN73Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN73Shard0000Tree (.splitRho (.splitZ finiteN73Shard0001Tree finiteN73Shard0002Tree) finiteN73Shard0003Tree)) finiteN73Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN73Shard0005Tree (.splitRho (.splitZ finiteN73Shard0006Tree finiteN73Shard0007Tree) finiteN73Shard0008Tree)) finiteN73Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN73Shard0010Tree (.splitRho (.splitZ finiteN73Shard0011Tree finiteN73Shard0012Tree) finiteN73Shard0013Tree)) finiteN73Shard0014Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN73Shard0015Tree (.splitRho (.splitZ finiteN73Shard0016Tree finiteN73Shard0017Tree) finiteN73Shard0018Tree)) finiteN73Shard0019Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN73Shard0020Tree finiteN73Shard0021Tree) finiteN73Shard0022Tree) (.splitRho (.splitZ finiteN73Shard0023Tree (.splitRho finiteN73Shard0024Tree finiteN73Shard0025Tree)) finiteN73Shard0026Tree)) finiteN73Shard0027Tree)) finiteN73Shard0028Tree)) finiteN73Shard0029Tree)) finiteN73Shard0030Tree))

theorem finiteN73_parsed :
    (certifiedOldLeafCode 73).bind dyadicRouteBLeafTreeOfCode =
      some finiteN73Tree := by
  native_decide

theorem finiteN73_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 73 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN73_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0001_checked finiteN73Shard0002_checked) finiteN73Shard0003_checked)) finiteN73Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0006_checked finiteN73Shard0007_checked) finiteN73Shard0008_checked)) finiteN73Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0010_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0011_checked finiteN73Shard0012_checked) finiteN73Shard0013_checked)) finiteN73Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0015_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0016_checked finiteN73Shard0017_checked) finiteN73Shard0018_checked)) finiteN73Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0020_checked finiteN73Shard0021_checked) finiteN73Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN73Shard0023_checked (bound4395FiniteVerifySplitRho_true finiteN73Shard0024_checked finiteN73Shard0025_checked)) finiteN73Shard0026_checked)) finiteN73Shard0027_checked)) finiteN73Shard0028_checked)) finiteN73Shard0029_checked)) finiteN73Shard0030_checked))

end BerryEsseen
