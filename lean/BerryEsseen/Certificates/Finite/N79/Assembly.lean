import BerryEsseen.Certificates.Finite.N79.Shard0000
import BerryEsseen.Certificates.Finite.N79.Shard0001
import BerryEsseen.Certificates.Finite.N79.Shard0002
import BerryEsseen.Certificates.Finite.N79.Shard0003
import BerryEsseen.Certificates.Finite.N79.Shard0004
import BerryEsseen.Certificates.Finite.N79.Shard0005
import BerryEsseen.Certificates.Finite.N79.Shard0006
import BerryEsseen.Certificates.Finite.N79.Shard0007
import BerryEsseen.Certificates.Finite.N79.Shard0008
import BerryEsseen.Certificates.Finite.N79.Shard0009
import BerryEsseen.Certificates.Finite.N79.Shard0010
import BerryEsseen.Certificates.Finite.N79.Shard0011
import BerryEsseen.Certificates.Finite.N79.Shard0012
import BerryEsseen.Certificates.Finite.N79.Shard0013
import BerryEsseen.Certificates.Finite.N79.Shard0014
import BerryEsseen.Certificates.Finite.N79.Shard0015
import BerryEsseen.Certificates.Finite.N79.Shard0016
import BerryEsseen.Certificates.Finite.N79.Shard0017
import BerryEsseen.Certificates.Finite.N79.Shard0018
import BerryEsseen.Certificates.Finite.N79.Shard0019
import BerryEsseen.Certificates.Finite.N79.Shard0020
import BerryEsseen.Certificates.Finite.N79.Shard0021
import BerryEsseen.Certificates.Finite.N79.Shard0022
import BerryEsseen.Certificates.Finite.N79.Shard0023
import BerryEsseen.Certificates.Finite.N79.Shard0024
import BerryEsseen.Certificates.Finite.N79.Shard0025
import BerryEsseen.Certificates.Finite.N79.Shard0026
import BerryEsseen.Certificates.Finite.N79.Shard0027
import BerryEsseen.Certificates.Finite.N79.Shard0028
import BerryEsseen.Certificates.Finite.N79.Shard0029
import BerryEsseen.Certificates.Finite.N79.Shard0030
import BerryEsseen.Certificates.Finite.N79.Shard0031
import BerryEsseen.Certificates.Finite.N79.Shard0032

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN79Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN79Shard0000Tree (.splitRho (.splitZ finiteN79Shard0001Tree finiteN79Shard0002Tree) finiteN79Shard0003Tree)) finiteN79Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN79Shard0005Tree (.splitRho (.splitZ finiteN79Shard0006Tree finiteN79Shard0007Tree) finiteN79Shard0008Tree)) finiteN79Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN79Shard0010Tree finiteN79Shard0011Tree) (.splitRho (.splitZ finiteN79Shard0012Tree finiteN79Shard0013Tree) finiteN79Shard0014Tree)) finiteN79Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN79Shard0016Tree (.splitRho finiteN79Shard0017Tree finiteN79Shard0018Tree)) finiteN79Shard0019Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN79Shard0020Tree finiteN79Shard0021Tree) finiteN79Shard0022Tree) (.splitRho (.splitZ (.splitRho finiteN79Shard0023Tree finiteN79Shard0024Tree) (.splitRho (.splitZ finiteN79Shard0025Tree finiteN79Shard0026Tree) finiteN79Shard0027Tree)) finiteN79Shard0028Tree)) finiteN79Shard0029Tree)) finiteN79Shard0030Tree)) finiteN79Shard0031Tree)) finiteN79Shard0032Tree))

theorem finiteN79_parsed :
    (certifiedOldLeafCode 79).bind dyadicRouteBLeafTreeOfCode =
      some finiteN79Tree := by
  native_decide

theorem finiteN79_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 79 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN79_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN79Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN79Shard0001_checked finiteN79Shard0002_checked) finiteN79Shard0003_checked)) finiteN79Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN79Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN79Shard0006_checked finiteN79Shard0007_checked) finiteN79Shard0008_checked)) finiteN79Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN79Shard0010_checked finiteN79Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN79Shard0012_checked finiteN79Shard0013_checked) finiteN79Shard0014_checked)) finiteN79Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN79Shard0016_checked (bound4395FiniteVerifySplitRho_true finiteN79Shard0017_checked finiteN79Shard0018_checked)) finiteN79Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN79Shard0020_checked finiteN79Shard0021_checked) finiteN79Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN79Shard0023_checked finiteN79Shard0024_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN79Shard0025_checked finiteN79Shard0026_checked) finiteN79Shard0027_checked)) finiteN79Shard0028_checked)) finiteN79Shard0029_checked)) finiteN79Shard0030_checked)) finiteN79Shard0031_checked)) finiteN79Shard0032_checked))

end BerryEsseen
