import BerryEsseen.Certificates.Finite.N66.Shard0000
import BerryEsseen.Certificates.Finite.N66.Shard0001
import BerryEsseen.Certificates.Finite.N66.Shard0002
import BerryEsseen.Certificates.Finite.N66.Shard0003
import BerryEsseen.Certificates.Finite.N66.Shard0004
import BerryEsseen.Certificates.Finite.N66.Shard0005
import BerryEsseen.Certificates.Finite.N66.Shard0006
import BerryEsseen.Certificates.Finite.N66.Shard0007
import BerryEsseen.Certificates.Finite.N66.Shard0008
import BerryEsseen.Certificates.Finite.N66.Shard0009
import BerryEsseen.Certificates.Finite.N66.Shard0010
import BerryEsseen.Certificates.Finite.N66.Shard0011
import BerryEsseen.Certificates.Finite.N66.Shard0012
import BerryEsseen.Certificates.Finite.N66.Shard0013
import BerryEsseen.Certificates.Finite.N66.Shard0014
import BerryEsseen.Certificates.Finite.N66.Shard0015
import BerryEsseen.Certificates.Finite.N66.Shard0016
import BerryEsseen.Certificates.Finite.N66.Shard0017
import BerryEsseen.Certificates.Finite.N66.Shard0018
import BerryEsseen.Certificates.Finite.N66.Shard0019
import BerryEsseen.Certificates.Finite.N66.Shard0020
import BerryEsseen.Certificates.Finite.N66.Shard0021
import BerryEsseen.Certificates.Finite.N66.Shard0022
import BerryEsseen.Certificates.Finite.N66.Shard0023

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN66Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN66Shard0000Tree (.splitRho finiteN66Shard0001Tree finiteN66Shard0002Tree)) finiteN66Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN66Shard0004Tree (.splitRho (.splitZ finiteN66Shard0005Tree finiteN66Shard0006Tree) finiteN66Shard0007Tree)) finiteN66Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN66Shard0009Tree (.splitRho finiteN66Shard0010Tree finiteN66Shard0011Tree)) finiteN66Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN66Shard0013Tree finiteN66Shard0014Tree) finiteN66Shard0015Tree) (.splitRho (.splitZ finiteN66Shard0016Tree (.splitRho (.splitZ finiteN66Shard0017Tree finiteN66Shard0018Tree) finiteN66Shard0019Tree)) finiteN66Shard0020Tree)) finiteN66Shard0021Tree)) finiteN66Shard0022Tree)) finiteN66Shard0023Tree))

theorem finiteN66_parsed :
    (certifiedOldLeafCode 66).bind dyadicRouteBLeafTreeOfCode =
      some finiteN66Tree := by
  native_decide

theorem finiteN66_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 66 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN66_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN66Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN66Shard0001_checked finiteN66Shard0002_checked)) finiteN66Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN66Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN66Shard0005_checked finiteN66Shard0006_checked) finiteN66Shard0007_checked)) finiteN66Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN66Shard0009_checked (bound4395FiniteVerifySplitRho_true finiteN66Shard0010_checked finiteN66Shard0011_checked)) finiteN66Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN66Shard0013_checked finiteN66Shard0014_checked) finiteN66Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN66Shard0016_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN66Shard0017_checked finiteN66Shard0018_checked) finiteN66Shard0019_checked)) finiteN66Shard0020_checked)) finiteN66Shard0021_checked)) finiteN66Shard0022_checked)) finiteN66Shard0023_checked))

end BerryEsseen
