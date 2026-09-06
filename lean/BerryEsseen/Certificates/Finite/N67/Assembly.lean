import BerryEsseen.Certificates.Finite.N67.Shard0000
import BerryEsseen.Certificates.Finite.N67.Shard0001
import BerryEsseen.Certificates.Finite.N67.Shard0002
import BerryEsseen.Certificates.Finite.N67.Shard0003
import BerryEsseen.Certificates.Finite.N67.Shard0004
import BerryEsseen.Certificates.Finite.N67.Shard0005
import BerryEsseen.Certificates.Finite.N67.Shard0006
import BerryEsseen.Certificates.Finite.N67.Shard0007
import BerryEsseen.Certificates.Finite.N67.Shard0008
import BerryEsseen.Certificates.Finite.N67.Shard0009
import BerryEsseen.Certificates.Finite.N67.Shard0010
import BerryEsseen.Certificates.Finite.N67.Shard0011
import BerryEsseen.Certificates.Finite.N67.Shard0012
import BerryEsseen.Certificates.Finite.N67.Shard0013
import BerryEsseen.Certificates.Finite.N67.Shard0014
import BerryEsseen.Certificates.Finite.N67.Shard0015
import BerryEsseen.Certificates.Finite.N67.Shard0016
import BerryEsseen.Certificates.Finite.N67.Shard0017
import BerryEsseen.Certificates.Finite.N67.Shard0018
import BerryEsseen.Certificates.Finite.N67.Shard0019
import BerryEsseen.Certificates.Finite.N67.Shard0020
import BerryEsseen.Certificates.Finite.N67.Shard0021
import BerryEsseen.Certificates.Finite.N67.Shard0022
import BerryEsseen.Certificates.Finite.N67.Shard0023
import BerryEsseen.Certificates.Finite.N67.Shard0024
import BerryEsseen.Certificates.Finite.N67.Shard0025
import BerryEsseen.Certificates.Finite.N67.Shard0026

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN67Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN67Shard0000Tree finiteN67Shard0001Tree) finiteN67Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN67Shard0003Tree (.splitRho (.splitZ finiteN67Shard0004Tree finiteN67Shard0005Tree) finiteN67Shard0006Tree)) finiteN67Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN67Shard0008Tree (.splitRho (.splitZ finiteN67Shard0009Tree finiteN67Shard0010Tree) finiteN67Shard0011Tree)) finiteN67Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN67Shard0013Tree (.splitRho finiteN67Shard0014Tree finiteN67Shard0015Tree)) finiteN67Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN67Shard0017Tree finiteN67Shard0018Tree) finiteN67Shard0019Tree) (.splitRho (.splitZ finiteN67Shard0020Tree finiteN67Shard0021Tree) finiteN67Shard0022Tree)) finiteN67Shard0023Tree)) finiteN67Shard0024Tree)) finiteN67Shard0025Tree)) finiteN67Shard0026Tree))

theorem finiteN67_parsed :
    (certifiedOldLeafCode 67).bind dyadicRouteBLeafTreeOfCode =
      some finiteN67Tree := by
  native_decide

theorem finiteN67_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 67 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN67_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN67Shard0000_checked finiteN67Shard0001_checked) finiteN67Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN67Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN67Shard0004_checked finiteN67Shard0005_checked) finiteN67Shard0006_checked)) finiteN67Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN67Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN67Shard0009_checked finiteN67Shard0010_checked) finiteN67Shard0011_checked)) finiteN67Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN67Shard0013_checked (bound4395FiniteVerifySplitRho_true finiteN67Shard0014_checked finiteN67Shard0015_checked)) finiteN67Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN67Shard0017_checked finiteN67Shard0018_checked) finiteN67Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN67Shard0020_checked finiteN67Shard0021_checked) finiteN67Shard0022_checked)) finiteN67Shard0023_checked)) finiteN67Shard0024_checked)) finiteN67Shard0025_checked)) finiteN67Shard0026_checked))

end BerryEsseen
