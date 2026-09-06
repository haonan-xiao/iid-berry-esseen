import BerryEsseen.Certificates.Finite.N74.Shard0000
import BerryEsseen.Certificates.Finite.N74.Shard0001
import BerryEsseen.Certificates.Finite.N74.Shard0002
import BerryEsseen.Certificates.Finite.N74.Shard0003
import BerryEsseen.Certificates.Finite.N74.Shard0004
import BerryEsseen.Certificates.Finite.N74.Shard0005
import BerryEsseen.Certificates.Finite.N74.Shard0006
import BerryEsseen.Certificates.Finite.N74.Shard0007
import BerryEsseen.Certificates.Finite.N74.Shard0008
import BerryEsseen.Certificates.Finite.N74.Shard0009
import BerryEsseen.Certificates.Finite.N74.Shard0010
import BerryEsseen.Certificates.Finite.N74.Shard0011
import BerryEsseen.Certificates.Finite.N74.Shard0012
import BerryEsseen.Certificates.Finite.N74.Shard0013
import BerryEsseen.Certificates.Finite.N74.Shard0014
import BerryEsseen.Certificates.Finite.N74.Shard0015
import BerryEsseen.Certificates.Finite.N74.Shard0016
import BerryEsseen.Certificates.Finite.N74.Shard0017
import BerryEsseen.Certificates.Finite.N74.Shard0018
import BerryEsseen.Certificates.Finite.N74.Shard0019
import BerryEsseen.Certificates.Finite.N74.Shard0020
import BerryEsseen.Certificates.Finite.N74.Shard0021
import BerryEsseen.Certificates.Finite.N74.Shard0022
import BerryEsseen.Certificates.Finite.N74.Shard0023
import BerryEsseen.Certificates.Finite.N74.Shard0024
import BerryEsseen.Certificates.Finite.N74.Shard0025
import BerryEsseen.Certificates.Finite.N74.Shard0026
import BerryEsseen.Certificates.Finite.N74.Shard0027

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN74Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN74Shard0000Tree finiteN74Shard0001Tree) finiteN74Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN74Shard0003Tree (.splitRho (.splitZ finiteN74Shard0004Tree finiteN74Shard0005Tree) finiteN74Shard0006Tree)) finiteN74Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN74Shard0008Tree (.splitRho (.splitZ finiteN74Shard0009Tree finiteN74Shard0010Tree) finiteN74Shard0011Tree)) finiteN74Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN74Shard0013Tree (.splitRho finiteN74Shard0014Tree finiteN74Shard0015Tree)) finiteN74Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN74Shard0017Tree finiteN74Shard0018Tree) finiteN74Shard0019Tree) (.splitRho (.splitZ finiteN74Shard0020Tree (.splitRho finiteN74Shard0021Tree finiteN74Shard0022Tree)) finiteN74Shard0023Tree)) finiteN74Shard0024Tree)) finiteN74Shard0025Tree)) finiteN74Shard0026Tree)) finiteN74Shard0027Tree))

theorem finiteN74_parsed :
    (certifiedOldLeafCode 74).bind dyadicRouteBLeafTreeOfCode =
      some finiteN74Tree := by
  native_decide

theorem finiteN74_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 74 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN74_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN74Shard0000_checked finiteN74Shard0001_checked) finiteN74Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN74Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN74Shard0004_checked finiteN74Shard0005_checked) finiteN74Shard0006_checked)) finiteN74Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN74Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN74Shard0009_checked finiteN74Shard0010_checked) finiteN74Shard0011_checked)) finiteN74Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN74Shard0013_checked (bound4395FiniteVerifySplitRho_true finiteN74Shard0014_checked finiteN74Shard0015_checked)) finiteN74Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN74Shard0017_checked finiteN74Shard0018_checked) finiteN74Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN74Shard0020_checked (bound4395FiniteVerifySplitRho_true finiteN74Shard0021_checked finiteN74Shard0022_checked)) finiteN74Shard0023_checked)) finiteN74Shard0024_checked)) finiteN74Shard0025_checked)) finiteN74Shard0026_checked)) finiteN74Shard0027_checked))

end BerryEsseen
