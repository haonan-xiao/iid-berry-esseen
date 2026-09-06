import BerryEsseen.Certificates.Finite.N64.Shard0000
import BerryEsseen.Certificates.Finite.N64.Shard0001
import BerryEsseen.Certificates.Finite.N64.Shard0002
import BerryEsseen.Certificates.Finite.N64.Shard0003
import BerryEsseen.Certificates.Finite.N64.Shard0004
import BerryEsseen.Certificates.Finite.N64.Shard0005
import BerryEsseen.Certificates.Finite.N64.Shard0006
import BerryEsseen.Certificates.Finite.N64.Shard0007
import BerryEsseen.Certificates.Finite.N64.Shard0008
import BerryEsseen.Certificates.Finite.N64.Shard0009
import BerryEsseen.Certificates.Finite.N64.Shard0010
import BerryEsseen.Certificates.Finite.N64.Shard0011
import BerryEsseen.Certificates.Finite.N64.Shard0012
import BerryEsseen.Certificates.Finite.N64.Shard0013
import BerryEsseen.Certificates.Finite.N64.Shard0014
import BerryEsseen.Certificates.Finite.N64.Shard0015
import BerryEsseen.Certificates.Finite.N64.Shard0016
import BerryEsseen.Certificates.Finite.N64.Shard0017
import BerryEsseen.Certificates.Finite.N64.Shard0018
import BerryEsseen.Certificates.Finite.N64.Shard0019
import BerryEsseen.Certificates.Finite.N64.Shard0020
import BerryEsseen.Certificates.Finite.N64.Shard0021
import BerryEsseen.Certificates.Finite.N64.Shard0022
import BerryEsseen.Certificates.Finite.N64.Shard0023
import BerryEsseen.Certificates.Finite.N64.Shard0024
import BerryEsseen.Certificates.Finite.N64.Shard0025
import BerryEsseen.Certificates.Finite.N64.Shard0026
import BerryEsseen.Certificates.Finite.N64.Shard0027

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN64Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN64Shard0000Tree (.splitRho finiteN64Shard0001Tree finiteN64Shard0002Tree)) finiteN64Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN64Shard0004Tree (.splitRho (.splitZ finiteN64Shard0005Tree finiteN64Shard0006Tree) finiteN64Shard0007Tree)) finiteN64Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN64Shard0009Tree (.splitRho (.splitZ finiteN64Shard0010Tree finiteN64Shard0011Tree) finiteN64Shard0012Tree)) finiteN64Shard0013Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN64Shard0014Tree (.splitRho finiteN64Shard0015Tree finiteN64Shard0016Tree)) finiteN64Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN64Shard0018Tree finiteN64Shard0019Tree) finiteN64Shard0020Tree) (.splitRho (.splitZ finiteN64Shard0021Tree finiteN64Shard0022Tree) finiteN64Shard0023Tree)) finiteN64Shard0024Tree)) finiteN64Shard0025Tree)) finiteN64Shard0026Tree)) finiteN64Shard0027Tree))

theorem finiteN64_parsed :
    (certifiedOldLeafCode 64).bind dyadicRouteBLeafTreeOfCode =
      some finiteN64Tree := by
  native_decide

theorem finiteN64_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 64 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN64_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN64Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN64Shard0001_checked finiteN64Shard0002_checked)) finiteN64Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN64Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN64Shard0005_checked finiteN64Shard0006_checked) finiteN64Shard0007_checked)) finiteN64Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN64Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN64Shard0010_checked finiteN64Shard0011_checked) finiteN64Shard0012_checked)) finiteN64Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN64Shard0014_checked (bound4395FiniteVerifySplitRho_true finiteN64Shard0015_checked finiteN64Shard0016_checked)) finiteN64Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN64Shard0018_checked finiteN64Shard0019_checked) finiteN64Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN64Shard0021_checked finiteN64Shard0022_checked) finiteN64Shard0023_checked)) finiteN64Shard0024_checked)) finiteN64Shard0025_checked)) finiteN64Shard0026_checked)) finiteN64Shard0027_checked))

end BerryEsseen
