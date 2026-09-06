import BerryEsseen.Certificates.Finite.N76.Shard0000
import BerryEsseen.Certificates.Finite.N76.Shard0001
import BerryEsseen.Certificates.Finite.N76.Shard0002
import BerryEsseen.Certificates.Finite.N76.Shard0003
import BerryEsseen.Certificates.Finite.N76.Shard0004
import BerryEsseen.Certificates.Finite.N76.Shard0005
import BerryEsseen.Certificates.Finite.N76.Shard0006
import BerryEsseen.Certificates.Finite.N76.Shard0007
import BerryEsseen.Certificates.Finite.N76.Shard0008
import BerryEsseen.Certificates.Finite.N76.Shard0009
import BerryEsseen.Certificates.Finite.N76.Shard0010
import BerryEsseen.Certificates.Finite.N76.Shard0011
import BerryEsseen.Certificates.Finite.N76.Shard0012
import BerryEsseen.Certificates.Finite.N76.Shard0013
import BerryEsseen.Certificates.Finite.N76.Shard0014
import BerryEsseen.Certificates.Finite.N76.Shard0015
import BerryEsseen.Certificates.Finite.N76.Shard0016
import BerryEsseen.Certificates.Finite.N76.Shard0017
import BerryEsseen.Certificates.Finite.N76.Shard0018
import BerryEsseen.Certificates.Finite.N76.Shard0019
import BerryEsseen.Certificates.Finite.N76.Shard0020
import BerryEsseen.Certificates.Finite.N76.Shard0021
import BerryEsseen.Certificates.Finite.N76.Shard0022
import BerryEsseen.Certificates.Finite.N76.Shard0023
import BerryEsseen.Certificates.Finite.N76.Shard0024
import BerryEsseen.Certificates.Finite.N76.Shard0025
import BerryEsseen.Certificates.Finite.N76.Shard0026
import BerryEsseen.Certificates.Finite.N76.Shard0027
import BerryEsseen.Certificates.Finite.N76.Shard0028

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN76Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN76Shard0000Tree (.splitRho (.splitZ finiteN76Shard0001Tree finiteN76Shard0002Tree) finiteN76Shard0003Tree)) finiteN76Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN76Shard0005Tree (.splitRho (.splitZ finiteN76Shard0006Tree finiteN76Shard0007Tree) finiteN76Shard0008Tree)) finiteN76Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN76Shard0010Tree (.splitRho (.splitZ finiteN76Shard0011Tree finiteN76Shard0012Tree) finiteN76Shard0013Tree)) finiteN76Shard0014Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN76Shard0015Tree finiteN76Shard0016Tree) finiteN76Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN76Shard0018Tree finiteN76Shard0019Tree) finiteN76Shard0020Tree) (.splitRho (.splitZ finiteN76Shard0021Tree (.splitRho finiteN76Shard0022Tree finiteN76Shard0023Tree)) finiteN76Shard0024Tree)) finiteN76Shard0025Tree)) finiteN76Shard0026Tree)) finiteN76Shard0027Tree)) finiteN76Shard0028Tree))

theorem finiteN76_parsed :
    (certifiedOldLeafCode 76).bind dyadicRouteBLeafTreeOfCode =
      some finiteN76Tree := by
  native_decide

theorem finiteN76_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 76 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN76_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN76Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN76Shard0001_checked finiteN76Shard0002_checked) finiteN76Shard0003_checked)) finiteN76Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN76Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN76Shard0006_checked finiteN76Shard0007_checked) finiteN76Shard0008_checked)) finiteN76Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN76Shard0010_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN76Shard0011_checked finiteN76Shard0012_checked) finiteN76Shard0013_checked)) finiteN76Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN76Shard0015_checked finiteN76Shard0016_checked) finiteN76Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN76Shard0018_checked finiteN76Shard0019_checked) finiteN76Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN76Shard0021_checked (bound4395FiniteVerifySplitRho_true finiteN76Shard0022_checked finiteN76Shard0023_checked)) finiteN76Shard0024_checked)) finiteN76Shard0025_checked)) finiteN76Shard0026_checked)) finiteN76Shard0027_checked)) finiteN76Shard0028_checked))

end BerryEsseen
