import BerryEsseen.Certificates.Finite.N65.Shard0000
import BerryEsseen.Certificates.Finite.N65.Shard0001
import BerryEsseen.Certificates.Finite.N65.Shard0002
import BerryEsseen.Certificates.Finite.N65.Shard0003
import BerryEsseen.Certificates.Finite.N65.Shard0004
import BerryEsseen.Certificates.Finite.N65.Shard0005
import BerryEsseen.Certificates.Finite.N65.Shard0006
import BerryEsseen.Certificates.Finite.N65.Shard0007
import BerryEsseen.Certificates.Finite.N65.Shard0008
import BerryEsseen.Certificates.Finite.N65.Shard0009
import BerryEsseen.Certificates.Finite.N65.Shard0010
import BerryEsseen.Certificates.Finite.N65.Shard0011
import BerryEsseen.Certificates.Finite.N65.Shard0012
import BerryEsseen.Certificates.Finite.N65.Shard0013
import BerryEsseen.Certificates.Finite.N65.Shard0014
import BerryEsseen.Certificates.Finite.N65.Shard0015
import BerryEsseen.Certificates.Finite.N65.Shard0016
import BerryEsseen.Certificates.Finite.N65.Shard0017
import BerryEsseen.Certificates.Finite.N65.Shard0018
import BerryEsseen.Certificates.Finite.N65.Shard0019
import BerryEsseen.Certificates.Finite.N65.Shard0020
import BerryEsseen.Certificates.Finite.N65.Shard0021
import BerryEsseen.Certificates.Finite.N65.Shard0022
import BerryEsseen.Certificates.Finite.N65.Shard0023
import BerryEsseen.Certificates.Finite.N65.Shard0024
import BerryEsseen.Certificates.Finite.N65.Shard0025
import BerryEsseen.Certificates.Finite.N65.Shard0026
import BerryEsseen.Certificates.Finite.N65.Shard0027
import BerryEsseen.Certificates.Finite.N65.Shard0028

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN65Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN65Shard0000Tree finiteN65Shard0001Tree) finiteN65Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN65Shard0003Tree (.splitRho (.splitZ finiteN65Shard0004Tree finiteN65Shard0005Tree) finiteN65Shard0006Tree)) finiteN65Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN65Shard0008Tree (.splitRho (.splitZ finiteN65Shard0009Tree finiteN65Shard0010Tree) finiteN65Shard0011Tree)) finiteN65Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN65Shard0013Tree (.splitRho (.splitZ finiteN65Shard0014Tree finiteN65Shard0015Tree) finiteN65Shard0016Tree)) finiteN65Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN65Shard0018Tree finiteN65Shard0019Tree) finiteN65Shard0020Tree) (.splitRho (.splitZ finiteN65Shard0021Tree (.splitRho finiteN65Shard0022Tree finiteN65Shard0023Tree)) finiteN65Shard0024Tree)) finiteN65Shard0025Tree)) finiteN65Shard0026Tree)) finiteN65Shard0027Tree)) finiteN65Shard0028Tree))

theorem finiteN65_parsed :
    (certifiedOldLeafCode 65).bind dyadicRouteBLeafTreeOfCode =
      some finiteN65Tree := by
  native_decide

theorem finiteN65_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 65 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN65_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN65Shard0000_checked finiteN65Shard0001_checked) finiteN65Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN65Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN65Shard0004_checked finiteN65Shard0005_checked) finiteN65Shard0006_checked)) finiteN65Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN65Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN65Shard0009_checked finiteN65Shard0010_checked) finiteN65Shard0011_checked)) finiteN65Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN65Shard0013_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN65Shard0014_checked finiteN65Shard0015_checked) finiteN65Shard0016_checked)) finiteN65Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN65Shard0018_checked finiteN65Shard0019_checked) finiteN65Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN65Shard0021_checked (bound4395FiniteVerifySplitRho_true finiteN65Shard0022_checked finiteN65Shard0023_checked)) finiteN65Shard0024_checked)) finiteN65Shard0025_checked)) finiteN65Shard0026_checked)) finiteN65Shard0027_checked)) finiteN65Shard0028_checked))

end BerryEsseen
