import BerryEsseen.Certificates.Finite.N72.Shard0000
import BerryEsseen.Certificates.Finite.N72.Shard0001
import BerryEsseen.Certificates.Finite.N72.Shard0002
import BerryEsseen.Certificates.Finite.N72.Shard0003
import BerryEsseen.Certificates.Finite.N72.Shard0004
import BerryEsseen.Certificates.Finite.N72.Shard0005
import BerryEsseen.Certificates.Finite.N72.Shard0006
import BerryEsseen.Certificates.Finite.N72.Shard0007
import BerryEsseen.Certificates.Finite.N72.Shard0008
import BerryEsseen.Certificates.Finite.N72.Shard0009
import BerryEsseen.Certificates.Finite.N72.Shard0010
import BerryEsseen.Certificates.Finite.N72.Shard0011
import BerryEsseen.Certificates.Finite.N72.Shard0012
import BerryEsseen.Certificates.Finite.N72.Shard0013
import BerryEsseen.Certificates.Finite.N72.Shard0014
import BerryEsseen.Certificates.Finite.N72.Shard0015
import BerryEsseen.Certificates.Finite.N72.Shard0016
import BerryEsseen.Certificates.Finite.N72.Shard0017
import BerryEsseen.Certificates.Finite.N72.Shard0018
import BerryEsseen.Certificates.Finite.N72.Shard0019
import BerryEsseen.Certificates.Finite.N72.Shard0020
import BerryEsseen.Certificates.Finite.N72.Shard0021
import BerryEsseen.Certificates.Finite.N72.Shard0022
import BerryEsseen.Certificates.Finite.N72.Shard0023
import BerryEsseen.Certificates.Finite.N72.Shard0024
import BerryEsseen.Certificates.Finite.N72.Shard0025
import BerryEsseen.Certificates.Finite.N72.Shard0026
import BerryEsseen.Certificates.Finite.N72.Shard0027
import BerryEsseen.Certificates.Finite.N72.Shard0028

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN72Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN72Shard0000Tree (.splitRho finiteN72Shard0001Tree finiteN72Shard0002Tree)) finiteN72Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN72Shard0004Tree (.splitRho (.splitZ finiteN72Shard0005Tree finiteN72Shard0006Tree) finiteN72Shard0007Tree)) finiteN72Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN72Shard0009Tree (.splitRho (.splitZ finiteN72Shard0010Tree finiteN72Shard0011Tree) finiteN72Shard0012Tree)) finiteN72Shard0013Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN72Shard0014Tree (.splitRho finiteN72Shard0015Tree finiteN72Shard0016Tree)) finiteN72Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN72Shard0018Tree finiteN72Shard0019Tree) finiteN72Shard0020Tree) (.splitRho (.splitZ finiteN72Shard0021Tree (.splitRho finiteN72Shard0022Tree finiteN72Shard0023Tree)) finiteN72Shard0024Tree)) finiteN72Shard0025Tree)) finiteN72Shard0026Tree)) finiteN72Shard0027Tree)) finiteN72Shard0028Tree))

theorem finiteN72_parsed :
    (certifiedOldLeafCode 72).bind dyadicRouteBLeafTreeOfCode =
      some finiteN72Tree := by
  native_decide

theorem finiteN72_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 72 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN72_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN72Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN72Shard0001_checked finiteN72Shard0002_checked)) finiteN72Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN72Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN72Shard0005_checked finiteN72Shard0006_checked) finiteN72Shard0007_checked)) finiteN72Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN72Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN72Shard0010_checked finiteN72Shard0011_checked) finiteN72Shard0012_checked)) finiteN72Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN72Shard0014_checked (bound4395FiniteVerifySplitRho_true finiteN72Shard0015_checked finiteN72Shard0016_checked)) finiteN72Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN72Shard0018_checked finiteN72Shard0019_checked) finiteN72Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN72Shard0021_checked (bound4395FiniteVerifySplitRho_true finiteN72Shard0022_checked finiteN72Shard0023_checked)) finiteN72Shard0024_checked)) finiteN72Shard0025_checked)) finiteN72Shard0026_checked)) finiteN72Shard0027_checked)) finiteN72Shard0028_checked))

end BerryEsseen
