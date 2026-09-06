import BerryEsseen.Certificates.Finite.N68.Shard0000
import BerryEsseen.Certificates.Finite.N68.Shard0001
import BerryEsseen.Certificates.Finite.N68.Shard0002
import BerryEsseen.Certificates.Finite.N68.Shard0003
import BerryEsseen.Certificates.Finite.N68.Shard0004
import BerryEsseen.Certificates.Finite.N68.Shard0005
import BerryEsseen.Certificates.Finite.N68.Shard0006
import BerryEsseen.Certificates.Finite.N68.Shard0007
import BerryEsseen.Certificates.Finite.N68.Shard0008
import BerryEsseen.Certificates.Finite.N68.Shard0009
import BerryEsseen.Certificates.Finite.N68.Shard0010
import BerryEsseen.Certificates.Finite.N68.Shard0011
import BerryEsseen.Certificates.Finite.N68.Shard0012
import BerryEsseen.Certificates.Finite.N68.Shard0013
import BerryEsseen.Certificates.Finite.N68.Shard0014
import BerryEsseen.Certificates.Finite.N68.Shard0015
import BerryEsseen.Certificates.Finite.N68.Shard0016
import BerryEsseen.Certificates.Finite.N68.Shard0017
import BerryEsseen.Certificates.Finite.N68.Shard0018
import BerryEsseen.Certificates.Finite.N68.Shard0019
import BerryEsseen.Certificates.Finite.N68.Shard0020
import BerryEsseen.Certificates.Finite.N68.Shard0021
import BerryEsseen.Certificates.Finite.N68.Shard0022
import BerryEsseen.Certificates.Finite.N68.Shard0023
import BerryEsseen.Certificates.Finite.N68.Shard0024
import BerryEsseen.Certificates.Finite.N68.Shard0025
import BerryEsseen.Certificates.Finite.N68.Shard0026
import BerryEsseen.Certificates.Finite.N68.Shard0027
import BerryEsseen.Certificates.Finite.N68.Shard0028

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN68Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN68Shard0000Tree (.splitRho finiteN68Shard0001Tree finiteN68Shard0002Tree)) finiteN68Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN68Shard0004Tree (.splitRho (.splitZ finiteN68Shard0005Tree finiteN68Shard0006Tree) finiteN68Shard0007Tree)) finiteN68Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN68Shard0009Tree finiteN68Shard0010Tree) (.splitRho (.splitZ finiteN68Shard0011Tree finiteN68Shard0012Tree) finiteN68Shard0013Tree)) finiteN68Shard0014Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN68Shard0015Tree (.splitRho finiteN68Shard0016Tree finiteN68Shard0017Tree)) finiteN68Shard0018Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN68Shard0019Tree finiteN68Shard0020Tree) finiteN68Shard0021Tree) (.splitRho (.splitZ finiteN68Shard0022Tree finiteN68Shard0023Tree) finiteN68Shard0024Tree)) finiteN68Shard0025Tree)) finiteN68Shard0026Tree)) finiteN68Shard0027Tree)) finiteN68Shard0028Tree))

theorem finiteN68_parsed :
    (certifiedOldLeafCode 68).bind dyadicRouteBLeafTreeOfCode =
      some finiteN68Tree := by
  native_decide

theorem finiteN68_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 68 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN68_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN68Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN68Shard0001_checked finiteN68Shard0002_checked)) finiteN68Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN68Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN68Shard0005_checked finiteN68Shard0006_checked) finiteN68Shard0007_checked)) finiteN68Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN68Shard0009_checked finiteN68Shard0010_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN68Shard0011_checked finiteN68Shard0012_checked) finiteN68Shard0013_checked)) finiteN68Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN68Shard0015_checked (bound4395FiniteVerifySplitRho_true finiteN68Shard0016_checked finiteN68Shard0017_checked)) finiteN68Shard0018_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN68Shard0019_checked finiteN68Shard0020_checked) finiteN68Shard0021_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN68Shard0022_checked finiteN68Shard0023_checked) finiteN68Shard0024_checked)) finiteN68Shard0025_checked)) finiteN68Shard0026_checked)) finiteN68Shard0027_checked)) finiteN68Shard0028_checked))

end BerryEsseen
