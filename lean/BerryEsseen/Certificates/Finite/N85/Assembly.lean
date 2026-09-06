import BerryEsseen.Certificates.Finite.N85.Shard0000
import BerryEsseen.Certificates.Finite.N85.Shard0001
import BerryEsseen.Certificates.Finite.N85.Shard0002
import BerryEsseen.Certificates.Finite.N85.Shard0003
import BerryEsseen.Certificates.Finite.N85.Shard0004
import BerryEsseen.Certificates.Finite.N85.Shard0005
import BerryEsseen.Certificates.Finite.N85.Shard0006
import BerryEsseen.Certificates.Finite.N85.Shard0007
import BerryEsseen.Certificates.Finite.N85.Shard0008
import BerryEsseen.Certificates.Finite.N85.Shard0009
import BerryEsseen.Certificates.Finite.N85.Shard0010
import BerryEsseen.Certificates.Finite.N85.Shard0011
import BerryEsseen.Certificates.Finite.N85.Shard0012
import BerryEsseen.Certificates.Finite.N85.Shard0013
import BerryEsseen.Certificates.Finite.N85.Shard0014
import BerryEsseen.Certificates.Finite.N85.Shard0015
import BerryEsseen.Certificates.Finite.N85.Shard0016
import BerryEsseen.Certificates.Finite.N85.Shard0017
import BerryEsseen.Certificates.Finite.N85.Shard0018
import BerryEsseen.Certificates.Finite.N85.Shard0019
import BerryEsseen.Certificates.Finite.N85.Shard0020
import BerryEsseen.Certificates.Finite.N85.Shard0021
import BerryEsseen.Certificates.Finite.N85.Shard0022
import BerryEsseen.Certificates.Finite.N85.Shard0023
import BerryEsseen.Certificates.Finite.N85.Shard0024
import BerryEsseen.Certificates.Finite.N85.Shard0025
import BerryEsseen.Certificates.Finite.N85.Shard0026
import BerryEsseen.Certificates.Finite.N85.Shard0027
import BerryEsseen.Certificates.Finite.N85.Shard0028
import BerryEsseen.Certificates.Finite.N85.Shard0029
import BerryEsseen.Certificates.Finite.N85.Shard0030
import BerryEsseen.Certificates.Finite.N85.Shard0031

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN85Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN85Shard0000Tree (.splitRho (.splitZ finiteN85Shard0001Tree finiteN85Shard0002Tree) finiteN85Shard0003Tree)) finiteN85Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN85Shard0005Tree (.splitRho (.splitZ finiteN85Shard0006Tree finiteN85Shard0007Tree) finiteN85Shard0008Tree)) finiteN85Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN85Shard0010Tree (.splitRho (.splitZ finiteN85Shard0011Tree finiteN85Shard0012Tree) finiteN85Shard0013Tree)) finiteN85Shard0014Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN85Shard0015Tree (.splitRho (.splitZ finiteN85Shard0016Tree finiteN85Shard0017Tree) finiteN85Shard0018Tree)) finiteN85Shard0019Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN85Shard0020Tree finiteN85Shard0021Tree) finiteN85Shard0022Tree) (.splitRho (.splitZ (.splitRho finiteN85Shard0023Tree finiteN85Shard0024Tree) (.splitRho finiteN85Shard0025Tree finiteN85Shard0026Tree)) finiteN85Shard0027Tree)) finiteN85Shard0028Tree)) finiteN85Shard0029Tree)) finiteN85Shard0030Tree)) finiteN85Shard0031Tree))

theorem finiteN85_parsed :
    (certifiedOldLeafCode 85).bind dyadicRouteBLeafTreeOfCode =
      some finiteN85Tree := by
  native_decide

theorem finiteN85_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 85 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN85_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN85Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN85Shard0001_checked finiteN85Shard0002_checked) finiteN85Shard0003_checked)) finiteN85Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN85Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN85Shard0006_checked finiteN85Shard0007_checked) finiteN85Shard0008_checked)) finiteN85Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN85Shard0010_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN85Shard0011_checked finiteN85Shard0012_checked) finiteN85Shard0013_checked)) finiteN85Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN85Shard0015_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN85Shard0016_checked finiteN85Shard0017_checked) finiteN85Shard0018_checked)) finiteN85Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN85Shard0020_checked finiteN85Shard0021_checked) finiteN85Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN85Shard0023_checked finiteN85Shard0024_checked) (bound4395FiniteVerifySplitRho_true finiteN85Shard0025_checked finiteN85Shard0026_checked)) finiteN85Shard0027_checked)) finiteN85Shard0028_checked)) finiteN85Shard0029_checked)) finiteN85Shard0030_checked)) finiteN85Shard0031_checked))

end BerryEsseen
