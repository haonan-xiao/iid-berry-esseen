import BerryEsseen.Certificates.Finite.N91.Shard0000
import BerryEsseen.Certificates.Finite.N91.Shard0001
import BerryEsseen.Certificates.Finite.N91.Shard0002
import BerryEsseen.Certificates.Finite.N91.Shard0003
import BerryEsseen.Certificates.Finite.N91.Shard0004
import BerryEsseen.Certificates.Finite.N91.Shard0005
import BerryEsseen.Certificates.Finite.N91.Shard0006
import BerryEsseen.Certificates.Finite.N91.Shard0007
import BerryEsseen.Certificates.Finite.N91.Shard0008
import BerryEsseen.Certificates.Finite.N91.Shard0009
import BerryEsseen.Certificates.Finite.N91.Shard0010
import BerryEsseen.Certificates.Finite.N91.Shard0011
import BerryEsseen.Certificates.Finite.N91.Shard0012
import BerryEsseen.Certificates.Finite.N91.Shard0013
import BerryEsseen.Certificates.Finite.N91.Shard0014
import BerryEsseen.Certificates.Finite.N91.Shard0015
import BerryEsseen.Certificates.Finite.N91.Shard0016
import BerryEsseen.Certificates.Finite.N91.Shard0017
import BerryEsseen.Certificates.Finite.N91.Shard0018
import BerryEsseen.Certificates.Finite.N91.Shard0019
import BerryEsseen.Certificates.Finite.N91.Shard0020
import BerryEsseen.Certificates.Finite.N91.Shard0021
import BerryEsseen.Certificates.Finite.N91.Shard0022
import BerryEsseen.Certificates.Finite.N91.Shard0023
import BerryEsseen.Certificates.Finite.N91.Shard0024
import BerryEsseen.Certificates.Finite.N91.Shard0025
import BerryEsseen.Certificates.Finite.N91.Shard0026
import BerryEsseen.Certificates.Finite.N91.Shard0027
import BerryEsseen.Certificates.Finite.N91.Shard0028
import BerryEsseen.Certificates.Finite.N91.Shard0029
import BerryEsseen.Certificates.Finite.N91.Shard0030
import BerryEsseen.Certificates.Finite.N91.Shard0031
import BerryEsseen.Certificates.Finite.N91.Shard0032
import BerryEsseen.Certificates.Finite.N91.Shard0033

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN91Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN91Shard0000Tree (.splitRho (.splitZ finiteN91Shard0001Tree finiteN91Shard0002Tree) finiteN91Shard0003Tree)) finiteN91Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN91Shard0005Tree (.splitRho (.splitZ finiteN91Shard0006Tree finiteN91Shard0007Tree) finiteN91Shard0008Tree)) finiteN91Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN91Shard0010Tree finiteN91Shard0011Tree) (.splitRho (.splitZ finiteN91Shard0012Tree finiteN91Shard0013Tree) finiteN91Shard0014Tree)) finiteN91Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN91Shard0016Tree finiteN91Shard0017Tree) (.splitRho (.splitZ finiteN91Shard0018Tree finiteN91Shard0019Tree) finiteN91Shard0020Tree)) finiteN91Shard0021Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN91Shard0022Tree finiteN91Shard0023Tree) finiteN91Shard0024Tree) (.splitRho (.splitZ (.splitRho finiteN91Shard0025Tree finiteN91Shard0026Tree) (.splitRho finiteN91Shard0027Tree finiteN91Shard0028Tree)) finiteN91Shard0029Tree)) finiteN91Shard0030Tree)) finiteN91Shard0031Tree)) finiteN91Shard0032Tree)) finiteN91Shard0033Tree))

theorem finiteN91_parsed :
    (certifiedOldLeafCode 91).bind dyadicRouteBLeafTreeOfCode =
      some finiteN91Tree := by
  native_decide

theorem finiteN91_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 91 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN91_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN91Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN91Shard0001_checked finiteN91Shard0002_checked) finiteN91Shard0003_checked)) finiteN91Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN91Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN91Shard0006_checked finiteN91Shard0007_checked) finiteN91Shard0008_checked)) finiteN91Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN91Shard0010_checked finiteN91Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN91Shard0012_checked finiteN91Shard0013_checked) finiteN91Shard0014_checked)) finiteN91Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN91Shard0016_checked finiteN91Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN91Shard0018_checked finiteN91Shard0019_checked) finiteN91Shard0020_checked)) finiteN91Shard0021_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN91Shard0022_checked finiteN91Shard0023_checked) finiteN91Shard0024_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN91Shard0025_checked finiteN91Shard0026_checked) (bound4395FiniteVerifySplitRho_true finiteN91Shard0027_checked finiteN91Shard0028_checked)) finiteN91Shard0029_checked)) finiteN91Shard0030_checked)) finiteN91Shard0031_checked)) finiteN91Shard0032_checked)) finiteN91Shard0033_checked))

end BerryEsseen
