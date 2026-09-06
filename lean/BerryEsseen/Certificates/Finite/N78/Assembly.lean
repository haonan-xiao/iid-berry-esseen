import BerryEsseen.Certificates.Finite.N78.Shard0000
import BerryEsseen.Certificates.Finite.N78.Shard0001
import BerryEsseen.Certificates.Finite.N78.Shard0002
import BerryEsseen.Certificates.Finite.N78.Shard0003
import BerryEsseen.Certificates.Finite.N78.Shard0004
import BerryEsseen.Certificates.Finite.N78.Shard0005
import BerryEsseen.Certificates.Finite.N78.Shard0006
import BerryEsseen.Certificates.Finite.N78.Shard0007
import BerryEsseen.Certificates.Finite.N78.Shard0008
import BerryEsseen.Certificates.Finite.N78.Shard0009
import BerryEsseen.Certificates.Finite.N78.Shard0010
import BerryEsseen.Certificates.Finite.N78.Shard0011
import BerryEsseen.Certificates.Finite.N78.Shard0012
import BerryEsseen.Certificates.Finite.N78.Shard0013
import BerryEsseen.Certificates.Finite.N78.Shard0014
import BerryEsseen.Certificates.Finite.N78.Shard0015
import BerryEsseen.Certificates.Finite.N78.Shard0016
import BerryEsseen.Certificates.Finite.N78.Shard0017
import BerryEsseen.Certificates.Finite.N78.Shard0018
import BerryEsseen.Certificates.Finite.N78.Shard0019
import BerryEsseen.Certificates.Finite.N78.Shard0020
import BerryEsseen.Certificates.Finite.N78.Shard0021
import BerryEsseen.Certificates.Finite.N78.Shard0022
import BerryEsseen.Certificates.Finite.N78.Shard0023
import BerryEsseen.Certificates.Finite.N78.Shard0024
import BerryEsseen.Certificates.Finite.N78.Shard0025
import BerryEsseen.Certificates.Finite.N78.Shard0026
import BerryEsseen.Certificates.Finite.N78.Shard0027
import BerryEsseen.Certificates.Finite.N78.Shard0028
import BerryEsseen.Certificates.Finite.N78.Shard0029
import BerryEsseen.Certificates.Finite.N78.Shard0030
import BerryEsseen.Certificates.Finite.N78.Shard0031
import BerryEsseen.Certificates.Finite.N78.Shard0032
import BerryEsseen.Certificates.Finite.N78.Shard0033
import BerryEsseen.Certificates.Finite.N78.Shard0034

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN78Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN78Shard0000Tree (.splitRho (.splitZ finiteN78Shard0001Tree finiteN78Shard0002Tree) finiteN78Shard0003Tree)) finiteN78Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN78Shard0005Tree (.splitRho (.splitZ finiteN78Shard0006Tree finiteN78Shard0007Tree) finiteN78Shard0008Tree)) finiteN78Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN78Shard0010Tree finiteN78Shard0011Tree) (.splitRho (.splitZ finiteN78Shard0012Tree finiteN78Shard0013Tree) finiteN78Shard0014Tree)) finiteN78Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN78Shard0016Tree finiteN78Shard0017Tree) (.splitRho (.splitZ finiteN78Shard0018Tree finiteN78Shard0019Tree) finiteN78Shard0020Tree)) finiteN78Shard0021Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN78Shard0022Tree finiteN78Shard0023Tree) finiteN78Shard0024Tree) (.splitRho (.splitZ (.splitRho finiteN78Shard0025Tree finiteN78Shard0026Tree) (.splitRho (.splitZ finiteN78Shard0027Tree finiteN78Shard0028Tree) finiteN78Shard0029Tree)) finiteN78Shard0030Tree)) finiteN78Shard0031Tree)) finiteN78Shard0032Tree)) finiteN78Shard0033Tree)) finiteN78Shard0034Tree))

theorem finiteN78_parsed :
    (certifiedOldLeafCode 78).bind dyadicRouteBLeafTreeOfCode =
      some finiteN78Tree := by
  native_decide

theorem finiteN78_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 78 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN78_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN78Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN78Shard0001_checked finiteN78Shard0002_checked) finiteN78Shard0003_checked)) finiteN78Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN78Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN78Shard0006_checked finiteN78Shard0007_checked) finiteN78Shard0008_checked)) finiteN78Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN78Shard0010_checked finiteN78Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN78Shard0012_checked finiteN78Shard0013_checked) finiteN78Shard0014_checked)) finiteN78Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN78Shard0016_checked finiteN78Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN78Shard0018_checked finiteN78Shard0019_checked) finiteN78Shard0020_checked)) finiteN78Shard0021_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN78Shard0022_checked finiteN78Shard0023_checked) finiteN78Shard0024_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN78Shard0025_checked finiteN78Shard0026_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN78Shard0027_checked finiteN78Shard0028_checked) finiteN78Shard0029_checked)) finiteN78Shard0030_checked)) finiteN78Shard0031_checked)) finiteN78Shard0032_checked)) finiteN78Shard0033_checked)) finiteN78Shard0034_checked))

end BerryEsseen
