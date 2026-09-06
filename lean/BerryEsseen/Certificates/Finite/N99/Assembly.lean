import BerryEsseen.Certificates.Finite.N99.Shard0000
import BerryEsseen.Certificates.Finite.N99.Shard0001
import BerryEsseen.Certificates.Finite.N99.Shard0002
import BerryEsseen.Certificates.Finite.N99.Shard0003
import BerryEsseen.Certificates.Finite.N99.Shard0004
import BerryEsseen.Certificates.Finite.N99.Shard0005
import BerryEsseen.Certificates.Finite.N99.Shard0006
import BerryEsseen.Certificates.Finite.N99.Shard0007
import BerryEsseen.Certificates.Finite.N99.Shard0008
import BerryEsseen.Certificates.Finite.N99.Shard0009
import BerryEsseen.Certificates.Finite.N99.Shard0010
import BerryEsseen.Certificates.Finite.N99.Shard0011
import BerryEsseen.Certificates.Finite.N99.Shard0012
import BerryEsseen.Certificates.Finite.N99.Shard0013
import BerryEsseen.Certificates.Finite.N99.Shard0014
import BerryEsseen.Certificates.Finite.N99.Shard0015
import BerryEsseen.Certificates.Finite.N99.Shard0016
import BerryEsseen.Certificates.Finite.N99.Shard0017
import BerryEsseen.Certificates.Finite.N99.Shard0018
import BerryEsseen.Certificates.Finite.N99.Shard0019
import BerryEsseen.Certificates.Finite.N99.Shard0020
import BerryEsseen.Certificates.Finite.N99.Shard0021
import BerryEsseen.Certificates.Finite.N99.Shard0022
import BerryEsseen.Certificates.Finite.N99.Shard0023
import BerryEsseen.Certificates.Finite.N99.Shard0024
import BerryEsseen.Certificates.Finite.N99.Shard0025
import BerryEsseen.Certificates.Finite.N99.Shard0026
import BerryEsseen.Certificates.Finite.N99.Shard0027
import BerryEsseen.Certificates.Finite.N99.Shard0028
import BerryEsseen.Certificates.Finite.N99.Shard0029
import BerryEsseen.Certificates.Finite.N99.Shard0030
import BerryEsseen.Certificates.Finite.N99.Shard0031
import BerryEsseen.Certificates.Finite.N99.Shard0032
import BerryEsseen.Certificates.Finite.N99.Shard0033
import BerryEsseen.Certificates.Finite.N99.Shard0034

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN99Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN99Shard0000Tree (.splitRho (.splitZ finiteN99Shard0001Tree finiteN99Shard0002Tree) finiteN99Shard0003Tree)) finiteN99Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN99Shard0005Tree (.splitRho (.splitZ finiteN99Shard0006Tree finiteN99Shard0007Tree) finiteN99Shard0008Tree)) finiteN99Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN99Shard0010Tree finiteN99Shard0011Tree) (.splitRho (.splitZ finiteN99Shard0012Tree finiteN99Shard0013Tree) finiteN99Shard0014Tree)) finiteN99Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN99Shard0016Tree finiteN99Shard0017Tree) (.splitRho (.splitZ finiteN99Shard0018Tree finiteN99Shard0019Tree) finiteN99Shard0020Tree)) finiteN99Shard0021Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN99Shard0022Tree (.splitRho finiteN99Shard0023Tree finiteN99Shard0024Tree)) finiteN99Shard0025Tree) (.splitRho (.splitZ (.splitRho finiteN99Shard0026Tree finiteN99Shard0027Tree) (.splitRho finiteN99Shard0028Tree finiteN99Shard0029Tree)) finiteN99Shard0030Tree)) finiteN99Shard0031Tree)) finiteN99Shard0032Tree)) finiteN99Shard0033Tree)) finiteN99Shard0034Tree))

theorem finiteN99_parsed :
    (certifiedOldLeafCode 99).bind dyadicRouteBLeafTreeOfCode =
      some finiteN99Tree := by
  native_decide

theorem finiteN99_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 99 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN99_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN99Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN99Shard0001_checked finiteN99Shard0002_checked) finiteN99Shard0003_checked)) finiteN99Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN99Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN99Shard0006_checked finiteN99Shard0007_checked) finiteN99Shard0008_checked)) finiteN99Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN99Shard0010_checked finiteN99Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN99Shard0012_checked finiteN99Shard0013_checked) finiteN99Shard0014_checked)) finiteN99Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN99Shard0016_checked finiteN99Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN99Shard0018_checked finiteN99Shard0019_checked) finiteN99Shard0020_checked)) finiteN99Shard0021_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN99Shard0022_checked (bound4395FiniteVerifySplitRho_true finiteN99Shard0023_checked finiteN99Shard0024_checked)) finiteN99Shard0025_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN99Shard0026_checked finiteN99Shard0027_checked) (bound4395FiniteVerifySplitRho_true finiteN99Shard0028_checked finiteN99Shard0029_checked)) finiteN99Shard0030_checked)) finiteN99Shard0031_checked)) finiteN99Shard0032_checked)) finiteN99Shard0033_checked)) finiteN99Shard0034_checked))

end BerryEsseen
