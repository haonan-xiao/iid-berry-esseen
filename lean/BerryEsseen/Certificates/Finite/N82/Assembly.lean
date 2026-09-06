import BerryEsseen.Certificates.Finite.N82.Shard0000
import BerryEsseen.Certificates.Finite.N82.Shard0001
import BerryEsseen.Certificates.Finite.N82.Shard0002
import BerryEsseen.Certificates.Finite.N82.Shard0003
import BerryEsseen.Certificates.Finite.N82.Shard0004
import BerryEsseen.Certificates.Finite.N82.Shard0005
import BerryEsseen.Certificates.Finite.N82.Shard0006
import BerryEsseen.Certificates.Finite.N82.Shard0007
import BerryEsseen.Certificates.Finite.N82.Shard0008
import BerryEsseen.Certificates.Finite.N82.Shard0009
import BerryEsseen.Certificates.Finite.N82.Shard0010
import BerryEsseen.Certificates.Finite.N82.Shard0011
import BerryEsseen.Certificates.Finite.N82.Shard0012
import BerryEsseen.Certificates.Finite.N82.Shard0013
import BerryEsseen.Certificates.Finite.N82.Shard0014
import BerryEsseen.Certificates.Finite.N82.Shard0015
import BerryEsseen.Certificates.Finite.N82.Shard0016
import BerryEsseen.Certificates.Finite.N82.Shard0017
import BerryEsseen.Certificates.Finite.N82.Shard0018
import BerryEsseen.Certificates.Finite.N82.Shard0019
import BerryEsseen.Certificates.Finite.N82.Shard0020
import BerryEsseen.Certificates.Finite.N82.Shard0021
import BerryEsseen.Certificates.Finite.N82.Shard0022
import BerryEsseen.Certificates.Finite.N82.Shard0023
import BerryEsseen.Certificates.Finite.N82.Shard0024
import BerryEsseen.Certificates.Finite.N82.Shard0025
import BerryEsseen.Certificates.Finite.N82.Shard0026
import BerryEsseen.Certificates.Finite.N82.Shard0027
import BerryEsseen.Certificates.Finite.N82.Shard0028
import BerryEsseen.Certificates.Finite.N82.Shard0029
import BerryEsseen.Certificates.Finite.N82.Shard0030
import BerryEsseen.Certificates.Finite.N82.Shard0031
import BerryEsseen.Certificates.Finite.N82.Shard0032
import BerryEsseen.Certificates.Finite.N82.Shard0033
import BerryEsseen.Certificates.Finite.N82.Shard0034
import BerryEsseen.Certificates.Finite.N82.Shard0035

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN82Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN82Shard0000Tree (.splitRho (.splitZ finiteN82Shard0001Tree finiteN82Shard0002Tree) finiteN82Shard0003Tree)) finiteN82Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN82Shard0005Tree (.splitRho (.splitZ finiteN82Shard0006Tree finiteN82Shard0007Tree) finiteN82Shard0008Tree)) finiteN82Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN82Shard0010Tree finiteN82Shard0011Tree) finiteN82Shard0012Tree) (.splitRho (.splitZ finiteN82Shard0013Tree finiteN82Shard0014Tree) finiteN82Shard0015Tree)) finiteN82Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN82Shard0017Tree finiteN82Shard0018Tree) finiteN82Shard0019Tree) (.splitRho (.splitZ finiteN82Shard0020Tree finiteN82Shard0021Tree) finiteN82Shard0022Tree)) finiteN82Shard0023Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN82Shard0024Tree finiteN82Shard0025Tree) finiteN82Shard0026Tree) (.splitRho (.splitZ (.splitRho finiteN82Shard0027Tree finiteN82Shard0028Tree) (.splitRho finiteN82Shard0029Tree finiteN82Shard0030Tree)) finiteN82Shard0031Tree)) finiteN82Shard0032Tree)) finiteN82Shard0033Tree)) finiteN82Shard0034Tree)) finiteN82Shard0035Tree))

theorem finiteN82_parsed :
    (certifiedOldLeafCode 82).bind dyadicRouteBLeafTreeOfCode =
      some finiteN82Tree := by
  native_decide

theorem finiteN82_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 82 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN82_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN82Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN82Shard0001_checked finiteN82Shard0002_checked) finiteN82Shard0003_checked)) finiteN82Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN82Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN82Shard0006_checked finiteN82Shard0007_checked) finiteN82Shard0008_checked)) finiteN82Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN82Shard0010_checked finiteN82Shard0011_checked) finiteN82Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN82Shard0013_checked finiteN82Shard0014_checked) finiteN82Shard0015_checked)) finiteN82Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN82Shard0017_checked finiteN82Shard0018_checked) finiteN82Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN82Shard0020_checked finiteN82Shard0021_checked) finiteN82Shard0022_checked)) finiteN82Shard0023_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN82Shard0024_checked finiteN82Shard0025_checked) finiteN82Shard0026_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN82Shard0027_checked finiteN82Shard0028_checked) (bound4395FiniteVerifySplitRho_true finiteN82Shard0029_checked finiteN82Shard0030_checked)) finiteN82Shard0031_checked)) finiteN82Shard0032_checked)) finiteN82Shard0033_checked)) finiteN82Shard0034_checked)) finiteN82Shard0035_checked))

end BerryEsseen
