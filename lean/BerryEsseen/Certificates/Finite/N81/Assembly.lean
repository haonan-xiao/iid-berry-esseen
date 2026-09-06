import BerryEsseen.Certificates.Finite.N81.Shard0000
import BerryEsseen.Certificates.Finite.N81.Shard0001
import BerryEsseen.Certificates.Finite.N81.Shard0002
import BerryEsseen.Certificates.Finite.N81.Shard0003
import BerryEsseen.Certificates.Finite.N81.Shard0004
import BerryEsseen.Certificates.Finite.N81.Shard0005
import BerryEsseen.Certificates.Finite.N81.Shard0006
import BerryEsseen.Certificates.Finite.N81.Shard0007
import BerryEsseen.Certificates.Finite.N81.Shard0008
import BerryEsseen.Certificates.Finite.N81.Shard0009
import BerryEsseen.Certificates.Finite.N81.Shard0010
import BerryEsseen.Certificates.Finite.N81.Shard0011
import BerryEsseen.Certificates.Finite.N81.Shard0012
import BerryEsseen.Certificates.Finite.N81.Shard0013
import BerryEsseen.Certificates.Finite.N81.Shard0014
import BerryEsseen.Certificates.Finite.N81.Shard0015
import BerryEsseen.Certificates.Finite.N81.Shard0016
import BerryEsseen.Certificates.Finite.N81.Shard0017
import BerryEsseen.Certificates.Finite.N81.Shard0018
import BerryEsseen.Certificates.Finite.N81.Shard0019
import BerryEsseen.Certificates.Finite.N81.Shard0020
import BerryEsseen.Certificates.Finite.N81.Shard0021
import BerryEsseen.Certificates.Finite.N81.Shard0022
import BerryEsseen.Certificates.Finite.N81.Shard0023
import BerryEsseen.Certificates.Finite.N81.Shard0024
import BerryEsseen.Certificates.Finite.N81.Shard0025
import BerryEsseen.Certificates.Finite.N81.Shard0026
import BerryEsseen.Certificates.Finite.N81.Shard0027
import BerryEsseen.Certificates.Finite.N81.Shard0028
import BerryEsseen.Certificates.Finite.N81.Shard0029
import BerryEsseen.Certificates.Finite.N81.Shard0030
import BerryEsseen.Certificates.Finite.N81.Shard0031

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN81Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN81Shard0000Tree (.splitRho finiteN81Shard0001Tree finiteN81Shard0002Tree)) finiteN81Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN81Shard0004Tree (.splitRho (.splitZ finiteN81Shard0005Tree finiteN81Shard0006Tree) finiteN81Shard0007Tree)) finiteN81Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN81Shard0009Tree (.splitRho (.splitZ finiteN81Shard0010Tree finiteN81Shard0011Tree) finiteN81Shard0012Tree)) finiteN81Shard0013Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN81Shard0014Tree finiteN81Shard0015Tree) (.splitRho (.splitZ finiteN81Shard0016Tree finiteN81Shard0017Tree) finiteN81Shard0018Tree)) finiteN81Shard0019Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN81Shard0020Tree finiteN81Shard0021Tree) finiteN81Shard0022Tree) (.splitRho (.splitZ (.splitRho finiteN81Shard0023Tree finiteN81Shard0024Tree) (.splitRho finiteN81Shard0025Tree finiteN81Shard0026Tree)) finiteN81Shard0027Tree)) finiteN81Shard0028Tree)) finiteN81Shard0029Tree)) finiteN81Shard0030Tree)) finiteN81Shard0031Tree))

theorem finiteN81_parsed :
    (certifiedOldLeafCode 81).bind dyadicRouteBLeafTreeOfCode =
      some finiteN81Tree := by
  native_decide

theorem finiteN81_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 81 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN81_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN81Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN81Shard0001_checked finiteN81Shard0002_checked)) finiteN81Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN81Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN81Shard0005_checked finiteN81Shard0006_checked) finiteN81Shard0007_checked)) finiteN81Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN81Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN81Shard0010_checked finiteN81Shard0011_checked) finiteN81Shard0012_checked)) finiteN81Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN81Shard0014_checked finiteN81Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN81Shard0016_checked finiteN81Shard0017_checked) finiteN81Shard0018_checked)) finiteN81Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN81Shard0020_checked finiteN81Shard0021_checked) finiteN81Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN81Shard0023_checked finiteN81Shard0024_checked) (bound4395FiniteVerifySplitRho_true finiteN81Shard0025_checked finiteN81Shard0026_checked)) finiteN81Shard0027_checked)) finiteN81Shard0028_checked)) finiteN81Shard0029_checked)) finiteN81Shard0030_checked)) finiteN81Shard0031_checked))

end BerryEsseen
