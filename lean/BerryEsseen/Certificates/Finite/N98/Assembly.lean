import BerryEsseen.Certificates.Finite.N98.Shard0000
import BerryEsseen.Certificates.Finite.N98.Shard0001
import BerryEsseen.Certificates.Finite.N98.Shard0002
import BerryEsseen.Certificates.Finite.N98.Shard0003
import BerryEsseen.Certificates.Finite.N98.Shard0004
import BerryEsseen.Certificates.Finite.N98.Shard0005
import BerryEsseen.Certificates.Finite.N98.Shard0006
import BerryEsseen.Certificates.Finite.N98.Shard0007
import BerryEsseen.Certificates.Finite.N98.Shard0008
import BerryEsseen.Certificates.Finite.N98.Shard0009
import BerryEsseen.Certificates.Finite.N98.Shard0010
import BerryEsseen.Certificates.Finite.N98.Shard0011
import BerryEsseen.Certificates.Finite.N98.Shard0012
import BerryEsseen.Certificates.Finite.N98.Shard0013
import BerryEsseen.Certificates.Finite.N98.Shard0014
import BerryEsseen.Certificates.Finite.N98.Shard0015
import BerryEsseen.Certificates.Finite.N98.Shard0016
import BerryEsseen.Certificates.Finite.N98.Shard0017
import BerryEsseen.Certificates.Finite.N98.Shard0018
import BerryEsseen.Certificates.Finite.N98.Shard0019
import BerryEsseen.Certificates.Finite.N98.Shard0020
import BerryEsseen.Certificates.Finite.N98.Shard0021
import BerryEsseen.Certificates.Finite.N98.Shard0022
import BerryEsseen.Certificates.Finite.N98.Shard0023
import BerryEsseen.Certificates.Finite.N98.Shard0024
import BerryEsseen.Certificates.Finite.N98.Shard0025
import BerryEsseen.Certificates.Finite.N98.Shard0026
import BerryEsseen.Certificates.Finite.N98.Shard0027
import BerryEsseen.Certificates.Finite.N98.Shard0028
import BerryEsseen.Certificates.Finite.N98.Shard0029
import BerryEsseen.Certificates.Finite.N98.Shard0030
import BerryEsseen.Certificates.Finite.N98.Shard0031
import BerryEsseen.Certificates.Finite.N98.Shard0032
import BerryEsseen.Certificates.Finite.N98.Shard0033
import BerryEsseen.Certificates.Finite.N98.Shard0034
import BerryEsseen.Certificates.Finite.N98.Shard0035
import BerryEsseen.Certificates.Finite.N98.Shard0036
import BerryEsseen.Certificates.Finite.N98.Shard0037

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN98Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN98Shard0000Tree (.splitRho (.splitZ finiteN98Shard0001Tree finiteN98Shard0002Tree) finiteN98Shard0003Tree)) finiteN98Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN98Shard0005Tree (.splitRho (.splitZ finiteN98Shard0006Tree finiteN98Shard0007Tree) finiteN98Shard0008Tree)) finiteN98Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN98Shard0010Tree finiteN98Shard0011Tree) finiteN98Shard0012Tree) (.splitRho (.splitZ finiteN98Shard0013Tree finiteN98Shard0014Tree) finiteN98Shard0015Tree)) finiteN98Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN98Shard0017Tree finiteN98Shard0018Tree) finiteN98Shard0019Tree) (.splitRho (.splitZ finiteN98Shard0020Tree finiteN98Shard0021Tree) finiteN98Shard0022Tree)) finiteN98Shard0023Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN98Shard0024Tree (.splitRho finiteN98Shard0025Tree finiteN98Shard0026Tree)) finiteN98Shard0027Tree) (.splitRho (.splitZ (.splitRho finiteN98Shard0028Tree finiteN98Shard0029Tree) (.splitRho (.splitZ finiteN98Shard0030Tree finiteN98Shard0031Tree) finiteN98Shard0032Tree)) finiteN98Shard0033Tree)) finiteN98Shard0034Tree)) finiteN98Shard0035Tree)) finiteN98Shard0036Tree)) finiteN98Shard0037Tree))

theorem finiteN98_parsed :
    (certifiedOldLeafCode 98).bind dyadicRouteBLeafTreeOfCode =
      some finiteN98Tree := by
  native_decide

theorem finiteN98_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 98 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN98_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0001_checked finiteN98Shard0002_checked) finiteN98Shard0003_checked)) finiteN98Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0006_checked finiteN98Shard0007_checked) finiteN98Shard0008_checked)) finiteN98Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0010_checked finiteN98Shard0011_checked) finiteN98Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0013_checked finiteN98Shard0014_checked) finiteN98Shard0015_checked)) finiteN98Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0017_checked finiteN98Shard0018_checked) finiteN98Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0020_checked finiteN98Shard0021_checked) finiteN98Shard0022_checked)) finiteN98Shard0023_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0024_checked (bound4395FiniteVerifySplitRho_true finiteN98Shard0025_checked finiteN98Shard0026_checked)) finiteN98Shard0027_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN98Shard0028_checked finiteN98Shard0029_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN98Shard0030_checked finiteN98Shard0031_checked) finiteN98Shard0032_checked)) finiteN98Shard0033_checked)) finiteN98Shard0034_checked)) finiteN98Shard0035_checked)) finiteN98Shard0036_checked)) finiteN98Shard0037_checked))

end BerryEsseen
