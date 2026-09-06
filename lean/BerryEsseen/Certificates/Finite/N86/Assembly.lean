import BerryEsseen.Certificates.Finite.N86.Shard0000
import BerryEsseen.Certificates.Finite.N86.Shard0001
import BerryEsseen.Certificates.Finite.N86.Shard0002
import BerryEsseen.Certificates.Finite.N86.Shard0003
import BerryEsseen.Certificates.Finite.N86.Shard0004
import BerryEsseen.Certificates.Finite.N86.Shard0005
import BerryEsseen.Certificates.Finite.N86.Shard0006
import BerryEsseen.Certificates.Finite.N86.Shard0007
import BerryEsseen.Certificates.Finite.N86.Shard0008
import BerryEsseen.Certificates.Finite.N86.Shard0009
import BerryEsseen.Certificates.Finite.N86.Shard0010
import BerryEsseen.Certificates.Finite.N86.Shard0011
import BerryEsseen.Certificates.Finite.N86.Shard0012
import BerryEsseen.Certificates.Finite.N86.Shard0013
import BerryEsseen.Certificates.Finite.N86.Shard0014
import BerryEsseen.Certificates.Finite.N86.Shard0015
import BerryEsseen.Certificates.Finite.N86.Shard0016
import BerryEsseen.Certificates.Finite.N86.Shard0017
import BerryEsseen.Certificates.Finite.N86.Shard0018
import BerryEsseen.Certificates.Finite.N86.Shard0019
import BerryEsseen.Certificates.Finite.N86.Shard0020
import BerryEsseen.Certificates.Finite.N86.Shard0021
import BerryEsseen.Certificates.Finite.N86.Shard0022
import BerryEsseen.Certificates.Finite.N86.Shard0023
import BerryEsseen.Certificates.Finite.N86.Shard0024
import BerryEsseen.Certificates.Finite.N86.Shard0025
import BerryEsseen.Certificates.Finite.N86.Shard0026
import BerryEsseen.Certificates.Finite.N86.Shard0027
import BerryEsseen.Certificates.Finite.N86.Shard0028
import BerryEsseen.Certificates.Finite.N86.Shard0029
import BerryEsseen.Certificates.Finite.N86.Shard0030
import BerryEsseen.Certificates.Finite.N86.Shard0031
import BerryEsseen.Certificates.Finite.N86.Shard0032
import BerryEsseen.Certificates.Finite.N86.Shard0033
import BerryEsseen.Certificates.Finite.N86.Shard0034

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN86Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN86Shard0000Tree (.splitRho (.splitZ finiteN86Shard0001Tree finiteN86Shard0002Tree) finiteN86Shard0003Tree)) finiteN86Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN86Shard0005Tree (.splitRho (.splitZ finiteN86Shard0006Tree finiteN86Shard0007Tree) finiteN86Shard0008Tree)) finiteN86Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN86Shard0010Tree finiteN86Shard0011Tree) (.splitRho (.splitZ finiteN86Shard0012Tree finiteN86Shard0013Tree) finiteN86Shard0014Tree)) finiteN86Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN86Shard0016Tree finiteN86Shard0017Tree) (.splitRho (.splitZ finiteN86Shard0018Tree finiteN86Shard0019Tree) finiteN86Shard0020Tree)) finiteN86Shard0021Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN86Shard0022Tree finiteN86Shard0023Tree) finiteN86Shard0024Tree) (.splitRho (.splitZ (.splitRho finiteN86Shard0025Tree finiteN86Shard0026Tree) (.splitRho (.splitZ finiteN86Shard0027Tree finiteN86Shard0028Tree) finiteN86Shard0029Tree)) finiteN86Shard0030Tree)) finiteN86Shard0031Tree)) finiteN86Shard0032Tree)) finiteN86Shard0033Tree)) finiteN86Shard0034Tree))

theorem finiteN86_parsed :
    (certifiedOldLeafCode 86).bind dyadicRouteBLeafTreeOfCode =
      some finiteN86Tree := by
  native_decide

theorem finiteN86_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 86 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN86_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN86Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN86Shard0001_checked finiteN86Shard0002_checked) finiteN86Shard0003_checked)) finiteN86Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN86Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN86Shard0006_checked finiteN86Shard0007_checked) finiteN86Shard0008_checked)) finiteN86Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN86Shard0010_checked finiteN86Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN86Shard0012_checked finiteN86Shard0013_checked) finiteN86Shard0014_checked)) finiteN86Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN86Shard0016_checked finiteN86Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN86Shard0018_checked finiteN86Shard0019_checked) finiteN86Shard0020_checked)) finiteN86Shard0021_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN86Shard0022_checked finiteN86Shard0023_checked) finiteN86Shard0024_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN86Shard0025_checked finiteN86Shard0026_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN86Shard0027_checked finiteN86Shard0028_checked) finiteN86Shard0029_checked)) finiteN86Shard0030_checked)) finiteN86Shard0031_checked)) finiteN86Shard0032_checked)) finiteN86Shard0033_checked)) finiteN86Shard0034_checked))

end BerryEsseen
