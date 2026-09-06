import BerryEsseen.Certificates.Finite.N96.Shard0000
import BerryEsseen.Certificates.Finite.N96.Shard0001
import BerryEsseen.Certificates.Finite.N96.Shard0002
import BerryEsseen.Certificates.Finite.N96.Shard0003
import BerryEsseen.Certificates.Finite.N96.Shard0004
import BerryEsseen.Certificates.Finite.N96.Shard0005
import BerryEsseen.Certificates.Finite.N96.Shard0006
import BerryEsseen.Certificates.Finite.N96.Shard0007
import BerryEsseen.Certificates.Finite.N96.Shard0008
import BerryEsseen.Certificates.Finite.N96.Shard0009
import BerryEsseen.Certificates.Finite.N96.Shard0010
import BerryEsseen.Certificates.Finite.N96.Shard0011
import BerryEsseen.Certificates.Finite.N96.Shard0012
import BerryEsseen.Certificates.Finite.N96.Shard0013
import BerryEsseen.Certificates.Finite.N96.Shard0014
import BerryEsseen.Certificates.Finite.N96.Shard0015
import BerryEsseen.Certificates.Finite.N96.Shard0016
import BerryEsseen.Certificates.Finite.N96.Shard0017
import BerryEsseen.Certificates.Finite.N96.Shard0018
import BerryEsseen.Certificates.Finite.N96.Shard0019
import BerryEsseen.Certificates.Finite.N96.Shard0020
import BerryEsseen.Certificates.Finite.N96.Shard0021
import BerryEsseen.Certificates.Finite.N96.Shard0022
import BerryEsseen.Certificates.Finite.N96.Shard0023
import BerryEsseen.Certificates.Finite.N96.Shard0024
import BerryEsseen.Certificates.Finite.N96.Shard0025
import BerryEsseen.Certificates.Finite.N96.Shard0026
import BerryEsseen.Certificates.Finite.N96.Shard0027
import BerryEsseen.Certificates.Finite.N96.Shard0028
import BerryEsseen.Certificates.Finite.N96.Shard0029
import BerryEsseen.Certificates.Finite.N96.Shard0030
import BerryEsseen.Certificates.Finite.N96.Shard0031
import BerryEsseen.Certificates.Finite.N96.Shard0032
import BerryEsseen.Certificates.Finite.N96.Shard0033
import BerryEsseen.Certificates.Finite.N96.Shard0034
import BerryEsseen.Certificates.Finite.N96.Shard0035
import BerryEsseen.Certificates.Finite.N96.Shard0036

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN96Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN96Shard0000Tree (.splitRho (.splitZ finiteN96Shard0001Tree finiteN96Shard0002Tree) finiteN96Shard0003Tree)) finiteN96Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN96Shard0005Tree finiteN96Shard0006Tree) (.splitRho (.splitZ finiteN96Shard0007Tree finiteN96Shard0008Tree) finiteN96Shard0009Tree)) finiteN96Shard0010Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN96Shard0011Tree finiteN96Shard0012Tree) finiteN96Shard0013Tree) (.splitRho (.splitZ finiteN96Shard0014Tree finiteN96Shard0015Tree) finiteN96Shard0016Tree)) finiteN96Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN96Shard0018Tree (.splitRho (.splitZ finiteN96Shard0019Tree finiteN96Shard0020Tree) finiteN96Shard0021Tree)) finiteN96Shard0022Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN96Shard0023Tree (.splitRho finiteN96Shard0024Tree finiteN96Shard0025Tree)) finiteN96Shard0026Tree) (.splitRho (.splitZ (.splitRho finiteN96Shard0027Tree finiteN96Shard0028Tree) (.splitRho (.splitZ finiteN96Shard0029Tree finiteN96Shard0030Tree) finiteN96Shard0031Tree)) finiteN96Shard0032Tree)) finiteN96Shard0033Tree)) finiteN96Shard0034Tree)) finiteN96Shard0035Tree)) finiteN96Shard0036Tree))

theorem finiteN96_parsed :
    (certifiedOldLeafCode 96).bind dyadicRouteBLeafTreeOfCode =
      some finiteN96Tree := by
  native_decide

theorem finiteN96_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 96 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN96_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN96Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN96Shard0001_checked finiteN96Shard0002_checked) finiteN96Shard0003_checked)) finiteN96Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN96Shard0005_checked finiteN96Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN96Shard0007_checked finiteN96Shard0008_checked) finiteN96Shard0009_checked)) finiteN96Shard0010_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN96Shard0011_checked finiteN96Shard0012_checked) finiteN96Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN96Shard0014_checked finiteN96Shard0015_checked) finiteN96Shard0016_checked)) finiteN96Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN96Shard0018_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN96Shard0019_checked finiteN96Shard0020_checked) finiteN96Shard0021_checked)) finiteN96Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN96Shard0023_checked (bound4395FiniteVerifySplitRho_true finiteN96Shard0024_checked finiteN96Shard0025_checked)) finiteN96Shard0026_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN96Shard0027_checked finiteN96Shard0028_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN96Shard0029_checked finiteN96Shard0030_checked) finiteN96Shard0031_checked)) finiteN96Shard0032_checked)) finiteN96Shard0033_checked)) finiteN96Shard0034_checked)) finiteN96Shard0035_checked)) finiteN96Shard0036_checked))

end BerryEsseen
