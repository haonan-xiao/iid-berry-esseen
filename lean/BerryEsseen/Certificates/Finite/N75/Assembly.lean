import BerryEsseen.Certificates.Finite.N75.Shard0000
import BerryEsseen.Certificates.Finite.N75.Shard0001
import BerryEsseen.Certificates.Finite.N75.Shard0002
import BerryEsseen.Certificates.Finite.N75.Shard0003
import BerryEsseen.Certificates.Finite.N75.Shard0004
import BerryEsseen.Certificates.Finite.N75.Shard0005
import BerryEsseen.Certificates.Finite.N75.Shard0006
import BerryEsseen.Certificates.Finite.N75.Shard0007
import BerryEsseen.Certificates.Finite.N75.Shard0008
import BerryEsseen.Certificates.Finite.N75.Shard0009
import BerryEsseen.Certificates.Finite.N75.Shard0010
import BerryEsseen.Certificates.Finite.N75.Shard0011
import BerryEsseen.Certificates.Finite.N75.Shard0012
import BerryEsseen.Certificates.Finite.N75.Shard0013
import BerryEsseen.Certificates.Finite.N75.Shard0014
import BerryEsseen.Certificates.Finite.N75.Shard0015
import BerryEsseen.Certificates.Finite.N75.Shard0016
import BerryEsseen.Certificates.Finite.N75.Shard0017
import BerryEsseen.Certificates.Finite.N75.Shard0018
import BerryEsseen.Certificates.Finite.N75.Shard0019
import BerryEsseen.Certificates.Finite.N75.Shard0020
import BerryEsseen.Certificates.Finite.N75.Shard0021
import BerryEsseen.Certificates.Finite.N75.Shard0022
import BerryEsseen.Certificates.Finite.N75.Shard0023
import BerryEsseen.Certificates.Finite.N75.Shard0024
import BerryEsseen.Certificates.Finite.N75.Shard0025
import BerryEsseen.Certificates.Finite.N75.Shard0026

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN75Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN75Shard0000Tree (.splitRho finiteN75Shard0001Tree finiteN75Shard0002Tree)) finiteN75Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN75Shard0004Tree (.splitRho (.splitZ finiteN75Shard0005Tree finiteN75Shard0006Tree) finiteN75Shard0007Tree)) finiteN75Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN75Shard0009Tree (.splitRho (.splitZ finiteN75Shard0010Tree finiteN75Shard0011Tree) finiteN75Shard0012Tree)) finiteN75Shard0013Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN75Shard0014Tree finiteN75Shard0015Tree) finiteN75Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN75Shard0017Tree finiteN75Shard0018Tree) finiteN75Shard0019Tree) (.splitRho (.splitZ finiteN75Shard0020Tree finiteN75Shard0021Tree) finiteN75Shard0022Tree)) finiteN75Shard0023Tree)) finiteN75Shard0024Tree)) finiteN75Shard0025Tree)) finiteN75Shard0026Tree))

theorem finiteN75_parsed :
    (certifiedOldLeafCode 75).bind dyadicRouteBLeafTreeOfCode =
      some finiteN75Tree := by
  native_decide

theorem finiteN75_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 75 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN75_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN75Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN75Shard0001_checked finiteN75Shard0002_checked)) finiteN75Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN75Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN75Shard0005_checked finiteN75Shard0006_checked) finiteN75Shard0007_checked)) finiteN75Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN75Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN75Shard0010_checked finiteN75Shard0011_checked) finiteN75Shard0012_checked)) finiteN75Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN75Shard0014_checked finiteN75Shard0015_checked) finiteN75Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN75Shard0017_checked finiteN75Shard0018_checked) finiteN75Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN75Shard0020_checked finiteN75Shard0021_checked) finiteN75Shard0022_checked)) finiteN75Shard0023_checked)) finiteN75Shard0024_checked)) finiteN75Shard0025_checked)) finiteN75Shard0026_checked))

end BerryEsseen
