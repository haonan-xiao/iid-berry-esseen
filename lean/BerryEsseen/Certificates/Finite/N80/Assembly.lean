import BerryEsseen.Certificates.Finite.N80.Shard0000
import BerryEsseen.Certificates.Finite.N80.Shard0001
import BerryEsseen.Certificates.Finite.N80.Shard0002
import BerryEsseen.Certificates.Finite.N80.Shard0003
import BerryEsseen.Certificates.Finite.N80.Shard0004
import BerryEsseen.Certificates.Finite.N80.Shard0005
import BerryEsseen.Certificates.Finite.N80.Shard0006
import BerryEsseen.Certificates.Finite.N80.Shard0007
import BerryEsseen.Certificates.Finite.N80.Shard0008
import BerryEsseen.Certificates.Finite.N80.Shard0009
import BerryEsseen.Certificates.Finite.N80.Shard0010
import BerryEsseen.Certificates.Finite.N80.Shard0011
import BerryEsseen.Certificates.Finite.N80.Shard0012
import BerryEsseen.Certificates.Finite.N80.Shard0013
import BerryEsseen.Certificates.Finite.N80.Shard0014
import BerryEsseen.Certificates.Finite.N80.Shard0015
import BerryEsseen.Certificates.Finite.N80.Shard0016
import BerryEsseen.Certificates.Finite.N80.Shard0017
import BerryEsseen.Certificates.Finite.N80.Shard0018
import BerryEsseen.Certificates.Finite.N80.Shard0019
import BerryEsseen.Certificates.Finite.N80.Shard0020
import BerryEsseen.Certificates.Finite.N80.Shard0021
import BerryEsseen.Certificates.Finite.N80.Shard0022
import BerryEsseen.Certificates.Finite.N80.Shard0023
import BerryEsseen.Certificates.Finite.N80.Shard0024
import BerryEsseen.Certificates.Finite.N80.Shard0025
import BerryEsseen.Certificates.Finite.N80.Shard0026

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN80Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN80Shard0000Tree (.splitRho finiteN80Shard0001Tree finiteN80Shard0002Tree)) finiteN80Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN80Shard0004Tree (.splitRho (.splitZ finiteN80Shard0005Tree finiteN80Shard0006Tree) finiteN80Shard0007Tree)) finiteN80Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN80Shard0009Tree (.splitRho (.splitZ finiteN80Shard0010Tree finiteN80Shard0011Tree) finiteN80Shard0012Tree)) finiteN80Shard0013Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN80Shard0014Tree finiteN80Shard0015Tree) finiteN80Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN80Shard0017Tree finiteN80Shard0018Tree) finiteN80Shard0019Tree) (.splitRho (.splitZ finiteN80Shard0020Tree finiteN80Shard0021Tree) finiteN80Shard0022Tree)) finiteN80Shard0023Tree)) finiteN80Shard0024Tree)) finiteN80Shard0025Tree)) finiteN80Shard0026Tree))

theorem finiteN80_parsed :
    (certifiedOldLeafCode 80).bind dyadicRouteBLeafTreeOfCode =
      some finiteN80Tree := by
  native_decide

theorem finiteN80_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 80 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN80_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN80Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN80Shard0001_checked finiteN80Shard0002_checked)) finiteN80Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN80Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN80Shard0005_checked finiteN80Shard0006_checked) finiteN80Shard0007_checked)) finiteN80Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN80Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN80Shard0010_checked finiteN80Shard0011_checked) finiteN80Shard0012_checked)) finiteN80Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN80Shard0014_checked finiteN80Shard0015_checked) finiteN80Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN80Shard0017_checked finiteN80Shard0018_checked) finiteN80Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN80Shard0020_checked finiteN80Shard0021_checked) finiteN80Shard0022_checked)) finiteN80Shard0023_checked)) finiteN80Shard0024_checked)) finiteN80Shard0025_checked)) finiteN80Shard0026_checked))

end BerryEsseen
