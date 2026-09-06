import BerryEsseen.Certificates.Finite.N47.Shard0000
import BerryEsseen.Certificates.Finite.N47.Shard0001
import BerryEsseen.Certificates.Finite.N47.Shard0002
import BerryEsseen.Certificates.Finite.N47.Shard0003
import BerryEsseen.Certificates.Finite.N47.Shard0004
import BerryEsseen.Certificates.Finite.N47.Shard0005
import BerryEsseen.Certificates.Finite.N47.Shard0006
import BerryEsseen.Certificates.Finite.N47.Shard0007
import BerryEsseen.Certificates.Finite.N47.Shard0008
import BerryEsseen.Certificates.Finite.N47.Shard0009
import BerryEsseen.Certificates.Finite.N47.Shard0010
import BerryEsseen.Certificates.Finite.N47.Shard0011
import BerryEsseen.Certificates.Finite.N47.Shard0012
import BerryEsseen.Certificates.Finite.N47.Shard0013
import BerryEsseen.Certificates.Finite.N47.Shard0014
import BerryEsseen.Certificates.Finite.N47.Shard0015
import BerryEsseen.Certificates.Finite.N47.Shard0016
import BerryEsseen.Certificates.Finite.N47.Shard0017
import BerryEsseen.Certificates.Finite.N47.Shard0018
import BerryEsseen.Certificates.Finite.N47.Shard0019
import BerryEsseen.Certificates.Finite.N47.Shard0020
import BerryEsseen.Certificates.Finite.N47.Shard0021
import BerryEsseen.Certificates.Finite.N47.Shard0022
import BerryEsseen.Certificates.Finite.N47.Shard0023
import BerryEsseen.Certificates.Finite.N47.Shard0024
import BerryEsseen.Certificates.Finite.N47.Shard0025
import BerryEsseen.Certificates.Finite.N47.Shard0026

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN47Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN47Shard0000Tree finiteN47Shard0001Tree) finiteN47Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN47Shard0003Tree (.splitRho (.splitZ finiteN47Shard0004Tree finiteN47Shard0005Tree) finiteN47Shard0006Tree)) finiteN47Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN47Shard0008Tree (.splitRho (.splitZ finiteN47Shard0009Tree finiteN47Shard0010Tree) finiteN47Shard0011Tree)) finiteN47Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN47Shard0013Tree (.splitRho finiteN47Shard0014Tree finiteN47Shard0015Tree)) finiteN47Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN47Shard0017Tree finiteN47Shard0018Tree) finiteN47Shard0019Tree) (.splitRho (.splitZ finiteN47Shard0020Tree finiteN47Shard0021Tree) finiteN47Shard0022Tree)) finiteN47Shard0023Tree)) finiteN47Shard0024Tree)) finiteN47Shard0025Tree)) finiteN47Shard0026Tree))

theorem finiteN47_parsed :
    (certifiedOldLeafCode 47).bind dyadicRouteBLeafTreeOfCode =
      some finiteN47Tree := by
  native_decide

theorem finiteN47_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 47 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN47_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN47Shard0000_checked finiteN47Shard0001_checked) finiteN47Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN47Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN47Shard0004_checked finiteN47Shard0005_checked) finiteN47Shard0006_checked)) finiteN47Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN47Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN47Shard0009_checked finiteN47Shard0010_checked) finiteN47Shard0011_checked)) finiteN47Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN47Shard0013_checked (bound4395FiniteVerifySplitRho_true finiteN47Shard0014_checked finiteN47Shard0015_checked)) finiteN47Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN47Shard0017_checked finiteN47Shard0018_checked) finiteN47Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN47Shard0020_checked finiteN47Shard0021_checked) finiteN47Shard0022_checked)) finiteN47Shard0023_checked)) finiteN47Shard0024_checked)) finiteN47Shard0025_checked)) finiteN47Shard0026_checked))

end BerryEsseen
