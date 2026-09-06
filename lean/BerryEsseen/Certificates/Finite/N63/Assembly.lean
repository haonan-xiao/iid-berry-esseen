import BerryEsseen.Certificates.Finite.N63.Shard0000
import BerryEsseen.Certificates.Finite.N63.Shard0001
import BerryEsseen.Certificates.Finite.N63.Shard0002
import BerryEsseen.Certificates.Finite.N63.Shard0003
import BerryEsseen.Certificates.Finite.N63.Shard0004
import BerryEsseen.Certificates.Finite.N63.Shard0005
import BerryEsseen.Certificates.Finite.N63.Shard0006
import BerryEsseen.Certificates.Finite.N63.Shard0007
import BerryEsseen.Certificates.Finite.N63.Shard0008
import BerryEsseen.Certificates.Finite.N63.Shard0009
import BerryEsseen.Certificates.Finite.N63.Shard0010
import BerryEsseen.Certificates.Finite.N63.Shard0011
import BerryEsseen.Certificates.Finite.N63.Shard0012
import BerryEsseen.Certificates.Finite.N63.Shard0013
import BerryEsseen.Certificates.Finite.N63.Shard0014
import BerryEsseen.Certificates.Finite.N63.Shard0015
import BerryEsseen.Certificates.Finite.N63.Shard0016
import BerryEsseen.Certificates.Finite.N63.Shard0017
import BerryEsseen.Certificates.Finite.N63.Shard0018
import BerryEsseen.Certificates.Finite.N63.Shard0019
import BerryEsseen.Certificates.Finite.N63.Shard0020
import BerryEsseen.Certificates.Finite.N63.Shard0021
import BerryEsseen.Certificates.Finite.N63.Shard0022
import BerryEsseen.Certificates.Finite.N63.Shard0023
import BerryEsseen.Certificates.Finite.N63.Shard0024
import BerryEsseen.Certificates.Finite.N63.Shard0025
import BerryEsseen.Certificates.Finite.N63.Shard0026

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN63Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN63Shard0000Tree finiteN63Shard0001Tree) finiteN63Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN63Shard0003Tree (.splitRho finiteN63Shard0004Tree finiteN63Shard0005Tree)) finiteN63Shard0006Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN63Shard0007Tree (.splitRho (.splitZ finiteN63Shard0008Tree finiteN63Shard0009Tree) finiteN63Shard0010Tree)) finiteN63Shard0011Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN63Shard0012Tree (.splitRho finiteN63Shard0013Tree finiteN63Shard0014Tree)) finiteN63Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN63Shard0016Tree finiteN63Shard0017Tree) finiteN63Shard0018Tree) (.splitRho (.splitZ finiteN63Shard0019Tree (.splitRho finiteN63Shard0020Tree finiteN63Shard0021Tree)) finiteN63Shard0022Tree)) finiteN63Shard0023Tree)) finiteN63Shard0024Tree)) finiteN63Shard0025Tree)) finiteN63Shard0026Tree))

theorem finiteN63_parsed :
    (certifiedOldLeafCode 63).bind dyadicRouteBLeafTreeOfCode =
      some finiteN63Tree := by
  native_decide

theorem finiteN63_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 63 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN63_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN63Shard0000_checked finiteN63Shard0001_checked) finiteN63Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN63Shard0003_checked (bound4395FiniteVerifySplitRho_true finiteN63Shard0004_checked finiteN63Shard0005_checked)) finiteN63Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN63Shard0007_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN63Shard0008_checked finiteN63Shard0009_checked) finiteN63Shard0010_checked)) finiteN63Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN63Shard0012_checked (bound4395FiniteVerifySplitRho_true finiteN63Shard0013_checked finiteN63Shard0014_checked)) finiteN63Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN63Shard0016_checked finiteN63Shard0017_checked) finiteN63Shard0018_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN63Shard0019_checked (bound4395FiniteVerifySplitRho_true finiteN63Shard0020_checked finiteN63Shard0021_checked)) finiteN63Shard0022_checked)) finiteN63Shard0023_checked)) finiteN63Shard0024_checked)) finiteN63Shard0025_checked)) finiteN63Shard0026_checked))

end BerryEsseen
