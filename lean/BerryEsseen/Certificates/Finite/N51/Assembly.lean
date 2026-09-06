import BerryEsseen.Certificates.Finite.N51.Shard0000
import BerryEsseen.Certificates.Finite.N51.Shard0001
import BerryEsseen.Certificates.Finite.N51.Shard0002
import BerryEsseen.Certificates.Finite.N51.Shard0003
import BerryEsseen.Certificates.Finite.N51.Shard0004
import BerryEsseen.Certificates.Finite.N51.Shard0005
import BerryEsseen.Certificates.Finite.N51.Shard0006
import BerryEsseen.Certificates.Finite.N51.Shard0007
import BerryEsseen.Certificates.Finite.N51.Shard0008
import BerryEsseen.Certificates.Finite.N51.Shard0009
import BerryEsseen.Certificates.Finite.N51.Shard0010
import BerryEsseen.Certificates.Finite.N51.Shard0011
import BerryEsseen.Certificates.Finite.N51.Shard0012
import BerryEsseen.Certificates.Finite.N51.Shard0013
import BerryEsseen.Certificates.Finite.N51.Shard0014
import BerryEsseen.Certificates.Finite.N51.Shard0015
import BerryEsseen.Certificates.Finite.N51.Shard0016
import BerryEsseen.Certificates.Finite.N51.Shard0017
import BerryEsseen.Certificates.Finite.N51.Shard0018
import BerryEsseen.Certificates.Finite.N51.Shard0019
import BerryEsseen.Certificates.Finite.N51.Shard0020
import BerryEsseen.Certificates.Finite.N51.Shard0021
import BerryEsseen.Certificates.Finite.N51.Shard0022
import BerryEsseen.Certificates.Finite.N51.Shard0023
import BerryEsseen.Certificates.Finite.N51.Shard0024
import BerryEsseen.Certificates.Finite.N51.Shard0025

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN51Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN51Shard0000Tree finiteN51Shard0001Tree) finiteN51Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN51Shard0003Tree (.splitRho finiteN51Shard0004Tree finiteN51Shard0005Tree)) finiteN51Shard0006Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN51Shard0007Tree (.splitRho (.splitZ finiteN51Shard0008Tree finiteN51Shard0009Tree) finiteN51Shard0010Tree)) finiteN51Shard0011Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN51Shard0012Tree (.splitRho finiteN51Shard0013Tree finiteN51Shard0014Tree)) finiteN51Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN51Shard0016Tree finiteN51Shard0017Tree) finiteN51Shard0018Tree) (.splitRho (.splitZ finiteN51Shard0019Tree finiteN51Shard0020Tree) finiteN51Shard0021Tree)) finiteN51Shard0022Tree)) finiteN51Shard0023Tree)) finiteN51Shard0024Tree)) finiteN51Shard0025Tree))

theorem finiteN51_parsed :
    (certifiedOldLeafCode 51).bind dyadicRouteBLeafTreeOfCode =
      some finiteN51Tree := by
  native_decide

theorem finiteN51_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 51 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN51_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN51Shard0000_checked finiteN51Shard0001_checked) finiteN51Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN51Shard0003_checked (bound4395FiniteVerifySplitRho_true finiteN51Shard0004_checked finiteN51Shard0005_checked)) finiteN51Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN51Shard0007_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN51Shard0008_checked finiteN51Shard0009_checked) finiteN51Shard0010_checked)) finiteN51Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN51Shard0012_checked (bound4395FiniteVerifySplitRho_true finiteN51Shard0013_checked finiteN51Shard0014_checked)) finiteN51Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN51Shard0016_checked finiteN51Shard0017_checked) finiteN51Shard0018_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN51Shard0019_checked finiteN51Shard0020_checked) finiteN51Shard0021_checked)) finiteN51Shard0022_checked)) finiteN51Shard0023_checked)) finiteN51Shard0024_checked)) finiteN51Shard0025_checked))

end BerryEsseen
