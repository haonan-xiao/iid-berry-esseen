import BerryEsseen.Certificates.Finite.N54.Shard0000
import BerryEsseen.Certificates.Finite.N54.Shard0001
import BerryEsseen.Certificates.Finite.N54.Shard0002
import BerryEsseen.Certificates.Finite.N54.Shard0003
import BerryEsseen.Certificates.Finite.N54.Shard0004
import BerryEsseen.Certificates.Finite.N54.Shard0005
import BerryEsseen.Certificates.Finite.N54.Shard0006
import BerryEsseen.Certificates.Finite.N54.Shard0007
import BerryEsseen.Certificates.Finite.N54.Shard0008
import BerryEsseen.Certificates.Finite.N54.Shard0009
import BerryEsseen.Certificates.Finite.N54.Shard0010
import BerryEsseen.Certificates.Finite.N54.Shard0011
import BerryEsseen.Certificates.Finite.N54.Shard0012
import BerryEsseen.Certificates.Finite.N54.Shard0013
import BerryEsseen.Certificates.Finite.N54.Shard0014
import BerryEsseen.Certificates.Finite.N54.Shard0015
import BerryEsseen.Certificates.Finite.N54.Shard0016
import BerryEsseen.Certificates.Finite.N54.Shard0017
import BerryEsseen.Certificates.Finite.N54.Shard0018
import BerryEsseen.Certificates.Finite.N54.Shard0019
import BerryEsseen.Certificates.Finite.N54.Shard0020
import BerryEsseen.Certificates.Finite.N54.Shard0021
import BerryEsseen.Certificates.Finite.N54.Shard0022
import BerryEsseen.Certificates.Finite.N54.Shard0023
import BerryEsseen.Certificates.Finite.N54.Shard0024
import BerryEsseen.Certificates.Finite.N54.Shard0025
import BerryEsseen.Certificates.Finite.N54.Shard0026

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN54Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN54Shard0000Tree finiteN54Shard0001Tree) finiteN54Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN54Shard0003Tree (.splitRho (.splitZ finiteN54Shard0004Tree finiteN54Shard0005Tree) finiteN54Shard0006Tree)) finiteN54Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN54Shard0008Tree (.splitRho (.splitZ finiteN54Shard0009Tree finiteN54Shard0010Tree) finiteN54Shard0011Tree)) finiteN54Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN54Shard0013Tree (.splitRho finiteN54Shard0014Tree finiteN54Shard0015Tree)) finiteN54Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN54Shard0017Tree finiteN54Shard0018Tree) finiteN54Shard0019Tree) (.splitRho (.splitZ finiteN54Shard0020Tree finiteN54Shard0021Tree) finiteN54Shard0022Tree)) finiteN54Shard0023Tree)) finiteN54Shard0024Tree)) finiteN54Shard0025Tree)) finiteN54Shard0026Tree))

theorem finiteN54_parsed :
    (certifiedOldLeafCode 54).bind dyadicRouteBLeafTreeOfCode =
      some finiteN54Tree := by
  native_decide

theorem finiteN54_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 54 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN54_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN54Shard0000_checked finiteN54Shard0001_checked) finiteN54Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN54Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN54Shard0004_checked finiteN54Shard0005_checked) finiteN54Shard0006_checked)) finiteN54Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN54Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN54Shard0009_checked finiteN54Shard0010_checked) finiteN54Shard0011_checked)) finiteN54Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN54Shard0013_checked (bound4395FiniteVerifySplitRho_true finiteN54Shard0014_checked finiteN54Shard0015_checked)) finiteN54Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN54Shard0017_checked finiteN54Shard0018_checked) finiteN54Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN54Shard0020_checked finiteN54Shard0021_checked) finiteN54Shard0022_checked)) finiteN54Shard0023_checked)) finiteN54Shard0024_checked)) finiteN54Shard0025_checked)) finiteN54Shard0026_checked))

end BerryEsseen
