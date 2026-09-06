import BerryEsseen.Certificates.Finite.N57.Shard0000
import BerryEsseen.Certificates.Finite.N57.Shard0001
import BerryEsseen.Certificates.Finite.N57.Shard0002
import BerryEsseen.Certificates.Finite.N57.Shard0003
import BerryEsseen.Certificates.Finite.N57.Shard0004
import BerryEsseen.Certificates.Finite.N57.Shard0005
import BerryEsseen.Certificates.Finite.N57.Shard0006
import BerryEsseen.Certificates.Finite.N57.Shard0007
import BerryEsseen.Certificates.Finite.N57.Shard0008
import BerryEsseen.Certificates.Finite.N57.Shard0009
import BerryEsseen.Certificates.Finite.N57.Shard0010
import BerryEsseen.Certificates.Finite.N57.Shard0011
import BerryEsseen.Certificates.Finite.N57.Shard0012
import BerryEsseen.Certificates.Finite.N57.Shard0013
import BerryEsseen.Certificates.Finite.N57.Shard0014
import BerryEsseen.Certificates.Finite.N57.Shard0015
import BerryEsseen.Certificates.Finite.N57.Shard0016
import BerryEsseen.Certificates.Finite.N57.Shard0017
import BerryEsseen.Certificates.Finite.N57.Shard0018
import BerryEsseen.Certificates.Finite.N57.Shard0019
import BerryEsseen.Certificates.Finite.N57.Shard0020
import BerryEsseen.Certificates.Finite.N57.Shard0021
import BerryEsseen.Certificates.Finite.N57.Shard0022
import BerryEsseen.Certificates.Finite.N57.Shard0023
import BerryEsseen.Certificates.Finite.N57.Shard0024

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN57Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN57Shard0000Tree finiteN57Shard0001Tree) finiteN57Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN57Shard0003Tree (.splitRho (.splitZ finiteN57Shard0004Tree finiteN57Shard0005Tree) finiteN57Shard0006Tree)) finiteN57Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN57Shard0008Tree (.splitRho (.splitZ finiteN57Shard0009Tree finiteN57Shard0010Tree) finiteN57Shard0011Tree)) finiteN57Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN57Shard0013Tree finiteN57Shard0014Tree) finiteN57Shard0015Tree) (.splitRho (.splitZ (.splitRho finiteN57Shard0016Tree finiteN57Shard0017Tree) (.splitRho (.splitZ finiteN57Shard0018Tree finiteN57Shard0019Tree) finiteN57Shard0020Tree)) finiteN57Shard0021Tree)) finiteN57Shard0022Tree)) finiteN57Shard0023Tree)) finiteN57Shard0024Tree))

theorem finiteN57_parsed :
    (certifiedOldLeafCode 57).bind dyadicRouteBLeafTreeOfCode =
      some finiteN57Tree := by
  native_decide

theorem finiteN57_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 57 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN57_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN57Shard0000_checked finiteN57Shard0001_checked) finiteN57Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN57Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN57Shard0004_checked finiteN57Shard0005_checked) finiteN57Shard0006_checked)) finiteN57Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN57Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN57Shard0009_checked finiteN57Shard0010_checked) finiteN57Shard0011_checked)) finiteN57Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN57Shard0013_checked finiteN57Shard0014_checked) finiteN57Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN57Shard0016_checked finiteN57Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN57Shard0018_checked finiteN57Shard0019_checked) finiteN57Shard0020_checked)) finiteN57Shard0021_checked)) finiteN57Shard0022_checked)) finiteN57Shard0023_checked)) finiteN57Shard0024_checked))

end BerryEsseen
