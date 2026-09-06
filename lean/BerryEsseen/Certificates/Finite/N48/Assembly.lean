import BerryEsseen.Certificates.Finite.N48.Shard0000
import BerryEsseen.Certificates.Finite.N48.Shard0001
import BerryEsseen.Certificates.Finite.N48.Shard0002
import BerryEsseen.Certificates.Finite.N48.Shard0003
import BerryEsseen.Certificates.Finite.N48.Shard0004
import BerryEsseen.Certificates.Finite.N48.Shard0005
import BerryEsseen.Certificates.Finite.N48.Shard0006
import BerryEsseen.Certificates.Finite.N48.Shard0007
import BerryEsseen.Certificates.Finite.N48.Shard0008
import BerryEsseen.Certificates.Finite.N48.Shard0009
import BerryEsseen.Certificates.Finite.N48.Shard0010
import BerryEsseen.Certificates.Finite.N48.Shard0011
import BerryEsseen.Certificates.Finite.N48.Shard0012
import BerryEsseen.Certificates.Finite.N48.Shard0013
import BerryEsseen.Certificates.Finite.N48.Shard0014
import BerryEsseen.Certificates.Finite.N48.Shard0015
import BerryEsseen.Certificates.Finite.N48.Shard0016
import BerryEsseen.Certificates.Finite.N48.Shard0017
import BerryEsseen.Certificates.Finite.N48.Shard0018
import BerryEsseen.Certificates.Finite.N48.Shard0019
import BerryEsseen.Certificates.Finite.N48.Shard0020
import BerryEsseen.Certificates.Finite.N48.Shard0021
import BerryEsseen.Certificates.Finite.N48.Shard0022
import BerryEsseen.Certificates.Finite.N48.Shard0023
import BerryEsseen.Certificates.Finite.N48.Shard0024

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN48Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN48Shard0000Tree finiteN48Shard0001Tree) finiteN48Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN48Shard0003Tree (.splitRho finiteN48Shard0004Tree finiteN48Shard0005Tree)) finiteN48Shard0006Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN48Shard0007Tree (.splitRho finiteN48Shard0008Tree finiteN48Shard0009Tree)) finiteN48Shard0010Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN48Shard0011Tree (.splitRho finiteN48Shard0012Tree finiteN48Shard0013Tree)) finiteN48Shard0014Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN48Shard0015Tree finiteN48Shard0016Tree) finiteN48Shard0017Tree) (.splitRho (.splitZ finiteN48Shard0018Tree finiteN48Shard0019Tree) finiteN48Shard0020Tree)) finiteN48Shard0021Tree)) finiteN48Shard0022Tree)) finiteN48Shard0023Tree)) finiteN48Shard0024Tree))

theorem finiteN48_parsed :
    (certifiedOldLeafCode 48).bind dyadicRouteBLeafTreeOfCode =
      some finiteN48Tree := by
  native_decide

theorem finiteN48_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 48 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN48_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN48Shard0000_checked finiteN48Shard0001_checked) finiteN48Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN48Shard0003_checked (bound4395FiniteVerifySplitRho_true finiteN48Shard0004_checked finiteN48Shard0005_checked)) finiteN48Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN48Shard0007_checked (bound4395FiniteVerifySplitRho_true finiteN48Shard0008_checked finiteN48Shard0009_checked)) finiteN48Shard0010_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN48Shard0011_checked (bound4395FiniteVerifySplitRho_true finiteN48Shard0012_checked finiteN48Shard0013_checked)) finiteN48Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN48Shard0015_checked finiteN48Shard0016_checked) finiteN48Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN48Shard0018_checked finiteN48Shard0019_checked) finiteN48Shard0020_checked)) finiteN48Shard0021_checked)) finiteN48Shard0022_checked)) finiteN48Shard0023_checked)) finiteN48Shard0024_checked))

end BerryEsseen
