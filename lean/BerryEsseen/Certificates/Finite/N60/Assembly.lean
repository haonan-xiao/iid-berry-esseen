import BerryEsseen.Certificates.Finite.N60.Shard0000
import BerryEsseen.Certificates.Finite.N60.Shard0001
import BerryEsseen.Certificates.Finite.N60.Shard0002
import BerryEsseen.Certificates.Finite.N60.Shard0003
import BerryEsseen.Certificates.Finite.N60.Shard0004
import BerryEsseen.Certificates.Finite.N60.Shard0005
import BerryEsseen.Certificates.Finite.N60.Shard0006
import BerryEsseen.Certificates.Finite.N60.Shard0007
import BerryEsseen.Certificates.Finite.N60.Shard0008
import BerryEsseen.Certificates.Finite.N60.Shard0009
import BerryEsseen.Certificates.Finite.N60.Shard0010
import BerryEsseen.Certificates.Finite.N60.Shard0011
import BerryEsseen.Certificates.Finite.N60.Shard0012
import BerryEsseen.Certificates.Finite.N60.Shard0013
import BerryEsseen.Certificates.Finite.N60.Shard0014
import BerryEsseen.Certificates.Finite.N60.Shard0015
import BerryEsseen.Certificates.Finite.N60.Shard0016
import BerryEsseen.Certificates.Finite.N60.Shard0017
import BerryEsseen.Certificates.Finite.N60.Shard0018
import BerryEsseen.Certificates.Finite.N60.Shard0019
import BerryEsseen.Certificates.Finite.N60.Shard0020
import BerryEsseen.Certificates.Finite.N60.Shard0021
import BerryEsseen.Certificates.Finite.N60.Shard0022
import BerryEsseen.Certificates.Finite.N60.Shard0023
import BerryEsseen.Certificates.Finite.N60.Shard0024

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN60Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN60Shard0000Tree (.splitRho finiteN60Shard0001Tree finiteN60Shard0002Tree)) finiteN60Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN60Shard0004Tree (.splitRho finiteN60Shard0005Tree finiteN60Shard0006Tree)) finiteN60Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN60Shard0008Tree (.splitRho (.splitZ finiteN60Shard0009Tree finiteN60Shard0010Tree) finiteN60Shard0011Tree)) finiteN60Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN60Shard0013Tree finiteN60Shard0014Tree) finiteN60Shard0015Tree) (.splitRho (.splitZ (.splitRho finiteN60Shard0016Tree finiteN60Shard0017Tree) (.splitRho (.splitZ finiteN60Shard0018Tree finiteN60Shard0019Tree) finiteN60Shard0020Tree)) finiteN60Shard0021Tree)) finiteN60Shard0022Tree)) finiteN60Shard0023Tree)) finiteN60Shard0024Tree))

theorem finiteN60_parsed :
    (certifiedOldLeafCode 60).bind dyadicRouteBLeafTreeOfCode =
      some finiteN60Tree := by
  native_decide

theorem finiteN60_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 60 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN60_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN60Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN60Shard0001_checked finiteN60Shard0002_checked)) finiteN60Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN60Shard0004_checked (bound4395FiniteVerifySplitRho_true finiteN60Shard0005_checked finiteN60Shard0006_checked)) finiteN60Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN60Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN60Shard0009_checked finiteN60Shard0010_checked) finiteN60Shard0011_checked)) finiteN60Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN60Shard0013_checked finiteN60Shard0014_checked) finiteN60Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN60Shard0016_checked finiteN60Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN60Shard0018_checked finiteN60Shard0019_checked) finiteN60Shard0020_checked)) finiteN60Shard0021_checked)) finiteN60Shard0022_checked)) finiteN60Shard0023_checked)) finiteN60Shard0024_checked))

end BerryEsseen
