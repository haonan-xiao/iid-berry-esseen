import BerryEsseen.Certificates.Finite.N07.Shard0000
import BerryEsseen.Certificates.Finite.N07.Shard0001
import BerryEsseen.Certificates.Finite.N07.Shard0002
import BerryEsseen.Certificates.Finite.N07.Shard0003
import BerryEsseen.Certificates.Finite.N07.Shard0004
import BerryEsseen.Certificates.Finite.N07.Shard0005
import BerryEsseen.Certificates.Finite.N07.Shard0006
import BerryEsseen.Certificates.Finite.N07.Shard0007
import BerryEsseen.Certificates.Finite.N07.Shard0008
import BerryEsseen.Certificates.Finite.N07.Shard0009
import BerryEsseen.Certificates.Finite.N07.Shard0010
import BerryEsseen.Certificates.Finite.N07.Shard0011
import BerryEsseen.Certificates.Finite.N07.Shard0012
import BerryEsseen.Certificates.Finite.N07.Shard0013
import BerryEsseen.Certificates.Finite.N07.Shard0014
import BerryEsseen.Certificates.Finite.N07.Shard0015
import BerryEsseen.Certificates.Finite.N07.Shard0016

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN07Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN07Shard0000Tree (.splitRho (.splitZ finiteN07Shard0001Tree (.splitRho (.splitZ (.splitRho finiteN07Shard0002Tree finiteN07Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN07Shard0004Tree finiteN07Shard0005Tree) finiteN07Shard0006Tree) (.splitRho (.splitZ (.splitRho finiteN07Shard0007Tree finiteN07Shard0008Tree) (.splitRho (.splitZ finiteN07Shard0009Tree finiteN07Shard0010Tree) finiteN07Shard0011Tree)) (.splitZ finiteN07Shard0012Tree finiteN07Shard0013Tree))) finiteN07Shard0014Tree)) finiteN07Shard0015Tree)) finiteN07Shard0016Tree))

theorem finiteN07_parsed :
    (certifiedOldLeafCode 7).bind dyadicRouteBLeafTreeOfCode =
      some finiteN07Tree := by
  native_decide

theorem finiteN07_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 7 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN07_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN07Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN07Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN07Shard0002_checked finiteN07Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN07Shard0004_checked finiteN07Shard0005_checked) finiteN07Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN07Shard0007_checked finiteN07Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN07Shard0009_checked finiteN07Shard0010_checked) finiteN07Shard0011_checked)) (bound4395FiniteVerifySplitZ_true finiteN07Shard0012_checked finiteN07Shard0013_checked))) finiteN07Shard0014_checked)) finiteN07Shard0015_checked)) finiteN07Shard0016_checked))

end BerryEsseen
