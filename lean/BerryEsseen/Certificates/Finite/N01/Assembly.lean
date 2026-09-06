import BerryEsseen.Certificates.Finite.N01.Shard0000
import BerryEsseen.Certificates.Finite.N01.Shard0001
import BerryEsseen.Certificates.Finite.N01.Shard0002
import BerryEsseen.Certificates.Finite.N01.Shard0003
import BerryEsseen.Certificates.Finite.N01.Shard0004
import BerryEsseen.Certificates.Finite.N01.Shard0005

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN01Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN01Shard0000Tree (.splitRho (.splitZ finiteN01Shard0001Tree (.splitRho (.splitZ finiteN01Shard0002Tree finiteN01Shard0003Tree) finiteN01Shard0004Tree)) finiteN01Shard0005Tree))

theorem finiteN01_parsed :
    (certifiedOldLeafCode 1).bind dyadicRouteBLeafTreeOfCode =
      some finiteN01Tree := by
  native_decide

theorem finiteN01_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 1 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN01_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN01Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN01Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN01Shard0002_checked finiteN01Shard0003_checked) finiteN01Shard0004_checked)) finiteN01Shard0005_checked))

end BerryEsseen
