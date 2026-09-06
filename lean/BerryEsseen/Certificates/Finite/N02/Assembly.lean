import BerryEsseen.Certificates.Finite.N02.Shard0000
import BerryEsseen.Certificates.Finite.N02.Shard0001
import BerryEsseen.Certificates.Finite.N02.Shard0002
import BerryEsseen.Certificates.Finite.N02.Shard0003
import BerryEsseen.Certificates.Finite.N02.Shard0004
import BerryEsseen.Certificates.Finite.N02.Shard0005
import BerryEsseen.Certificates.Finite.N02.Shard0006
import BerryEsseen.Certificates.Finite.N02.Shard0007
import BerryEsseen.Certificates.Finite.N02.Shard0008
import BerryEsseen.Certificates.Finite.N02.Shard0009
import BerryEsseen.Certificates.Finite.N02.Shard0010

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN02Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN02Shard0000Tree (.splitRho (.splitZ finiteN02Shard0001Tree (.splitRho (.splitZ finiteN02Shard0002Tree (.splitRho (.splitZ finiteN02Shard0003Tree (.splitRho (.splitZ finiteN02Shard0004Tree (.splitRho finiteN02Shard0005Tree finiteN02Shard0006Tree)) finiteN02Shard0007Tree)) finiteN02Shard0008Tree)) finiteN02Shard0009Tree)) finiteN02Shard0010Tree))

theorem finiteN02_parsed :
    (certifiedOldLeafCode 2).bind dyadicRouteBLeafTreeOfCode =
      some finiteN02Tree := by
  native_decide

theorem finiteN02_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 2 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN02_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN02Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN02Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN02Shard0002_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN02Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN02Shard0004_checked (bound4395FiniteVerifySplitRho_true finiteN02Shard0005_checked finiteN02Shard0006_checked)) finiteN02Shard0007_checked)) finiteN02Shard0008_checked)) finiteN02Shard0009_checked)) finiteN02Shard0010_checked))

end BerryEsseen
