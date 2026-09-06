import BerryEsseen.Certificates.Finite.N09.Shard0000
import BerryEsseen.Certificates.Finite.N09.Shard0001
import BerryEsseen.Certificates.Finite.N09.Shard0002
import BerryEsseen.Certificates.Finite.N09.Shard0003
import BerryEsseen.Certificates.Finite.N09.Shard0004
import BerryEsseen.Certificates.Finite.N09.Shard0005
import BerryEsseen.Certificates.Finite.N09.Shard0006
import BerryEsseen.Certificates.Finite.N09.Shard0007
import BerryEsseen.Certificates.Finite.N09.Shard0008
import BerryEsseen.Certificates.Finite.N09.Shard0009
import BerryEsseen.Certificates.Finite.N09.Shard0010
import BerryEsseen.Certificates.Finite.N09.Shard0011
import BerryEsseen.Certificates.Finite.N09.Shard0012
import BerryEsseen.Certificates.Finite.N09.Shard0013
import BerryEsseen.Certificates.Finite.N09.Shard0014

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN09Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN09Shard0000Tree (.splitRho (.splitZ finiteN09Shard0001Tree (.splitRho (.splitZ finiteN09Shard0002Tree (.splitRho (.splitZ (.splitRho (.splitZ finiteN09Shard0003Tree finiteN09Shard0004Tree) finiteN09Shard0005Tree) (.splitRho (.splitZ (.splitRho finiteN09Shard0006Tree finiteN09Shard0007Tree) (.splitRho (.splitZ finiteN09Shard0008Tree finiteN09Shard0009Tree) finiteN09Shard0010Tree)) finiteN09Shard0011Tree)) finiteN09Shard0012Tree)) finiteN09Shard0013Tree)) finiteN09Shard0014Tree))

theorem finiteN09_parsed :
    (certifiedOldLeafCode 9).bind dyadicRouteBLeafTreeOfCode =
      some finiteN09Tree := by
  native_decide

theorem finiteN09_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 9 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN09_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN09Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN09Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN09Shard0002_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN09Shard0003_checked finiteN09Shard0004_checked) finiteN09Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN09Shard0006_checked finiteN09Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN09Shard0008_checked finiteN09Shard0009_checked) finiteN09Shard0010_checked)) finiteN09Shard0011_checked)) finiteN09Shard0012_checked)) finiteN09Shard0013_checked)) finiteN09Shard0014_checked))

end BerryEsseen
