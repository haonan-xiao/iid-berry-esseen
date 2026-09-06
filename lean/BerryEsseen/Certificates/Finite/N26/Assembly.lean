import BerryEsseen.Certificates.Finite.N26.Shard0000
import BerryEsseen.Certificates.Finite.N26.Shard0001
import BerryEsseen.Certificates.Finite.N26.Shard0002
import BerryEsseen.Certificates.Finite.N26.Shard0003
import BerryEsseen.Certificates.Finite.N26.Shard0004
import BerryEsseen.Certificates.Finite.N26.Shard0005
import BerryEsseen.Certificates.Finite.N26.Shard0006
import BerryEsseen.Certificates.Finite.N26.Shard0007
import BerryEsseen.Certificates.Finite.N26.Shard0008
import BerryEsseen.Certificates.Finite.N26.Shard0009
import BerryEsseen.Certificates.Finite.N26.Shard0010
import BerryEsseen.Certificates.Finite.N26.Shard0011
import BerryEsseen.Certificates.Finite.N26.Shard0012
import BerryEsseen.Certificates.Finite.N26.Shard0013
import BerryEsseen.Certificates.Finite.N26.Shard0014
import BerryEsseen.Certificates.Finite.N26.Shard0015
import BerryEsseen.Certificates.Finite.N26.Shard0016

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN26Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho finiteN26Shard0000Tree finiteN26Shard0001Tree) (.splitRho (.splitZ (.splitRho finiteN26Shard0002Tree finiteN26Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN26Shard0004Tree finiteN26Shard0005Tree) finiteN26Shard0006Tree) (.splitRho (.splitZ (.splitRho finiteN26Shard0007Tree finiteN26Shard0008Tree) (.splitRho (.splitZ finiteN26Shard0009Tree (.splitRho (.splitZ finiteN26Shard0010Tree finiteN26Shard0011Tree) finiteN26Shard0012Tree)) finiteN26Shard0013Tree)) finiteN26Shard0014Tree)) finiteN26Shard0015Tree)) finiteN26Shard0016Tree))

theorem finiteN26_parsed :
    (certifiedOldLeafCode 26).bind dyadicRouteBLeafTreeOfCode =
      some finiteN26Tree := by
  native_decide

theorem finiteN26_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 26 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN26_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN26Shard0000_checked finiteN26Shard0001_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN26Shard0002_checked finiteN26Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN26Shard0004_checked finiteN26Shard0005_checked) finiteN26Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN26Shard0007_checked finiteN26Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN26Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN26Shard0010_checked finiteN26Shard0011_checked) finiteN26Shard0012_checked)) finiteN26Shard0013_checked)) finiteN26Shard0014_checked)) finiteN26Shard0015_checked)) finiteN26Shard0016_checked))

end BerryEsseen
