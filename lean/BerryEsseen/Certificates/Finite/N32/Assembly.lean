import BerryEsseen.Certificates.Finite.N32.Shard0000
import BerryEsseen.Certificates.Finite.N32.Shard0001
import BerryEsseen.Certificates.Finite.N32.Shard0002
import BerryEsseen.Certificates.Finite.N32.Shard0003
import BerryEsseen.Certificates.Finite.N32.Shard0004
import BerryEsseen.Certificates.Finite.N32.Shard0005
import BerryEsseen.Certificates.Finite.N32.Shard0006
import BerryEsseen.Certificates.Finite.N32.Shard0007
import BerryEsseen.Certificates.Finite.N32.Shard0008
import BerryEsseen.Certificates.Finite.N32.Shard0009
import BerryEsseen.Certificates.Finite.N32.Shard0010
import BerryEsseen.Certificates.Finite.N32.Shard0011
import BerryEsseen.Certificates.Finite.N32.Shard0012
import BerryEsseen.Certificates.Finite.N32.Shard0013
import BerryEsseen.Certificates.Finite.N32.Shard0014
import BerryEsseen.Certificates.Finite.N32.Shard0015
import BerryEsseen.Certificates.Finite.N32.Shard0016
import BerryEsseen.Certificates.Finite.N32.Shard0017
import BerryEsseen.Certificates.Finite.N32.Shard0018

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN32Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN32Shard0000Tree finiteN32Shard0001Tree) finiteN32Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN32Shard0003Tree finiteN32Shard0004Tree) finiteN32Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN32Shard0006Tree finiteN32Shard0007Tree) finiteN32Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN32Shard0009Tree finiteN32Shard0010Tree) finiteN32Shard0011Tree) (.splitRho (.splitZ finiteN32Shard0012Tree (.splitRho finiteN32Shard0013Tree finiteN32Shard0014Tree)) finiteN32Shard0015Tree)) finiteN32Shard0016Tree)) finiteN32Shard0017Tree)) finiteN32Shard0018Tree))

theorem finiteN32_parsed :
    (certifiedOldLeafCode 32).bind dyadicRouteBLeafTreeOfCode =
      some finiteN32Tree := by
  native_decide

theorem finiteN32_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 32 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN32_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN32Shard0000_checked finiteN32Shard0001_checked) finiteN32Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN32Shard0003_checked finiteN32Shard0004_checked) finiteN32Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN32Shard0006_checked finiteN32Shard0007_checked) finiteN32Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN32Shard0009_checked finiteN32Shard0010_checked) finiteN32Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN32Shard0012_checked (bound4395FiniteVerifySplitRho_true finiteN32Shard0013_checked finiteN32Shard0014_checked)) finiteN32Shard0015_checked)) finiteN32Shard0016_checked)) finiteN32Shard0017_checked)) finiteN32Shard0018_checked))

end BerryEsseen
