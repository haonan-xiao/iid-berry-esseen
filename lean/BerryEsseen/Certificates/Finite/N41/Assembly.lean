import BerryEsseen.Certificates.Finite.N41.Shard0000
import BerryEsseen.Certificates.Finite.N41.Shard0001
import BerryEsseen.Certificates.Finite.N41.Shard0002
import BerryEsseen.Certificates.Finite.N41.Shard0003
import BerryEsseen.Certificates.Finite.N41.Shard0004
import BerryEsseen.Certificates.Finite.N41.Shard0005
import BerryEsseen.Certificates.Finite.N41.Shard0006
import BerryEsseen.Certificates.Finite.N41.Shard0007
import BerryEsseen.Certificates.Finite.N41.Shard0008
import BerryEsseen.Certificates.Finite.N41.Shard0009
import BerryEsseen.Certificates.Finite.N41.Shard0010
import BerryEsseen.Certificates.Finite.N41.Shard0011
import BerryEsseen.Certificates.Finite.N41.Shard0012
import BerryEsseen.Certificates.Finite.N41.Shard0013
import BerryEsseen.Certificates.Finite.N41.Shard0014
import BerryEsseen.Certificates.Finite.N41.Shard0015
import BerryEsseen.Certificates.Finite.N41.Shard0016
import BerryEsseen.Certificates.Finite.N41.Shard0017
import BerryEsseen.Certificates.Finite.N41.Shard0018

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN41Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN41Shard0000Tree finiteN41Shard0001Tree) finiteN41Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN41Shard0003Tree finiteN41Shard0004Tree) finiteN41Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN41Shard0006Tree finiteN41Shard0007Tree) finiteN41Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN41Shard0009Tree finiteN41Shard0010Tree) finiteN41Shard0011Tree) (.splitRho (.splitZ finiteN41Shard0012Tree (.splitRho finiteN41Shard0013Tree finiteN41Shard0014Tree)) finiteN41Shard0015Tree)) finiteN41Shard0016Tree)) finiteN41Shard0017Tree)) finiteN41Shard0018Tree))

theorem finiteN41_parsed :
    (certifiedOldLeafCode 41).bind dyadicRouteBLeafTreeOfCode =
      some finiteN41Tree := by
  native_decide

theorem finiteN41_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 41 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN41_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN41Shard0000_checked finiteN41Shard0001_checked) finiteN41Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN41Shard0003_checked finiteN41Shard0004_checked) finiteN41Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN41Shard0006_checked finiteN41Shard0007_checked) finiteN41Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN41Shard0009_checked finiteN41Shard0010_checked) finiteN41Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN41Shard0012_checked (bound4395FiniteVerifySplitRho_true finiteN41Shard0013_checked finiteN41Shard0014_checked)) finiteN41Shard0015_checked)) finiteN41Shard0016_checked)) finiteN41Shard0017_checked)) finiteN41Shard0018_checked))

end BerryEsseen
