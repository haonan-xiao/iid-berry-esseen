import BerryEsseen.Certificates.Finite.N24.Shard0000
import BerryEsseen.Certificates.Finite.N24.Shard0001
import BerryEsseen.Certificates.Finite.N24.Shard0002
import BerryEsseen.Certificates.Finite.N24.Shard0003
import BerryEsseen.Certificates.Finite.N24.Shard0004
import BerryEsseen.Certificates.Finite.N24.Shard0005
import BerryEsseen.Certificates.Finite.N24.Shard0006
import BerryEsseen.Certificates.Finite.N24.Shard0007
import BerryEsseen.Certificates.Finite.N24.Shard0008
import BerryEsseen.Certificates.Finite.N24.Shard0009
import BerryEsseen.Certificates.Finite.N24.Shard0010
import BerryEsseen.Certificates.Finite.N24.Shard0011
import BerryEsseen.Certificates.Finite.N24.Shard0012
import BerryEsseen.Certificates.Finite.N24.Shard0013
import BerryEsseen.Certificates.Finite.N24.Shard0014
import BerryEsseen.Certificates.Finite.N24.Shard0015
import BerryEsseen.Certificates.Finite.N24.Shard0016
import BerryEsseen.Certificates.Finite.N24.Shard0017
import BerryEsseen.Certificates.Finite.N24.Shard0018

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN24Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN24Shard0000Tree finiteN24Shard0001Tree) finiteN24Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN24Shard0003Tree finiteN24Shard0004Tree) finiteN24Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN24Shard0006Tree finiteN24Shard0007Tree) finiteN24Shard0008Tree) (.splitRho (.splitZ (.splitRho finiteN24Shard0009Tree finiteN24Shard0010Tree) (.splitRho (.splitZ finiteN24Shard0011Tree (.splitRho (.splitZ finiteN24Shard0012Tree finiteN24Shard0013Tree) finiteN24Shard0014Tree)) finiteN24Shard0015Tree)) finiteN24Shard0016Tree)) finiteN24Shard0017Tree)) finiteN24Shard0018Tree))

theorem finiteN24_parsed :
    (certifiedOldLeafCode 24).bind dyadicRouteBLeafTreeOfCode =
      some finiteN24Tree := by
  native_decide

theorem finiteN24_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 24 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN24_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN24Shard0000_checked finiteN24Shard0001_checked) finiteN24Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN24Shard0003_checked finiteN24Shard0004_checked) finiteN24Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN24Shard0006_checked finiteN24Shard0007_checked) finiteN24Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN24Shard0009_checked finiteN24Shard0010_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN24Shard0011_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN24Shard0012_checked finiteN24Shard0013_checked) finiteN24Shard0014_checked)) finiteN24Shard0015_checked)) finiteN24Shard0016_checked)) finiteN24Shard0017_checked)) finiteN24Shard0018_checked))

end BerryEsseen
