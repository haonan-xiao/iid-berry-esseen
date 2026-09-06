import BerryEsseen.Certificates.Finite.N44.Shard0000
import BerryEsseen.Certificates.Finite.N44.Shard0001
import BerryEsseen.Certificates.Finite.N44.Shard0002
import BerryEsseen.Certificates.Finite.N44.Shard0003
import BerryEsseen.Certificates.Finite.N44.Shard0004
import BerryEsseen.Certificates.Finite.N44.Shard0005
import BerryEsseen.Certificates.Finite.N44.Shard0006
import BerryEsseen.Certificates.Finite.N44.Shard0007
import BerryEsseen.Certificates.Finite.N44.Shard0008
import BerryEsseen.Certificates.Finite.N44.Shard0009
import BerryEsseen.Certificates.Finite.N44.Shard0010
import BerryEsseen.Certificates.Finite.N44.Shard0011
import BerryEsseen.Certificates.Finite.N44.Shard0012
import BerryEsseen.Certificates.Finite.N44.Shard0013
import BerryEsseen.Certificates.Finite.N44.Shard0014
import BerryEsseen.Certificates.Finite.N44.Shard0015
import BerryEsseen.Certificates.Finite.N44.Shard0016
import BerryEsseen.Certificates.Finite.N44.Shard0017
import BerryEsseen.Certificates.Finite.N44.Shard0018

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN44Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN44Shard0000Tree finiteN44Shard0001Tree) finiteN44Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN44Shard0003Tree finiteN44Shard0004Tree) finiteN44Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN44Shard0006Tree finiteN44Shard0007Tree) finiteN44Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN44Shard0009Tree finiteN44Shard0010Tree) finiteN44Shard0011Tree) (.splitRho (.splitZ finiteN44Shard0012Tree (.splitRho finiteN44Shard0013Tree finiteN44Shard0014Tree)) finiteN44Shard0015Tree)) finiteN44Shard0016Tree)) finiteN44Shard0017Tree)) finiteN44Shard0018Tree))

theorem finiteN44_parsed :
    (certifiedOldLeafCode 44).bind dyadicRouteBLeafTreeOfCode =
      some finiteN44Tree := by
  native_decide

theorem finiteN44_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 44 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN44_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN44Shard0000_checked finiteN44Shard0001_checked) finiteN44Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN44Shard0003_checked finiteN44Shard0004_checked) finiteN44Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN44Shard0006_checked finiteN44Shard0007_checked) finiteN44Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN44Shard0009_checked finiteN44Shard0010_checked) finiteN44Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN44Shard0012_checked (bound4395FiniteVerifySplitRho_true finiteN44Shard0013_checked finiteN44Shard0014_checked)) finiteN44Shard0015_checked)) finiteN44Shard0016_checked)) finiteN44Shard0017_checked)) finiteN44Shard0018_checked))

end BerryEsseen
