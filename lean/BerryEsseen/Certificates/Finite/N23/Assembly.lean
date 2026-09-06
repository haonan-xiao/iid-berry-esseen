import BerryEsseen.Certificates.Finite.N23.Shard0000
import BerryEsseen.Certificates.Finite.N23.Shard0001
import BerryEsseen.Certificates.Finite.N23.Shard0002
import BerryEsseen.Certificates.Finite.N23.Shard0003
import BerryEsseen.Certificates.Finite.N23.Shard0004
import BerryEsseen.Certificates.Finite.N23.Shard0005
import BerryEsseen.Certificates.Finite.N23.Shard0006
import BerryEsseen.Certificates.Finite.N23.Shard0007
import BerryEsseen.Certificates.Finite.N23.Shard0008
import BerryEsseen.Certificates.Finite.N23.Shard0009
import BerryEsseen.Certificates.Finite.N23.Shard0010
import BerryEsseen.Certificates.Finite.N23.Shard0011
import BerryEsseen.Certificates.Finite.N23.Shard0012
import BerryEsseen.Certificates.Finite.N23.Shard0013
import BerryEsseen.Certificates.Finite.N23.Shard0014
import BerryEsseen.Certificates.Finite.N23.Shard0015
import BerryEsseen.Certificates.Finite.N23.Shard0016
import BerryEsseen.Certificates.Finite.N23.Shard0017
import BerryEsseen.Certificates.Finite.N23.Shard0018

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN23Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN23Shard0000Tree finiteN23Shard0001Tree) finiteN23Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN23Shard0003Tree finiteN23Shard0004Tree) finiteN23Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN23Shard0006Tree finiteN23Shard0007Tree) finiteN23Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN23Shard0009Tree finiteN23Shard0010Tree) finiteN23Shard0011Tree) (.splitRho (.splitZ finiteN23Shard0012Tree (.splitRho finiteN23Shard0013Tree finiteN23Shard0014Tree)) finiteN23Shard0015Tree)) finiteN23Shard0016Tree)) finiteN23Shard0017Tree)) finiteN23Shard0018Tree))

theorem finiteN23_parsed :
    (certifiedOldLeafCode 23).bind dyadicRouteBLeafTreeOfCode =
      some finiteN23Tree := by
  native_decide

theorem finiteN23_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 23 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN23_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN23Shard0000_checked finiteN23Shard0001_checked) finiteN23Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN23Shard0003_checked finiteN23Shard0004_checked) finiteN23Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN23Shard0006_checked finiteN23Shard0007_checked) finiteN23Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN23Shard0009_checked finiteN23Shard0010_checked) finiteN23Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN23Shard0012_checked (bound4395FiniteVerifySplitRho_true finiteN23Shard0013_checked finiteN23Shard0014_checked)) finiteN23Shard0015_checked)) finiteN23Shard0016_checked)) finiteN23Shard0017_checked)) finiteN23Shard0018_checked))

end BerryEsseen
