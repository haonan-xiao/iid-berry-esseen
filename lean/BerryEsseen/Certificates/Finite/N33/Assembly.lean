import BerryEsseen.Certificates.Finite.N33.Shard0000
import BerryEsseen.Certificates.Finite.N33.Shard0001
import BerryEsseen.Certificates.Finite.N33.Shard0002
import BerryEsseen.Certificates.Finite.N33.Shard0003
import BerryEsseen.Certificates.Finite.N33.Shard0004
import BerryEsseen.Certificates.Finite.N33.Shard0005
import BerryEsseen.Certificates.Finite.N33.Shard0006
import BerryEsseen.Certificates.Finite.N33.Shard0007
import BerryEsseen.Certificates.Finite.N33.Shard0008
import BerryEsseen.Certificates.Finite.N33.Shard0009
import BerryEsseen.Certificates.Finite.N33.Shard0010
import BerryEsseen.Certificates.Finite.N33.Shard0011
import BerryEsseen.Certificates.Finite.N33.Shard0012
import BerryEsseen.Certificates.Finite.N33.Shard0013
import BerryEsseen.Certificates.Finite.N33.Shard0014
import BerryEsseen.Certificates.Finite.N33.Shard0015
import BerryEsseen.Certificates.Finite.N33.Shard0016
import BerryEsseen.Certificates.Finite.N33.Shard0017
import BerryEsseen.Certificates.Finite.N33.Shard0018
import BerryEsseen.Certificates.Finite.N33.Shard0019
import BerryEsseen.Certificates.Finite.N33.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN33Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN33Shard0000Tree finiteN33Shard0001Tree) finiteN33Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN33Shard0003Tree finiteN33Shard0004Tree) finiteN33Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN33Shard0006Tree finiteN33Shard0007Tree) finiteN33Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN33Shard0009Tree finiteN33Shard0010Tree) finiteN33Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN33Shard0012Tree finiteN33Shard0013Tree) (.splitRho (.splitZ finiteN33Shard0014Tree finiteN33Shard0015Tree) finiteN33Shard0016Tree)) finiteN33Shard0017Tree)) finiteN33Shard0018Tree)) finiteN33Shard0019Tree)) finiteN33Shard0020Tree))

theorem finiteN33_parsed :
    (certifiedOldLeafCode 33).bind dyadicRouteBLeafTreeOfCode =
      some finiteN33Tree := by
  native_decide

theorem finiteN33_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 33 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN33_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN33Shard0000_checked finiteN33Shard0001_checked) finiteN33Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN33Shard0003_checked finiteN33Shard0004_checked) finiteN33Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN33Shard0006_checked finiteN33Shard0007_checked) finiteN33Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN33Shard0009_checked finiteN33Shard0010_checked) finiteN33Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN33Shard0012_checked finiteN33Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN33Shard0014_checked finiteN33Shard0015_checked) finiteN33Shard0016_checked)) finiteN33Shard0017_checked)) finiteN33Shard0018_checked)) finiteN33Shard0019_checked)) finiteN33Shard0020_checked))

end BerryEsseen
