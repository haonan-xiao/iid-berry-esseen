import BerryEsseen.Certificates.Finite.N46.Shard0000
import BerryEsseen.Certificates.Finite.N46.Shard0001
import BerryEsseen.Certificates.Finite.N46.Shard0002
import BerryEsseen.Certificates.Finite.N46.Shard0003
import BerryEsseen.Certificates.Finite.N46.Shard0004
import BerryEsseen.Certificates.Finite.N46.Shard0005
import BerryEsseen.Certificates.Finite.N46.Shard0006
import BerryEsseen.Certificates.Finite.N46.Shard0007
import BerryEsseen.Certificates.Finite.N46.Shard0008
import BerryEsseen.Certificates.Finite.N46.Shard0009
import BerryEsseen.Certificates.Finite.N46.Shard0010
import BerryEsseen.Certificates.Finite.N46.Shard0011
import BerryEsseen.Certificates.Finite.N46.Shard0012
import BerryEsseen.Certificates.Finite.N46.Shard0013
import BerryEsseen.Certificates.Finite.N46.Shard0014
import BerryEsseen.Certificates.Finite.N46.Shard0015
import BerryEsseen.Certificates.Finite.N46.Shard0016
import BerryEsseen.Certificates.Finite.N46.Shard0017
import BerryEsseen.Certificates.Finite.N46.Shard0018
import BerryEsseen.Certificates.Finite.N46.Shard0019
import BerryEsseen.Certificates.Finite.N46.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN46Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN46Shard0000Tree finiteN46Shard0001Tree) finiteN46Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN46Shard0003Tree finiteN46Shard0004Tree) finiteN46Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN46Shard0006Tree finiteN46Shard0007Tree) finiteN46Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN46Shard0009Tree finiteN46Shard0010Tree) finiteN46Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN46Shard0012Tree finiteN46Shard0013Tree) (.splitRho (.splitZ finiteN46Shard0014Tree finiteN46Shard0015Tree) finiteN46Shard0016Tree)) finiteN46Shard0017Tree)) finiteN46Shard0018Tree)) finiteN46Shard0019Tree)) finiteN46Shard0020Tree))

theorem finiteN46_parsed :
    (certifiedOldLeafCode 46).bind dyadicRouteBLeafTreeOfCode =
      some finiteN46Tree := by
  native_decide

theorem finiteN46_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 46 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN46_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN46Shard0000_checked finiteN46Shard0001_checked) finiteN46Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN46Shard0003_checked finiteN46Shard0004_checked) finiteN46Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN46Shard0006_checked finiteN46Shard0007_checked) finiteN46Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN46Shard0009_checked finiteN46Shard0010_checked) finiteN46Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN46Shard0012_checked finiteN46Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN46Shard0014_checked finiteN46Shard0015_checked) finiteN46Shard0016_checked)) finiteN46Shard0017_checked)) finiteN46Shard0018_checked)) finiteN46Shard0019_checked)) finiteN46Shard0020_checked))

end BerryEsseen
