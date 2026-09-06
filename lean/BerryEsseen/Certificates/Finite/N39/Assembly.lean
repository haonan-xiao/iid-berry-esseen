import BerryEsseen.Certificates.Finite.N39.Shard0000
import BerryEsseen.Certificates.Finite.N39.Shard0001
import BerryEsseen.Certificates.Finite.N39.Shard0002
import BerryEsseen.Certificates.Finite.N39.Shard0003
import BerryEsseen.Certificates.Finite.N39.Shard0004
import BerryEsseen.Certificates.Finite.N39.Shard0005
import BerryEsseen.Certificates.Finite.N39.Shard0006
import BerryEsseen.Certificates.Finite.N39.Shard0007
import BerryEsseen.Certificates.Finite.N39.Shard0008
import BerryEsseen.Certificates.Finite.N39.Shard0009
import BerryEsseen.Certificates.Finite.N39.Shard0010
import BerryEsseen.Certificates.Finite.N39.Shard0011
import BerryEsseen.Certificates.Finite.N39.Shard0012
import BerryEsseen.Certificates.Finite.N39.Shard0013
import BerryEsseen.Certificates.Finite.N39.Shard0014
import BerryEsseen.Certificates.Finite.N39.Shard0015
import BerryEsseen.Certificates.Finite.N39.Shard0016
import BerryEsseen.Certificates.Finite.N39.Shard0017
import BerryEsseen.Certificates.Finite.N39.Shard0018

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN39Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN39Shard0000Tree finiteN39Shard0001Tree) finiteN39Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN39Shard0003Tree finiteN39Shard0004Tree) finiteN39Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN39Shard0006Tree finiteN39Shard0007Tree) finiteN39Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN39Shard0009Tree finiteN39Shard0010Tree) finiteN39Shard0011Tree) (.splitRho (.splitZ finiteN39Shard0012Tree (.splitRho finiteN39Shard0013Tree finiteN39Shard0014Tree)) finiteN39Shard0015Tree)) finiteN39Shard0016Tree)) finiteN39Shard0017Tree)) finiteN39Shard0018Tree))

theorem finiteN39_parsed :
    (certifiedOldLeafCode 39).bind dyadicRouteBLeafTreeOfCode =
      some finiteN39Tree := by
  native_decide

theorem finiteN39_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 39 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN39_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN39Shard0000_checked finiteN39Shard0001_checked) finiteN39Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN39Shard0003_checked finiteN39Shard0004_checked) finiteN39Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN39Shard0006_checked finiteN39Shard0007_checked) finiteN39Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN39Shard0009_checked finiteN39Shard0010_checked) finiteN39Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN39Shard0012_checked (bound4395FiniteVerifySplitRho_true finiteN39Shard0013_checked finiteN39Shard0014_checked)) finiteN39Shard0015_checked)) finiteN39Shard0016_checked)) finiteN39Shard0017_checked)) finiteN39Shard0018_checked))

end BerryEsseen
