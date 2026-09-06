import BerryEsseen.Certificates.Finite.N40.Shard0000
import BerryEsseen.Certificates.Finite.N40.Shard0001
import BerryEsseen.Certificates.Finite.N40.Shard0002
import BerryEsseen.Certificates.Finite.N40.Shard0003
import BerryEsseen.Certificates.Finite.N40.Shard0004
import BerryEsseen.Certificates.Finite.N40.Shard0005
import BerryEsseen.Certificates.Finite.N40.Shard0006
import BerryEsseen.Certificates.Finite.N40.Shard0007
import BerryEsseen.Certificates.Finite.N40.Shard0008
import BerryEsseen.Certificates.Finite.N40.Shard0009
import BerryEsseen.Certificates.Finite.N40.Shard0010
import BerryEsseen.Certificates.Finite.N40.Shard0011
import BerryEsseen.Certificates.Finite.N40.Shard0012
import BerryEsseen.Certificates.Finite.N40.Shard0013
import BerryEsseen.Certificates.Finite.N40.Shard0014
import BerryEsseen.Certificates.Finite.N40.Shard0015
import BerryEsseen.Certificates.Finite.N40.Shard0016
import BerryEsseen.Certificates.Finite.N40.Shard0017
import BerryEsseen.Certificates.Finite.N40.Shard0018
import BerryEsseen.Certificates.Finite.N40.Shard0019
import BerryEsseen.Certificates.Finite.N40.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN40Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN40Shard0000Tree finiteN40Shard0001Tree) finiteN40Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN40Shard0003Tree finiteN40Shard0004Tree) finiteN40Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN40Shard0006Tree finiteN40Shard0007Tree) finiteN40Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN40Shard0009Tree finiteN40Shard0010Tree) finiteN40Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN40Shard0012Tree finiteN40Shard0013Tree) (.splitRho (.splitZ finiteN40Shard0014Tree finiteN40Shard0015Tree) finiteN40Shard0016Tree)) finiteN40Shard0017Tree)) finiteN40Shard0018Tree)) finiteN40Shard0019Tree)) finiteN40Shard0020Tree))

theorem finiteN40_parsed :
    (certifiedOldLeafCode 40).bind dyadicRouteBLeafTreeOfCode =
      some finiteN40Tree := by
  native_decide

theorem finiteN40_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 40 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN40_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN40Shard0000_checked finiteN40Shard0001_checked) finiteN40Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN40Shard0003_checked finiteN40Shard0004_checked) finiteN40Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN40Shard0006_checked finiteN40Shard0007_checked) finiteN40Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN40Shard0009_checked finiteN40Shard0010_checked) finiteN40Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN40Shard0012_checked finiteN40Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN40Shard0014_checked finiteN40Shard0015_checked) finiteN40Shard0016_checked)) finiteN40Shard0017_checked)) finiteN40Shard0018_checked)) finiteN40Shard0019_checked)) finiteN40Shard0020_checked))

end BerryEsseen
