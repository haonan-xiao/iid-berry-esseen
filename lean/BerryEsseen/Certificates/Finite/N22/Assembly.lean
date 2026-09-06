import BerryEsseen.Certificates.Finite.N22.Shard0000
import BerryEsseen.Certificates.Finite.N22.Shard0001
import BerryEsseen.Certificates.Finite.N22.Shard0002
import BerryEsseen.Certificates.Finite.N22.Shard0003
import BerryEsseen.Certificates.Finite.N22.Shard0004
import BerryEsseen.Certificates.Finite.N22.Shard0005
import BerryEsseen.Certificates.Finite.N22.Shard0006
import BerryEsseen.Certificates.Finite.N22.Shard0007
import BerryEsseen.Certificates.Finite.N22.Shard0008
import BerryEsseen.Certificates.Finite.N22.Shard0009
import BerryEsseen.Certificates.Finite.N22.Shard0010
import BerryEsseen.Certificates.Finite.N22.Shard0011
import BerryEsseen.Certificates.Finite.N22.Shard0012
import BerryEsseen.Certificates.Finite.N22.Shard0013
import BerryEsseen.Certificates.Finite.N22.Shard0014
import BerryEsseen.Certificates.Finite.N22.Shard0015
import BerryEsseen.Certificates.Finite.N22.Shard0016
import BerryEsseen.Certificates.Finite.N22.Shard0017
import BerryEsseen.Certificates.Finite.N22.Shard0018
import BerryEsseen.Certificates.Finite.N22.Shard0019
import BerryEsseen.Certificates.Finite.N22.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN22Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN22Shard0000Tree finiteN22Shard0001Tree) finiteN22Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN22Shard0003Tree finiteN22Shard0004Tree) finiteN22Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN22Shard0006Tree finiteN22Shard0007Tree) finiteN22Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN22Shard0009Tree finiteN22Shard0010Tree) finiteN22Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN22Shard0012Tree finiteN22Shard0013Tree) (.splitRho (.splitZ finiteN22Shard0014Tree finiteN22Shard0015Tree) finiteN22Shard0016Tree)) finiteN22Shard0017Tree)) finiteN22Shard0018Tree)) finiteN22Shard0019Tree)) finiteN22Shard0020Tree))

theorem finiteN22_parsed :
    (certifiedOldLeafCode 22).bind dyadicRouteBLeafTreeOfCode =
      some finiteN22Tree := by
  native_decide

theorem finiteN22_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 22 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN22_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN22Shard0000_checked finiteN22Shard0001_checked) finiteN22Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN22Shard0003_checked finiteN22Shard0004_checked) finiteN22Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN22Shard0006_checked finiteN22Shard0007_checked) finiteN22Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN22Shard0009_checked finiteN22Shard0010_checked) finiteN22Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN22Shard0012_checked finiteN22Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN22Shard0014_checked finiteN22Shard0015_checked) finiteN22Shard0016_checked)) finiteN22Shard0017_checked)) finiteN22Shard0018_checked)) finiteN22Shard0019_checked)) finiteN22Shard0020_checked))

end BerryEsseen
