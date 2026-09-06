import BerryEsseen.Certificates.Finite.N36.Shard0000
import BerryEsseen.Certificates.Finite.N36.Shard0001
import BerryEsseen.Certificates.Finite.N36.Shard0002
import BerryEsseen.Certificates.Finite.N36.Shard0003
import BerryEsseen.Certificates.Finite.N36.Shard0004
import BerryEsseen.Certificates.Finite.N36.Shard0005
import BerryEsseen.Certificates.Finite.N36.Shard0006
import BerryEsseen.Certificates.Finite.N36.Shard0007
import BerryEsseen.Certificates.Finite.N36.Shard0008
import BerryEsseen.Certificates.Finite.N36.Shard0009
import BerryEsseen.Certificates.Finite.N36.Shard0010
import BerryEsseen.Certificates.Finite.N36.Shard0011
import BerryEsseen.Certificates.Finite.N36.Shard0012
import BerryEsseen.Certificates.Finite.N36.Shard0013
import BerryEsseen.Certificates.Finite.N36.Shard0014
import BerryEsseen.Certificates.Finite.N36.Shard0015
import BerryEsseen.Certificates.Finite.N36.Shard0016
import BerryEsseen.Certificates.Finite.N36.Shard0017
import BerryEsseen.Certificates.Finite.N36.Shard0018
import BerryEsseen.Certificates.Finite.N36.Shard0019
import BerryEsseen.Certificates.Finite.N36.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN36Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN36Shard0000Tree finiteN36Shard0001Tree) finiteN36Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN36Shard0003Tree finiteN36Shard0004Tree) finiteN36Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN36Shard0006Tree finiteN36Shard0007Tree) finiteN36Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN36Shard0009Tree finiteN36Shard0010Tree) finiteN36Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN36Shard0012Tree finiteN36Shard0013Tree) (.splitRho (.splitZ finiteN36Shard0014Tree finiteN36Shard0015Tree) finiteN36Shard0016Tree)) finiteN36Shard0017Tree)) finiteN36Shard0018Tree)) finiteN36Shard0019Tree)) finiteN36Shard0020Tree))

theorem finiteN36_parsed :
    (certifiedOldLeafCode 36).bind dyadicRouteBLeafTreeOfCode =
      some finiteN36Tree := by
  native_decide

theorem finiteN36_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 36 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN36_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN36Shard0000_checked finiteN36Shard0001_checked) finiteN36Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN36Shard0003_checked finiteN36Shard0004_checked) finiteN36Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN36Shard0006_checked finiteN36Shard0007_checked) finiteN36Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN36Shard0009_checked finiteN36Shard0010_checked) finiteN36Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN36Shard0012_checked finiteN36Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN36Shard0014_checked finiteN36Shard0015_checked) finiteN36Shard0016_checked)) finiteN36Shard0017_checked)) finiteN36Shard0018_checked)) finiteN36Shard0019_checked)) finiteN36Shard0020_checked))

end BerryEsseen
