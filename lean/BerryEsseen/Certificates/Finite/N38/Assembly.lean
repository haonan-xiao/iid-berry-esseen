import BerryEsseen.Certificates.Finite.N38.Shard0000
import BerryEsseen.Certificates.Finite.N38.Shard0001
import BerryEsseen.Certificates.Finite.N38.Shard0002
import BerryEsseen.Certificates.Finite.N38.Shard0003
import BerryEsseen.Certificates.Finite.N38.Shard0004
import BerryEsseen.Certificates.Finite.N38.Shard0005
import BerryEsseen.Certificates.Finite.N38.Shard0006
import BerryEsseen.Certificates.Finite.N38.Shard0007
import BerryEsseen.Certificates.Finite.N38.Shard0008
import BerryEsseen.Certificates.Finite.N38.Shard0009
import BerryEsseen.Certificates.Finite.N38.Shard0010
import BerryEsseen.Certificates.Finite.N38.Shard0011
import BerryEsseen.Certificates.Finite.N38.Shard0012
import BerryEsseen.Certificates.Finite.N38.Shard0013
import BerryEsseen.Certificates.Finite.N38.Shard0014
import BerryEsseen.Certificates.Finite.N38.Shard0015
import BerryEsseen.Certificates.Finite.N38.Shard0016
import BerryEsseen.Certificates.Finite.N38.Shard0017
import BerryEsseen.Certificates.Finite.N38.Shard0018
import BerryEsseen.Certificates.Finite.N38.Shard0019
import BerryEsseen.Certificates.Finite.N38.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN38Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN38Shard0000Tree finiteN38Shard0001Tree) finiteN38Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN38Shard0003Tree finiteN38Shard0004Tree) finiteN38Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN38Shard0006Tree finiteN38Shard0007Tree) finiteN38Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN38Shard0009Tree finiteN38Shard0010Tree) finiteN38Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN38Shard0012Tree finiteN38Shard0013Tree) (.splitRho (.splitZ finiteN38Shard0014Tree finiteN38Shard0015Tree) finiteN38Shard0016Tree)) finiteN38Shard0017Tree)) finiteN38Shard0018Tree)) finiteN38Shard0019Tree)) finiteN38Shard0020Tree))

theorem finiteN38_parsed :
    (certifiedOldLeafCode 38).bind dyadicRouteBLeafTreeOfCode =
      some finiteN38Tree := by
  native_decide

theorem finiteN38_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 38 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN38_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN38Shard0000_checked finiteN38Shard0001_checked) finiteN38Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN38Shard0003_checked finiteN38Shard0004_checked) finiteN38Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN38Shard0006_checked finiteN38Shard0007_checked) finiteN38Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN38Shard0009_checked finiteN38Shard0010_checked) finiteN38Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN38Shard0012_checked finiteN38Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN38Shard0014_checked finiteN38Shard0015_checked) finiteN38Shard0016_checked)) finiteN38Shard0017_checked)) finiteN38Shard0018_checked)) finiteN38Shard0019_checked)) finiteN38Shard0020_checked))

end BerryEsseen
