import BerryEsseen.Certificates.Finite.N08.Shard0000
import BerryEsseen.Certificates.Finite.N08.Shard0001
import BerryEsseen.Certificates.Finite.N08.Shard0002
import BerryEsseen.Certificates.Finite.N08.Shard0003
import BerryEsseen.Certificates.Finite.N08.Shard0004
import BerryEsseen.Certificates.Finite.N08.Shard0005
import BerryEsseen.Certificates.Finite.N08.Shard0006
import BerryEsseen.Certificates.Finite.N08.Shard0007
import BerryEsseen.Certificates.Finite.N08.Shard0008
import BerryEsseen.Certificates.Finite.N08.Shard0009
import BerryEsseen.Certificates.Finite.N08.Shard0010
import BerryEsseen.Certificates.Finite.N08.Shard0011
import BerryEsseen.Certificates.Finite.N08.Shard0012
import BerryEsseen.Certificates.Finite.N08.Shard0013

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN08Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN08Shard0000Tree (.splitRho (.splitZ finiteN08Shard0001Tree (.splitRho (.splitZ finiteN08Shard0002Tree (.splitRho (.splitZ (.splitRho finiteN08Shard0003Tree finiteN08Shard0004Tree) (.splitRho (.splitZ (.splitRho finiteN08Shard0005Tree finiteN08Shard0006Tree) (.splitRho (.splitZ finiteN08Shard0007Tree finiteN08Shard0008Tree) finiteN08Shard0009Tree)) finiteN08Shard0010Tree)) finiteN08Shard0011Tree)) finiteN08Shard0012Tree)) finiteN08Shard0013Tree))

theorem finiteN08_parsed :
    (certifiedOldLeafCode 8).bind dyadicRouteBLeafTreeOfCode =
      some finiteN08Tree := by
  native_decide

theorem finiteN08_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 8 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN08_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN08Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN08Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN08Shard0002_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN08Shard0003_checked finiteN08Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN08Shard0005_checked finiteN08Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN08Shard0007_checked finiteN08Shard0008_checked) finiteN08Shard0009_checked)) finiteN08Shard0010_checked)) finiteN08Shard0011_checked)) finiteN08Shard0012_checked)) finiteN08Shard0013_checked))

end BerryEsseen
