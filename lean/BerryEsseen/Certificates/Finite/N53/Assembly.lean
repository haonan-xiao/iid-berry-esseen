import BerryEsseen.Certificates.Finite.N53.Shard0000
import BerryEsseen.Certificates.Finite.N53.Shard0001
import BerryEsseen.Certificates.Finite.N53.Shard0002
import BerryEsseen.Certificates.Finite.N53.Shard0003
import BerryEsseen.Certificates.Finite.N53.Shard0004
import BerryEsseen.Certificates.Finite.N53.Shard0005
import BerryEsseen.Certificates.Finite.N53.Shard0006
import BerryEsseen.Certificates.Finite.N53.Shard0007
import BerryEsseen.Certificates.Finite.N53.Shard0008
import BerryEsseen.Certificates.Finite.N53.Shard0009
import BerryEsseen.Certificates.Finite.N53.Shard0010
import BerryEsseen.Certificates.Finite.N53.Shard0011
import BerryEsseen.Certificates.Finite.N53.Shard0012
import BerryEsseen.Certificates.Finite.N53.Shard0013
import BerryEsseen.Certificates.Finite.N53.Shard0014
import BerryEsseen.Certificates.Finite.N53.Shard0015
import BerryEsseen.Certificates.Finite.N53.Shard0016
import BerryEsseen.Certificates.Finite.N53.Shard0017
import BerryEsseen.Certificates.Finite.N53.Shard0018
import BerryEsseen.Certificates.Finite.N53.Shard0019
import BerryEsseen.Certificates.Finite.N53.Shard0020
import BerryEsseen.Certificates.Finite.N53.Shard0021

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN53Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN53Shard0000Tree finiteN53Shard0001Tree) finiteN53Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN53Shard0003Tree finiteN53Shard0004Tree) finiteN53Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN53Shard0006Tree (.splitRho finiteN53Shard0007Tree finiteN53Shard0008Tree)) finiteN53Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN53Shard0010Tree finiteN53Shard0011Tree) finiteN53Shard0012Tree) (.splitRho (.splitZ (.splitRho finiteN53Shard0013Tree finiteN53Shard0014Tree) (.splitRho (.splitZ finiteN53Shard0015Tree finiteN53Shard0016Tree) finiteN53Shard0017Tree)) finiteN53Shard0018Tree)) finiteN53Shard0019Tree)) finiteN53Shard0020Tree)) finiteN53Shard0021Tree))

theorem finiteN53_parsed :
    (certifiedOldLeafCode 53).bind dyadicRouteBLeafTreeOfCode =
      some finiteN53Tree := by
  native_decide

theorem finiteN53_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 53 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN53_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN53Shard0000_checked finiteN53Shard0001_checked) finiteN53Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN53Shard0003_checked finiteN53Shard0004_checked) finiteN53Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN53Shard0006_checked (bound4395FiniteVerifySplitRho_true finiteN53Shard0007_checked finiteN53Shard0008_checked)) finiteN53Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN53Shard0010_checked finiteN53Shard0011_checked) finiteN53Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN53Shard0013_checked finiteN53Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN53Shard0015_checked finiteN53Shard0016_checked) finiteN53Shard0017_checked)) finiteN53Shard0018_checked)) finiteN53Shard0019_checked)) finiteN53Shard0020_checked)) finiteN53Shard0021_checked))

end BerryEsseen
