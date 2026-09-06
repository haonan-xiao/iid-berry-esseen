import BerryEsseen.Certificates.Finite.N25.Shard0000
import BerryEsseen.Certificates.Finite.N25.Shard0001
import BerryEsseen.Certificates.Finite.N25.Shard0002
import BerryEsseen.Certificates.Finite.N25.Shard0003
import BerryEsseen.Certificates.Finite.N25.Shard0004
import BerryEsseen.Certificates.Finite.N25.Shard0005
import BerryEsseen.Certificates.Finite.N25.Shard0006
import BerryEsseen.Certificates.Finite.N25.Shard0007
import BerryEsseen.Certificates.Finite.N25.Shard0008
import BerryEsseen.Certificates.Finite.N25.Shard0009
import BerryEsseen.Certificates.Finite.N25.Shard0010
import BerryEsseen.Certificates.Finite.N25.Shard0011
import BerryEsseen.Certificates.Finite.N25.Shard0012
import BerryEsseen.Certificates.Finite.N25.Shard0013
import BerryEsseen.Certificates.Finite.N25.Shard0014
import BerryEsseen.Certificates.Finite.N25.Shard0015
import BerryEsseen.Certificates.Finite.N25.Shard0016
import BerryEsseen.Certificates.Finite.N25.Shard0017
import BerryEsseen.Certificates.Finite.N25.Shard0018
import BerryEsseen.Certificates.Finite.N25.Shard0019
import BerryEsseen.Certificates.Finite.N25.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN25Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN25Shard0000Tree finiteN25Shard0001Tree) finiteN25Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN25Shard0003Tree finiteN25Shard0004Tree) finiteN25Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN25Shard0006Tree finiteN25Shard0007Tree) finiteN25Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN25Shard0009Tree finiteN25Shard0010Tree) finiteN25Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN25Shard0012Tree finiteN25Shard0013Tree) (.splitRho (.splitZ finiteN25Shard0014Tree finiteN25Shard0015Tree) finiteN25Shard0016Tree)) finiteN25Shard0017Tree)) finiteN25Shard0018Tree)) finiteN25Shard0019Tree)) finiteN25Shard0020Tree))

theorem finiteN25_parsed :
    (certifiedOldLeafCode 25).bind dyadicRouteBLeafTreeOfCode =
      some finiteN25Tree := by
  native_decide

theorem finiteN25_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 25 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN25_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN25Shard0000_checked finiteN25Shard0001_checked) finiteN25Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN25Shard0003_checked finiteN25Shard0004_checked) finiteN25Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN25Shard0006_checked finiteN25Shard0007_checked) finiteN25Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN25Shard0009_checked finiteN25Shard0010_checked) finiteN25Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN25Shard0012_checked finiteN25Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN25Shard0014_checked finiteN25Shard0015_checked) finiteN25Shard0016_checked)) finiteN25Shard0017_checked)) finiteN25Shard0018_checked)) finiteN25Shard0019_checked)) finiteN25Shard0020_checked))

end BerryEsseen
