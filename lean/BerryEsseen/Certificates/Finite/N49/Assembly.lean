import BerryEsseen.Certificates.Finite.N49.Shard0000
import BerryEsseen.Certificates.Finite.N49.Shard0001
import BerryEsseen.Certificates.Finite.N49.Shard0002
import BerryEsseen.Certificates.Finite.N49.Shard0003
import BerryEsseen.Certificates.Finite.N49.Shard0004
import BerryEsseen.Certificates.Finite.N49.Shard0005
import BerryEsseen.Certificates.Finite.N49.Shard0006
import BerryEsseen.Certificates.Finite.N49.Shard0007
import BerryEsseen.Certificates.Finite.N49.Shard0008
import BerryEsseen.Certificates.Finite.N49.Shard0009
import BerryEsseen.Certificates.Finite.N49.Shard0010
import BerryEsseen.Certificates.Finite.N49.Shard0011
import BerryEsseen.Certificates.Finite.N49.Shard0012
import BerryEsseen.Certificates.Finite.N49.Shard0013
import BerryEsseen.Certificates.Finite.N49.Shard0014
import BerryEsseen.Certificates.Finite.N49.Shard0015
import BerryEsseen.Certificates.Finite.N49.Shard0016
import BerryEsseen.Certificates.Finite.N49.Shard0017
import BerryEsseen.Certificates.Finite.N49.Shard0018
import BerryEsseen.Certificates.Finite.N49.Shard0019
import BerryEsseen.Certificates.Finite.N49.Shard0020
import BerryEsseen.Certificates.Finite.N49.Shard0021

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN49Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN49Shard0000Tree finiteN49Shard0001Tree) finiteN49Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN49Shard0003Tree (.splitRho finiteN49Shard0004Tree finiteN49Shard0005Tree)) finiteN49Shard0006Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN49Shard0007Tree finiteN49Shard0008Tree) finiteN49Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN49Shard0010Tree finiteN49Shard0011Tree) finiteN49Shard0012Tree) (.splitRho (.splitZ (.splitRho finiteN49Shard0013Tree finiteN49Shard0014Tree) (.splitRho (.splitZ finiteN49Shard0015Tree finiteN49Shard0016Tree) finiteN49Shard0017Tree)) finiteN49Shard0018Tree)) finiteN49Shard0019Tree)) finiteN49Shard0020Tree)) finiteN49Shard0021Tree))

theorem finiteN49_parsed :
    (certifiedOldLeafCode 49).bind dyadicRouteBLeafTreeOfCode =
      some finiteN49Tree := by
  native_decide

theorem finiteN49_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 49 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN49_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN49Shard0000_checked finiteN49Shard0001_checked) finiteN49Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN49Shard0003_checked (bound4395FiniteVerifySplitRho_true finiteN49Shard0004_checked finiteN49Shard0005_checked)) finiteN49Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN49Shard0007_checked finiteN49Shard0008_checked) finiteN49Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN49Shard0010_checked finiteN49Shard0011_checked) finiteN49Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN49Shard0013_checked finiteN49Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN49Shard0015_checked finiteN49Shard0016_checked) finiteN49Shard0017_checked)) finiteN49Shard0018_checked)) finiteN49Shard0019_checked)) finiteN49Shard0020_checked)) finiteN49Shard0021_checked))

end BerryEsseen
