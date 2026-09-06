import BerryEsseen.Certificates.Finite.N43.Shard0000
import BerryEsseen.Certificates.Finite.N43.Shard0001
import BerryEsseen.Certificates.Finite.N43.Shard0002
import BerryEsseen.Certificates.Finite.N43.Shard0003
import BerryEsseen.Certificates.Finite.N43.Shard0004
import BerryEsseen.Certificates.Finite.N43.Shard0005
import BerryEsseen.Certificates.Finite.N43.Shard0006
import BerryEsseen.Certificates.Finite.N43.Shard0007
import BerryEsseen.Certificates.Finite.N43.Shard0008
import BerryEsseen.Certificates.Finite.N43.Shard0009
import BerryEsseen.Certificates.Finite.N43.Shard0010
import BerryEsseen.Certificates.Finite.N43.Shard0011
import BerryEsseen.Certificates.Finite.N43.Shard0012
import BerryEsseen.Certificates.Finite.N43.Shard0013
import BerryEsseen.Certificates.Finite.N43.Shard0014
import BerryEsseen.Certificates.Finite.N43.Shard0015
import BerryEsseen.Certificates.Finite.N43.Shard0016
import BerryEsseen.Certificates.Finite.N43.Shard0017
import BerryEsseen.Certificates.Finite.N43.Shard0018
import BerryEsseen.Certificates.Finite.N43.Shard0019
import BerryEsseen.Certificates.Finite.N43.Shard0020
import BerryEsseen.Certificates.Finite.N43.Shard0021

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN43Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN43Shard0000Tree finiteN43Shard0001Tree) finiteN43Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN43Shard0003Tree (.splitRho finiteN43Shard0004Tree finiteN43Shard0005Tree)) finiteN43Shard0006Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN43Shard0007Tree (.splitRho finiteN43Shard0008Tree finiteN43Shard0009Tree)) finiteN43Shard0010Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN43Shard0011Tree finiteN43Shard0012Tree) finiteN43Shard0013Tree) (.splitRho (.splitZ (.splitRho finiteN43Shard0014Tree finiteN43Shard0015Tree) (.splitRho finiteN43Shard0016Tree finiteN43Shard0017Tree)) finiteN43Shard0018Tree)) finiteN43Shard0019Tree)) finiteN43Shard0020Tree)) finiteN43Shard0021Tree))

theorem finiteN43_parsed :
    (certifiedOldLeafCode 43).bind dyadicRouteBLeafTreeOfCode =
      some finiteN43Tree := by
  native_decide

theorem finiteN43_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 43 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN43_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN43Shard0000_checked finiteN43Shard0001_checked) finiteN43Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN43Shard0003_checked (bound4395FiniteVerifySplitRho_true finiteN43Shard0004_checked finiteN43Shard0005_checked)) finiteN43Shard0006_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN43Shard0007_checked (bound4395FiniteVerifySplitRho_true finiteN43Shard0008_checked finiteN43Shard0009_checked)) finiteN43Shard0010_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN43Shard0011_checked finiteN43Shard0012_checked) finiteN43Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN43Shard0014_checked finiteN43Shard0015_checked) (bound4395FiniteVerifySplitRho_true finiteN43Shard0016_checked finiteN43Shard0017_checked)) finiteN43Shard0018_checked)) finiteN43Shard0019_checked)) finiteN43Shard0020_checked)) finiteN43Shard0021_checked))

end BerryEsseen
