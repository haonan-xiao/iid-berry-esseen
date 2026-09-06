import BerryEsseen.Certificates.Finite.N27.Shard0000
import BerryEsseen.Certificates.Finite.N27.Shard0001
import BerryEsseen.Certificates.Finite.N27.Shard0002
import BerryEsseen.Certificates.Finite.N27.Shard0003
import BerryEsseen.Certificates.Finite.N27.Shard0004
import BerryEsseen.Certificates.Finite.N27.Shard0005
import BerryEsseen.Certificates.Finite.N27.Shard0006
import BerryEsseen.Certificates.Finite.N27.Shard0007
import BerryEsseen.Certificates.Finite.N27.Shard0008
import BerryEsseen.Certificates.Finite.N27.Shard0009
import BerryEsseen.Certificates.Finite.N27.Shard0010
import BerryEsseen.Certificates.Finite.N27.Shard0011
import BerryEsseen.Certificates.Finite.N27.Shard0012
import BerryEsseen.Certificates.Finite.N27.Shard0013
import BerryEsseen.Certificates.Finite.N27.Shard0014
import BerryEsseen.Certificates.Finite.N27.Shard0015
import BerryEsseen.Certificates.Finite.N27.Shard0016
import BerryEsseen.Certificates.Finite.N27.Shard0017
import BerryEsseen.Certificates.Finite.N27.Shard0018
import BerryEsseen.Certificates.Finite.N27.Shard0019

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN27Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho finiteN27Shard0000Tree finiteN27Shard0001Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN27Shard0002Tree finiteN27Shard0003Tree) finiteN27Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN27Shard0005Tree finiteN27Shard0006Tree) finiteN27Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN27Shard0008Tree finiteN27Shard0009Tree) finiteN27Shard0010Tree) (.splitRho (.splitZ (.splitRho finiteN27Shard0011Tree finiteN27Shard0012Tree) (.splitRho (.splitZ finiteN27Shard0013Tree finiteN27Shard0014Tree) finiteN27Shard0015Tree)) finiteN27Shard0016Tree)) finiteN27Shard0017Tree)) finiteN27Shard0018Tree)) finiteN27Shard0019Tree))

theorem finiteN27_parsed :
    (certifiedOldLeafCode 27).bind dyadicRouteBLeafTreeOfCode =
      some finiteN27Tree := by
  native_decide

theorem finiteN27_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 27 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN27_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN27Shard0000_checked finiteN27Shard0001_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN27Shard0002_checked finiteN27Shard0003_checked) finiteN27Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN27Shard0005_checked finiteN27Shard0006_checked) finiteN27Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN27Shard0008_checked finiteN27Shard0009_checked) finiteN27Shard0010_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN27Shard0011_checked finiteN27Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN27Shard0013_checked finiteN27Shard0014_checked) finiteN27Shard0015_checked)) finiteN27Shard0016_checked)) finiteN27Shard0017_checked)) finiteN27Shard0018_checked)) finiteN27Shard0019_checked))

end BerryEsseen
