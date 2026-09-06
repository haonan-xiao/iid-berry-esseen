import BerryEsseen.Certificates.Finite.N45.Shard0000
import BerryEsseen.Certificates.Finite.N45.Shard0001
import BerryEsseen.Certificates.Finite.N45.Shard0002
import BerryEsseen.Certificates.Finite.N45.Shard0003
import BerryEsseen.Certificates.Finite.N45.Shard0004
import BerryEsseen.Certificates.Finite.N45.Shard0005
import BerryEsseen.Certificates.Finite.N45.Shard0006
import BerryEsseen.Certificates.Finite.N45.Shard0007
import BerryEsseen.Certificates.Finite.N45.Shard0008
import BerryEsseen.Certificates.Finite.N45.Shard0009
import BerryEsseen.Certificates.Finite.N45.Shard0010
import BerryEsseen.Certificates.Finite.N45.Shard0011
import BerryEsseen.Certificates.Finite.N45.Shard0012
import BerryEsseen.Certificates.Finite.N45.Shard0013
import BerryEsseen.Certificates.Finite.N45.Shard0014
import BerryEsseen.Certificates.Finite.N45.Shard0015
import BerryEsseen.Certificates.Finite.N45.Shard0016
import BerryEsseen.Certificates.Finite.N45.Shard0017
import BerryEsseen.Certificates.Finite.N45.Shard0018
import BerryEsseen.Certificates.Finite.N45.Shard0019
import BerryEsseen.Certificates.Finite.N45.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN45Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN45Shard0000Tree finiteN45Shard0001Tree) finiteN45Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN45Shard0003Tree finiteN45Shard0004Tree) finiteN45Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN45Shard0006Tree finiteN45Shard0007Tree) finiteN45Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN45Shard0009Tree finiteN45Shard0010Tree) finiteN45Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN45Shard0012Tree finiteN45Shard0013Tree) (.splitRho (.splitZ finiteN45Shard0014Tree finiteN45Shard0015Tree) finiteN45Shard0016Tree)) finiteN45Shard0017Tree)) finiteN45Shard0018Tree)) finiteN45Shard0019Tree)) finiteN45Shard0020Tree))

theorem finiteN45_parsed :
    (certifiedOldLeafCode 45).bind dyadicRouteBLeafTreeOfCode =
      some finiteN45Tree := by
  native_decide

theorem finiteN45_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 45 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN45_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN45Shard0000_checked finiteN45Shard0001_checked) finiteN45Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN45Shard0003_checked finiteN45Shard0004_checked) finiteN45Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN45Shard0006_checked finiteN45Shard0007_checked) finiteN45Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN45Shard0009_checked finiteN45Shard0010_checked) finiteN45Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN45Shard0012_checked finiteN45Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN45Shard0014_checked finiteN45Shard0015_checked) finiteN45Shard0016_checked)) finiteN45Shard0017_checked)) finiteN45Shard0018_checked)) finiteN45Shard0019_checked)) finiteN45Shard0020_checked))

end BerryEsseen
