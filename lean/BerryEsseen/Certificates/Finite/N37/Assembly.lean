import BerryEsseen.Certificates.Finite.N37.Shard0000
import BerryEsseen.Certificates.Finite.N37.Shard0001
import BerryEsseen.Certificates.Finite.N37.Shard0002
import BerryEsseen.Certificates.Finite.N37.Shard0003
import BerryEsseen.Certificates.Finite.N37.Shard0004
import BerryEsseen.Certificates.Finite.N37.Shard0005
import BerryEsseen.Certificates.Finite.N37.Shard0006
import BerryEsseen.Certificates.Finite.N37.Shard0007
import BerryEsseen.Certificates.Finite.N37.Shard0008
import BerryEsseen.Certificates.Finite.N37.Shard0009
import BerryEsseen.Certificates.Finite.N37.Shard0010
import BerryEsseen.Certificates.Finite.N37.Shard0011
import BerryEsseen.Certificates.Finite.N37.Shard0012
import BerryEsseen.Certificates.Finite.N37.Shard0013
import BerryEsseen.Certificates.Finite.N37.Shard0014
import BerryEsseen.Certificates.Finite.N37.Shard0015
import BerryEsseen.Certificates.Finite.N37.Shard0016
import BerryEsseen.Certificates.Finite.N37.Shard0017
import BerryEsseen.Certificates.Finite.N37.Shard0018
import BerryEsseen.Certificates.Finite.N37.Shard0019
import BerryEsseen.Certificates.Finite.N37.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN37Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN37Shard0000Tree finiteN37Shard0001Tree) finiteN37Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN37Shard0003Tree finiteN37Shard0004Tree) finiteN37Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN37Shard0006Tree finiteN37Shard0007Tree) finiteN37Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN37Shard0009Tree finiteN37Shard0010Tree) finiteN37Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN37Shard0012Tree finiteN37Shard0013Tree) (.splitRho (.splitZ finiteN37Shard0014Tree finiteN37Shard0015Tree) finiteN37Shard0016Tree)) finiteN37Shard0017Tree)) finiteN37Shard0018Tree)) finiteN37Shard0019Tree)) finiteN37Shard0020Tree))

theorem finiteN37_parsed :
    (certifiedOldLeafCode 37).bind dyadicRouteBLeafTreeOfCode =
      some finiteN37Tree := by
  native_decide

theorem finiteN37_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 37 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN37_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN37Shard0000_checked finiteN37Shard0001_checked) finiteN37Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN37Shard0003_checked finiteN37Shard0004_checked) finiteN37Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN37Shard0006_checked finiteN37Shard0007_checked) finiteN37Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN37Shard0009_checked finiteN37Shard0010_checked) finiteN37Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN37Shard0012_checked finiteN37Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN37Shard0014_checked finiteN37Shard0015_checked) finiteN37Shard0016_checked)) finiteN37Shard0017_checked)) finiteN37Shard0018_checked)) finiteN37Shard0019_checked)) finiteN37Shard0020_checked))

end BerryEsseen
