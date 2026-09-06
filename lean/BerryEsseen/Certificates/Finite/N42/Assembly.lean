import BerryEsseen.Certificates.Finite.N42.Shard0000
import BerryEsseen.Certificates.Finite.N42.Shard0001
import BerryEsseen.Certificates.Finite.N42.Shard0002
import BerryEsseen.Certificates.Finite.N42.Shard0003
import BerryEsseen.Certificates.Finite.N42.Shard0004
import BerryEsseen.Certificates.Finite.N42.Shard0005
import BerryEsseen.Certificates.Finite.N42.Shard0006
import BerryEsseen.Certificates.Finite.N42.Shard0007
import BerryEsseen.Certificates.Finite.N42.Shard0008
import BerryEsseen.Certificates.Finite.N42.Shard0009
import BerryEsseen.Certificates.Finite.N42.Shard0010
import BerryEsseen.Certificates.Finite.N42.Shard0011
import BerryEsseen.Certificates.Finite.N42.Shard0012
import BerryEsseen.Certificates.Finite.N42.Shard0013
import BerryEsseen.Certificates.Finite.N42.Shard0014
import BerryEsseen.Certificates.Finite.N42.Shard0015
import BerryEsseen.Certificates.Finite.N42.Shard0016
import BerryEsseen.Certificates.Finite.N42.Shard0017
import BerryEsseen.Certificates.Finite.N42.Shard0018
import BerryEsseen.Certificates.Finite.N42.Shard0019
import BerryEsseen.Certificates.Finite.N42.Shard0020
import BerryEsseen.Certificates.Finite.N42.Shard0021
import BerryEsseen.Certificates.Finite.N42.Shard0022

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN42Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN42Shard0000Tree finiteN42Shard0001Tree) finiteN42Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN42Shard0003Tree finiteN42Shard0004Tree) finiteN42Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN42Shard0006Tree (.splitRho finiteN42Shard0007Tree finiteN42Shard0008Tree)) finiteN42Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN42Shard0010Tree finiteN42Shard0011Tree) finiteN42Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN42Shard0013Tree finiteN42Shard0014Tree) finiteN42Shard0015Tree) (.splitRho (.splitZ finiteN42Shard0016Tree finiteN42Shard0017Tree) finiteN42Shard0018Tree)) finiteN42Shard0019Tree)) finiteN42Shard0020Tree)) finiteN42Shard0021Tree)) finiteN42Shard0022Tree))

theorem finiteN42_parsed :
    (certifiedOldLeafCode 42).bind dyadicRouteBLeafTreeOfCode =
      some finiteN42Tree := by
  native_decide

theorem finiteN42_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 42 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN42_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN42Shard0000_checked finiteN42Shard0001_checked) finiteN42Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN42Shard0003_checked finiteN42Shard0004_checked) finiteN42Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN42Shard0006_checked (bound4395FiniteVerifySplitRho_true finiteN42Shard0007_checked finiteN42Shard0008_checked)) finiteN42Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN42Shard0010_checked finiteN42Shard0011_checked) finiteN42Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN42Shard0013_checked finiteN42Shard0014_checked) finiteN42Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN42Shard0016_checked finiteN42Shard0017_checked) finiteN42Shard0018_checked)) finiteN42Shard0019_checked)) finiteN42Shard0020_checked)) finiteN42Shard0021_checked)) finiteN42Shard0022_checked))

end BerryEsseen
