import BerryEsseen.Certificates.Finite.N03.Shard0000
import BerryEsseen.Certificates.Finite.N03.Shard0001
import BerryEsseen.Certificates.Finite.N03.Shard0002
import BerryEsseen.Certificates.Finite.N03.Shard0003
import BerryEsseen.Certificates.Finite.N03.Shard0004
import BerryEsseen.Certificates.Finite.N03.Shard0005
import BerryEsseen.Certificates.Finite.N03.Shard0006
import BerryEsseen.Certificates.Finite.N03.Shard0007
import BerryEsseen.Certificates.Finite.N03.Shard0008
import BerryEsseen.Certificates.Finite.N03.Shard0009
import BerryEsseen.Certificates.Finite.N03.Shard0010
import BerryEsseen.Certificates.Finite.N03.Shard0011
import BerryEsseen.Certificates.Finite.N03.Shard0012
import BerryEsseen.Certificates.Finite.N03.Shard0013
import BerryEsseen.Certificates.Finite.N03.Shard0014
import BerryEsseen.Certificates.Finite.N03.Shard0015
import BerryEsseen.Certificates.Finite.N03.Shard0016
import BerryEsseen.Certificates.Finite.N03.Shard0017
import BerryEsseen.Certificates.Finite.N03.Shard0018
import BerryEsseen.Certificates.Finite.N03.Shard0019
import BerryEsseen.Certificates.Finite.N03.Shard0020
import BerryEsseen.Certificates.Finite.N03.Shard0021
import BerryEsseen.Certificates.Finite.N03.Shard0022
import BerryEsseen.Certificates.Finite.N03.Shard0023
import BerryEsseen.Certificates.Finite.N03.Shard0024
import BerryEsseen.Certificates.Finite.N03.Shard0025

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN03Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN03Shard0000Tree (.splitRho (.splitZ finiteN03Shard0001Tree (.splitRho (.splitZ finiteN03Shard0002Tree (.splitRho (.splitZ finiteN03Shard0003Tree (.splitRho (.splitZ finiteN03Shard0004Tree (.splitRho (.splitZ finiteN03Shard0005Tree (.splitRho (.splitZ finiteN03Shard0006Tree (.splitRho (.splitZ finiteN03Shard0007Tree finiteN03Shard0008Tree) finiteN03Shard0009Tree)) (.splitZ finiteN03Shard0010Tree (.splitRho finiteN03Shard0011Tree finiteN03Shard0012Tree)))) (.splitZ finiteN03Shard0013Tree (.splitRho (.splitZ finiteN03Shard0014Tree (.splitRho finiteN03Shard0015Tree finiteN03Shard0016Tree)) finiteN03Shard0017Tree)))) (.splitZ finiteN03Shard0018Tree (.splitRho (.splitZ finiteN03Shard0019Tree finiteN03Shard0020Tree) finiteN03Shard0021Tree)))) (.splitRho finiteN03Shard0022Tree finiteN03Shard0023Tree))) finiteN03Shard0024Tree)) finiteN03Shard0025Tree))

theorem finiteN03_parsed :
    (certifiedOldLeafCode 3).bind dyadicRouteBLeafTreeOfCode =
      some finiteN03Tree := by
  native_decide

theorem finiteN03_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 3 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN03_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN03Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN03Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN03Shard0002_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN03Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN03Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN03Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN03Shard0006_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN03Shard0007_checked finiteN03Shard0008_checked) finiteN03Shard0009_checked)) (bound4395FiniteVerifySplitZ_true finiteN03Shard0010_checked (bound4395FiniteVerifySplitRho_true finiteN03Shard0011_checked finiteN03Shard0012_checked)))) (bound4395FiniteVerifySplitZ_true finiteN03Shard0013_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN03Shard0014_checked (bound4395FiniteVerifySplitRho_true finiteN03Shard0015_checked finiteN03Shard0016_checked)) finiteN03Shard0017_checked)))) (bound4395FiniteVerifySplitZ_true finiteN03Shard0018_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN03Shard0019_checked finiteN03Shard0020_checked) finiteN03Shard0021_checked)))) (bound4395FiniteVerifySplitRho_true finiteN03Shard0022_checked finiteN03Shard0023_checked))) finiteN03Shard0024_checked)) finiteN03Shard0025_checked))

end BerryEsseen
