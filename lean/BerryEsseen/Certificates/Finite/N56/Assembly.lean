import BerryEsseen.Certificates.Finite.N56.Shard0000
import BerryEsseen.Certificates.Finite.N56.Shard0001
import BerryEsseen.Certificates.Finite.N56.Shard0002
import BerryEsseen.Certificates.Finite.N56.Shard0003
import BerryEsseen.Certificates.Finite.N56.Shard0004
import BerryEsseen.Certificates.Finite.N56.Shard0005
import BerryEsseen.Certificates.Finite.N56.Shard0006
import BerryEsseen.Certificates.Finite.N56.Shard0007
import BerryEsseen.Certificates.Finite.N56.Shard0008
import BerryEsseen.Certificates.Finite.N56.Shard0009
import BerryEsseen.Certificates.Finite.N56.Shard0010
import BerryEsseen.Certificates.Finite.N56.Shard0011
import BerryEsseen.Certificates.Finite.N56.Shard0012
import BerryEsseen.Certificates.Finite.N56.Shard0013
import BerryEsseen.Certificates.Finite.N56.Shard0014
import BerryEsseen.Certificates.Finite.N56.Shard0015
import BerryEsseen.Certificates.Finite.N56.Shard0016
import BerryEsseen.Certificates.Finite.N56.Shard0017
import BerryEsseen.Certificates.Finite.N56.Shard0018
import BerryEsseen.Certificates.Finite.N56.Shard0019
import BerryEsseen.Certificates.Finite.N56.Shard0020
import BerryEsseen.Certificates.Finite.N56.Shard0021
import BerryEsseen.Certificates.Finite.N56.Shard0022
import BerryEsseen.Certificates.Finite.N56.Shard0023

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN56Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN56Shard0000Tree (.splitRho finiteN56Shard0001Tree finiteN56Shard0002Tree)) finiteN56Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN56Shard0004Tree (.splitRho (.splitZ finiteN56Shard0005Tree finiteN56Shard0006Tree) finiteN56Shard0007Tree)) finiteN56Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN56Shard0009Tree (.splitRho finiteN56Shard0010Tree finiteN56Shard0011Tree)) finiteN56Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN56Shard0013Tree finiteN56Shard0014Tree) finiteN56Shard0015Tree) (.splitRho (.splitZ finiteN56Shard0016Tree (.splitRho (.splitZ finiteN56Shard0017Tree finiteN56Shard0018Tree) finiteN56Shard0019Tree)) finiteN56Shard0020Tree)) finiteN56Shard0021Tree)) finiteN56Shard0022Tree)) finiteN56Shard0023Tree))

theorem finiteN56_parsed :
    (certifiedOldLeafCode 56).bind dyadicRouteBLeafTreeOfCode =
      some finiteN56Tree := by
  native_decide

theorem finiteN56_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 56 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN56_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN56Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN56Shard0001_checked finiteN56Shard0002_checked)) finiteN56Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN56Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN56Shard0005_checked finiteN56Shard0006_checked) finiteN56Shard0007_checked)) finiteN56Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN56Shard0009_checked (bound4395FiniteVerifySplitRho_true finiteN56Shard0010_checked finiteN56Shard0011_checked)) finiteN56Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN56Shard0013_checked finiteN56Shard0014_checked) finiteN56Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN56Shard0016_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN56Shard0017_checked finiteN56Shard0018_checked) finiteN56Shard0019_checked)) finiteN56Shard0020_checked)) finiteN56Shard0021_checked)) finiteN56Shard0022_checked)) finiteN56Shard0023_checked))

end BerryEsseen
