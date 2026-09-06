import BerryEsseen.Certificates.Finite.N62.Shard0000
import BerryEsseen.Certificates.Finite.N62.Shard0001
import BerryEsseen.Certificates.Finite.N62.Shard0002
import BerryEsseen.Certificates.Finite.N62.Shard0003
import BerryEsseen.Certificates.Finite.N62.Shard0004
import BerryEsseen.Certificates.Finite.N62.Shard0005
import BerryEsseen.Certificates.Finite.N62.Shard0006
import BerryEsseen.Certificates.Finite.N62.Shard0007
import BerryEsseen.Certificates.Finite.N62.Shard0008
import BerryEsseen.Certificates.Finite.N62.Shard0009
import BerryEsseen.Certificates.Finite.N62.Shard0010
import BerryEsseen.Certificates.Finite.N62.Shard0011
import BerryEsseen.Certificates.Finite.N62.Shard0012
import BerryEsseen.Certificates.Finite.N62.Shard0013
import BerryEsseen.Certificates.Finite.N62.Shard0014
import BerryEsseen.Certificates.Finite.N62.Shard0015
import BerryEsseen.Certificates.Finite.N62.Shard0016
import BerryEsseen.Certificates.Finite.N62.Shard0017
import BerryEsseen.Certificates.Finite.N62.Shard0018
import BerryEsseen.Certificates.Finite.N62.Shard0019
import BerryEsseen.Certificates.Finite.N62.Shard0020
import BerryEsseen.Certificates.Finite.N62.Shard0021
import BerryEsseen.Certificates.Finite.N62.Shard0022
import BerryEsseen.Certificates.Finite.N62.Shard0023
import BerryEsseen.Certificates.Finite.N62.Shard0024

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN62Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN62Shard0000Tree finiteN62Shard0001Tree) finiteN62Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN62Shard0003Tree (.splitRho (.splitZ finiteN62Shard0004Tree finiteN62Shard0005Tree) finiteN62Shard0006Tree)) finiteN62Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN62Shard0008Tree (.splitRho (.splitZ finiteN62Shard0009Tree finiteN62Shard0010Tree) finiteN62Shard0011Tree)) finiteN62Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN62Shard0013Tree finiteN62Shard0014Tree) finiteN62Shard0015Tree) (.splitRho (.splitZ (.splitRho finiteN62Shard0016Tree finiteN62Shard0017Tree) (.splitRho (.splitZ finiteN62Shard0018Tree finiteN62Shard0019Tree) finiteN62Shard0020Tree)) finiteN62Shard0021Tree)) finiteN62Shard0022Tree)) finiteN62Shard0023Tree)) finiteN62Shard0024Tree))

theorem finiteN62_parsed :
    (certifiedOldLeafCode 62).bind dyadicRouteBLeafTreeOfCode =
      some finiteN62Tree := by
  native_decide

theorem finiteN62_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 62 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN62_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN62Shard0000_checked finiteN62Shard0001_checked) finiteN62Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN62Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN62Shard0004_checked finiteN62Shard0005_checked) finiteN62Shard0006_checked)) finiteN62Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN62Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN62Shard0009_checked finiteN62Shard0010_checked) finiteN62Shard0011_checked)) finiteN62Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN62Shard0013_checked finiteN62Shard0014_checked) finiteN62Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN62Shard0016_checked finiteN62Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN62Shard0018_checked finiteN62Shard0019_checked) finiteN62Shard0020_checked)) finiteN62Shard0021_checked)) finiteN62Shard0022_checked)) finiteN62Shard0023_checked)) finiteN62Shard0024_checked))

end BerryEsseen
