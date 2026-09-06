import BerryEsseen.Certificates.Finite.N70.Shard0000
import BerryEsseen.Certificates.Finite.N70.Shard0001
import BerryEsseen.Certificates.Finite.N70.Shard0002
import BerryEsseen.Certificates.Finite.N70.Shard0003
import BerryEsseen.Certificates.Finite.N70.Shard0004
import BerryEsseen.Certificates.Finite.N70.Shard0005
import BerryEsseen.Certificates.Finite.N70.Shard0006
import BerryEsseen.Certificates.Finite.N70.Shard0007
import BerryEsseen.Certificates.Finite.N70.Shard0008
import BerryEsseen.Certificates.Finite.N70.Shard0009
import BerryEsseen.Certificates.Finite.N70.Shard0010
import BerryEsseen.Certificates.Finite.N70.Shard0011
import BerryEsseen.Certificates.Finite.N70.Shard0012
import BerryEsseen.Certificates.Finite.N70.Shard0013
import BerryEsseen.Certificates.Finite.N70.Shard0014
import BerryEsseen.Certificates.Finite.N70.Shard0015
import BerryEsseen.Certificates.Finite.N70.Shard0016
import BerryEsseen.Certificates.Finite.N70.Shard0017
import BerryEsseen.Certificates.Finite.N70.Shard0018
import BerryEsseen.Certificates.Finite.N70.Shard0019
import BerryEsseen.Certificates.Finite.N70.Shard0020
import BerryEsseen.Certificates.Finite.N70.Shard0021
import BerryEsseen.Certificates.Finite.N70.Shard0022
import BerryEsseen.Certificates.Finite.N70.Shard0023
import BerryEsseen.Certificates.Finite.N70.Shard0024
import BerryEsseen.Certificates.Finite.N70.Shard0025
import BerryEsseen.Certificates.Finite.N70.Shard0026
import BerryEsseen.Certificates.Finite.N70.Shard0027
import BerryEsseen.Certificates.Finite.N70.Shard0028
import BerryEsseen.Certificates.Finite.N70.Shard0029
import BerryEsseen.Certificates.Finite.N70.Shard0030

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN70Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN70Shard0000Tree (.splitRho (.splitZ finiteN70Shard0001Tree finiteN70Shard0002Tree) finiteN70Shard0003Tree)) finiteN70Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN70Shard0005Tree (.splitRho (.splitZ finiteN70Shard0006Tree finiteN70Shard0007Tree) finiteN70Shard0008Tree)) finiteN70Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN70Shard0010Tree finiteN70Shard0011Tree) (.splitRho (.splitZ finiteN70Shard0012Tree finiteN70Shard0013Tree) finiteN70Shard0014Tree)) finiteN70Shard0015Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN70Shard0016Tree (.splitRho finiteN70Shard0017Tree finiteN70Shard0018Tree)) finiteN70Shard0019Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN70Shard0020Tree finiteN70Shard0021Tree) finiteN70Shard0022Tree) (.splitRho (.splitZ finiteN70Shard0023Tree (.splitRho finiteN70Shard0024Tree finiteN70Shard0025Tree)) finiteN70Shard0026Tree)) finiteN70Shard0027Tree)) finiteN70Shard0028Tree)) finiteN70Shard0029Tree)) finiteN70Shard0030Tree))

theorem finiteN70_parsed :
    (certifiedOldLeafCode 70).bind dyadicRouteBLeafTreeOfCode =
      some finiteN70Tree := by
  native_decide

theorem finiteN70_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 70 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN70_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN70Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN70Shard0001_checked finiteN70Shard0002_checked) finiteN70Shard0003_checked)) finiteN70Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN70Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN70Shard0006_checked finiteN70Shard0007_checked) finiteN70Shard0008_checked)) finiteN70Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN70Shard0010_checked finiteN70Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN70Shard0012_checked finiteN70Shard0013_checked) finiteN70Shard0014_checked)) finiteN70Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN70Shard0016_checked (bound4395FiniteVerifySplitRho_true finiteN70Shard0017_checked finiteN70Shard0018_checked)) finiteN70Shard0019_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN70Shard0020_checked finiteN70Shard0021_checked) finiteN70Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN70Shard0023_checked (bound4395FiniteVerifySplitRho_true finiteN70Shard0024_checked finiteN70Shard0025_checked)) finiteN70Shard0026_checked)) finiteN70Shard0027_checked)) finiteN70Shard0028_checked)) finiteN70Shard0029_checked)) finiteN70Shard0030_checked))

end BerryEsseen
