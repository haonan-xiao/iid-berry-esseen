import BerryEsseen.Certificates.Finite.N55.Shard0000
import BerryEsseen.Certificates.Finite.N55.Shard0001
import BerryEsseen.Certificates.Finite.N55.Shard0002
import BerryEsseen.Certificates.Finite.N55.Shard0003
import BerryEsseen.Certificates.Finite.N55.Shard0004
import BerryEsseen.Certificates.Finite.N55.Shard0005
import BerryEsseen.Certificates.Finite.N55.Shard0006
import BerryEsseen.Certificates.Finite.N55.Shard0007
import BerryEsseen.Certificates.Finite.N55.Shard0008
import BerryEsseen.Certificates.Finite.N55.Shard0009
import BerryEsseen.Certificates.Finite.N55.Shard0010
import BerryEsseen.Certificates.Finite.N55.Shard0011
import BerryEsseen.Certificates.Finite.N55.Shard0012
import BerryEsseen.Certificates.Finite.N55.Shard0013
import BerryEsseen.Certificates.Finite.N55.Shard0014
import BerryEsseen.Certificates.Finite.N55.Shard0015
import BerryEsseen.Certificates.Finite.N55.Shard0016
import BerryEsseen.Certificates.Finite.N55.Shard0017
import BerryEsseen.Certificates.Finite.N55.Shard0018
import BerryEsseen.Certificates.Finite.N55.Shard0019
import BerryEsseen.Certificates.Finite.N55.Shard0020
import BerryEsseen.Certificates.Finite.N55.Shard0021
import BerryEsseen.Certificates.Finite.N55.Shard0022
import BerryEsseen.Certificates.Finite.N55.Shard0023
import BerryEsseen.Certificates.Finite.N55.Shard0024
import BerryEsseen.Certificates.Finite.N55.Shard0025
import BerryEsseen.Certificates.Finite.N55.Shard0026
import BerryEsseen.Certificates.Finite.N55.Shard0027

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN55Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN55Shard0000Tree (.splitRho finiteN55Shard0001Tree finiteN55Shard0002Tree)) finiteN55Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN55Shard0004Tree (.splitRho (.splitZ finiteN55Shard0005Tree finiteN55Shard0006Tree) finiteN55Shard0007Tree)) finiteN55Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN55Shard0009Tree (.splitRho (.splitZ finiteN55Shard0010Tree finiteN55Shard0011Tree) finiteN55Shard0012Tree)) finiteN55Shard0013Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN55Shard0014Tree (.splitRho finiteN55Shard0015Tree finiteN55Shard0016Tree)) finiteN55Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN55Shard0018Tree finiteN55Shard0019Tree) finiteN55Shard0020Tree) (.splitRho (.splitZ finiteN55Shard0021Tree finiteN55Shard0022Tree) finiteN55Shard0023Tree)) finiteN55Shard0024Tree)) finiteN55Shard0025Tree)) finiteN55Shard0026Tree)) finiteN55Shard0027Tree))

theorem finiteN55_parsed :
    (certifiedOldLeafCode 55).bind dyadicRouteBLeafTreeOfCode =
      some finiteN55Tree := by
  native_decide

theorem finiteN55_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 55 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN55_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN55Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN55Shard0001_checked finiteN55Shard0002_checked)) finiteN55Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN55Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN55Shard0005_checked finiteN55Shard0006_checked) finiteN55Shard0007_checked)) finiteN55Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN55Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN55Shard0010_checked finiteN55Shard0011_checked) finiteN55Shard0012_checked)) finiteN55Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN55Shard0014_checked (bound4395FiniteVerifySplitRho_true finiteN55Shard0015_checked finiteN55Shard0016_checked)) finiteN55Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN55Shard0018_checked finiteN55Shard0019_checked) finiteN55Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN55Shard0021_checked finiteN55Shard0022_checked) finiteN55Shard0023_checked)) finiteN55Shard0024_checked)) finiteN55Shard0025_checked)) finiteN55Shard0026_checked)) finiteN55Shard0027_checked))

end BerryEsseen
