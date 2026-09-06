import BerryEsseen.Certificates.Finite.N58.Shard0000
import BerryEsseen.Certificates.Finite.N58.Shard0001
import BerryEsseen.Certificates.Finite.N58.Shard0002
import BerryEsseen.Certificates.Finite.N58.Shard0003
import BerryEsseen.Certificates.Finite.N58.Shard0004
import BerryEsseen.Certificates.Finite.N58.Shard0005
import BerryEsseen.Certificates.Finite.N58.Shard0006
import BerryEsseen.Certificates.Finite.N58.Shard0007
import BerryEsseen.Certificates.Finite.N58.Shard0008
import BerryEsseen.Certificates.Finite.N58.Shard0009
import BerryEsseen.Certificates.Finite.N58.Shard0010
import BerryEsseen.Certificates.Finite.N58.Shard0011
import BerryEsseen.Certificates.Finite.N58.Shard0012
import BerryEsseen.Certificates.Finite.N58.Shard0013
import BerryEsseen.Certificates.Finite.N58.Shard0014
import BerryEsseen.Certificates.Finite.N58.Shard0015
import BerryEsseen.Certificates.Finite.N58.Shard0016
import BerryEsseen.Certificates.Finite.N58.Shard0017
import BerryEsseen.Certificates.Finite.N58.Shard0018
import BerryEsseen.Certificates.Finite.N58.Shard0019
import BerryEsseen.Certificates.Finite.N58.Shard0020
import BerryEsseen.Certificates.Finite.N58.Shard0021
import BerryEsseen.Certificates.Finite.N58.Shard0022
import BerryEsseen.Certificates.Finite.N58.Shard0023
import BerryEsseen.Certificates.Finite.N58.Shard0024
import BerryEsseen.Certificates.Finite.N58.Shard0025
import BerryEsseen.Certificates.Finite.N58.Shard0026
import BerryEsseen.Certificates.Finite.N58.Shard0027

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN58Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN58Shard0000Tree (.splitRho finiteN58Shard0001Tree finiteN58Shard0002Tree)) finiteN58Shard0003Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN58Shard0004Tree (.splitRho (.splitZ finiteN58Shard0005Tree finiteN58Shard0006Tree) finiteN58Shard0007Tree)) finiteN58Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN58Shard0009Tree (.splitRho (.splitZ finiteN58Shard0010Tree finiteN58Shard0011Tree) finiteN58Shard0012Tree)) finiteN58Shard0013Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN58Shard0014Tree (.splitRho finiteN58Shard0015Tree finiteN58Shard0016Tree)) finiteN58Shard0017Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN58Shard0018Tree finiteN58Shard0019Tree) finiteN58Shard0020Tree) (.splitRho (.splitZ finiteN58Shard0021Tree finiteN58Shard0022Tree) finiteN58Shard0023Tree)) finiteN58Shard0024Tree)) finiteN58Shard0025Tree)) finiteN58Shard0026Tree)) finiteN58Shard0027Tree))

theorem finiteN58_parsed :
    (certifiedOldLeafCode 58).bind dyadicRouteBLeafTreeOfCode =
      some finiteN58Tree := by
  native_decide

theorem finiteN58_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 58 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN58_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN58Shard0000_checked (bound4395FiniteVerifySplitRho_true finiteN58Shard0001_checked finiteN58Shard0002_checked)) finiteN58Shard0003_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN58Shard0004_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN58Shard0005_checked finiteN58Shard0006_checked) finiteN58Shard0007_checked)) finiteN58Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN58Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN58Shard0010_checked finiteN58Shard0011_checked) finiteN58Shard0012_checked)) finiteN58Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN58Shard0014_checked (bound4395FiniteVerifySplitRho_true finiteN58Shard0015_checked finiteN58Shard0016_checked)) finiteN58Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN58Shard0018_checked finiteN58Shard0019_checked) finiteN58Shard0020_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN58Shard0021_checked finiteN58Shard0022_checked) finiteN58Shard0023_checked)) finiteN58Shard0024_checked)) finiteN58Shard0025_checked)) finiteN58Shard0026_checked)) finiteN58Shard0027_checked))

end BerryEsseen
