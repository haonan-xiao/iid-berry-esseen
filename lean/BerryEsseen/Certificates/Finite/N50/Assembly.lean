import BerryEsseen.Certificates.Finite.N50.Shard0000
import BerryEsseen.Certificates.Finite.N50.Shard0001
import BerryEsseen.Certificates.Finite.N50.Shard0002
import BerryEsseen.Certificates.Finite.N50.Shard0003
import BerryEsseen.Certificates.Finite.N50.Shard0004
import BerryEsseen.Certificates.Finite.N50.Shard0005
import BerryEsseen.Certificates.Finite.N50.Shard0006
import BerryEsseen.Certificates.Finite.N50.Shard0007
import BerryEsseen.Certificates.Finite.N50.Shard0008
import BerryEsseen.Certificates.Finite.N50.Shard0009
import BerryEsseen.Certificates.Finite.N50.Shard0010
import BerryEsseen.Certificates.Finite.N50.Shard0011
import BerryEsseen.Certificates.Finite.N50.Shard0012
import BerryEsseen.Certificates.Finite.N50.Shard0013
import BerryEsseen.Certificates.Finite.N50.Shard0014
import BerryEsseen.Certificates.Finite.N50.Shard0015
import BerryEsseen.Certificates.Finite.N50.Shard0016
import BerryEsseen.Certificates.Finite.N50.Shard0017
import BerryEsseen.Certificates.Finite.N50.Shard0018
import BerryEsseen.Certificates.Finite.N50.Shard0019
import BerryEsseen.Certificates.Finite.N50.Shard0020
import BerryEsseen.Certificates.Finite.N50.Shard0021

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN50Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN50Shard0000Tree finiteN50Shard0001Tree) finiteN50Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN50Shard0003Tree finiteN50Shard0004Tree) finiteN50Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN50Shard0006Tree (.splitRho finiteN50Shard0007Tree finiteN50Shard0008Tree)) finiteN50Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN50Shard0010Tree finiteN50Shard0011Tree) finiteN50Shard0012Tree) (.splitRho (.splitZ (.splitRho finiteN50Shard0013Tree finiteN50Shard0014Tree) (.splitRho (.splitZ finiteN50Shard0015Tree finiteN50Shard0016Tree) finiteN50Shard0017Tree)) finiteN50Shard0018Tree)) finiteN50Shard0019Tree)) finiteN50Shard0020Tree)) finiteN50Shard0021Tree))

theorem finiteN50_parsed :
    (certifiedOldLeafCode 50).bind dyadicRouteBLeafTreeOfCode =
      some finiteN50Tree := by
  native_decide

theorem finiteN50_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 50 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN50_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN50Shard0000_checked finiteN50Shard0001_checked) finiteN50Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN50Shard0003_checked finiteN50Shard0004_checked) finiteN50Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN50Shard0006_checked (bound4395FiniteVerifySplitRho_true finiteN50Shard0007_checked finiteN50Shard0008_checked)) finiteN50Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN50Shard0010_checked finiteN50Shard0011_checked) finiteN50Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN50Shard0013_checked finiteN50Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN50Shard0015_checked finiteN50Shard0016_checked) finiteN50Shard0017_checked)) finiteN50Shard0018_checked)) finiteN50Shard0019_checked)) finiteN50Shard0020_checked)) finiteN50Shard0021_checked))

end BerryEsseen
