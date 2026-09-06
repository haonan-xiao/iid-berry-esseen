import BerryEsseen.Certificates.Finite.N28.Shard0000
import BerryEsseen.Certificates.Finite.N28.Shard0001
import BerryEsseen.Certificates.Finite.N28.Shard0002
import BerryEsseen.Certificates.Finite.N28.Shard0003
import BerryEsseen.Certificates.Finite.N28.Shard0004
import BerryEsseen.Certificates.Finite.N28.Shard0005
import BerryEsseen.Certificates.Finite.N28.Shard0006
import BerryEsseen.Certificates.Finite.N28.Shard0007
import BerryEsseen.Certificates.Finite.N28.Shard0008
import BerryEsseen.Certificates.Finite.N28.Shard0009
import BerryEsseen.Certificates.Finite.N28.Shard0010
import BerryEsseen.Certificates.Finite.N28.Shard0011
import BerryEsseen.Certificates.Finite.N28.Shard0012
import BerryEsseen.Certificates.Finite.N28.Shard0013
import BerryEsseen.Certificates.Finite.N28.Shard0014
import BerryEsseen.Certificates.Finite.N28.Shard0015
import BerryEsseen.Certificates.Finite.N28.Shard0016
import BerryEsseen.Certificates.Finite.N28.Shard0017
import BerryEsseen.Certificates.Finite.N28.Shard0018
import BerryEsseen.Certificates.Finite.N28.Shard0019
import BerryEsseen.Certificates.Finite.N28.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN28Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN28Shard0000Tree finiteN28Shard0001Tree) finiteN28Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN28Shard0003Tree finiteN28Shard0004Tree) finiteN28Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN28Shard0006Tree finiteN28Shard0007Tree) finiteN28Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN28Shard0009Tree finiteN28Shard0010Tree) finiteN28Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN28Shard0012Tree finiteN28Shard0013Tree) (.splitRho (.splitZ finiteN28Shard0014Tree finiteN28Shard0015Tree) finiteN28Shard0016Tree)) finiteN28Shard0017Tree)) finiteN28Shard0018Tree)) finiteN28Shard0019Tree)) finiteN28Shard0020Tree))

theorem finiteN28_parsed :
    (certifiedOldLeafCode 28).bind dyadicRouteBLeafTreeOfCode =
      some finiteN28Tree := by
  native_decide

theorem finiteN28_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 28 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN28_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN28Shard0000_checked finiteN28Shard0001_checked) finiteN28Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN28Shard0003_checked finiteN28Shard0004_checked) finiteN28Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN28Shard0006_checked finiteN28Shard0007_checked) finiteN28Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN28Shard0009_checked finiteN28Shard0010_checked) finiteN28Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN28Shard0012_checked finiteN28Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN28Shard0014_checked finiteN28Shard0015_checked) finiteN28Shard0016_checked)) finiteN28Shard0017_checked)) finiteN28Shard0018_checked)) finiteN28Shard0019_checked)) finiteN28Shard0020_checked))

end BerryEsseen
