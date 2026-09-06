import BerryEsseen.Certificates.Finite.N52.Shard0000
import BerryEsseen.Certificates.Finite.N52.Shard0001
import BerryEsseen.Certificates.Finite.N52.Shard0002
import BerryEsseen.Certificates.Finite.N52.Shard0003
import BerryEsseen.Certificates.Finite.N52.Shard0004
import BerryEsseen.Certificates.Finite.N52.Shard0005
import BerryEsseen.Certificates.Finite.N52.Shard0006
import BerryEsseen.Certificates.Finite.N52.Shard0007
import BerryEsseen.Certificates.Finite.N52.Shard0008
import BerryEsseen.Certificates.Finite.N52.Shard0009
import BerryEsseen.Certificates.Finite.N52.Shard0010
import BerryEsseen.Certificates.Finite.N52.Shard0011
import BerryEsseen.Certificates.Finite.N52.Shard0012
import BerryEsseen.Certificates.Finite.N52.Shard0013
import BerryEsseen.Certificates.Finite.N52.Shard0014
import BerryEsseen.Certificates.Finite.N52.Shard0015
import BerryEsseen.Certificates.Finite.N52.Shard0016
import BerryEsseen.Certificates.Finite.N52.Shard0017
import BerryEsseen.Certificates.Finite.N52.Shard0018
import BerryEsseen.Certificates.Finite.N52.Shard0019

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN52Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN52Shard0000Tree finiteN52Shard0001Tree) finiteN52Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN52Shard0003Tree finiteN52Shard0004Tree) finiteN52Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN52Shard0006Tree finiteN52Shard0007Tree) finiteN52Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN52Shard0009Tree finiteN52Shard0010Tree) finiteN52Shard0011Tree) (.splitRho (.splitZ finiteN52Shard0012Tree (.splitRho (.splitZ finiteN52Shard0013Tree finiteN52Shard0014Tree) finiteN52Shard0015Tree)) finiteN52Shard0016Tree)) finiteN52Shard0017Tree)) finiteN52Shard0018Tree)) finiteN52Shard0019Tree))

theorem finiteN52_parsed :
    (certifiedOldLeafCode 52).bind dyadicRouteBLeafTreeOfCode =
      some finiteN52Tree := by
  native_decide

theorem finiteN52_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 52 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN52_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN52Shard0000_checked finiteN52Shard0001_checked) finiteN52Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN52Shard0003_checked finiteN52Shard0004_checked) finiteN52Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN52Shard0006_checked finiteN52Shard0007_checked) finiteN52Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN52Shard0009_checked finiteN52Shard0010_checked) finiteN52Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN52Shard0012_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN52Shard0013_checked finiteN52Shard0014_checked) finiteN52Shard0015_checked)) finiteN52Shard0016_checked)) finiteN52Shard0017_checked)) finiteN52Shard0018_checked)) finiteN52Shard0019_checked))

end BerryEsseen
