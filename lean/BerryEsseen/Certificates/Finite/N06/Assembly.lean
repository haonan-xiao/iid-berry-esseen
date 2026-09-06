import BerryEsseen.Certificates.Finite.N06.Shard0000
import BerryEsseen.Certificates.Finite.N06.Shard0001
import BerryEsseen.Certificates.Finite.N06.Shard0002
import BerryEsseen.Certificates.Finite.N06.Shard0003
import BerryEsseen.Certificates.Finite.N06.Shard0004
import BerryEsseen.Certificates.Finite.N06.Shard0005
import BerryEsseen.Certificates.Finite.N06.Shard0006
import BerryEsseen.Certificates.Finite.N06.Shard0007
import BerryEsseen.Certificates.Finite.N06.Shard0008
import BerryEsseen.Certificates.Finite.N06.Shard0009
import BerryEsseen.Certificates.Finite.N06.Shard0010
import BerryEsseen.Certificates.Finite.N06.Shard0011
import BerryEsseen.Certificates.Finite.N06.Shard0012
import BerryEsseen.Certificates.Finite.N06.Shard0013
import BerryEsseen.Certificates.Finite.N06.Shard0014
import BerryEsseen.Certificates.Finite.N06.Shard0015
import BerryEsseen.Certificates.Finite.N06.Shard0016
import BerryEsseen.Certificates.Finite.N06.Shard0017
import BerryEsseen.Certificates.Finite.N06.Shard0018
import BerryEsseen.Certificates.Finite.N06.Shard0019

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN06Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN06Shard0000Tree (.splitRho (.splitZ finiteN06Shard0001Tree (.splitRho (.splitZ finiteN06Shard0002Tree (.splitRho (.splitZ (.splitRho (.splitZ finiteN06Shard0003Tree finiteN06Shard0004Tree) finiteN06Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN06Shard0006Tree finiteN06Shard0007Tree) finiteN06Shard0008Tree) (.splitRho (.splitZ finiteN06Shard0009Tree (.splitRho (.splitZ finiteN06Shard0010Tree finiteN06Shard0011Tree) finiteN06Shard0012Tree)) (.splitRho finiteN06Shard0013Tree finiteN06Shard0014Tree))) (.splitZ finiteN06Shard0015Tree finiteN06Shard0016Tree))) finiteN06Shard0017Tree)) finiteN06Shard0018Tree)) finiteN06Shard0019Tree))

theorem finiteN06_parsed :
    (certifiedOldLeafCode 6).bind dyadicRouteBLeafTreeOfCode =
      some finiteN06Tree := by
  native_decide

theorem finiteN06_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 6 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN06_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN06Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN06Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN06Shard0002_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN06Shard0003_checked finiteN06Shard0004_checked) finiteN06Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN06Shard0006_checked finiteN06Shard0007_checked) finiteN06Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN06Shard0009_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN06Shard0010_checked finiteN06Shard0011_checked) finiteN06Shard0012_checked)) (bound4395FiniteVerifySplitRho_true finiteN06Shard0013_checked finiteN06Shard0014_checked))) (bound4395FiniteVerifySplitZ_true finiteN06Shard0015_checked finiteN06Shard0016_checked))) finiteN06Shard0017_checked)) finiteN06Shard0018_checked)) finiteN06Shard0019_checked))

end BerryEsseen
