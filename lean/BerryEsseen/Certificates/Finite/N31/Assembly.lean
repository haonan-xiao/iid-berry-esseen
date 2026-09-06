import BerryEsseen.Certificates.Finite.N31.Shard0000
import BerryEsseen.Certificates.Finite.N31.Shard0001
import BerryEsseen.Certificates.Finite.N31.Shard0002
import BerryEsseen.Certificates.Finite.N31.Shard0003
import BerryEsseen.Certificates.Finite.N31.Shard0004
import BerryEsseen.Certificates.Finite.N31.Shard0005
import BerryEsseen.Certificates.Finite.N31.Shard0006
import BerryEsseen.Certificates.Finite.N31.Shard0007
import BerryEsseen.Certificates.Finite.N31.Shard0008
import BerryEsseen.Certificates.Finite.N31.Shard0009
import BerryEsseen.Certificates.Finite.N31.Shard0010
import BerryEsseen.Certificates.Finite.N31.Shard0011
import BerryEsseen.Certificates.Finite.N31.Shard0012
import BerryEsseen.Certificates.Finite.N31.Shard0013
import BerryEsseen.Certificates.Finite.N31.Shard0014
import BerryEsseen.Certificates.Finite.N31.Shard0015
import BerryEsseen.Certificates.Finite.N31.Shard0016
import BerryEsseen.Certificates.Finite.N31.Shard0017
import BerryEsseen.Certificates.Finite.N31.Shard0018
import BerryEsseen.Certificates.Finite.N31.Shard0019
import BerryEsseen.Certificates.Finite.N31.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN31Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN31Shard0000Tree finiteN31Shard0001Tree) finiteN31Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN31Shard0003Tree finiteN31Shard0004Tree) finiteN31Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN31Shard0006Tree finiteN31Shard0007Tree) finiteN31Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN31Shard0009Tree finiteN31Shard0010Tree) finiteN31Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN31Shard0012Tree finiteN31Shard0013Tree) (.splitRho (.splitZ finiteN31Shard0014Tree finiteN31Shard0015Tree) finiteN31Shard0016Tree)) finiteN31Shard0017Tree)) finiteN31Shard0018Tree)) finiteN31Shard0019Tree)) finiteN31Shard0020Tree))

theorem finiteN31_parsed :
    (certifiedOldLeafCode 31).bind dyadicRouteBLeafTreeOfCode =
      some finiteN31Tree := by
  native_decide

theorem finiteN31_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 31 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN31_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN31Shard0000_checked finiteN31Shard0001_checked) finiteN31Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN31Shard0003_checked finiteN31Shard0004_checked) finiteN31Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN31Shard0006_checked finiteN31Shard0007_checked) finiteN31Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN31Shard0009_checked finiteN31Shard0010_checked) finiteN31Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN31Shard0012_checked finiteN31Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN31Shard0014_checked finiteN31Shard0015_checked) finiteN31Shard0016_checked)) finiteN31Shard0017_checked)) finiteN31Shard0018_checked)) finiteN31Shard0019_checked)) finiteN31Shard0020_checked))

end BerryEsseen
