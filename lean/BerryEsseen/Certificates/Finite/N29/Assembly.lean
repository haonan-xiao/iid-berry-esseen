import BerryEsseen.Certificates.Finite.N29.Shard0000
import BerryEsseen.Certificates.Finite.N29.Shard0001
import BerryEsseen.Certificates.Finite.N29.Shard0002
import BerryEsseen.Certificates.Finite.N29.Shard0003
import BerryEsseen.Certificates.Finite.N29.Shard0004
import BerryEsseen.Certificates.Finite.N29.Shard0005
import BerryEsseen.Certificates.Finite.N29.Shard0006
import BerryEsseen.Certificates.Finite.N29.Shard0007
import BerryEsseen.Certificates.Finite.N29.Shard0008
import BerryEsseen.Certificates.Finite.N29.Shard0009
import BerryEsseen.Certificates.Finite.N29.Shard0010
import BerryEsseen.Certificates.Finite.N29.Shard0011
import BerryEsseen.Certificates.Finite.N29.Shard0012
import BerryEsseen.Certificates.Finite.N29.Shard0013
import BerryEsseen.Certificates.Finite.N29.Shard0014
import BerryEsseen.Certificates.Finite.N29.Shard0015
import BerryEsseen.Certificates.Finite.N29.Shard0016
import BerryEsseen.Certificates.Finite.N29.Shard0017
import BerryEsseen.Certificates.Finite.N29.Shard0018
import BerryEsseen.Certificates.Finite.N29.Shard0019
import BerryEsseen.Certificates.Finite.N29.Shard0020

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN29Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN29Shard0000Tree finiteN29Shard0001Tree) finiteN29Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN29Shard0003Tree finiteN29Shard0004Tree) finiteN29Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN29Shard0006Tree finiteN29Shard0007Tree) finiteN29Shard0008Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN29Shard0009Tree finiteN29Shard0010Tree) finiteN29Shard0011Tree) (.splitRho (.splitZ (.splitRho finiteN29Shard0012Tree finiteN29Shard0013Tree) (.splitRho (.splitZ finiteN29Shard0014Tree finiteN29Shard0015Tree) finiteN29Shard0016Tree)) finiteN29Shard0017Tree)) finiteN29Shard0018Tree)) finiteN29Shard0019Tree)) finiteN29Shard0020Tree))

theorem finiteN29_parsed :
    (certifiedOldLeafCode 29).bind dyadicRouteBLeafTreeOfCode =
      some finiteN29Tree := by
  native_decide

theorem finiteN29_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 29 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN29_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN29Shard0000_checked finiteN29Shard0001_checked) finiteN29Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN29Shard0003_checked finiteN29Shard0004_checked) finiteN29Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN29Shard0006_checked finiteN29Shard0007_checked) finiteN29Shard0008_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN29Shard0009_checked finiteN29Shard0010_checked) finiteN29Shard0011_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN29Shard0012_checked finiteN29Shard0013_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN29Shard0014_checked finiteN29Shard0015_checked) finiteN29Shard0016_checked)) finiteN29Shard0017_checked)) finiteN29Shard0018_checked)) finiteN29Shard0019_checked)) finiteN29Shard0020_checked))

end BerryEsseen
