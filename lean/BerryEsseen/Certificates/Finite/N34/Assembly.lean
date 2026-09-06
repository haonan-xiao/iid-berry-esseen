import BerryEsseen.Certificates.Finite.N34.Shard0000
import BerryEsseen.Certificates.Finite.N34.Shard0001
import BerryEsseen.Certificates.Finite.N34.Shard0002
import BerryEsseen.Certificates.Finite.N34.Shard0003
import BerryEsseen.Certificates.Finite.N34.Shard0004
import BerryEsseen.Certificates.Finite.N34.Shard0005
import BerryEsseen.Certificates.Finite.N34.Shard0006
import BerryEsseen.Certificates.Finite.N34.Shard0007
import BerryEsseen.Certificates.Finite.N34.Shard0008
import BerryEsseen.Certificates.Finite.N34.Shard0009
import BerryEsseen.Certificates.Finite.N34.Shard0010
import BerryEsseen.Certificates.Finite.N34.Shard0011
import BerryEsseen.Certificates.Finite.N34.Shard0012
import BerryEsseen.Certificates.Finite.N34.Shard0013
import BerryEsseen.Certificates.Finite.N34.Shard0014
import BerryEsseen.Certificates.Finite.N34.Shard0015
import BerryEsseen.Certificates.Finite.N34.Shard0016
import BerryEsseen.Certificates.Finite.N34.Shard0017
import BerryEsseen.Certificates.Finite.N34.Shard0018
import BerryEsseen.Certificates.Finite.N34.Shard0019
import BerryEsseen.Certificates.Finite.N34.Shard0020
import BerryEsseen.Certificates.Finite.N34.Shard0021

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN34Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN34Shard0000Tree finiteN34Shard0001Tree) finiteN34Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN34Shard0003Tree finiteN34Shard0004Tree) finiteN34Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN34Shard0006Tree (.splitRho finiteN34Shard0007Tree finiteN34Shard0008Tree)) finiteN34Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN34Shard0010Tree finiteN34Shard0011Tree) finiteN34Shard0012Tree) (.splitRho (.splitZ (.splitRho finiteN34Shard0013Tree finiteN34Shard0014Tree) (.splitRho (.splitZ finiteN34Shard0015Tree finiteN34Shard0016Tree) finiteN34Shard0017Tree)) finiteN34Shard0018Tree)) finiteN34Shard0019Tree)) finiteN34Shard0020Tree)) finiteN34Shard0021Tree))

theorem finiteN34_parsed :
    (certifiedOldLeafCode 34).bind dyadicRouteBLeafTreeOfCode =
      some finiteN34Tree := by
  native_decide

theorem finiteN34_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 34 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN34_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN34Shard0000_checked finiteN34Shard0001_checked) finiteN34Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN34Shard0003_checked finiteN34Shard0004_checked) finiteN34Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN34Shard0006_checked (bound4395FiniteVerifySplitRho_true finiteN34Shard0007_checked finiteN34Shard0008_checked)) finiteN34Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN34Shard0010_checked finiteN34Shard0011_checked) finiteN34Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN34Shard0013_checked finiteN34Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN34Shard0015_checked finiteN34Shard0016_checked) finiteN34Shard0017_checked)) finiteN34Shard0018_checked)) finiteN34Shard0019_checked)) finiteN34Shard0020_checked)) finiteN34Shard0021_checked))

end BerryEsseen
