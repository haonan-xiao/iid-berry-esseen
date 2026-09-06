import BerryEsseen.Certificates.Finite.N30.Shard0000
import BerryEsseen.Certificates.Finite.N30.Shard0001
import BerryEsseen.Certificates.Finite.N30.Shard0002
import BerryEsseen.Certificates.Finite.N30.Shard0003
import BerryEsseen.Certificates.Finite.N30.Shard0004
import BerryEsseen.Certificates.Finite.N30.Shard0005
import BerryEsseen.Certificates.Finite.N30.Shard0006
import BerryEsseen.Certificates.Finite.N30.Shard0007
import BerryEsseen.Certificates.Finite.N30.Shard0008
import BerryEsseen.Certificates.Finite.N30.Shard0009
import BerryEsseen.Certificates.Finite.N30.Shard0010
import BerryEsseen.Certificates.Finite.N30.Shard0011
import BerryEsseen.Certificates.Finite.N30.Shard0012
import BerryEsseen.Certificates.Finite.N30.Shard0013
import BerryEsseen.Certificates.Finite.N30.Shard0014
import BerryEsseen.Certificates.Finite.N30.Shard0015
import BerryEsseen.Certificates.Finite.N30.Shard0016
import BerryEsseen.Certificates.Finite.N30.Shard0017
import BerryEsseen.Certificates.Finite.N30.Shard0018
import BerryEsseen.Certificates.Finite.N30.Shard0019
import BerryEsseen.Certificates.Finite.N30.Shard0020
import BerryEsseen.Certificates.Finite.N30.Shard0021

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN30Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN30Shard0000Tree finiteN30Shard0001Tree) finiteN30Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN30Shard0003Tree finiteN30Shard0004Tree) finiteN30Shard0005Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN30Shard0006Tree (.splitRho finiteN30Shard0007Tree finiteN30Shard0008Tree)) finiteN30Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN30Shard0010Tree finiteN30Shard0011Tree) finiteN30Shard0012Tree) (.splitRho (.splitZ (.splitRho finiteN30Shard0013Tree finiteN30Shard0014Tree) (.splitRho (.splitZ finiteN30Shard0015Tree finiteN30Shard0016Tree) finiteN30Shard0017Tree)) finiteN30Shard0018Tree)) finiteN30Shard0019Tree)) finiteN30Shard0020Tree)) finiteN30Shard0021Tree))

theorem finiteN30_parsed :
    (certifiedOldLeafCode 30).bind dyadicRouteBLeafTreeOfCode =
      some finiteN30Tree := by
  native_decide

theorem finiteN30_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 30 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN30_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN30Shard0000_checked finiteN30Shard0001_checked) finiteN30Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN30Shard0003_checked finiteN30Shard0004_checked) finiteN30Shard0005_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN30Shard0006_checked (bound4395FiniteVerifySplitRho_true finiteN30Shard0007_checked finiteN30Shard0008_checked)) finiteN30Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN30Shard0010_checked finiteN30Shard0011_checked) finiteN30Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN30Shard0013_checked finiteN30Shard0014_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN30Shard0015_checked finiteN30Shard0016_checked) finiteN30Shard0017_checked)) finiteN30Shard0018_checked)) finiteN30Shard0019_checked)) finiteN30Shard0020_checked)) finiteN30Shard0021_checked))

end BerryEsseen
