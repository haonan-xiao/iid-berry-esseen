import BerryEsseen.Certificates.Finite.N71.Shard0000
import BerryEsseen.Certificates.Finite.N71.Shard0001
import BerryEsseen.Certificates.Finite.N71.Shard0002
import BerryEsseen.Certificates.Finite.N71.Shard0003
import BerryEsseen.Certificates.Finite.N71.Shard0004
import BerryEsseen.Certificates.Finite.N71.Shard0005
import BerryEsseen.Certificates.Finite.N71.Shard0006
import BerryEsseen.Certificates.Finite.N71.Shard0007
import BerryEsseen.Certificates.Finite.N71.Shard0008
import BerryEsseen.Certificates.Finite.N71.Shard0009
import BerryEsseen.Certificates.Finite.N71.Shard0010
import BerryEsseen.Certificates.Finite.N71.Shard0011
import BerryEsseen.Certificates.Finite.N71.Shard0012
import BerryEsseen.Certificates.Finite.N71.Shard0013
import BerryEsseen.Certificates.Finite.N71.Shard0014
import BerryEsseen.Certificates.Finite.N71.Shard0015
import BerryEsseen.Certificates.Finite.N71.Shard0016
import BerryEsseen.Certificates.Finite.N71.Shard0017
import BerryEsseen.Certificates.Finite.N71.Shard0018
import BerryEsseen.Certificates.Finite.N71.Shard0019
import BerryEsseen.Certificates.Finite.N71.Shard0020
import BerryEsseen.Certificates.Finite.N71.Shard0021
import BerryEsseen.Certificates.Finite.N71.Shard0022
import BerryEsseen.Certificates.Finite.N71.Shard0023
import BerryEsseen.Certificates.Finite.N71.Shard0024
import BerryEsseen.Certificates.Finite.N71.Shard0025

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN71Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN71Shard0000Tree finiteN71Shard0001Tree) finiteN71Shard0002Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN71Shard0003Tree (.splitRho (.splitZ finiteN71Shard0004Tree finiteN71Shard0005Tree) finiteN71Shard0006Tree)) finiteN71Shard0007Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN71Shard0008Tree (.splitRho (.splitZ finiteN71Shard0009Tree finiteN71Shard0010Tree) finiteN71Shard0011Tree)) finiteN71Shard0012Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN71Shard0013Tree finiteN71Shard0014Tree) finiteN71Shard0015Tree) (.splitRho (.splitZ (.splitRho finiteN71Shard0016Tree finiteN71Shard0017Tree) (.splitRho (.splitZ finiteN71Shard0018Tree (.splitRho finiteN71Shard0019Tree finiteN71Shard0020Tree)) finiteN71Shard0021Tree)) finiteN71Shard0022Tree)) finiteN71Shard0023Tree)) finiteN71Shard0024Tree)) finiteN71Shard0025Tree))

theorem finiteN71_parsed :
    (certifiedOldLeafCode 71).bind dyadicRouteBLeafTreeOfCode =
      some finiteN71Tree := by
  native_decide

theorem finiteN71_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 71 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN71_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN71Shard0000_checked finiteN71Shard0001_checked) finiteN71Shard0002_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN71Shard0003_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN71Shard0004_checked finiteN71Shard0005_checked) finiteN71Shard0006_checked)) finiteN71Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN71Shard0008_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN71Shard0009_checked finiteN71Shard0010_checked) finiteN71Shard0011_checked)) finiteN71Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN71Shard0013_checked finiteN71Shard0014_checked) finiteN71Shard0015_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN71Shard0016_checked finiteN71Shard0017_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN71Shard0018_checked (bound4395FiniteVerifySplitRho_true finiteN71Shard0019_checked finiteN71Shard0020_checked)) finiteN71Shard0021_checked)) finiteN71Shard0022_checked)) finiteN71Shard0023_checked)) finiteN71Shard0024_checked)) finiteN71Shard0025_checked))

end BerryEsseen
