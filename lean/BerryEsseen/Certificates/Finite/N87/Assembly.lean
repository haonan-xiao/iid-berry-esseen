import BerryEsseen.Certificates.Finite.N87.Shard0000
import BerryEsseen.Certificates.Finite.N87.Shard0001
import BerryEsseen.Certificates.Finite.N87.Shard0002
import BerryEsseen.Certificates.Finite.N87.Shard0003
import BerryEsseen.Certificates.Finite.N87.Shard0004
import BerryEsseen.Certificates.Finite.N87.Shard0005
import BerryEsseen.Certificates.Finite.N87.Shard0006
import BerryEsseen.Certificates.Finite.N87.Shard0007
import BerryEsseen.Certificates.Finite.N87.Shard0008
import BerryEsseen.Certificates.Finite.N87.Shard0009
import BerryEsseen.Certificates.Finite.N87.Shard0010
import BerryEsseen.Certificates.Finite.N87.Shard0011
import BerryEsseen.Certificates.Finite.N87.Shard0012
import BerryEsseen.Certificates.Finite.N87.Shard0013
import BerryEsseen.Certificates.Finite.N87.Shard0014
import BerryEsseen.Certificates.Finite.N87.Shard0015
import BerryEsseen.Certificates.Finite.N87.Shard0016
import BerryEsseen.Certificates.Finite.N87.Shard0017
import BerryEsseen.Certificates.Finite.N87.Shard0018
import BerryEsseen.Certificates.Finite.N87.Shard0019
import BerryEsseen.Certificates.Finite.N87.Shard0020
import BerryEsseen.Certificates.Finite.N87.Shard0021
import BerryEsseen.Certificates.Finite.N87.Shard0022
import BerryEsseen.Certificates.Finite.N87.Shard0023
import BerryEsseen.Certificates.Finite.N87.Shard0024
import BerryEsseen.Certificates.Finite.N87.Shard0025
import BerryEsseen.Certificates.Finite.N87.Shard0026
import BerryEsseen.Certificates.Finite.N87.Shard0027
import BerryEsseen.Certificates.Finite.N87.Shard0028
import BerryEsseen.Certificates.Finite.N87.Shard0029
import BerryEsseen.Certificates.Finite.N87.Shard0030
import BerryEsseen.Certificates.Finite.N87.Shard0031
import BerryEsseen.Certificates.Finite.N87.Shard0032
import BerryEsseen.Certificates.Finite.N87.Shard0033
import BerryEsseen.Certificates.Finite.N87.Shard0034
import BerryEsseen.Certificates.Finite.N87.Shard0035
import BerryEsseen.Certificates.Finite.N87.Shard0036
import BerryEsseen.Certificates.Finite.N87.Shard0037

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN87Tree : DyadicRouteBLeafTree :=
  (.splitZ (.splitRho (.splitZ finiteN87Shard0000Tree (.splitRho (.splitZ finiteN87Shard0001Tree finiteN87Shard0002Tree) finiteN87Shard0003Tree)) finiteN87Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN87Shard0005Tree (.splitRho (.splitZ finiteN87Shard0006Tree finiteN87Shard0007Tree) finiteN87Shard0008Tree)) finiteN87Shard0009Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho (.splitZ finiteN87Shard0010Tree finiteN87Shard0011Tree) finiteN87Shard0012Tree) (.splitRho (.splitZ finiteN87Shard0013Tree finiteN87Shard0014Tree) finiteN87Shard0015Tree)) finiteN87Shard0016Tree) (.splitRho (.splitZ (.splitRho (.splitZ (.splitRho finiteN87Shard0017Tree finiteN87Shard0018Tree) (.splitRho (.splitZ finiteN87Shard0019Tree finiteN87Shard0020Tree) finiteN87Shard0021Tree)) finiteN87Shard0022Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN87Shard0023Tree (.splitRho finiteN87Shard0024Tree finiteN87Shard0025Tree)) finiteN87Shard0026Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN87Shard0027Tree finiteN87Shard0028Tree) finiteN87Shard0029Tree) (.splitRho (.splitZ finiteN87Shard0030Tree finiteN87Shard0031Tree) finiteN87Shard0032Tree)) finiteN87Shard0033Tree)) finiteN87Shard0034Tree)) finiteN87Shard0035Tree)) finiteN87Shard0036Tree)) finiteN87Shard0037Tree))

theorem finiteN87_parsed :
    (certifiedOldLeafCode 87).bind dyadicRouteBLeafTreeOfCode =
      some finiteN87Tree := by
  native_decide

theorem finiteN87_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 87 5 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN87_parsed
  exact (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0001_checked finiteN87Shard0002_checked) finiteN87Shard0003_checked)) finiteN87Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0005_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0006_checked finiteN87Shard0007_checked) finiteN87Shard0008_checked)) finiteN87Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0010_checked finiteN87Shard0011_checked) finiteN87Shard0012_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0013_checked finiteN87Shard0014_checked) finiteN87Shard0015_checked)) finiteN87Shard0016_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN87Shard0017_checked finiteN87Shard0018_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0019_checked finiteN87Shard0020_checked) finiteN87Shard0021_checked)) finiteN87Shard0022_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0023_checked (bound4395FiniteVerifySplitRho_true finiteN87Shard0024_checked finiteN87Shard0025_checked)) finiteN87Shard0026_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0027_checked finiteN87Shard0028_checked) finiteN87Shard0029_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN87Shard0030_checked finiteN87Shard0031_checked) finiteN87Shard0032_checked)) finiteN87Shard0033_checked)) finiteN87Shard0034_checked)) finiteN87Shard0035_checked)) finiteN87Shard0036_checked)) finiteN87Shard0037_checked))

end BerryEsseen
