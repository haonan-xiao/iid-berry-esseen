import BerryEsseen.Certificates.Finite.N05.Shard0000
import BerryEsseen.Certificates.Finite.N05.Shard0001
import BerryEsseen.Certificates.Finite.N05.Shard0002
import BerryEsseen.Certificates.Finite.N05.Shard0003
import BerryEsseen.Certificates.Finite.N05.Shard0004
import BerryEsseen.Certificates.Finite.N05.Shard0005
import BerryEsseen.Certificates.Finite.N05.Shard0006
import BerryEsseen.Certificates.Finite.N05.Shard0007
import BerryEsseen.Certificates.Finite.N05.Shard0008
import BerryEsseen.Certificates.Finite.N05.Shard0009
import BerryEsseen.Certificates.Finite.N05.Shard0010
import BerryEsseen.Certificates.Finite.N05.Shard0011
import BerryEsseen.Certificates.Finite.N05.Shard0012
import BerryEsseen.Certificates.Finite.N05.Shard0013
import BerryEsseen.Certificates.Finite.N05.Shard0014
import BerryEsseen.Certificates.Finite.N05.Shard0015
import BerryEsseen.Certificates.Finite.N05.Shard0016
import BerryEsseen.Certificates.Finite.N05.Shard0017
import BerryEsseen.Certificates.Finite.N05.Shard0018
import BerryEsseen.Certificates.Finite.N05.Shard0019
import BerryEsseen.Certificates.Finite.N05.Shard0020
import BerryEsseen.Certificates.Finite.N05.Shard0021
import BerryEsseen.Certificates.Finite.N05.Shard0022
import BerryEsseen.Certificates.Finite.N05.Shard0023

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN05Tree : DyadicRouteBLeafTree :=
  (.splitZ finiteN05Shard0000Tree (.splitRho (.splitZ finiteN05Shard0001Tree (.splitRho (.splitZ finiteN05Shard0002Tree (.splitRho (.splitZ (.splitRho finiteN05Shard0003Tree finiteN05Shard0004Tree) (.splitRho (.splitZ (.splitRho (.splitZ finiteN05Shard0005Tree finiteN05Shard0006Tree) finiteN05Shard0007Tree) (.splitRho (.splitZ (.splitRho finiteN05Shard0008Tree finiteN05Shard0009Tree) (.splitRho (.splitZ finiteN05Shard0010Tree finiteN05Shard0011Tree) (.splitRho finiteN05Shard0012Tree finiteN05Shard0013Tree))) (.splitRho (.splitZ finiteN05Shard0014Tree finiteN05Shard0015Tree) finiteN05Shard0016Tree))) (.splitZ finiteN05Shard0017Tree (.splitRho finiteN05Shard0018Tree finiteN05Shard0019Tree)))) (.splitRho finiteN05Shard0020Tree finiteN05Shard0021Tree))) finiteN05Shard0022Tree)) finiteN05Shard0023Tree))

theorem finiteN05_parsed :
    (certifiedOldLeafCode 5).bind dyadicRouteBLeafTreeOfCode =
      some finiteN05Tree := by
  native_decide

theorem finiteN05_checked :
    bound4395OldFiniteTargetAwareLeafCodeCertificate 5 6 = true := by
  apply bound4395OldFiniteCertificate_of_parsed_tree finiteN05_parsed
  exact (bound4395FiniteVerifySplitZ_true finiteN05Shard0000_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN05Shard0001_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN05Shard0002_checked (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN05Shard0003_checked finiteN05Shard0004_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN05Shard0005_checked finiteN05Shard0006_checked) finiteN05Shard0007_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true (bound4395FiniteVerifySplitRho_true finiteN05Shard0008_checked finiteN05Shard0009_checked) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN05Shard0010_checked finiteN05Shard0011_checked) (bound4395FiniteVerifySplitRho_true finiteN05Shard0012_checked finiteN05Shard0013_checked))) (bound4395FiniteVerifySplitRho_true (bound4395FiniteVerifySplitZ_true finiteN05Shard0014_checked finiteN05Shard0015_checked) finiteN05Shard0016_checked))) (bound4395FiniteVerifySplitZ_true finiteN05Shard0017_checked (bound4395FiniteVerifySplitRho_true finiteN05Shard0018_checked finiteN05Shard0019_checked)))) (bound4395FiniteVerifySplitRho_true finiteN05Shard0020_checked finiteN05Shard0021_checked))) finiteN05Shard0022_checked)) finiteN05Shard0023_checked))

end BerryEsseen
