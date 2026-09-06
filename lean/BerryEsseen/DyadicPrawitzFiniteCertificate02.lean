import BerryEsseen.DyadicPrawitzFiniteCertificate

/-!
# Finite Route B certificate: `n = 2`

This module isolates the second exhaustive cover so its proof-producing native evaluation can
be rebuilt independently from the already checked `n = 1` certificate.
-/

namespace BerryEsseen

set_option maxRecDepth 10000

theorem dyadicRouteBCachedFiniteCertificate_two :
    dyadicRouteBCachedFiniteCertificate 2 = true := by
  native_decide

end BerryEsseen
