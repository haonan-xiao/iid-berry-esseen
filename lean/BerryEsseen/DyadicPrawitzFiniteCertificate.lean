import BerryEsseen.DyadicPrawitzFiniteCachedCover

/-!
# Concrete finite-`n` Route B certificates

The declarations in this module are proof-producing evaluations of the exhaustive dyadic cover.
They are intentionally kept separate from the generic soundness development so the numerical
work can be rebuilt and audited independently.
-/

namespace BerryEsseen

set_option maxRecDepth 10000

theorem dyadicRouteBCachedFiniteCertificate_one :
    dyadicRouteBCachedFiniteCertificate 1 = true := by
  native_decide

end BerryEsseen
