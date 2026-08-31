import BerryEsseen.Certificate.Finite.LeafTree
/-!
# Shared-cache batches of finite Route B leaf certificates

The individual finite certificates use the same parameter-independent cell
and exponential-integral caches.  This helper lets one `native_decide` theorem
check several prefix codes while constructing that cache only once.  The
checker and its soundness theorem are unchanged.
-/

namespace BerryEsseen

set_option maxRecDepth 10000

/-- Check one finite prefix code using an explicitly supplied resolution
cache. -/
def dyadicRouteBLeafCodeCertificateWithCache
    (cache : DyadicRouteBResolutionCache) (n : ℕ) (code : String) : Bool :=
  match dyadicRouteBLeafTreeOfCode code with
  | some tree =>
      dyadicRouteBVerifyLeafTree cache n tree
        (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ
  | none => false

/-- Supplying the canonical cache is definitionally the original certificate
checker. -/
theorem dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq
    (n : ℕ) (code : String) :
    dyadicRouteBLeafCodeCertificateWithCache
        dyadicRouteBBuildResolutionCache n code =
      dyadicRouteBLeafCodeCertificate n code := by
  rfl

end BerryEsseen
