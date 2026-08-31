import BerryEsseen.Certificate.LargeN.SmallLeafTree
/-!
# Checked endpoint-regular certificate for the large-`n` Route B bound

The prefix code below was proposed by an untrusted exact-arithmetic generator.
Lean reparses the tree and recomputes every leaf. Generator report:
region=0, leaves=208, nodes=415, depth=12, resolutions=20/155/33,
worst=0.449498791979873857.
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def routeBLargeSmallLeafCode : String :=
  "XZXZ01Z01XZXZ01Z01XZXZ01Z01XZ2XZ11Z11Z2XZ11Z11ZXZ01Z01XZ2XZ12Z12Z2XZ12Z12ZXZ01Z01XZXZ01Z01XZ2XZ12Z12Z2XZ12Z12ZXZ01Z01XZX2Z11XZ12Z12ZXZ11Z11XZ12Z12ZXZ01Z01XZXZ01Z01XZXZ11Z11XZXZ11Z11XZ12Z1X22ZXZ11Z11XZ1XZ11Z11Z1XZ11Z11ZXZ11Z11XZXZ11Z11XZ1XZ11Z11Z1XZ11Z11ZXZ11Z11XZ1XZ11Z11Z1XZ11Z11ZXZ01Z01XZXZ11Z11XZXZ11Z11XZ1XZ11Z11Z2XZ11Z11ZXZ11Z11XZ2XZ11Z11Z2XZ11Z11ZXZ11Z11XZXZ11Z11XZ2XZ11Z11Z2XZ11Z11ZXZ11Z11XZ2XZ12Z12Z2XZ12Z12"

theorem routeBLargeSmallLeafCode_checked :
    dyadicRouteBLargeSmallLeafCodeCertificate
      routeBLargeSmallLeafCode = true := by
  native_decide

/-- The checked endpoint-regular certificate instantiated in the analytic
theorem. -/
theorem routeB_normalizedRouteBU_lt_threshold_of_checkedLargeSmall
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hL : routeBSmoothingScale n rho ≤ (1 : ℝ) / 16) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) <
      (4495 : ℝ) / 10000 :=
  routeB_normalizedRouteBU_lt_threshold_of_largeSmallCertificate
    routeBLargeSmallLeafCode_checked hn hrho heta0 heta1 hL

end BerryEsseen
