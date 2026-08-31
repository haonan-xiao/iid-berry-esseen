import BerryEsseen.Interface

/-!
# Boundary of the Route B numerical certificate

No numerical claim is postulated as an axiom.  `CertifiedNumericalBound U` is a proposition that
L1 may take as an explicit hypothesis and L2 must eventually prove from a Lean-checked dyadic
certificate.
-/

namespace BerryEsseen

/-- The full continuous parameter domain of the supplied numerical lemma (5.5). -/
structure NumericalDomain (n : ℕ) (rho r : ℝ) : Prop where
  n_lower : 1 ≤ n
  rho_lower : 1 ≤ rho
  rho_upper : rho ≤ cutoff * Real.sqrt (n : ℝ)
  r_lower : 1 ≤ r
  r_upper : r ≤ 1 + 1 / rho

/-- Exact L1/L2 boundary: `U` obeys the `0.4495` estimate throughout the source domain. -/
def CertifiedNumericalBound (U : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (rho r : ℝ), NumericalDomain n rho r →
    U n rho r ≤ normalizedRate certificateConstant rho n

theorem NumericalDomain.n_pos {n : ℕ} {rho r : ℝ} (h : NumericalDomain n rho r) :
    0 < n := by
  exact lt_of_lt_of_le Nat.zero_lt_one h.n_lower

theorem NumericalDomain.rho_pos {n : ℕ} {rho r : ℝ} (h : NumericalDomain n rho r) :
    0 < rho := by
  linarith [h.rho_lower]

end BerryEsseen
