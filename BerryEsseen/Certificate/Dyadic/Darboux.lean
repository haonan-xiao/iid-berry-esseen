import BerryEsseen.Certificate.Dyadic.Elementary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Dyadic upper Darboux certificates

This module connects pointwise dyadic interval evaluation to interval-integral bounds.  For any
finite monotone partition, if an interval evaluator encloses the integrand on every cell and a
width interval encloses the exact cell width, the upper endpoint of the outward-rounded sum of
width-times-value intervals bounds the whole interval integral.  The theorem is independent of
the Route B formulas, so the finite-`n` and tail checkers can share the same proved integration
kernel.
-/

open Finset MeasureTheory intervalIntegral

namespace BerryEsseen

open DyadicInterval

def intervalNatSum (F : ℕ → DyadicInterval) : ℕ → DyadicInterval
  | 0 => DyadicInterval.point 0
  | n + 1 => DyadicInterval.add (intervalNatSum F n) (F n)

noncomputable section

theorem intervalNatSum_sound {F : ℕ → DyadicInterval} {g : ℕ → ℝ}
    (N : ℕ) (hF : ∀ n < N, (F n).Contains (g n)) :
    (intervalNatSum F N).Contains (∑ n ∈ Finset.range N, g n) := by
  induction N with
  | zero =>
      simpa [intervalNatSum] using DyadicInterval.contains_point (0 : ℤ)
  | succ N ih =>
      have hprev := ih (fun n hn => hF n (hn.trans_le N.le_succ))
      simpa [intervalNatSum, Finset.sum_range_succ] using
        hprev.add (hF N N.lt_succ_self)

theorem intervalIntegral_le_intervalNatSum_upper
    {f : ℝ → ℝ} {p : ℕ → ℝ} {N : ℕ}
    (hmono : ∀ k < N, p k ≤ p (k + 1))
    (hint : ∀ k < N, IntervalIntegrable f volume (p k) (p (k + 1)))
    (E W : ℕ → DyadicInterval)
    (hEordered : ∀ k < N, (E k).Ordered)
    (hupper : ∀ k < N, ∀ x ∈ Set.Icc (p k) (p (k + 1)), f x ≤ (E k).upper)
    (hwidth : ∀ k < N, (W k).Contains (p (k + 1) - p k)) :
    (∫ x in p 0..p N, f x) ≤
      (intervalNatSum (fun k => DyadicInterval.mul (W k) (E k)) N).upper := by
  have hcell : ∀ k < N,
      (∫ x in p k..p (k + 1), f x) ≤
        (p (k + 1) - p k) * (E k).upper := by
    intro k hk
    calc
      (∫ x in p k..p (k + 1), f x) ≤
          ∫ _ in p k..p (k + 1), (E k).upper := by
        apply intervalIntegral.integral_mono_on (hmono k hk) (hint k hk)
          (intervalIntegrable_const)
        exact hupper k hk
      _ = (p (k + 1) - p k) * (E k).upper := by
        rw [intervalIntegral.integral_const]
        rfl
  have hterm : ∀ k < N, (DyadicInterval.mul (W k) (E k)).Contains
      ((p (k + 1) - p k) * (E k).upper) := by
    intro k hk
    exact (hwidth k hk).mul (DyadicInterval.contains_upper (hEordered k hk))
  have hsum := intervalNatSum_sound N hterm
  calc
    (∫ x in p 0..p N, f x) =
        ∑ k ∈ Finset.range N, ∫ x in p k..p (k + 1), f x := by
      symm
      exact intervalIntegral.sum_integral_adjacent_intervals hint
    _ ≤ ∑ k ∈ Finset.range N, (p (k + 1) - p k) * (E k).upper := by
      exact Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.mp hk)
    _ ≤ (intervalNatSum (fun k => DyadicInterval.mul (W k) (E k)) N).upper :=
      hsum.2

theorem intervalIntegral_le_intervalNatSum_upper_of_contains
    {f : ℝ → ℝ} {p : ℕ → ℝ} {N : ℕ}
    (hmono : ∀ k < N, p k ≤ p (k + 1))
    (hint : ∀ k < N, IntervalIntegrable f volume (p k) (p (k + 1)))
    (E W : ℕ → DyadicInterval)
    (heval : ∀ k < N, ∀ x ∈ Set.Icc (p k) (p (k + 1)), (E k).Contains (f x))
    (hwidth : ∀ k < N, (W k).Contains (p (k + 1) - p k)) :
    (∫ x in p 0..p N, f x) ≤
      (intervalNatSum (fun k => DyadicInterval.mul (W k) (E k)) N).upper := by
  apply intervalIntegral_le_intervalNatSum_upper hmono hint E W
  · intro k hk
    exact (heval k hk (p k) ⟨le_rfl, hmono k hk⟩).ordered
  · intro k hk x hx
    exact (heval k hk x hx).2
  · exact hwidth

end

end BerryEsseen
