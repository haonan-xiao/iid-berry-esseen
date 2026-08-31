import BerryEsseen.Certificate.Dyadic.Interval
/-!
# Verifier-matching dyadic integer powers

This module implements and verifies the exact checker's accumulator-based binary exponentiation.
The multiplication and squaring order is preserved because outward-rounded interval
multiplication is not definitionally associative, so a mathematically equivalent reassociation
could produce wider endpoints and consume certificate slack.
-/

namespace BerryEsseen

open DyadicInterval

def powiLoop (z a : DyadicInterval) (n : ℕ) : DyadicInterval :=
  if hzero : n = 0 then z
  else
    let z' := if Odd n then DyadicInterval.mul z a else z
    powiLoop z' (DyadicInterval.mul a a) (n / 2)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by norm_num)

def powi (a : DyadicInterval) (n : ℕ) : DyadicInterval :=
  powiLoop (DyadicInterval.point 1) a n

noncomputable section

theorem powiLoop_sound {z a : DyadicInterval} {zr ar : ℝ}
    (hz : z.Contains zr) (ha : a.Contains ar) (n : ℕ) :
    (powiLoop z a n).Contains (zr * ar ^ n) := by
  induction n using Nat.strong_induction_on generalizing z a zr ar with
  | h n ih =>
      rw [powiLoop]
      by_cases hzero : n = 0
      · subst n
        simpa using hz
      · rw [dif_neg hzero]
        by_cases hodd : Odd n
        · rw [if_pos hodd]
          have hnPos : 0 < n := Nat.pos_of_ne_zero hzero
          have hdiv : n / 2 < n := Nat.div_lt_self hnPos (by norm_num)
          have hrec := ih (n / 2) hdiv (hz.mul ha) (ha.mul ha)
          rcases hodd with ⟨k, hk⟩
          subst n
          have hhalf : (2 * k + 1) / 2 = k := by omega
          rw [hhalf] at hrec ⊢
          convert hrec using 1
          simp [pow_add, pow_mul]
          ring
        · rw [if_neg hodd]
          have hnPos : 0 < n := Nat.pos_of_ne_zero hzero
          have hdiv : n / 2 < n := Nat.div_lt_self hnPos (by norm_num)
          have hrec := ih (n / 2) hdiv hz (ha.mul ha)
          have heven : Even n := (Nat.not_odd_iff_even.mp hodd)
          rcases heven with ⟨k, hk⟩
          subst n
          have hhalf : (k + k) / 2 = k := by omega
          rw [hhalf] at hrec ⊢
          convert hrec using 1
          rw [mul_pow, pow_add]

theorem powi_sound {a : DyadicInterval} {x : ℝ} (ha : a.Contains x) (n : ℕ) :
    (powi a n).Contains (x ^ n) := by
  simpa [powi] using powiLoop_sound (DyadicInterval.contains_point (1 : ℤ)) ha n

end

end BerryEsseen
