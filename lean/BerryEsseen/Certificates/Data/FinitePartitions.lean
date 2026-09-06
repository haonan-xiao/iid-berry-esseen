import BerryEsseen.Interval.Finite.Leaf

/-!
# Certificates / Data / Finite Partitions
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory

def certifiedOldLeafSource : ℕ → Option String
  | 1 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate01.lean")
  | 2 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate02.lean")
  | 3 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate03.lean")
  | 4 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate04.lean")
  | 5 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate05.lean")
  | 6 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate06.lean")
  | 7 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate07.lean")
  | 8 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate08.lean")
  | 9 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate09.lean")
  | 10 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate10.lean")
  | 11 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate11.lean")
  | 12 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate12.lean")
  | 13 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate13.lean")
  | 14 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate14.lean")
  | 15 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate15.lean")
  | 16 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate16.lean")
  | 17 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate17.lean")
  | 18 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate18.lean")
  | 19 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate19.lean")
  | 20 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate20.lean")
  | 21 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate21.lean")
  | 22 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate22.lean")
  | 23 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate23.lean")
  | 24 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate24.lean")
  | 25 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate25.lean")
  | 26 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate26.lean")
  | 27 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate27.lean")
  | 28 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate28.lean")
  | 29 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate29.lean")
  | 30 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate30.lean")
  | 31 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate31.lean")
  | 32 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate32.lean")
  | 33 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate33.lean")
  | 34 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate34.lean")
  | 35 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate35.lean")
  | 36 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate36.lean")
  | 37 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate37.lean")
  | 38 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate38.lean")
  | 39 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate39.lean")
  | 40 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate40.lean")
  | 41 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate41.lean")
  | 42 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate42.lean")
  | 43 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate43.lean")
  | 44 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate44.lean")
  | 45 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate45.lean")
  | 46 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate46.lean")
  | 47 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate47.lean")
  | 48 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate48.lean")
  | 49 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate49.lean")
  | 50 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate50.lean")
  | 51 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate51.lean")
  | 52 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate52.lean")
  | 53 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate53.lean")
  | 54 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate54.lean")
  | 55 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate55.lean")
  | 56 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate56.lean")
  | 57 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate57.lean")
  | 58 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate58.lean")
  | 59 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate59.lean")
  | 60 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate60.lean")
  | 61 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate61.lean")
  | 62 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate62.lean")
  | 63 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate63.lean")
  | 64 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate64.lean")
  | 65 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate65.lean")
  | 66 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate66.lean")
  | 67 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate67.lean")
  | 68 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate68.lean")
  | 69 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate69.lean")
  | 70 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate70.lean")
  | 71 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate71.lean")
  | 72 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate72.lean")
  | 73 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate73.lean")
  | 74 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate74.lean")
  | 75 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate75.lean")
  | 76 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate76.lean")
  | 77 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate77.lean")
  | 78 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate78.lean")
  | 79 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate79.lean")
  | 80 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate80.lean")
  | 81 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate81.lean")
  | 82 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate82.lean")
  | 83 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate83.lean")
  | 84 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate84.lean")
  | 85 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate85.lean")
  | 86 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate86.lean")
  | 87 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate87.lean")
  | 88 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate88.lean")
  | 89 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate89.lean")
  | 90 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate90.lean")
  | 91 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate91.lean")
  | 92 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate92.lean")
  | 93 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate93.lean")
  | 94 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate94.lean")
  | 95 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate95.lean")
  | 96 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate96.lean")
  | 97 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate97.lean")
  | 98 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate98.lean")
  | 99 => some (include_str "../../DyadicPrawitzFiniteLeafCertificate99.lean")
  | _ => none

def certifiedOldLeafCode (n : ℕ) : Option String := do
  let source ← certifiedOldLeafSource n
  let suffix := if n < 10 then "0" ++ toString n else toString n
  let marker := "def dyadicRouteBLeafCode" ++ suffix ++ " : String :="
  match source.splitOn marker with
  | _before :: after :: _ =>
      match after.toList.dropWhile (fun c => c != '"') with
      | '"' :: code =>
          some (String.ofList (code.takeWhile (fun c => c != '"')))
      | _ => none
  | _ => none

def certifiedOldRefinedLeafCodeCertificate
    (n extraFuel : ℕ) : Bool :=
  match certifiedOldLeafCode n with
  | some code => certifiedRefinedLeafCodeCertificate n extraFuel code
  | none => false

theorem normalizedKolmogorovDistance_lt_044_of_oldRefinedLeafCodeCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {extraFuel : ℕ}
    (hcertificate :
      certifiedOldRefinedLeafCodeCertificate n extraFuel = true)
    (hrhoLower : 1 ≤ thirdAbsoluteMoment (P.map (X 0)))
    (hrhoUpper : thirdAbsoluteMoment (P.map (X 0)) ≤
      ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1))
    (hzUpper : thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1) ≤ 1) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  unfold certifiedOldRefinedLeafCodeCertificate at hcertificate
  cases hcode : certifiedOldLeafCode n with
  | none => simp [hcode] at hcertificate
  | some code =>
      rw [hcode] at hcertificate
      exact
        normalizedKolmogorovDistance_lt_044_of_certifiedRefinedLeafCodeCertificate
          P X hindep hident hX hmean hsecond hn hcertificate
            hrhoLower hrhoUpper hzLower hzUpper

end BerryEsseen
