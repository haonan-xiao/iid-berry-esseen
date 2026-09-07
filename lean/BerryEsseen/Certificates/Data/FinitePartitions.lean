import BerryEsseen.Interval.Finite.Leaf

/-!
# Certificates / Data / Finite Partitions
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory

def certifiedOldLeafSource : ℕ → Option String
  | 1 => some (include_str "../../../certificate-data/finite/N01.lean.txt")
  | 2 => some (include_str "../../../certificate-data/finite/N02.lean.txt")
  | 3 => some (include_str "../../../certificate-data/finite/N03.lean.txt")
  | 4 => some (include_str "../../../certificate-data/finite/N04.lean.txt")
  | 5 => some (include_str "../../../certificate-data/finite/N05.lean.txt")
  | 6 => some (include_str "../../../certificate-data/finite/N06.lean.txt")
  | 7 => some (include_str "../../../certificate-data/finite/N07.lean.txt")
  | 8 => some (include_str "../../../certificate-data/finite/N08.lean.txt")
  | 9 => some (include_str "../../../certificate-data/finite/N09.lean.txt")
  | 10 => some (include_str "../../../certificate-data/finite/N10.lean.txt")
  | 11 => some (include_str "../../../certificate-data/finite/N11.lean.txt")
  | 12 => some (include_str "../../../certificate-data/finite/N12.lean.txt")
  | 13 => some (include_str "../../../certificate-data/finite/N13.lean.txt")
  | 14 => some (include_str "../../../certificate-data/finite/N14.lean.txt")
  | 15 => some (include_str "../../../certificate-data/finite/N15.lean.txt")
  | 16 => some (include_str "../../../certificate-data/finite/N16.lean.txt")
  | 17 => some (include_str "../../../certificate-data/finite/N17.lean.txt")
  | 18 => some (include_str "../../../certificate-data/finite/N18.lean.txt")
  | 19 => some (include_str "../../../certificate-data/finite/N19.lean.txt")
  | 20 => some (include_str "../../../certificate-data/finite/N20.lean.txt")
  | 21 => some (include_str "../../../certificate-data/finite/N21.lean.txt")
  | 22 => some (include_str "../../../certificate-data/finite/N22.lean.txt")
  | 23 => some (include_str "../../../certificate-data/finite/N23.lean.txt")
  | 24 => some (include_str "../../../certificate-data/finite/N24.lean.txt")
  | 25 => some (include_str "../../../certificate-data/finite/N25.lean.txt")
  | 26 => some (include_str "../../../certificate-data/finite/N26.lean.txt")
  | 27 => some (include_str "../../../certificate-data/finite/N27.lean.txt")
  | 28 => some (include_str "../../../certificate-data/finite/N28.lean.txt")
  | 29 => some (include_str "../../../certificate-data/finite/N29.lean.txt")
  | 30 => some (include_str "../../../certificate-data/finite/N30.lean.txt")
  | 31 => some (include_str "../../../certificate-data/finite/N31.lean.txt")
  | 32 => some (include_str "../../../certificate-data/finite/N32.lean.txt")
  | 33 => some (include_str "../../../certificate-data/finite/N33.lean.txt")
  | 34 => some (include_str "../../../certificate-data/finite/N34.lean.txt")
  | 35 => some (include_str "../../../certificate-data/finite/N35.lean.txt")
  | 36 => some (include_str "../../../certificate-data/finite/N36.lean.txt")
  | 37 => some (include_str "../../../certificate-data/finite/N37.lean.txt")
  | 38 => some (include_str "../../../certificate-data/finite/N38.lean.txt")
  | 39 => some (include_str "../../../certificate-data/finite/N39.lean.txt")
  | 40 => some (include_str "../../../certificate-data/finite/N40.lean.txt")
  | 41 => some (include_str "../../../certificate-data/finite/N41.lean.txt")
  | 42 => some (include_str "../../../certificate-data/finite/N42.lean.txt")
  | 43 => some (include_str "../../../certificate-data/finite/N43.lean.txt")
  | 44 => some (include_str "../../../certificate-data/finite/N44.lean.txt")
  | 45 => some (include_str "../../../certificate-data/finite/N45.lean.txt")
  | 46 => some (include_str "../../../certificate-data/finite/N46.lean.txt")
  | 47 => some (include_str "../../../certificate-data/finite/N47.lean.txt")
  | 48 => some (include_str "../../../certificate-data/finite/N48.lean.txt")
  | 49 => some (include_str "../../../certificate-data/finite/N49.lean.txt")
  | 50 => some (include_str "../../../certificate-data/finite/N50.lean.txt")
  | 51 => some (include_str "../../../certificate-data/finite/N51.lean.txt")
  | 52 => some (include_str "../../../certificate-data/finite/N52.lean.txt")
  | 53 => some (include_str "../../../certificate-data/finite/N53.lean.txt")
  | 54 => some (include_str "../../../certificate-data/finite/N54.lean.txt")
  | 55 => some (include_str "../../../certificate-data/finite/N55.lean.txt")
  | 56 => some (include_str "../../../certificate-data/finite/N56.lean.txt")
  | 57 => some (include_str "../../../certificate-data/finite/N57.lean.txt")
  | 58 => some (include_str "../../../certificate-data/finite/N58.lean.txt")
  | 59 => some (include_str "../../../certificate-data/finite/N59.lean.txt")
  | 60 => some (include_str "../../../certificate-data/finite/N60.lean.txt")
  | 61 => some (include_str "../../../certificate-data/finite/N61.lean.txt")
  | 62 => some (include_str "../../../certificate-data/finite/N62.lean.txt")
  | 63 => some (include_str "../../../certificate-data/finite/N63.lean.txt")
  | 64 => some (include_str "../../../certificate-data/finite/N64.lean.txt")
  | 65 => some (include_str "../../../certificate-data/finite/N65.lean.txt")
  | 66 => some (include_str "../../../certificate-data/finite/N66.lean.txt")
  | 67 => some (include_str "../../../certificate-data/finite/N67.lean.txt")
  | 68 => some (include_str "../../../certificate-data/finite/N68.lean.txt")
  | 69 => some (include_str "../../../certificate-data/finite/N69.lean.txt")
  | 70 => some (include_str "../../../certificate-data/finite/N70.lean.txt")
  | 71 => some (include_str "../../../certificate-data/finite/N71.lean.txt")
  | 72 => some (include_str "../../../certificate-data/finite/N72.lean.txt")
  | 73 => some (include_str "../../../certificate-data/finite/N73.lean.txt")
  | 74 => some (include_str "../../../certificate-data/finite/N74.lean.txt")
  | 75 => some (include_str "../../../certificate-data/finite/N75.lean.txt")
  | 76 => some (include_str "../../../certificate-data/finite/N76.lean.txt")
  | 77 => some (include_str "../../../certificate-data/finite/N77.lean.txt")
  | 78 => some (include_str "../../../certificate-data/finite/N78.lean.txt")
  | 79 => some (include_str "../../../certificate-data/finite/N79.lean.txt")
  | 80 => some (include_str "../../../certificate-data/finite/N80.lean.txt")
  | 81 => some (include_str "../../../certificate-data/finite/N81.lean.txt")
  | 82 => some (include_str "../../../certificate-data/finite/N82.lean.txt")
  | 83 => some (include_str "../../../certificate-data/finite/N83.lean.txt")
  | 84 => some (include_str "../../../certificate-data/finite/N84.lean.txt")
  | 85 => some (include_str "../../../certificate-data/finite/N85.lean.txt")
  | 86 => some (include_str "../../../certificate-data/finite/N86.lean.txt")
  | 87 => some (include_str "../../../certificate-data/finite/N87.lean.txt")
  | 88 => some (include_str "../../../certificate-data/finite/N88.lean.txt")
  | 89 => some (include_str "../../../certificate-data/finite/N89.lean.txt")
  | 90 => some (include_str "../../../certificate-data/finite/N90.lean.txt")
  | 91 => some (include_str "../../../certificate-data/finite/N91.lean.txt")
  | 92 => some (include_str "../../../certificate-data/finite/N92.lean.txt")
  | 93 => some (include_str "../../../certificate-data/finite/N93.lean.txt")
  | 94 => some (include_str "../../../certificate-data/finite/N94.lean.txt")
  | 95 => some (include_str "../../../certificate-data/finite/N95.lean.txt")
  | 96 => some (include_str "../../../certificate-data/finite/N96.lean.txt")
  | 97 => some (include_str "../../../certificate-data/finite/N97.lean.txt")
  | 98 => some (include_str "../../../certificate-data/finite/N98.lean.txt")
  | 99 => some (include_str "../../../certificate-data/finite/N99.lean.txt")
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
