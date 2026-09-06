import BerryEsseen.Certificates.Finite.Batches.Range01_10
import BerryEsseen.Certificates.Finite.Batches.Range11_20
import BerryEsseen.Certificates.Finite.Batches.Range21_30
import BerryEsseen.Certificates.Finite.Batches.Range31_40
import BerryEsseen.Certificates.Finite.Batches.Range41_50
import BerryEsseen.Certificates.Finite.Batches.Range51_60
import BerryEsseen.Certificates.Finite.Batches.Range61_70
import BerryEsseen.Certificates.Finite.Batches.Range71_80
import BerryEsseen.Certificates.Finite.Batches.Range81_90
import BerryEsseen.Certificates.Finite.Batches.Range91_99

namespace BerryEsseen

theorem bound4395FiniteTargetAwareCertificates_checked :
    ∀ n : ℕ, 1 ≤ n → n < 100 →
      ∃ extraFuel : ℕ,
        bound4395OldFiniteTargetAwareLeafCodeCertificate
          n extraFuel = true := by
  intro n hn hn100
  by_cases hn11 : n < 11
  · refine ⟨6, ?_⟩
    simpa using bound4395FiniteTargetAwareBatch01_10_checked
      (⟨n, hn11⟩ : Fin 11) hn
  · refine ⟨5, ?_⟩
    by_cases hn21 : n < 21
    · have hnLower : 11 ≤ n := by omega
      simpa using bound4395FiniteTargetAwareBatch11_20_checked
        (⟨n, hn21⟩ : Fin 21) hnLower
    by_cases hn31 : n < 31
    · have hnLower : 21 ≤ n := by omega
      simpa using bound4395FiniteTargetAwareBatch21_30_checked
        (⟨n, hn31⟩ : Fin 31) hnLower
    by_cases hn41 : n < 41
    · have hnLower : 31 ≤ n := by omega
      simpa using bound4395FiniteTargetAwareBatch31_40_checked
        (⟨n, hn41⟩ : Fin 41) hnLower
    by_cases hn51 : n < 51
    · have hnLower : 41 ≤ n := by omega
      simpa using bound4395FiniteTargetAwareBatch41_50_checked
        (⟨n, hn51⟩ : Fin 51) hnLower
    by_cases hn61 : n < 61
    · have hnLower : 51 ≤ n := by omega
      simpa using bound4395FiniteTargetAwareBatch51_60_checked
        (⟨n, hn61⟩ : Fin 61) hnLower
    by_cases hn71 : n < 71
    · have hnLower : 61 ≤ n := by omega
      simpa using bound4395FiniteTargetAwareBatch61_70_checked
        (⟨n, hn71⟩ : Fin 71) hnLower
    by_cases hn81 : n < 81
    · have hnLower : 71 ≤ n := by omega
      simpa using bound4395FiniteTargetAwareBatch71_80_checked
        (⟨n, hn81⟩ : Fin 81) hnLower
    by_cases hn91 : n < 91
    · have hnLower : 81 ≤ n := by omega
      simpa using bound4395FiniteTargetAwareBatch81_90_checked
        (⟨n, hn91⟩ : Fin 91) hnLower
    · have hnLower : 91 ≤ n := by omega
      simpa using bound4395FiniteTargetAwareBatch91_99_checked
        (⟨n, hn100⟩ : Fin 100) hnLower

  end BerryEsseen
