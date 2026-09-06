import BerryEsseen.Certificates.Finite.N41.Assembly
import BerryEsseen.Certificates.Finite.N42.Assembly
import BerryEsseen.Certificates.Finite.N43.Assembly
import BerryEsseen.Certificates.Finite.N44.Assembly
import BerryEsseen.Certificates.Finite.N45.Assembly
import BerryEsseen.Certificates.Finite.N46.Assembly
import BerryEsseen.Certificates.Finite.N47.Assembly
import BerryEsseen.Certificates.Finite.N48.Assembly
import BerryEsseen.Certificates.Finite.N49.Assembly
import BerryEsseen.Certificates.Finite.N50.Assembly

namespace BerryEsseen
set_option maxRecDepth 10000
theorem bound4395FiniteTargetAwareBatch41_50_checked :
    ∀ n : Fin 51, 41 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 5 = true := by
  intro n hn
  have cases_n : n.val = 41 ∨ n.val = 42 ∨ n.val = 43 ∨ n.val = 44 ∨ n.val = 45 ∨ n.val = 46 ∨ n.val = 47 ∨ n.val = 48 ∨ n.val = 49 ∨ n.val = 50 := by omega
  rcases cases_n with h | h | h | h | h | h | h | h | h | h
  · simpa only [h] using finiteN41_checked
  · simpa only [h] using finiteN42_checked
  · simpa only [h] using finiteN43_checked
  · simpa only [h] using finiteN44_checked
  · simpa only [h] using finiteN45_checked
  · simpa only [h] using finiteN46_checked
  · simpa only [h] using finiteN47_checked
  · simpa only [h] using finiteN48_checked
  · simpa only [h] using finiteN49_checked
  · simpa only [h] using finiteN50_checked

end BerryEsseen
