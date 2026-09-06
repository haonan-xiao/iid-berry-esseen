import BerryEsseen.Certificates.Finite.N51.Assembly
import BerryEsseen.Certificates.Finite.N52.Assembly
import BerryEsseen.Certificates.Finite.N53.Assembly
import BerryEsseen.Certificates.Finite.N54.Assembly
import BerryEsseen.Certificates.Finite.N55.Assembly
import BerryEsseen.Certificates.Finite.N56.Assembly
import BerryEsseen.Certificates.Finite.N57.Assembly
import BerryEsseen.Certificates.Finite.N58.Assembly
import BerryEsseen.Certificates.Finite.N59.Assembly
import BerryEsseen.Certificates.Finite.N60.Assembly

namespace BerryEsseen
set_option maxRecDepth 10000
theorem bound4395FiniteTargetAwareBatch51_60_checked :
    ∀ n : Fin 61, 51 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 5 = true := by
  intro n hn
  have cases_n : n.val = 51 ∨ n.val = 52 ∨ n.val = 53 ∨ n.val = 54 ∨ n.val = 55 ∨ n.val = 56 ∨ n.val = 57 ∨ n.val = 58 ∨ n.val = 59 ∨ n.val = 60 := by omega
  rcases cases_n with h | h | h | h | h | h | h | h | h | h
  · simpa only [h] using finiteN51_checked
  · simpa only [h] using finiteN52_checked
  · simpa only [h] using finiteN53_checked
  · simpa only [h] using finiteN54_checked
  · simpa only [h] using finiteN55_checked
  · simpa only [h] using finiteN56_checked
  · simpa only [h] using finiteN57_checked
  · simpa only [h] using finiteN58_checked
  · simpa only [h] using finiteN59_checked
  · simpa only [h] using finiteN60_checked

end BerryEsseen
