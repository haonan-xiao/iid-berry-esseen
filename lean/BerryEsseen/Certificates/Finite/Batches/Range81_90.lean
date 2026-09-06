import BerryEsseen.Certificates.Finite.N81.Assembly
import BerryEsseen.Certificates.Finite.N82.Assembly
import BerryEsseen.Certificates.Finite.N83.Assembly
import BerryEsseen.Certificates.Finite.N84.Assembly
import BerryEsseen.Certificates.Finite.N85.Assembly
import BerryEsseen.Certificates.Finite.N86.Assembly
import BerryEsseen.Certificates.Finite.N87.Assembly
import BerryEsseen.Certificates.Finite.N88.Assembly
import BerryEsseen.Certificates.Finite.N89.Assembly
import BerryEsseen.Certificates.Finite.N90.Assembly

namespace BerryEsseen
set_option maxRecDepth 10000
theorem bound4395FiniteTargetAwareBatch81_90_checked :
    ∀ n : Fin 91, 81 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 5 = true := by
  intro n hn
  have cases_n : n.val = 81 ∨ n.val = 82 ∨ n.val = 83 ∨ n.val = 84 ∨ n.val = 85 ∨ n.val = 86 ∨ n.val = 87 ∨ n.val = 88 ∨ n.val = 89 ∨ n.val = 90 := by omega
  rcases cases_n with h | h | h | h | h | h | h | h | h | h
  · simpa only [h] using finiteN81_checked
  · simpa only [h] using finiteN82_checked
  · simpa only [h] using finiteN83_checked
  · simpa only [h] using finiteN84_checked
  · simpa only [h] using finiteN85_checked
  · simpa only [h] using finiteN86_checked
  · simpa only [h] using finiteN87_checked
  · simpa only [h] using finiteN88_checked
  · simpa only [h] using finiteN89_checked
  · simpa only [h] using finiteN90_checked

end BerryEsseen
