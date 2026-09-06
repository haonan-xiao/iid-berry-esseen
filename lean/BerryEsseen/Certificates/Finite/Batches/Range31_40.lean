import BerryEsseen.Certificates.Finite.N31.Assembly
import BerryEsseen.Certificates.Finite.N32.Assembly
import BerryEsseen.Certificates.Finite.N33.Assembly
import BerryEsseen.Certificates.Finite.N34.Assembly
import BerryEsseen.Certificates.Finite.N35.Assembly
import BerryEsseen.Certificates.Finite.N36.Assembly
import BerryEsseen.Certificates.Finite.N37.Assembly
import BerryEsseen.Certificates.Finite.N38.Assembly
import BerryEsseen.Certificates.Finite.N39.Assembly
import BerryEsseen.Certificates.Finite.N40.Assembly

namespace BerryEsseen
set_option maxRecDepth 10000
theorem bound4395FiniteTargetAwareBatch31_40_checked :
    ∀ n : Fin 41, 31 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 5 = true := by
  intro n hn
  have cases_n : n.val = 31 ∨ n.val = 32 ∨ n.val = 33 ∨ n.val = 34 ∨ n.val = 35 ∨ n.val = 36 ∨ n.val = 37 ∨ n.val = 38 ∨ n.val = 39 ∨ n.val = 40 := by omega
  rcases cases_n with h | h | h | h | h | h | h | h | h | h
  · simpa only [h] using finiteN31_checked
  · simpa only [h] using finiteN32_checked
  · simpa only [h] using finiteN33_checked
  · simpa only [h] using finiteN34_checked
  · simpa only [h] using finiteN35_checked
  · simpa only [h] using finiteN36_checked
  · simpa only [h] using finiteN37_checked
  · simpa only [h] using finiteN38_checked
  · simpa only [h] using finiteN39_checked
  · simpa only [h] using finiteN40_checked

end BerryEsseen
