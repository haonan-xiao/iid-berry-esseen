import BerryEsseen.Certificates.Finite.N71.Assembly
import BerryEsseen.Certificates.Finite.N72.Assembly
import BerryEsseen.Certificates.Finite.N73.Assembly
import BerryEsseen.Certificates.Finite.N74.Assembly
import BerryEsseen.Certificates.Finite.N75.Assembly
import BerryEsseen.Certificates.Finite.N76.Assembly
import BerryEsseen.Certificates.Finite.N77.Assembly
import BerryEsseen.Certificates.Finite.N78.Assembly
import BerryEsseen.Certificates.Finite.N79.Assembly
import BerryEsseen.Certificates.Finite.N80.Assembly

namespace BerryEsseen
set_option maxRecDepth 10000
theorem bound4395FiniteTargetAwareBatch71_80_checked :
    ∀ n : Fin 81, 71 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 5 = true := by
  intro n hn
  have cases_n : n.val = 71 ∨ n.val = 72 ∨ n.val = 73 ∨ n.val = 74 ∨ n.val = 75 ∨ n.val = 76 ∨ n.val = 77 ∨ n.val = 78 ∨ n.val = 79 ∨ n.val = 80 := by omega
  rcases cases_n with h | h | h | h | h | h | h | h | h | h
  · simpa only [h] using finiteN71_checked
  · simpa only [h] using finiteN72_checked
  · simpa only [h] using finiteN73_checked
  · simpa only [h] using finiteN74_checked
  · simpa only [h] using finiteN75_checked
  · simpa only [h] using finiteN76_checked
  · simpa only [h] using finiteN77_checked
  · simpa only [h] using finiteN78_checked
  · simpa only [h] using finiteN79_checked
  · simpa only [h] using finiteN80_checked

end BerryEsseen
