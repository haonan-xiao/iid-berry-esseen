import BerryEsseen.Certificates.Finite.N61.Assembly
import BerryEsseen.Certificates.Finite.N62.Assembly
import BerryEsseen.Certificates.Finite.N63.Assembly
import BerryEsseen.Certificates.Finite.N64.Assembly
import BerryEsseen.Certificates.Finite.N65.Assembly
import BerryEsseen.Certificates.Finite.N66.Assembly
import BerryEsseen.Certificates.Finite.N67.Assembly
import BerryEsseen.Certificates.Finite.N68.Assembly
import BerryEsseen.Certificates.Finite.N69.Assembly
import BerryEsseen.Certificates.Finite.N70.Assembly

namespace BerryEsseen
set_option maxRecDepth 10000
theorem bound4395FiniteTargetAwareBatch61_70_checked :
    ∀ n : Fin 71, 61 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 5 = true := by
  intro n hn
  have cases_n : n.val = 61 ∨ n.val = 62 ∨ n.val = 63 ∨ n.val = 64 ∨ n.val = 65 ∨ n.val = 66 ∨ n.val = 67 ∨ n.val = 68 ∨ n.val = 69 ∨ n.val = 70 := by omega
  rcases cases_n with h | h | h | h | h | h | h | h | h | h
  · simpa only [h] using finiteN61_checked
  · simpa only [h] using finiteN62_checked
  · simpa only [h] using finiteN63_checked
  · simpa only [h] using finiteN64_checked
  · simpa only [h] using finiteN65_checked
  · simpa only [h] using finiteN66_checked
  · simpa only [h] using finiteN67_checked
  · simpa only [h] using finiteN68_checked
  · simpa only [h] using finiteN69_checked
  · simpa only [h] using finiteN70_checked

end BerryEsseen
