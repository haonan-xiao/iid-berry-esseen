import BerryEsseen.Certificates.Finite.N21.Assembly
import BerryEsseen.Certificates.Finite.N22.Assembly
import BerryEsseen.Certificates.Finite.N23.Assembly
import BerryEsseen.Certificates.Finite.N24.Assembly
import BerryEsseen.Certificates.Finite.N25.Assembly
import BerryEsseen.Certificates.Finite.N26.Assembly
import BerryEsseen.Certificates.Finite.N27.Assembly
import BerryEsseen.Certificates.Finite.N28.Assembly
import BerryEsseen.Certificates.Finite.N29.Assembly
import BerryEsseen.Certificates.Finite.N30.Assembly

namespace BerryEsseen
set_option maxRecDepth 10000
theorem bound4395FiniteTargetAwareBatch21_30_checked :
    ∀ n : Fin 31, 21 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 5 = true := by
  intro n hn
  have cases_n : n.val = 21 ∨ n.val = 22 ∨ n.val = 23 ∨ n.val = 24 ∨ n.val = 25 ∨ n.val = 26 ∨ n.val = 27 ∨ n.val = 28 ∨ n.val = 29 ∨ n.val = 30 := by omega
  rcases cases_n with h | h | h | h | h | h | h | h | h | h
  · simpa only [h] using finiteN21_checked
  · simpa only [h] using finiteN22_checked
  · simpa only [h] using finiteN23_checked
  · simpa only [h] using finiteN24_checked
  · simpa only [h] using finiteN25_checked
  · simpa only [h] using finiteN26_checked
  · simpa only [h] using finiteN27_checked
  · simpa only [h] using finiteN28_checked
  · simpa only [h] using finiteN29_checked
  · simpa only [h] using finiteN30_checked

end BerryEsseen
