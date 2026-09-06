import BerryEsseen.Certificates.Finite.N01.Assembly
import BerryEsseen.Certificates.Finite.N02.Assembly
import BerryEsseen.Certificates.Finite.N03.Assembly
import BerryEsseen.Certificates.Finite.N04.Assembly
import BerryEsseen.Certificates.Finite.N05.Assembly
import BerryEsseen.Certificates.Finite.N06.Assembly
import BerryEsseen.Certificates.Finite.N07.Assembly
import BerryEsseen.Certificates.Finite.N08.Assembly
import BerryEsseen.Certificates.Finite.N09.Assembly
import BerryEsseen.Certificates.Finite.N10.Assembly

namespace BerryEsseen
set_option maxRecDepth 10000
theorem bound4395FiniteTargetAwareBatch01_10_checked :
    ∀ n : Fin 11, 1 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 6 = true := by
  intro n hn
  have cases_n : n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨ n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 9 ∨ n.val = 10 := by omega
  rcases cases_n with h | h | h | h | h | h | h | h | h | h
  · simpa only [h] using finiteN01_checked
  · simpa only [h] using finiteN02_checked
  · simpa only [h] using finiteN03_checked
  · simpa only [h] using finiteN04_checked
  · simpa only [h] using finiteN05_checked
  · simpa only [h] using finiteN06_checked
  · simpa only [h] using finiteN07_checked
  · simpa only [h] using finiteN08_checked
  · simpa only [h] using finiteN09_checked
  · simpa only [h] using finiteN10_checked

end BerryEsseen
