import BerryEsseen.Certificates.Finite.N91.Assembly
import BerryEsseen.Certificates.Finite.N92.Assembly
import BerryEsseen.Certificates.Finite.N93.Assembly
import BerryEsseen.Certificates.Finite.N94.Assembly
import BerryEsseen.Certificates.Finite.N95.Assembly
import BerryEsseen.Certificates.Finite.N96.Assembly
import BerryEsseen.Certificates.Finite.N97.Assembly
import BerryEsseen.Certificates.Finite.N98.Assembly
import BerryEsseen.Certificates.Finite.N99.Assembly

namespace BerryEsseen
set_option maxRecDepth 10000
theorem bound4395FiniteTargetAwareBatch91_99_checked :
    ∀ n : Fin 100, 91 ≤ n.val →
      bound4395OldFiniteTargetAwareLeafCodeCertificate n.val 5 = true := by
  intro n hn
  have cases_n : n.val = 91 ∨ n.val = 92 ∨ n.val = 93 ∨ n.val = 94 ∨ n.val = 95 ∨ n.val = 96 ∨ n.val = 97 ∨ n.val = 98 ∨ n.val = 99 := by omega
  rcases cases_n with h | h | h | h | h | h | h | h | h
  · simpa only [h] using finiteN91_checked
  · simpa only [h] using finiteN92_checked
  · simpa only [h] using finiteN93_checked
  · simpa only [h] using finiteN94_checked
  · simpa only [h] using finiteN95_checked
  · simpa only [h] using finiteN96_checked
  · simpa only [h] using finiteN97_checked
  · simpa only [h] using finiteN98_checked
  · simpa only [h] using finiteN99_checked

end BerryEsseen
