import BerryEsseen.DyadicPrawitzFiniteLeafBatch
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate18
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate28
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate36
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate42
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate51
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate52
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate54
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate55
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate70
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate82
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate98

/-!
# Shared-cache finite Route B certificate batch 5

This batch checks 11 concrete finite prefix codes with one canonical
resolution cache. The single native computation is decomposed below into the
individual certificate theorems consumed by the finite-domain assembly.
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def dyadicRouteBFiniteLeafBatch05 : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLeafCodeCertificateWithCache cache 18
    dyadicRouteBLeafCode18 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 28
    dyadicRouteBLeafCode28 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 36
    dyadicRouteBLeafCode36 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 42
    dyadicRouteBLeafCode42 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 51
    dyadicRouteBLeafCode51 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 52
    dyadicRouteBLeafCode52 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 54
    dyadicRouteBLeafCode54 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 55
    dyadicRouteBLeafCode55 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 70
    dyadicRouteBLeafCode70 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 82
    dyadicRouteBLeafCode82 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 98
    dyadicRouteBLeafCode98

theorem dyadicRouteBFiniteLeafBatch05_checked :
    dyadicRouteBFiniteLeafBatch05 = true := by
  native_decide

theorem dyadicRouteBLeafCodeCertificate_n18 :
    dyadicRouteBLeafCodeCertificate 18 dyadicRouteBLeafCode18 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

theorem dyadicRouteBLeafCodeCertificate_n28 :
    dyadicRouteBLeafCodeCertificate 28 dyadicRouteBLeafCode28 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n36 :
    dyadicRouteBLeafCodeCertificate 36 dyadicRouteBLeafCode36 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n42 :
    dyadicRouteBLeafCodeCertificate 42 dyadicRouteBLeafCode42 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n51 :
    dyadicRouteBLeafCodeCertificate 51 dyadicRouteBLeafCode51 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n52 :
    dyadicRouteBLeafCodeCertificate 52 dyadicRouteBLeafCode52 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n54 :
    dyadicRouteBLeafCodeCertificate 54 dyadicRouteBLeafCode54 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n55 :
    dyadicRouteBLeafCodeCertificate 55 dyadicRouteBLeafCode55 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n70 :
    dyadicRouteBLeafCodeCertificate 70 dyadicRouteBLeafCode70 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n82 :
    dyadicRouteBLeafCodeCertificate 82 dyadicRouteBLeafCode82 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem dyadicRouteBLeafCodeCertificate_n98 :
    dyadicRouteBLeafCodeCertificate 98 dyadicRouteBLeafCode98 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch05_checked
  unfold dyadicRouteBFiniteLeafBatch05 at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end BerryEsseen
