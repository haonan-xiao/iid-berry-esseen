import BerryEsseen.DyadicPrawitzFiniteLeafBatch
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate24
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate30
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate32
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate33
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate49
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate56
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate73
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate74
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate77
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate86
import BerryEsseen.DyadicPrawitzFiniteLeafCertificate96

/-!
# Shared-cache finite Route B certificate batch 8

This batch checks 11 concrete finite prefix codes with one canonical
resolution cache. The single native computation is decomposed below into the
individual certificate theorems consumed by the finite-domain assembly.
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def dyadicRouteBFiniteLeafBatch08 : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLeafCodeCertificateWithCache cache 24
    dyadicRouteBLeafCode24 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 30
    dyadicRouteBLeafCode30 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 32
    dyadicRouteBLeafCode32 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 33
    dyadicRouteBLeafCode33 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 49
    dyadicRouteBLeafCode49 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 56
    dyadicRouteBLeafCode56 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 73
    dyadicRouteBLeafCode73 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 74
    dyadicRouteBLeafCode74 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 77
    dyadicRouteBLeafCode77 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 86
    dyadicRouteBLeafCode86 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 96
    dyadicRouteBLeafCode96

theorem dyadicRouteBFiniteLeafBatch08_checked :
    dyadicRouteBFiniteLeafBatch08 = true := by
  native_decide

theorem dyadicRouteBLeafCodeCertificate_n24 :
    dyadicRouteBLeafCodeCertificate 24 dyadicRouteBLeafCode24 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

theorem dyadicRouteBLeafCodeCertificate_n30 :
    dyadicRouteBLeafCodeCertificate 30 dyadicRouteBLeafCode30 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n32 :
    dyadicRouteBLeafCodeCertificate 32 dyadicRouteBLeafCode32 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n33 :
    dyadicRouteBLeafCodeCertificate 33 dyadicRouteBLeafCode33 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n49 :
    dyadicRouteBLeafCodeCertificate 49 dyadicRouteBLeafCode49 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n56 :
    dyadicRouteBLeafCodeCertificate 56 dyadicRouteBLeafCode56 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n73 :
    dyadicRouteBLeafCodeCertificate 73 dyadicRouteBLeafCode73 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n74 :
    dyadicRouteBLeafCodeCertificate 74 dyadicRouteBLeafCode74 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n77 :
    dyadicRouteBLeafCodeCertificate 77 dyadicRouteBLeafCode77 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n86 :
    dyadicRouteBLeafCodeCertificate 86 dyadicRouteBLeafCode86 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem dyadicRouteBLeafCodeCertificate_n96 :
    dyadicRouteBLeafCodeCertificate 96 dyadicRouteBLeafCode96 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch08_checked
  unfold dyadicRouteBFiniteLeafBatch08 at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end BerryEsseen
