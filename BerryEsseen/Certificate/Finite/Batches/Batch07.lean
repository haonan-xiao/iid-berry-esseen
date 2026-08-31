import BerryEsseen.Certificate.Finite.Batch
import BerryEsseen.Certificate.Finite.Data.N013
import BerryEsseen.Certificate.Finite.Data.N016
import BerryEsseen.Certificate.Finite.Data.N020
import BerryEsseen.Certificate.Finite.Data.N029
import BerryEsseen.Certificate.Finite.Data.N040
import BerryEsseen.Certificate.Finite.Data.N057
import BerryEsseen.Certificate.Finite.Data.N066
import BerryEsseen.Certificate.Finite.Data.N068
import BerryEsseen.Certificate.Finite.Data.N072
import BerryEsseen.Certificate.Finite.Data.N084
import BerryEsseen.Certificate.Finite.Data.N090
import BerryEsseen.Certificate.Finite.Data.N092
/-!
# Shared-cache finite Route B certificate batch 7

This batch checks 12 concrete finite prefix codes with one canonical
resolution cache. The single native computation is decomposed below into the
individual certificate theorems consumed by the finite-domain assembly.
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def dyadicRouteBFiniteLeafBatch07 : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLeafCodeCertificateWithCache cache 13
    dyadicRouteBLeafCode13 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 16
    dyadicRouteBLeafCode16 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 20
    dyadicRouteBLeafCode20 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 29
    dyadicRouteBLeafCode29 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 40
    dyadicRouteBLeafCode40 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 57
    dyadicRouteBLeafCode57 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 66
    dyadicRouteBLeafCode66 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 68
    dyadicRouteBLeafCode68 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 72
    dyadicRouteBLeafCode72 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 84
    dyadicRouteBLeafCode84 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 90
    dyadicRouteBLeafCode90 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 92
    dyadicRouteBLeafCode92

theorem dyadicRouteBFiniteLeafBatch07_checked :
    dyadicRouteBFiniteLeafBatch07 = true := by
  native_decide

theorem dyadicRouteBLeafCodeCertificate_n13 :
    dyadicRouteBLeafCodeCertificate 13 dyadicRouteBLeafCode13 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1

theorem dyadicRouteBLeafCodeCertificate_n16 :
    dyadicRouteBLeafCodeCertificate 16 dyadicRouteBLeafCode16 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n20 :
    dyadicRouteBLeafCodeCertificate 20 dyadicRouteBLeafCode20 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n29 :
    dyadicRouteBLeafCodeCertificate 29 dyadicRouteBLeafCode29 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n40 :
    dyadicRouteBLeafCodeCertificate 40 dyadicRouteBLeafCode40 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n57 :
    dyadicRouteBLeafCodeCertificate 57 dyadicRouteBLeafCode57 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n66 :
    dyadicRouteBLeafCodeCertificate 66 dyadicRouteBLeafCode66 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n68 :
    dyadicRouteBLeafCodeCertificate 68 dyadicRouteBLeafCode68 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n72 :
    dyadicRouteBLeafCodeCertificate 72 dyadicRouteBLeafCode72 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n84 :
    dyadicRouteBLeafCodeCertificate 84 dyadicRouteBLeafCode84 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n90 :
    dyadicRouteBLeafCodeCertificate 90 dyadicRouteBLeafCode90 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem dyadicRouteBLeafCodeCertificate_n92 :
    dyadicRouteBLeafCodeCertificate 92 dyadicRouteBLeafCode92 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch07_checked
  unfold dyadicRouteBFiniteLeafBatch07 at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end BerryEsseen
