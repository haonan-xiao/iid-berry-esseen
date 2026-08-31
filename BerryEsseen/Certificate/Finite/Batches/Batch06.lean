import BerryEsseen.Certificate.Finite.Batch
import BerryEsseen.Certificate.Finite.Data.N015
import BerryEsseen.Certificate.Finite.Data.N021
import BerryEsseen.Certificate.Finite.Data.N025
import BerryEsseen.Certificate.Finite.Data.N031
import BerryEsseen.Certificate.Finite.Data.N034
import BerryEsseen.Certificate.Finite.Data.N047
import BerryEsseen.Certificate.Finite.Data.N060
import BerryEsseen.Certificate.Finite.Data.N075
import BerryEsseen.Certificate.Finite.Data.N083
import BerryEsseen.Certificate.Finite.Data.N088
import BerryEsseen.Certificate.Finite.Data.N099
/-!
# Shared-cache finite Route B certificate batch 6

This batch checks 11 concrete finite prefix codes with one canonical
resolution cache. The single native computation is decomposed below into the
individual certificate theorems consumed by the finite-domain assembly.
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def dyadicRouteBFiniteLeafBatch06 : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLeafCodeCertificateWithCache cache 15
    dyadicRouteBLeafCode15 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 21
    dyadicRouteBLeafCode21 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 25
    dyadicRouteBLeafCode25 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 31
    dyadicRouteBLeafCode31 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 34
    dyadicRouteBLeafCode34 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 47
    dyadicRouteBLeafCode47 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 60
    dyadicRouteBLeafCode60 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 75
    dyadicRouteBLeafCode75 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 83
    dyadicRouteBLeafCode83 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 88
    dyadicRouteBLeafCode88 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 99
    dyadicRouteBLeafCode99

theorem dyadicRouteBFiniteLeafBatch06_checked :
    dyadicRouteBFiniteLeafBatch06 = true := by
  native_decide

theorem dyadicRouteBLeafCodeCertificate_n15 :
    dyadicRouteBLeafCodeCertificate 15 dyadicRouteBLeafCode15 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

theorem dyadicRouteBLeafCodeCertificate_n21 :
    dyadicRouteBLeafCodeCertificate 21 dyadicRouteBLeafCode21 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n25 :
    dyadicRouteBLeafCodeCertificate 25 dyadicRouteBLeafCode25 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n31 :
    dyadicRouteBLeafCodeCertificate 31 dyadicRouteBLeafCode31 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n34 :
    dyadicRouteBLeafCodeCertificate 34 dyadicRouteBLeafCode34 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n47 :
    dyadicRouteBLeafCodeCertificate 47 dyadicRouteBLeafCode47 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n60 :
    dyadicRouteBLeafCodeCertificate 60 dyadicRouteBLeafCode60 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n75 :
    dyadicRouteBLeafCodeCertificate 75 dyadicRouteBLeafCode75 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n83 :
    dyadicRouteBLeafCodeCertificate 83 dyadicRouteBLeafCode83 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n88 :
    dyadicRouteBLeafCodeCertificate 88 dyadicRouteBLeafCode88 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem dyadicRouteBLeafCodeCertificate_n99 :
    dyadicRouteBLeafCodeCertificate 99 dyadicRouteBLeafCode99 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch06_checked
  unfold dyadicRouteBFiniteLeafBatch06 at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end BerryEsseen
