import BerryEsseen.Certificate.Finite.Batch
import BerryEsseen.Certificate.Finite.Data.N012
import BerryEsseen.Certificate.Finite.Data.N014
import BerryEsseen.Certificate.Finite.Data.N035
import BerryEsseen.Certificate.Finite.Data.N038
import BerryEsseen.Certificate.Finite.Data.N043
import BerryEsseen.Certificate.Finite.Data.N059
import BerryEsseen.Certificate.Finite.Data.N063
import BerryEsseen.Certificate.Finite.Data.N069
import BerryEsseen.Certificate.Finite.Data.N079
import BerryEsseen.Certificate.Finite.Data.N080
import BerryEsseen.Certificate.Finite.Data.N097
/-!
# Shared-cache finite Route B certificate batch 1

This batch checks 11 concrete finite prefix codes with one canonical
resolution cache. The single native computation is decomposed below into the
individual certificate theorems consumed by the finite-domain assembly.
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def dyadicRouteBFiniteLeafBatch01 : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLeafCodeCertificateWithCache cache 12
    dyadicRouteBLeafCode12 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 14
    dyadicRouteBLeafCode14 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 35
    dyadicRouteBLeafCode35 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 38
    dyadicRouteBLeafCode38 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 43
    dyadicRouteBLeafCode43 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 59
    dyadicRouteBLeafCode59 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 63
    dyadicRouteBLeafCode63 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 69
    dyadicRouteBLeafCode69 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 79
    dyadicRouteBLeafCode79 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 80
    dyadicRouteBLeafCode80 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 97
    dyadicRouteBLeafCode97

theorem dyadicRouteBFiniteLeafBatch01_checked :
    dyadicRouteBFiniteLeafBatch01 = true := by
  native_decide

theorem dyadicRouteBLeafCodeCertificate_n12 :
    dyadicRouteBLeafCodeCertificate 12 dyadicRouteBLeafCode12 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

theorem dyadicRouteBLeafCodeCertificate_n14 :
    dyadicRouteBLeafCodeCertificate 14 dyadicRouteBLeafCode14 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n35 :
    dyadicRouteBLeafCodeCertificate 35 dyadicRouteBLeafCode35 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n38 :
    dyadicRouteBLeafCodeCertificate 38 dyadicRouteBLeafCode38 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n43 :
    dyadicRouteBLeafCodeCertificate 43 dyadicRouteBLeafCode43 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n59 :
    dyadicRouteBLeafCodeCertificate 59 dyadicRouteBLeafCode59 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n63 :
    dyadicRouteBLeafCodeCertificate 63 dyadicRouteBLeafCode63 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n69 :
    dyadicRouteBLeafCodeCertificate 69 dyadicRouteBLeafCode69 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n79 :
    dyadicRouteBLeafCodeCertificate 79 dyadicRouteBLeafCode79 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n80 :
    dyadicRouteBLeafCodeCertificate 80 dyadicRouteBLeafCode80 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem dyadicRouteBLeafCodeCertificate_n97 :
    dyadicRouteBLeafCodeCertificate 97 dyadicRouteBLeafCode97 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch01_checked
  unfold dyadicRouteBFiniteLeafBatch01 at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end BerryEsseen
