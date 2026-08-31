import BerryEsseen.Certificate.Finite.Batch
import BerryEsseen.Certificate.Finite.Data.N011
import BerryEsseen.Certificate.Finite.Data.N017
import BerryEsseen.Certificate.Finite.Data.N022
import BerryEsseen.Certificate.Finite.Data.N045
import BerryEsseen.Certificate.Finite.Data.N050
import BerryEsseen.Certificate.Finite.Data.N058
import BerryEsseen.Certificate.Finite.Data.N064
import BerryEsseen.Certificate.Finite.Data.N067
import BerryEsseen.Certificate.Finite.Data.N081
import BerryEsseen.Certificate.Finite.Data.N087
import BerryEsseen.Certificate.Finite.Data.N095
/-!
# Shared-cache finite Route B certificate batch 4

This batch checks 11 concrete finite prefix codes with one canonical
resolution cache. The single native computation is decomposed below into the
individual certificate theorems consumed by the finite-domain assembly.
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def dyadicRouteBFiniteLeafBatch04 : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLeafCodeCertificateWithCache cache 11
    dyadicRouteBLeafCode11 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 17
    dyadicRouteBLeafCode17 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 22
    dyadicRouteBLeafCode22 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 45
    dyadicRouteBLeafCode45 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 50
    dyadicRouteBLeafCode50 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 58
    dyadicRouteBLeafCode58 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 64
    dyadicRouteBLeafCode64 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 67
    dyadicRouteBLeafCode67 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 81
    dyadicRouteBLeafCode81 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 87
    dyadicRouteBLeafCode87 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 95
    dyadicRouteBLeafCode95

theorem dyadicRouteBFiniteLeafBatch04_checked :
    dyadicRouteBFiniteLeafBatch04 = true := by
  native_decide

theorem dyadicRouteBLeafCodeCertificate_n11 :
    dyadicRouteBLeafCodeCertificate 11 dyadicRouteBLeafCode11 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

theorem dyadicRouteBLeafCodeCertificate_n17 :
    dyadicRouteBLeafCodeCertificate 17 dyadicRouteBLeafCode17 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n22 :
    dyadicRouteBLeafCodeCertificate 22 dyadicRouteBLeafCode22 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n45 :
    dyadicRouteBLeafCodeCertificate 45 dyadicRouteBLeafCode45 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n50 :
    dyadicRouteBLeafCodeCertificate 50 dyadicRouteBLeafCode50 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n58 :
    dyadicRouteBLeafCodeCertificate 58 dyadicRouteBLeafCode58 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n64 :
    dyadicRouteBLeafCodeCertificate 64 dyadicRouteBLeafCode64 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n67 :
    dyadicRouteBLeafCodeCertificate 67 dyadicRouteBLeafCode67 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n81 :
    dyadicRouteBLeafCodeCertificate 81 dyadicRouteBLeafCode81 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n87 :
    dyadicRouteBLeafCodeCertificate 87 dyadicRouteBLeafCode87 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem dyadicRouteBLeafCodeCertificate_n95 :
    dyadicRouteBLeafCodeCertificate 95 dyadicRouteBLeafCode95 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch04_checked
  unfold dyadicRouteBFiniteLeafBatch04 at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end BerryEsseen
