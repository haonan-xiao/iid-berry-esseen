import BerryEsseen.Certificate.Finite.Batch
import BerryEsseen.Certificate.Finite.Data.N019
import BerryEsseen.Certificate.Finite.Data.N023
import BerryEsseen.Certificate.Finite.Data.N037
import BerryEsseen.Certificate.Finite.Data.N044
import BerryEsseen.Certificate.Finite.Data.N048
import BerryEsseen.Certificate.Finite.Data.N062
import BerryEsseen.Certificate.Finite.Data.N071
import BerryEsseen.Certificate.Finite.Data.N085
import BerryEsseen.Certificate.Finite.Data.N089
import BerryEsseen.Certificate.Finite.Data.N091
import BerryEsseen.Certificate.Finite.Data.N094
/-!
# Shared-cache finite Route B certificate batch 3

This batch checks 11 concrete finite prefix codes with one canonical
resolution cache. The single native computation is decomposed below into the
individual certificate theorems consumed by the finite-domain assembly.
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def dyadicRouteBFiniteLeafBatch03 : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLeafCodeCertificateWithCache cache 19
    dyadicRouteBLeafCode19 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 23
    dyadicRouteBLeafCode23 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 37
    dyadicRouteBLeafCode37 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 44
    dyadicRouteBLeafCode44 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 48
    dyadicRouteBLeafCode48 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 62
    dyadicRouteBLeafCode62 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 71
    dyadicRouteBLeafCode71 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 85
    dyadicRouteBLeafCode85 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 89
    dyadicRouteBLeafCode89 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 91
    dyadicRouteBLeafCode91 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 94
    dyadicRouteBLeafCode94

theorem dyadicRouteBFiniteLeafBatch03_checked :
    dyadicRouteBFiniteLeafBatch03 = true := by
  native_decide

theorem dyadicRouteBLeafCodeCertificate_n19 :
    dyadicRouteBLeafCodeCertificate 19 dyadicRouteBLeafCode19 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

theorem dyadicRouteBLeafCodeCertificate_n23 :
    dyadicRouteBLeafCodeCertificate 23 dyadicRouteBLeafCode23 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n37 :
    dyadicRouteBLeafCodeCertificate 37 dyadicRouteBLeafCode37 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n44 :
    dyadicRouteBLeafCodeCertificate 44 dyadicRouteBLeafCode44 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n48 :
    dyadicRouteBLeafCodeCertificate 48 dyadicRouteBLeafCode48 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n62 :
    dyadicRouteBLeafCodeCertificate 62 dyadicRouteBLeafCode62 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n71 :
    dyadicRouteBLeafCodeCertificate 71 dyadicRouteBLeafCode71 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n85 :
    dyadicRouteBLeafCodeCertificate 85 dyadicRouteBLeafCode85 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n89 :
    dyadicRouteBLeafCodeCertificate 89 dyadicRouteBLeafCode89 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n91 :
    dyadicRouteBLeafCodeCertificate 91 dyadicRouteBLeafCode91 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem dyadicRouteBLeafCodeCertificate_n94 :
    dyadicRouteBLeafCodeCertificate 94 dyadicRouteBLeafCode94 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch03_checked
  unfold dyadicRouteBFiniteLeafBatch03 at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end BerryEsseen
