import BerryEsseen.Certificate.Finite.Batch
import BerryEsseen.Certificate.Finite.Data.N026
import BerryEsseen.Certificate.Finite.Data.N027
import BerryEsseen.Certificate.Finite.Data.N039
import BerryEsseen.Certificate.Finite.Data.N041
import BerryEsseen.Certificate.Finite.Data.N046
import BerryEsseen.Certificate.Finite.Data.N053
import BerryEsseen.Certificate.Finite.Data.N061
import BerryEsseen.Certificate.Finite.Data.N065
import BerryEsseen.Certificate.Finite.Data.N076
import BerryEsseen.Certificate.Finite.Data.N078
import BerryEsseen.Certificate.Finite.Data.N093
/-!
# Shared-cache finite Route B certificate batch 2

This batch checks 11 concrete finite prefix codes with one canonical
resolution cache. The single native computation is decomposed below into the
individual certificate theorems consumed by the finite-domain assembly.
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def dyadicRouteBFiniteLeafBatch02 : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBLeafCodeCertificateWithCache cache 26
    dyadicRouteBLeafCode26 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 27
    dyadicRouteBLeafCode27 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 39
    dyadicRouteBLeafCode39 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 41
    dyadicRouteBLeafCode41 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 46
    dyadicRouteBLeafCode46 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 53
    dyadicRouteBLeafCode53 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 61
    dyadicRouteBLeafCode61 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 65
    dyadicRouteBLeafCode65 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 76
    dyadicRouteBLeafCode76 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 78
    dyadicRouteBLeafCode78 &&
  dyadicRouteBLeafCodeCertificateWithCache cache 93
    dyadicRouteBLeafCode93

theorem dyadicRouteBFiniteLeafBatch02_checked :
    dyadicRouteBFiniteLeafBatch02 = true := by
  native_decide

theorem dyadicRouteBLeafCodeCertificate_n26 :
    dyadicRouteBLeafCodeCertificate 26 dyadicRouteBLeafCode26 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

theorem dyadicRouteBLeafCodeCertificate_n27 :
    dyadicRouteBLeafCodeCertificate 27 dyadicRouteBLeafCode27 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n39 :
    dyadicRouteBLeafCodeCertificate 39 dyadicRouteBLeafCode39 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n41 :
    dyadicRouteBLeafCodeCertificate 41 dyadicRouteBLeafCode41 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n46 :
    dyadicRouteBLeafCodeCertificate 46 dyadicRouteBLeafCode46 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n53 :
    dyadicRouteBLeafCodeCertificate 53 dyadicRouteBLeafCode53 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n61 :
    dyadicRouteBLeafCodeCertificate 61 dyadicRouteBLeafCode61 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n65 :
    dyadicRouteBLeafCodeCertificate 65 dyadicRouteBLeafCode65 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n76 :
    dyadicRouteBLeafCodeCertificate 76 dyadicRouteBLeafCode76 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem dyadicRouteBLeafCodeCertificate_n78 :
    dyadicRouteBLeafCodeCertificate 78 dyadicRouteBLeafCode78 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem dyadicRouteBLeafCodeCertificate_n93 :
    dyadicRouteBLeafCodeCertificate 93 dyadicRouteBLeafCode93 = true := by
  rw [← dyadicRouteBLeafCodeCertificateWithCanonicalCache_eq]
  have h := dyadicRouteBFiniteLeafBatch02_checked
  unfold dyadicRouteBFiniteLeafBatch02 at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end BerryEsseen
