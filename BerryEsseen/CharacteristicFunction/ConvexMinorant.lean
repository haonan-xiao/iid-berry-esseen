import BerryEsseen.CharacteristicFunction.SineCircle
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Piecewise
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The Route B convex minorant and modulus reduction

This module begins Route B equations (3.3)--(3.5).  The finite verification
which locates the breakpoint and checks the derivative signs is kept separate
from the analytic reduction.  The results below first expose the exact
minorant interface and then prove the size-biased Jensen argument used by the
characteristic-function modulus bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real Topology

namespace BerryEsseen

noncomputable section

/-- The trigonometric quotient majorized by Route B's convex minorant.  The
value at zero is its continuous extension. -/
def cosineQuotient (v : ℝ) : ℝ :=
  if v = 0 then (1 : ℝ) / 2 else (1 - Real.cos v) / v ^ 2

/-- The positive-frequency formula `(1-cos v)/v^2`. -/
def routeBPsi (v : ℝ) : ℝ :=
  (1 - Real.cos v) / v ^ 2

/-- Route B equation (3.3), parameterized by the certified slope `kappa` and
breakpoint `theta`. -/
def routeBMinorant (kappa theta v : ℝ) : ℝ :=
  if v ≤ theta then (1 : ℝ) / 2 - kappa * v
  else if v ≤ 2 * Real.pi then routeBPsi v
  else 0

/-- The middle piece continued by its horizontal tangent at `2*pi`. -/
def routeBRightMinorant (v : ℝ) : ℝ :=
  if v ≤ 2 * Real.pi then routeBPsi v else 0

/-- The exact analytic facts delivered by Route B's breakpoint and
derivative-sign verification. `BreakpointCertificate.lean` constructs this
proposition for the exact maximizing breakpoint and slope. -/
structure RouteBMinorantCertificate (kappa theta : ℝ) : Prop where
  theta_pos : 0 < theta
  theta_lt_two_pi : theta < 2 * Real.pi
  kappa_nonneg : 0 ≤ kappa
  line_minorant : ∀ v : ℝ, 0 < v → (1 : ℝ) / 2 - kappa * v ≤ routeBPsi v
  match_theta : routeBPsi theta = (1 : ℝ) / 2 - kappa * theta
  psi_convex : ConvexOn ℝ (Set.Icc theta (2 * Real.pi)) routeBPsi
  psi_antitone : AntitoneOn routeBPsi (Set.Icc theta (2 * Real.pi))
  psi_add_linear_monotone :
    MonotoneOn (fun v => routeBPsi v + kappa * v)
      (Set.Icc theta (2 * Real.pi))

/-- The analytic interface supplied by the breakpoint/derivative certificate.
It records exactly the properties of (3.3) consumed later in Route B. -/
structure RouteBMinorantSpec (q : ℝ → ℝ) : Prop where
  convexOn_nonnegative : ConvexOn ℝ (Set.Ici 0) q
  continuousOn_nonnegative : ContinuousOn q (Set.Ici 0)
  antitoneOn_nonnegative : AntitoneOn q (Set.Ici 0)
  minorant : ∀ v : ℝ, 0 < v → q v ≤ (1 - Real.cos v) / v ^ 2
  measurable : Measurable q
  abs_le_half : ∀ v : ℝ, 0 ≤ v → |q v| ≤ (1 : ℝ) / 2

/-- A localized version of the standard convex-piecewise gluing lemma.  It is
used twice: first at `2*pi`, then at the certified breakpoint. -/
theorem convexOn_Ici_piecewise_Iic_of_antitoneOn_Icc_monotoneOn_Ici
    {a e : ℝ} {f g : ℝ → ℝ} (hae : a ≤ e)
    (hf : ConvexOn ℝ (Set.Icc a e) f)
    (hg : ConvexOn ℝ (Set.Ici e) g)
    (hanti : AntitoneOn f (Set.Icc a e))
    (hmono : MonotoneOn g (Set.Ici e))
    (heq : f e = g e) :
    ConvexOn ℝ (Set.Ici a) ((Set.Iic e).piecewise f g) := by
  refine ⟨convex_Ici a, fun x hx y hy c d hc hd hcd => ?_⟩
  have hcombo_a : a ≤ c • x + d • y :=
    (convex_Ici a) hx hy hc hd hcd
  obtain hxe | hxe := le_or_gt x e <;> obtain hye | hye := le_or_gt y e
  · have hcombo_e : c • x + d • y ≤ e :=
      (Convex.combo_le_max x y hc hd hcd).trans (max_le hxe hye)
    rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hxe,
      Set.piecewise_eq_of_mem (Set.Iic e) f g hye,
      Set.piecewise_eq_of_mem (Set.Iic e) f g hcombo_e]
    exact hf.2 ⟨hx, hxe⟩ ⟨hy, hye⟩ hc hd hcd
  · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hxe,
      Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hye)]
    obtain hcombo_e | hcombo_e := le_or_gt (c • x + d • y) e
    · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hcombo_e]
      have hmove : c • x + d • e ≤ c • x + d • y := by gcongr
      have hleft_a : a ≤ c • x + d • e :=
        (convex_Ici a) hx hae hc hd hcd
      trans c • f x + d • f e
      · exact (hanti ⟨hleft_a, hmove.trans hcombo_e⟩ ⟨hcombo_a, hcombo_e⟩ hmove).trans
          (hf.2 ⟨hx, hxe⟩ ⟨hae, le_rfl⟩ hc hd hcd)
      · rw [heq]
        gcongr
        exact hmono Set.self_mem_Ici hye.le hye.le
    · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g
        (Set.notMem_Iic.mpr hcombo_e)]
      have hmove : c • x + d • y ≤ c • e + d • y := by gcongr
      trans c • g e + d • g y
      · exact (hmono hcombo_e.le (hcombo_e.le.trans hmove) hmove).trans
          (hg.2 Set.self_mem_Ici hye.le hc hd hcd)
      · rw [← heq]
        gcongr
        exact hanti ⟨hx, hxe⟩ ⟨hae, le_rfl⟩ hxe
  · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hxe),
      Set.piecewise_eq_of_mem (Set.Iic e) f g hye]
    obtain hcombo_e | hcombo_e := le_or_gt (c • x + d • y) e
    · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hcombo_e]
      have hmove : c • e + d • y ≤ c • x + d • y := by gcongr
      have hleft_a : a ≤ c • e + d • y :=
        (convex_Ici a) hae hy hc hd hcd
      trans c • f e + d • f y
      · exact (hanti ⟨hleft_a, hmove.trans hcombo_e⟩ ⟨hcombo_a, hcombo_e⟩ hmove).trans
          (hf.2 ⟨hae, le_rfl⟩ ⟨hy, hye⟩ hc hd hcd)
      · rw [heq]
        gcongr
        exact hmono Set.self_mem_Ici hxe.le hxe.le
    · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g
        (Set.notMem_Iic.mpr hcombo_e)]
      have hmove : c • x + d • y ≤ c • x + d • e := by gcongr
      trans c • g x + d • g e
      · exact (hmono hcombo_e.le (hcombo_e.le.trans hmove) hmove).trans
          (hg.2 hxe.le Set.self_mem_Ici hc hd hcd)
      · rw [← heq]
        gcongr
        exact hanti ⟨hy, hye⟩ ⟨hae, le_rfl⟩ hye
  · have hcombo_e : e < c • x + d • y :=
      (lt_min hxe hye).trans_le (Convex.min_le_combo x y hc hd hcd)
    rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hxe),
      Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hye),
      Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hcombo_e)]
    exact hg.2 hxe.le hye.le hc hd hcd

/-- Antitonicity glues across a breakpoint when the two pieces agree there. -/
theorem antitoneOn_Ici_piecewise_Iic_of_antitoneOn_Icc_antitoneOn_Ici
    {a e : ℝ} {f g : ℝ → ℝ} (hae : a ≤ e)
    (hf : AntitoneOn f (Set.Icc a e))
    (hg : AntitoneOn g (Set.Ici e))
    (heq : f e = g e) :
    AntitoneOn ((Set.Iic e).piecewise f g) (Set.Ici a) := by
  intro x hx y hy hxy
  by_cases hye : y ≤ e
  · have hxe : x ≤ e := hxy.trans hye
    rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hxe,
      Set.piecewise_eq_of_mem (Set.Iic e) f g hye]
    exact hf ⟨hx, hxe⟩ ⟨hy, hye⟩ hxy
  · have hey : e ≤ y := (lt_of_not_ge hye).le
    rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g hye]
    by_cases hxe : x ≤ e
    · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hxe]
      calc
        g y ≤ g e := hg Set.self_mem_Ici hey hey
        _ = f e := heq.symm
        _ ≤ f x := hf ⟨hx, hxe⟩ ⟨hae, le_rfl⟩ hxe
    · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g hxe]
      exact hg (lt_of_not_ge hxe).le hey hxy

@[simp] theorem routeBPsi_two_pi : routeBPsi (2 * Real.pi) = 0 := by
  simp [routeBPsi]

theorem routeBRightMinorant_convexOn {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    ConvexOn ℝ (Set.Ici theta) routeBRightMinorant := by
  have h := convexOn_Ici_piecewise_Iic_of_antitoneOn_Icc_monotoneOn_Ici
    hcert.theta_lt_two_pi.le hcert.psi_convex
    (convexOn_const 0 (convex_Ici (2 * Real.pi))) hcert.psi_antitone
    (monotoneOn_const : MonotoneOn (fun _v : ℝ => (0 : ℝ)) (Set.Ici (2 * Real.pi)))
    routeBPsi_two_pi
  simpa only [routeBRightMinorant, Set.piecewise, Set.mem_Iic] using h

theorem routeBRightMinorant_antitoneOn {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    AntitoneOn routeBRightMinorant (Set.Ici theta) := by
  have h := antitoneOn_Ici_piecewise_Iic_of_antitoneOn_Icc_antitoneOn_Ici
    hcert.theta_lt_two_pi.le hcert.psi_antitone
    (antitoneOn_const : AntitoneOn (fun _v : ℝ => (0 : ℝ)) (Set.Ici (2 * Real.pi)))
    routeBPsi_two_pi
  simpa only [routeBRightMinorant, Set.piecewise, Set.mem_Iic] using h

theorem routeBRightMinorant_add_linear_monotoneOn {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    MonotoneOn (fun v => routeBRightMinorant v + kappa * v) (Set.Ici theta) := by
  intro x hx y hy hxy
  by_cases hyend : y ≤ 2 * Real.pi
  · have hxend : x ≤ 2 * Real.pi := hxy.trans hyend
    simpa only [routeBRightMinorant, if_pos hxend, if_pos hyend] using
      hcert.psi_add_linear_monotone ⟨hx, hxend⟩ ⟨hy, hyend⟩ hxy
  · have hendy : 2 * Real.pi ≤ y := (lt_of_not_ge hyend).le
    by_cases hxend : x ≤ 2 * Real.pi
    · have hmid := hcert.psi_add_linear_monotone
        ⟨hx, hxend⟩ ⟨hcert.theta_lt_two_pi.le, le_rfl⟩ hxend
      have htail : kappa * (2 * Real.pi) ≤ kappa * y :=
        mul_le_mul_of_nonneg_left hendy hcert.kappa_nonneg
      simp only [routeBRightMinorant, if_pos hxend, if_neg hyend]
      change routeBPsi x + kappa * x ≤
        routeBPsi (2 * Real.pi) + kappa * (2 * Real.pi) at hmid
      rw [routeBPsi_two_pi] at hmid
      linarith
    · have hxright : 2 * Real.pi ≤ x := (lt_of_not_ge hxend).le
      simp only [routeBRightMinorant, if_neg hxend, if_neg hyend, zero_add]
      exact mul_le_mul_of_nonneg_left hxy hcert.kappa_nonneg

theorem routeBRightMinorant_add_linear_convexOn {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    ConvexOn ℝ (Set.Ici theta)
      (fun v => routeBRightMinorant v + kappa * v) := by
  have hlinear : ConvexOn ℝ (Set.Ici theta) (fun v : ℝ => kappa * v) := by
    have h := (convexOn_id (convex_Ici theta)).smul hcert.kappa_nonneg
    simpa only [id_eq, smul_eq_mul] using h
  have hsum := (routeBRightMinorant_convexOn hcert).add hlinear
  simpa only [Pi.add_apply] using hsum

theorem routeBMinorant_convexOn {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    ConvexOn ℝ (Set.Ici 0) (routeBMinorant kappa theta) := by
  have htheta : 0 ≤ theta := hcert.theta_pos.le
  have hmatch : (1 : ℝ) / 2 =
      routeBRightMinorant theta + kappa * theta := by
    rw [show routeBRightMinorant theta = routeBPsi theta by
      simp [routeBRightMinorant, hcert.theta_lt_two_pi.le]]
    rw [hcert.match_theta]
    ring
  have hadjustedPiece : ConvexOn ℝ (Set.Ici 0)
      ((Set.Iic theta).piecewise (fun _v : ℝ => (1 : ℝ) / 2)
        (fun v => routeBRightMinorant v + kappa * v)) :=
    convexOn_Ici_piecewise_Iic_of_antitoneOn_Icc_monotoneOn_Ici htheta
      (convexOn_const ((1 : ℝ) / 2) (convex_Icc 0 theta))
      (routeBRightMinorant_add_linear_convexOn hcert)
      (antitoneOn_const : AntitoneOn (fun _v : ℝ => (1 : ℝ) / 2) (Set.Icc 0 theta))
      (routeBRightMinorant_add_linear_monotoneOn hcert) hmatch
  have hadjusted : ConvexOn ℝ (Set.Ici 0)
      (fun v => routeBMinorant kappa theta v + kappa * v) := by
    apply hadjustedPiece.congr
    intro v hv
    by_cases hvt : v ≤ theta
    · simp [Set.piecewise, routeBMinorant, hvt]
    · simp [Set.piecewise, routeBMinorant, routeBRightMinorant, hvt]
  have hlinearConcave : ConcaveOn ℝ (Set.Ici 0) (fun v : ℝ => kappa * v) := by
    have h := (concaveOn_id (convex_Ici (0 : ℝ))).smul hcert.kappa_nonneg
    simpa only [id_eq, smul_eq_mul] using h
  have hsub := hadjusted.sub hlinearConcave
  apply hsub.congr
  intro v hv
  simp only [Pi.sub_apply]
  ring

theorem routeBMinorant_antitoneOn {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    AntitoneOn (routeBMinorant kappa theta) (Set.Ici 0) := by
  have htheta : 0 ≤ theta := hcert.theta_pos.le
  have hline : AntitoneOn (fun v : ℝ => (1 : ℝ) / 2 - kappa * v)
      (Set.Icc 0 theta) := by
    intro x hx y hy hxy
    have hmul := mul_le_mul_of_nonneg_left hxy hcert.kappa_nonneg
    dsimp
    linarith
  have hmatch : (1 : ℝ) / 2 - kappa * theta = routeBRightMinorant theta := by
    rw [show routeBRightMinorant theta = routeBPsi theta by
      simp [routeBRightMinorant, hcert.theta_lt_two_pi.le], hcert.match_theta]
  have hpiece := antitoneOn_Ici_piecewise_Iic_of_antitoneOn_Icc_antitoneOn_Ici
    htheta hline (routeBRightMinorant_antitoneOn hcert) hmatch
  apply hpiece.congr
  intro v hv
  by_cases hvt : v ≤ theta
  · simp [Set.piecewise, routeBMinorant, hvt]
  · simp [Set.piecewise, routeBMinorant, routeBRightMinorant, hvt]

theorem routeBMinorant_measurable (kappa theta : ℝ) :
    Measurable (routeBMinorant kappa theta) := by
  unfold routeBMinorant routeBPsi
  refine Measurable.ite measurableSet_Iic ?_ ?_
  · fun_prop
  · refine Measurable.ite measurableSet_Iic ?_ measurable_const
    fun_prop

theorem routeBMinorant_continuousOn {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    ContinuousOn (routeBMinorant kappa theta) (Set.Ici 0) := by
  have hInterior : ContinuousOn (routeBMinorant kappa theta) (Set.Ioi 0) := by
    simpa only [interior_Ici] using
      (routeBMinorant_convexOn hcert).continuousOn_interior
  intro v hv
  by_cases hvzero : v = 0
  · subst v
    let L : ℝ → ℝ := fun w => (1 : ℝ) / 2 - kappa * w
    have hL : ContinuousWithinAt L (Set.Ici 0) 0 := by
      apply Continuous.continuousWithinAt
      dsimp [L]
      fun_prop
    have hevent : routeBMinorant kappa theta =ᶠ[𝓝[Set.Ici 0] (0 : ℝ)] L := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds hcert.theta_pos)] with w hw
      have hwle : w ≤ theta := le_of_lt hw
      simp [routeBMinorant, L, hwle]
    exact hL.congr_of_eventuallyEq hevent (by
      simp [routeBMinorant, L, hcert.theta_pos.le])
  · have hvpos : v ∈ Set.Ioi (0 : ℝ) := lt_of_le_of_ne hv (Ne.symm hvzero)
    exact ((isOpen_Ioi.continuousOn_iff.mp hInterior) hvpos).continuousWithinAt

theorem routeBMinorant_minorant {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    ∀ v : ℝ, 0 < v →
      routeBMinorant kappa theta v ≤ (1 - Real.cos v) / v ^ 2 := by
  intro v hv
  by_cases hvt : v ≤ theta
  · simpa only [routeBMinorant, if_pos hvt, routeBPsi] using
      hcert.line_minorant v hv
  · by_cases hvend : v ≤ 2 * Real.pi
    · simp only [routeBMinorant, if_neg hvt, if_pos hvend, routeBPsi]
      exact le_rfl
    · simp only [routeBMinorant, if_neg hvt, if_neg hvend]
      exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one v)) (sq_nonneg v)

/-- The Route B minorant is nonnegative on the nonnegative half-line. -/
theorem routeBMinorant_nonneg {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    ∀ v : ℝ, 0 ≤ v → 0 ≤ routeBMinorant kappa theta v := by
  intro v hv
  by_cases hvt : v ≤ theta
  · have hpsiTheta : 0 ≤ routeBPsi theta := by
      exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one theta)) (sq_nonneg theta)
    have hlineTheta : 0 ≤ (1 : ℝ) / 2 - kappa * theta := by
      rw [← hcert.match_theta]
      exact hpsiTheta
    have hmul : kappa * v ≤ kappa * theta :=
      mul_le_mul_of_nonneg_left hvt hcert.kappa_nonneg
    simp only [routeBMinorant, if_pos hvt]
    linarith
  · by_cases hvend : v ≤ 2 * Real.pi
    · simp only [routeBMinorant, if_neg hvt, if_pos hvend]
      exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one v)) (sq_nonneg v)
    · simp [routeBMinorant, hvt, hvend]

theorem routeBMinorant_abs_le_half {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    ∀ v : ℝ, 0 ≤ v → |routeBMinorant kappa theta v| ≤ (1 : ℝ) / 2 := by
  intro v hv
  have hupper : routeBMinorant kappa theta v ≤ (1 : ℝ) / 2 := by
    have hanti := routeBMinorant_antitoneOn hcert
      (show (0 : ℝ) ∈ Set.Ici 0 by simp) hv hv
    simpa [routeBMinorant, hcert.theta_pos.le] using hanti
  have hlower : 0 ≤ routeBMinorant kappa theta v :=
    routeBMinorant_nonneg hcert v hv
  rw [abs_of_nonneg hlower]
  exact hupper

/-- The explicit Route B minorant satisfies the complete analytic interface as
soon as the finite breakpoint/derivative certificate has been checked. -/
theorem routeBMinorant_spec_of_certificate {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) :
    RouteBMinorantSpec (routeBMinorant kappa theta) where
  convexOn_nonnegative := routeBMinorant_convexOn hcert
  continuousOn_nonnegative := routeBMinorant_continuousOn hcert
  antitoneOn_nonnegative := routeBMinorant_antitoneOn hcert
  minorant := routeBMinorant_minorant hcert
  measurable := routeBMinorant_measurable kappa theta
  abs_le_half := routeBMinorant_abs_le_half hcert

/-- Multiplying the minorant inequality by the size-biasing factor removes its
apparent singularity at zero. -/
theorem weighted_minorant_le_cosine_loss {q : ℝ → ℝ}
    (hminorant : ∀ v : ℝ, 0 < v → q v ≤ (1 - Real.cos v) / v ^ 2)
    (u d : ℝ) :
    u ^ 2 * d ^ 2 * q (|u| * |d|) ≤ 1 - Real.cos (u * d) := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hd : d = 0
  · simp [hd]
  let v := |u| * |d|
  have hv : 0 < v := mul_pos (abs_pos.mpr hu) (abs_pos.mpr hd)
  have h := hminorant v hv
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg v)
  have hvne : v ^ 2 ≠ 0 := pow_ne_zero 2 hv.ne'
  have hcancel : v ^ 2 * ((1 - Real.cos v) / v ^ 2) = 1 - Real.cos v := by
    field_simp
  have hv_sq : v ^ 2 = u ^ 2 * d ^ 2 := by
    dsimp [v]
    rw [mul_pow, sq_abs, sq_abs]
  have hcos : Real.cos v = Real.cos (u * d) := by
    dsimp [v]
    rw [← abs_mul, Real.cos_abs]
  rw [hcancel, hv_sq, hcos] at hmul
  simpa [mul_assoc] using hmul

/-- The squared modulus of a characteristic function is the cosine transform
of the difference of two independent copies. -/
theorem norm_charFun_sq_eq_integral_cos_sub (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (u : ℝ) :
    ‖charFun mu u‖ ^ 2 =
      ∫ p : ℝ × ℝ, Real.cos (u * (p.1 - p.2)) ∂mu.prod mu := by
  let F : ℝ → ℂ := fun x => Complex.exp ((u * x : ℝ) * Complex.I)
  let G : ℝ → ℂ := fun y => Complex.exp (((-u) * y : ℝ) * Complex.I)
  let H : ℝ × ℝ → ℂ := fun p =>
    Complex.exp ((u * (p.1 - p.2) : ℝ) * Complex.I)
  have hcomplex :
      ((‖charFun mu u‖ ^ 2 : ℝ) : ℂ) = ∫ p, H p ∂mu.prod mu := by
    calc
      ((‖charFun mu u‖ ^ 2 : ℝ) : ℂ) =
          charFun mu u * starRingEnd ℂ (charFun mu u) := by
            simpa using (Complex.mul_conj' (charFun mu u)).symm
      _ = charFun mu u * charFun mu (-u) := by rw [charFun_neg]
      _ = (∫ x, F x ∂mu) * ∫ y, G y ∂mu := by
        rw [charFun_apply_real, charFun_apply_real]
        congr 1
        · apply integral_congr_ae
          exact ae_of_all _ fun x => by
            dsimp [F]
            congr 1
            push_cast
            ring
        · apply integral_congr_ae
          exact ae_of_all _ fun y => by
            dsimp [G]
            congr 1
            push_cast
            ring
      _ = ∫ p, F p.1 * G p.2 ∂mu.prod mu := by
        exact (integral_prod_mul F G).symm
      _ = ∫ p, H p ∂mu.prod mu := by
        apply integral_congr_ae
        exact ae_of_all _ fun p => by
          dsimp [F, G, H]
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
  have hH_integrable : Integrable H (mu.prod mu) := by
    have hOne : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) (mu.prod mu) := integrable_const 1
    refine hOne.mono' (by fun_prop) ?_
    exact ae_of_all _ fun p => by
      dsimp [H]
      exact (Complex.norm_exp_ofReal_mul_I (u * (p.1 - p.2))).le
  calc
    ‖charFun mu u‖ ^ 2 =
        Complex.re (((‖charFun mu u‖ ^ 2 : ℝ) : ℂ)) := by simp [pow_two]
    _ = Complex.re (∫ p, H p ∂mu.prod mu) := congrArg Complex.re hcomplex
    _ = ∫ p, Complex.re (H p) ∂mu.prod mu := by
      rw [← RCLike.re_eq_complex_re]
      exact (integral_re hH_integrable).symm
    _ = ∫ p, Real.cos (u * (p.1 - p.2)) ∂mu.prod mu := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by
        change (H p).re = Real.cos (u * (p.1 - p.2))
        dsimp [H]
        simpa using Complex.exp_ofReal_mul_I_re (u * (p.1 - p.2))

/-- Integral form of the preceding identity, matching the left side of the
size-biased Jensen calculation in the source proof. -/
theorem integral_one_sub_cos_sub_eq_one_sub_norm_charFun_sq
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (u : ℝ) :
    (∫ p : ℝ × ℝ, 1 - Real.cos (u * (p.1 - p.2)) ∂mu.prod mu) =
      1 - ‖charFun mu u‖ ^ 2 := by
  have hcos : Integrable
      (fun p : ℝ × ℝ => Real.cos (u * (p.1 - p.2))) (mu.prod mu) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs, norm_one] using Real.abs_cos_le_one (u * (p.1 - p.2))
  rw [integral_sub (integrable_const 1) hcos,
    norm_charFun_sq_eq_integral_cos_sub]
  simp

/-- The density `D²/2` used to size-bias the difference `D = X-X'`.
It is `NNReal`-valued so nonnegativity is carried by the type. -/
def differenceSquareWeight (p : ℝ × ℝ) : ℝ≥0 :=
  ⟨(p.1 - p.2) ^ 2 / 2, by positivity⟩

/-- The probability measure `D² dP / 2` from the source proof.  It becomes a
probability measure under the centered variance-one hypotheses below. -/
def differenceSizeBiasedMeasure (mu : Measure ℝ) : Measure (ℝ × ℝ) :=
  (mu.prod mu).withDensity fun p => (differenceSquareWeight p : ℝ≥0∞)

theorem measurable_differenceSquareWeight : Measurable differenceSquareWeight := by
  apply Measurable.subtype_mk
  fun_prop

theorem integrable_difference_sq (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (mu.prod mu) := by
  have hfirst : MemLp (fun p : ℝ × ℝ => p.1) 3 (mu.prod mu) := by
    simpa only [id_eq] using hX.comp_fst mu
  have hsecond : MemLp (fun p : ℝ × ℝ => p.2) 3 (mu.prod mu) := by
    simpa only [id_eq] using hX.comp_snd mu
  exact ((hfirst.sub hsecond).mono_exponent (by norm_num)).integrable_sq

/-- For two independent centered variance-one copies, `E(X-X')² = 2`. -/
theorem integral_difference_sq_eq_two (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂mu.prod mu) = 2 := by
  have hId : Integrable (id : ℝ → ℝ) mu := hX.integrable (by norm_num)
  have hSq : Integrable (fun x : ℝ => x ^ 2) mu :=
    (hX.mono_exponent (by norm_num)).integrable_sq
  have hfstSq : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (mu.prod mu) := by
    simpa only using hSq.comp_fst mu
  have hsndSq : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (mu.prod mu) := by
    simpa only using hSq.comp_snd mu
  have hcross : Integrable (fun p : ℝ × ℝ => p.1 * p.2) (mu.prod mu) := by
    simpa only [id_eq] using hId.mul_prod hId
  have hfstIntegral : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂mu.prod mu) = 1 := by
    have hprod := integral_prod_mul (μ := mu) (ν := mu)
      (fun x : ℝ => x ^ 2) (fun _x : ℝ => (1 : ℝ))
    simpa only [mul_one, integral_const, probReal_univ, one_smul, hsecond] using hprod
  have hsndIntegral : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂mu.prod mu) = 1 := by
    have hprod := integral_prod_mul (μ := mu) (ν := mu)
      (fun _x : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 2)
    simpa only [one_mul, integral_const, probReal_univ, one_smul, hsecond] using hprod
  have hcrossIntegral : (∫ p : ℝ × ℝ, p.1 * p.2 ∂mu.prod mu) = 0 := by
    have hprod := integral_prod_mul (μ := mu) (ν := mu) id id
    simpa only [id_eq, hmean, zero_mul] using hprod
  calc
    (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂mu.prod mu) =
        ∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 - 2 * (p.1 * p.2) ∂mu.prod mu := by
          apply integral_congr_ae
          exact ae_of_all _ fun p => by ring
    _ = (∫ p : ℝ × ℝ, p.1 ^ 2 ∂mu.prod mu) +
          (∫ p : ℝ × ℝ, p.2 ^ 2 ∂mu.prod mu) -
          2 * ∫ p : ℝ × ℝ, p.1 * p.2 ∂mu.prod mu := by
          calc
            (∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 - 2 * (p.1 * p.2) ∂mu.prod mu) =
                (∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 ∂mu.prod mu) -
                  ∫ p : ℝ × ℝ, 2 * (p.1 * p.2) ∂mu.prod mu := by
                    exact integral_sub (hfstSq.add hsndSq) (hcross.const_mul 2)
            _ = (∫ p : ℝ × ℝ, p.1 ^ 2 ∂mu.prod mu) +
                  (∫ p : ℝ × ℝ, p.2 ^ 2 ∂mu.prod mu) -
                  2 * ∫ p : ℝ × ℝ, p.1 * p.2 ∂mu.prod mu := by
                    rw [integral_add hfstSq hsndSq, integral_const_mul]
    _ = 2 := by rw [hfstIntegral, hsndIntegral, hcrossIntegral]; norm_num

theorem integrable_differenceSquareWeight_real
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun p : ℝ × ℝ => (differenceSquareWeight p : ℝ)) (mu.prod mu) := by
  have h := (integrable_difference_sq mu hX).div_const 2
  simpa only [differenceSquareWeight, NNReal.coe_mk] using h

theorem integral_differenceSquareWeight_eq_one
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    (∫ p : ℝ × ℝ, (differenceSquareWeight p : ℝ) ∂mu.prod mu) = 1 := by
  change (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 / 2 ∂mu.prod mu) = 1
  rw [integral_div, integral_difference_sq_eq_two mu hX hmean hsecond]
  norm_num

theorem isProbabilityMeasure_differenceSizeBiasedMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    IsProbabilityMeasure (differenceSizeBiasedMeasure mu) := by
  rw [isProbabilityMeasure_iff]
  unfold differenceSizeBiasedMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_coe_eq_integral differenceSquareWeight
      (integrable_differenceSquareWeight_real mu hX),
    integral_differenceSquareWeight_eq_one mu hX hmean hsecond]
  norm_num

/-- Integration against the size-biased law is weighted integration against
the product law. -/
theorem integral_differenceSizeBiasedMeasure (mu : Measure ℝ)
    (g : ℝ × ℝ → ℝ) :
    (∫ p, g p ∂differenceSizeBiasedMeasure mu) =
      ∫ p, (differenceSquareWeight p : ℝ) * g p ∂mu.prod mu := by
  unfold differenceSizeBiasedMeasure
  rw [integral_withDensity_eq_integral_smul measurable_differenceSquareWeight]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    change (differenceSquareWeight p : ℝ) * g p =
      (differenceSquareWeight p : ℝ) * g p
    rfl

theorem integrable_abs_difference_differenceSizeBiasedMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun p : ℝ × ℝ => |p.1 - p.2|)
      (differenceSizeBiasedMeasure mu) := by
  unfold differenceSizeBiasedMeasure
  apply (integrable_withDensity_iff_integrable_smul
    measurable_differenceSquareWeight).2
  have hbase := (integrable_symmetrized_abs_sub_cube mu hX).div_const 2
  apply hbase.congr
  exact ae_of_all _ fun p => by
    change |p.1 - p.2| ^ 3 / 2 =
      (differenceSquareWeight p : ℝ) * |p.1 - p.2|
    simp only [differenceSquareWeight, NNReal.coe_mk]
    rw [← sq_abs]
    ring

theorem integral_abs_difference_differenceSizeBiasedMeasure
    (mu : Measure ℝ) :
    (∫ p : ℝ × ℝ, |p.1 - p.2| ∂differenceSizeBiasedMeasure mu) =
      symmetrizedThirdAbsoluteMoment mu / 2 := by
  rw [integral_differenceSizeBiasedMeasure]
  calc
    (∫ p : ℝ × ℝ,
        (differenceSquareWeight p : ℝ) * |p.1 - p.2| ∂mu.prod mu) =
        ∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 / 2 ∂mu.prod mu := by
          apply integral_congr_ae
          exact ae_of_all _ fun p => by
            simp only [differenceSquareWeight, NNReal.coe_mk]
            rw [← sq_abs]
            ring
    _ = symmetrizedThirdAbsoluteMoment mu / 2 := by
      rw [integral_div]
      rfl

theorem integrable_scaled_abs_difference_differenceSizeBiasedMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) (u : ℝ) :
    Integrable (fun p : ℝ × ℝ => |u| * |p.1 - p.2|)
      (differenceSizeBiasedMeasure mu) :=
  (integrable_abs_difference_differenceSizeBiasedMeasure mu hX).const_mul |u|

theorem integral_scaled_abs_difference_differenceSizeBiasedMeasure
    (mu : Measure ℝ) (u : ℝ) :
    (∫ p : ℝ × ℝ, |u| * |p.1 - p.2| ∂differenceSizeBiasedMeasure mu) =
      |u| * (symmetrizedThirdAbsoluteMoment mu / 2) := by
  rw [integral_const_mul,
    integral_abs_difference_differenceSizeBiasedMeasure]

/-- The size-biased Jensen reduction behind Route B (3.5), stated first in
terms of the symmetrized third moment. -/
theorem norm_charFun_sq_le_of_convex_minorant
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {q : ℝ → ℝ} (hq : RouteBMinorantSpec q) (u : ℝ) :
    ‖charFun mu u‖ ^ 2 ≤
      1 - 2 * u ^ 2 * q (|u| * (symmetrizedThirdAbsoluteMoment mu / 2)) := by
  let nu : Measure (ℝ × ℝ) := differenceSizeBiasedMeasure mu
  let V : ℝ × ℝ → ℝ := fun p => |u| * |p.1 - p.2|
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    exact isProbabilityMeasure_differenceSizeBiasedMeasure mu hX hmean hsecond
  have hVnonneg (p : ℝ × ℝ) : 0 ≤ V p := by
    dsimp [V]
    positivity
  have hVmeas : Measurable V := by
    dsimp [V]
    fun_prop
  have hVint : Integrable V nu := by
    simpa only [V, nu] using
      integrable_scaled_abs_difference_differenceSizeBiasedMeasure mu hX u
  have hqVint : Integrable (fun p => q (V p)) nu := by
    have hhalf : Integrable (fun _p : ℝ × ℝ => (1 : ℝ) / 2) nu := integrable_const _
    refine hhalf.mono' ((hq.measurable.comp hVmeas).aestronglyMeasurable) ?_
    exact ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs] using hq.abs_le_half (V p) (hVnonneg p)
  have hJensen : q (∫ p, V p ∂nu) ≤ ∫ p, q (V p) ∂nu :=
    hq.convexOn_nonnegative.map_integral_le hq.continuousOn_nonnegative
      isClosed_Ici (ae_of_all _ hVnonneg) hVint hqVint
  have hJensenScaled :
      2 * u ^ 2 * q (∫ p, V p ∂nu) ≤
        2 * u ^ 2 * ∫ p, q (V p) ∂nu := by
    exact mul_le_mul_of_nonneg_left hJensen (by positivity)
  have hscale :
      2 * u ^ 2 * (∫ p, q (V p) ∂nu) =
        ∫ p : ℝ × ℝ, u ^ 2 * (p.1 - p.2) ^ 2 * q (V p) ∂mu.prod mu := by
    calc
      2 * u ^ 2 * (∫ p, q (V p) ∂nu) =
          2 * u ^ 2 *
            ∫ p : ℝ × ℝ, (differenceSquareWeight p : ℝ) * q (V p) ∂mu.prod mu := by
              dsimp [nu]
              rw [integral_differenceSizeBiasedMeasure]
      _ = ∫ p : ℝ × ℝ,
            (2 * u ^ 2) * ((differenceSquareWeight p : ℝ) * q (V p)) ∂mu.prod mu := by
              rw [integral_const_mul]
      _ = ∫ p : ℝ × ℝ, u ^ 2 * (p.1 - p.2) ^ 2 * q (V p) ∂mu.prod mu := by
              apply integral_congr_ae
              exact ae_of_all _ fun p => by
                simp only [differenceSquareWeight, NNReal.coe_mk]
                ring
  have hleftIntegrable : Integrable
      (fun p : ℝ × ℝ => u ^ 2 * (p.1 - p.2) ^ 2 * q (V p)) (mu.prod mu) := by
    have hdom := (integrable_difference_sq mu hX).const_mul (u ^ 2 / 2)
    refine hdom.mono' (by
      have hpoly : Measurable
          (fun p : ℝ × ℝ => u ^ 2 * (p.1 - p.2) ^ 2) := by fun_prop
      exact (hpoly.mul (hq.measurable.comp hVmeas)).aestronglyMeasurable) ?_
    exact ae_of_all _ fun p => by
      have hqabs := hq.abs_le_half (V p) (hVnonneg p)
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg u), abs_of_nonneg (sq_nonneg (p.1 - p.2))]
      have hmul := mul_le_mul_of_nonneg_left hqabs
        (mul_nonneg (sq_nonneg u) (sq_nonneg (p.1 - p.2)))
      nlinarith
  have hrightIntegrable : Integrable
      (fun p : ℝ × ℝ => 1 - Real.cos (u * (p.1 - p.2))) (mu.prod mu) := by
    have htwo : Integrable (fun _p : ℝ × ℝ => (2 : ℝ)) (mu.prod mu) := integrable_const _
    refine htwo.mono' (by fun_prop) ?_
    exact ae_of_all _ fun p => by
      have hnonneg : 0 ≤ 1 - Real.cos (u * (p.1 - p.2)) := by
        linarith [Real.cos_le_one (u * (p.1 - p.2))]
      have hle : 1 - Real.cos (u * (p.1 - p.2)) ≤ 2 := by
        linarith [Real.neg_one_le_cos (u * (p.1 - p.2))]
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hintegral :
      (∫ p : ℝ × ℝ, u ^ 2 * (p.1 - p.2) ^ 2 * q (V p) ∂mu.prod mu) ≤
        ∫ p : ℝ × ℝ, 1 - Real.cos (u * (p.1 - p.2)) ∂mu.prod mu := by
    apply integral_mono hleftIntegrable hrightIntegrable
    intro p
    simpa only [V] using weighted_minorant_le_cosine_loss hq.minorant u (p.1 - p.2)
  have hmain :
      2 * u ^ 2 * q (∫ p, V p ∂nu) ≤
        ∫ p : ℝ × ℝ, 1 - Real.cos (u * (p.1 - p.2)) ∂mu.prod mu := by
    calc
      2 * u ^ 2 * q (∫ p, V p ∂nu) ≤
          2 * u ^ 2 * ∫ p, q (V p) ∂nu := hJensenScaled
      _ = ∫ p : ℝ × ℝ, u ^ 2 * (p.1 - p.2) ^ 2 * q (V p) ∂mu.prod mu := hscale
      _ ≤ ∫ p : ℝ × ℝ, 1 - Real.cos (u * (p.1 - p.2)) ∂mu.prod mu := hintegral
  have hVmean : (∫ p, V p ∂nu) =
      |u| * (symmetrizedThirdAbsoluteMoment mu / 2) := by
    simpa only [V, nu] using
      integral_scaled_abs_difference_differenceSizeBiasedMeasure mu u
  rw [hVmean, integral_one_sub_cos_sub_eq_one_sub_norm_charFun_sq] at hmain
  linarith

/-- Route B equation (3.5), with the Jensen argument expressed in the source
parameter `r rho = E|X-X'|³/2`. -/
theorem routeB_characteristicFunction_modulus_sq_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {q : ℝ → ℝ} (hq : RouteBMinorantSpec q) (u : ℝ) :
    ‖charFun mu u‖ ^ 2 ≤
      1 - 2 * u ^ 2 *
        q (symmetrizationRatio mu * thirdAbsoluteMoment mu * |u|) := by
  have hbase := norm_charFun_sq_le_of_convex_minorant mu hX hmean hsecond hq u
  have hrho : 0 < thirdAbsoluteMoment mu := by
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have harg :
      |u| * (symmetrizedThirdAbsoluteMoment mu / 2) =
        symmetrizationRatio mu * thirdAbsoluteMoment mu * |u| := by
    unfold symmetrizationRatio
    field_simp [hrho.ne']
  rwa [harg] at hbase

/-- Equation (3.5) specialized to the explicit piecewise function (3.3).  Its
only remaining input is the finite Route B breakpoint certificate. -/
theorem routeB_modulus_sq_le_of_certificate
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (u : ℝ) :
    ‖charFun mu u‖ ^ 2 ≤
      1 - 2 * u ^ 2 *
        routeBMinorant kappa theta
          (symmetrizationRatio mu * thirdAbsoluteMoment mu * |u|) :=
  routeB_characteristicFunction_modulus_sq_le mu hX hmean hsecond
    (routeBMinorant_spec_of_certificate hcert) u

end

end BerryEsseen
