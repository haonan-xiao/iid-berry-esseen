import BerryEsseen.Interval.Finite.AdaptiveFailureDiagnostic

/-!
# Interval / Finite / Adaptive Diagnostic Correctness
-/

namespace BerryEsseen

set_option maxRecDepth 10000

theorem findBound4395FiniteTargetAwareCoverFailure_eq_none_iff
    (cache : DyadicRouteBResolutionCache) (n fuel : ℕ)
    (path : String) (rho z : DyadicInterval) :
    findBound4395FiniteTargetAwareCoverFailure
        cache n fuel path rho z = none ↔
      bound4395FiniteTargetAwareCover cache n fuel rho z = true := by
  induction fuel generalizing path rho z with
  | zero =>
      simp [findBound4395FiniteTargetAwareCoverFailure,
        bound4395FiniteTargetAwareCover]
  | succ fuel ih =>
      cases haccepted :
          bound4395FiniteTargetAwareAccepted cache n rho z with
      | true =>
          simp [findBound4395FiniteTargetAwareCoverFailure,
            bound4395FiniteTargetAwareCover, haccepted]
      | false =>
          by_cases hsplit : dyadicRouteBSplitRho n rho z
          · simp only [findBound4395FiniteTargetAwareCoverFailure,
              bound4395FiniteTargetAwareCover, haccepted, hsplit,
              Bool.false_eq_true, if_false, if_pos, Bool.and_eq_true]
            cases hleft : findBound4395FiniteTargetAwareCoverFailure
                cache n fuel (path ++ "rho0")
                  (dyadicRouteBLeftHalf rho) z with
            | none =>
                have hleftCover :
                    bound4395FiniteTargetAwareCover cache n fuel
                      (dyadicRouteBLeftHalf rho) z = true :=
                  (ih (path ++ "rho0") (dyadicRouteBLeftHalf rho) z).mp hleft
                simpa [hleft, hleftCover] using
                  (ih (path ++ "rho1") (dyadicRouteBRightHalf rho) z)
            | some failure =>
                have hleftCover :
                    bound4395FiniteTargetAwareCover cache n fuel
                      (dyadicRouteBLeftHalf rho) z ≠ true := by
                  intro hcover
                  have hnone :=
                    (ih (path ++ "rho0") (dyadicRouteBLeftHalf rho) z).mpr
                      hcover
                  rw [hleft] at hnone
                  contradiction
                simp [hleftCover]
          · simp only [findBound4395FiniteTargetAwareCoverFailure,
              bound4395FiniteTargetAwareCover, haccepted, hsplit,
              Bool.false_eq_true, if_false, Bool.and_eq_true]
            cases hleft : findBound4395FiniteTargetAwareCoverFailure
                cache n fuel (path ++ "z0") rho
                  (dyadicRouteBLeftHalf z) with
            | none =>
                have hleftCover :
                    bound4395FiniteTargetAwareCover cache n fuel rho
                      (dyadicRouteBLeftHalf z) = true :=
                  (ih (path ++ "z0") rho (dyadicRouteBLeftHalf z)).mp hleft
                simpa [hleft, hleftCover] using
                  (ih (path ++ "z1") rho (dyadicRouteBRightHalf z))
            | some failure =>
                have hleftCover :
                    bound4395FiniteTargetAwareCover cache n fuel rho
                      (dyadicRouteBLeftHalf z) ≠ true := by
                  intro hcover
                  have hnone :=
                    (ih (path ++ "z0") rho (dyadicRouteBLeftHalf z)).mpr
                      hcover
                  rw [hleft] at hnone
                  contradiction
                simp [hleftCover]

theorem findBound4395FiniteTargetAwareTreeFailure_eq_none_iff
    (cache : DyadicRouteBResolutionCache) (n extraFuel : ℕ)
    (tree : DyadicRouteBLeafTree) (path : String)
    (rho z : DyadicInterval) :
    findBound4395FiniteTargetAwareTreeFailure
        cache n extraFuel tree path rho z = none ↔
      bound4395FiniteTargetAwareVerifyLeafTree
        cache n extraFuel tree rho z = true := by
  induction tree generalizing path rho z with
  | leaf =>
      exact findBound4395FiniteTargetAwareCoverFailure_eq_none_iff
        cache n extraFuel path rho z
  | splitRho left right ihLeft ihRight =>
      simp only [findBound4395FiniteTargetAwareTreeFailure,
        bound4395FiniteTargetAwareVerifyLeafTree, Bool.and_eq_true]
      cases hleft : findBound4395FiniteTargetAwareTreeFailure
          cache n extraFuel left (path ++ "R0")
            (dyadicRouteBLeftHalf rho) z with
      | none =>
          have hleftVerify :
              bound4395FiniteTargetAwareVerifyLeafTree
                cache n extraFuel left (dyadicRouteBLeftHalf rho) z = true :=
            (ihLeft (path ++ "R0") (dyadicRouteBLeftHalf rho) z).mp hleft
          simpa [hleft, hleftVerify] using
            (ihRight (path ++ "R1") (dyadicRouteBRightHalf rho) z)
      | some failure =>
          have hleftVerify :
              bound4395FiniteTargetAwareVerifyLeafTree
                cache n extraFuel left (dyadicRouteBLeftHalf rho) z ≠ true := by
            intro hverify
            have hnone :=
              (ihLeft (path ++ "R0") (dyadicRouteBLeftHalf rho) z).mpr
                hverify
            rw [hleft] at hnone
            contradiction
          simp [hleftVerify]
  | splitZ left right ihLeft ihRight =>
      simp only [findBound4395FiniteTargetAwareTreeFailure,
        bound4395FiniteTargetAwareVerifyLeafTree, Bool.and_eq_true]
      cases hleft : findBound4395FiniteTargetAwareTreeFailure
          cache n extraFuel left (path ++ "Z0") rho
            (dyadicRouteBLeftHalf z) with
      | none =>
          have hleftVerify :
              bound4395FiniteTargetAwareVerifyLeafTree
                cache n extraFuel left rho (dyadicRouteBLeftHalf z) = true :=
            (ihLeft (path ++ "Z0") rho (dyadicRouteBLeftHalf z)).mp hleft
          simpa [hleft, hleftVerify] using
            (ihRight (path ++ "Z1") rho (dyadicRouteBRightHalf z))
      | some failure =>
          have hleftVerify :
              bound4395FiniteTargetAwareVerifyLeafTree
                cache n extraFuel left rho (dyadicRouteBLeftHalf z) ≠ true := by
            intro hverify
            have hnone :=
              (ihLeft (path ++ "Z0") rho (dyadicRouteBLeftHalf z)).mpr
                hverify
            rw [hleft] at hnone
            contradiction
          simp [hleftVerify]

theorem bound4395FiniteTargetAwareDiagnostic_eq_allAccepted_iff
    (n extraFuel : ℕ) :
    bound4395FiniteTargetAwareDiagnostic n extraFuel =
        .allAccepted n ↔
      bound4395OldFiniteTargetAwareLeafCodeCertificate
        n extraFuel = true := by
  unfold bound4395FiniteTargetAwareDiagnostic
  unfold bound4395OldFiniteTargetAwareLeafCodeCertificate
  cases hcode : certifiedOldLeafCode n with
  | none => simp
  | some code =>
      unfold bound4395FiniteTargetAwareLeafCodeCertificate
      cases htree : dyadicRouteBLeafTreeOfCode code with
      | none => simp [htree]
      | some tree =>
          simp only [htree]
          unfold bound4395FiniteTargetAwareLeafTreeCertificate
          cases hfailure : findBound4395FiniteTargetAwareTreeFailure
              dyadicRouteBBuildResolutionCache n extraFuel tree ""
                (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ with
          | none =>
              have hverify :=
                (findBound4395FiniteTargetAwareTreeFailure_eq_none_iff
                  dyadicRouteBBuildResolutionCache n extraFuel tree ""
                    (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ).mp
                      hfailure
              simp [hfailure, hverify]
          | some failure =>
              have hverify :
                  bound4395FiniteTargetAwareVerifyLeafTree
                    dyadicRouteBBuildResolutionCache n extraFuel tree
                      (dyadicRouteBFiniteRootRho n)
                        dyadicRouteBFiniteRootZ ≠ true := by
                intro hcertificate
                have hnone :=
                  (findBound4395FiniteTargetAwareTreeFailure_eq_none_iff
                    dyadicRouteBBuildResolutionCache n extraFuel tree ""
                      (dyadicRouteBFiniteRootRho n)
                        dyadicRouteBFiniteRootZ).mpr hcertificate
                rw [hfailure] at hnone
                contradiction
              simp [hfailure, hverify]

end BerryEsseen
