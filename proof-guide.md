# Human proof and verified source alignment for `C = 879/2000`

This document gives the detailed argument for the unconditional bound
`879/2000` and its correspondence with the Lean sources. Section 9 describes
the exact continuous-domain certificates, executed verification evidence,
and native-evaluation trust boundary. The shorter presentation is in
`paper/main.tex` and the accompanying PDF.

The module and lemma names below follow the publication layout.
Section 9 records the completed 0.4395 verification before these names were
changed. The source correspondence and current rebuild status are documented
in [FORMALIZATION.md](FORMALIZATION.md).

## 1. Exact theorem

Let `(Omega, F, P)` be an arbitrary probability space and let
`X : Nat -> Omega -> Real` be independent and identically distributed under
`P`.  Assume

```text
E X_0 = 0,              E X_0^2 = 1,
rho := E |X_0|^3 < infinity.
```

For every integer `n >= 1`, define

```text
S_n = (X_0 + ... + X_(n-1))/sqrt(n),
Delta_n = sup_x |P(S_n <= x) - Phi(x)|.
```

The conclusion is

```text
Delta_n <= (879/2000) rho/sqrt(n).                         (1.1)
```

The Lean statement uses the same measurable space, probability measure,
independence, identical-distribution, `MemLp 3`, mean, second-moment, and
all-`n` binders as `BerryEsseen.iidBerryEsseen45`.  Only the conclusion
constant changes from `9/20` to `879/2000`.  In particular,

```text
879/2000 = 0.4395 < 11/25 = 0.44 < 9/20 = 0.45.
```

## 2. Shared parameter and feasible moment region

Let `X'` be an independent copy of `X_0` and put

```text
r = E|X_0-X'|^3/(2 rho),       eta = rho(r-1),
s = E|X_0|,                    d = 1-s.
```

The finite checker calls the same excess coordinate `z`; thus `z=eta` there.
The distinct unit-square coordinates used for large `n` are defined in
Section 6.

The symmetrization argument for the 0.45 bound gives

```text
1 <= r <= 1+1/rho,             0 <= eta <= 1.             (2.1)
```

The exact baseline locators are `symmetrizationRatio_lower`,
`symmetrizationRatio_upper`, and `thirdAbsoluteMoment_ge_one` in
`MomentGeometry.lean`; multiplying the ratio bounds by the positive `rho`
gives the displayed bounds on `eta=rho(r-1)`.

The variance normalization gives `rho >= 1`.  Cauchy--Schwarz gives

```text
1 = (E|X_0|^2)^2 <= (E|X_0|)(E|X_0|^3) = s rho,
```

so `s rho >= 1`.  A second Cauchy--Schwarz application gives
`0 <= s=E|X_0| <= sqrt(E|X_0|^2)=1`, hence `0<=d<=1`.  The stop-loss
identities used in the 0.45 bound give

```text
E|X_0-X'|^3-2rho <= 2s,
```

and hence `eta <= s`.  Therefore

```text
0 <= d <= min(1-1/rho, 1-eta).                            (2.2)
```

These are consequences of the original law hypotheses, not restrictions on
the admissible distribution class.  In Lean,
`one_le_firstAbsoluteMoment_mul_thirdAbsoluteMoment` proves
`1<=s*rho`,
`thirdAbsoluteMoment_mul_ratioExcess_le_firstAbsoluteMoment` proves
`eta<=s`, and `radialDefect_constraints` packages the two upper bounds
on `d` under exactly `MemLp 3`, centering, and unit second moment.

## 3. Characteristic-function envelopes

Put `Y=|X_0|` and define `A=1` on `{X_0>=0}` and `A=-1` on
`{X_0<0}`.  Thus `A` takes values in `{-1,1}`, including at `X_0=0`, and
`X_0=A Y`.  Then

```text
E Y=s,       E Y^2=1,       E(A Y)=0,       E(Y-1)^2=2d.
```

Since `E[A(Y-1)]=E(AY)-EA=-EA` and `A^2=1`, Cauchy--Schwarz gives

```text
|EA|=|E[A(Y-1)]| <= sqrt(E A^2) sqrt(E(Y-1)^2)=sqrt(2d).
```

For arbitrary real `u`, the global second-order Taylor remainder bounds are

```text
cos(uY)=cos u-u sin u (Y-1)+R_c,
sin(uY)=sin u+u cos u (Y-1)+R_s,
|R_c|, |R_s| <= u^2(Y-1)^2/2.                              (3.1a)
```

Cosine is even and `sin(uX_0)=A sin(uY)`.  Taking expectations in (3.1a),
using `E(Y-1)=-d` and `E[A(Y-1)]=-EA`, gives the exact decompositions

```text
Re f(u)-cos u = d u sin u+E R_c,
Im f(u) = EA(sin u-u cos u)+E(A R_s),
|E R_c|, |E(A R_s)| <= d u^2.                              (3.1b)
```

The triangle inequality and the preceding Cauchy--Schwarz estimate therefore
give

```text
|Re f(u)-cos u| <= d(|u sin u|+u^2),                      (3.1)
|Im f(u)| <= sqrt(2d)|sin u-u cos u|+d u^2.               (3.2)
```

The exact Lean source chain for (3.1a)--(3.2) is
`abs_cos_sub_linearization_le`,
`abs_sin_sub_linearization_le`,
`integral_abs_sub_one_sq`, `sign_mul_abs`,
`abs_integral_sign_le_sqrt_defect`,
`integral_radialCosRemainder_abs_le`,
`integral_radialCosRemainder_eq`,
`integral_radialSinRemainder_abs_le`,
`integral_radialSinRemainder_eq`, and finally
`charFun_real_radial_bound` and
`charFun_imag_radial_bound`.  The real-part theorem needs only the
variance-one third-moment assumptions; the imaginary-part theorem additionally
uses the original centering hypothesis.  Neither theorem assumes symmetry of
the law.

Intersect (3.1) with the 0.45 third-order real interval and (3.2) with its
shared-`r` imaginary remainder:

```text
g(v)=cos(v)-1+v^2/2,       kappa=max_(v>0) g(v)/v^3,
0.09916191350 < kappa < 0.09916191353.
```

The maximum and the displayed rational decimal enclosure are proved in the 0.45 bound;
the minorant and disk semantics use the exact `routeBKappa`. The strengthened
finite real strip uses the separately certified rational upper bound
`kappaPlus=9916191353/100000000000=0.09916191353`, as in
`scalarRealHigh`. This is an outward relaxation of the exact inequality,
not a machine floating-point value.

```text
1-u^2/2 <= Re f(u) <= 1-u^2/2+kappa rho |u|^3,
|Im f(u)| <= rho |u|^3 sqrt(1-(r-1)^2)/6.                 (3.3)
```

If `[a,b]` is the resulting real interval and `c` the resulting imaginary
radius, then

```text
|f(u)| <= sqrt(max(|a|,|b|)^2+c^2),
|f(u)-cos u| <= sqrt(max(|a-cos u|,|b-cos u|)^2+c^2).     (3.4)
```

The modulus bound is intersected with the 0.45 modulus and with 1. The
real error to `cos u` is also intersected with the radius in (3.1); the exact
formulas appear in Section 5. The comparison with the Rademacher
characteristic function `cos u` is new in the 0.4395 bound. For
complex `a,b`, telescoping gives

```text
|a^n-b^n| <= n |a-b| max(|a|,|b|)^(n-1).                 (3.5)
```

Thus the disk, trivial, and Rademacher comparisons each bound
`|f(u)^n-exp(-nu^2/2)|`; taking their pointwise minimum remains an upper bound
without assuming which branch is active.  The finite target-aware checker
uses exactly this envelope.

For `n>=100`, put `L=rho/sqrt(n)`.  Then `rho>=max(1,10L)`.  From (2.2),

```text
sqrt(r-1) <= max(1/rho, rho(r-1)).                       (3.6a)
```

Indeed, writing `t=sqrt(r-1)`, either `t<=1/rho`, or
`rho t>=1` and hence `t<=rho t^2=rho(r-1)`.  The two defect
bounds in (2.2) therefore give

```text
d <= 1-max(1/rho,rho(r-1)) <= 1-sqrt(r-1).
```

Moreover `rho>=10L` and `r-1>=0` turn the stop-loss bound
`d<=1-rho(r-1)` into `d<=1-10L(r-1)`.  Consequently,

```text
d <= min(1-sqrt(r-1), 1-10L(r-1)).                       (3.6)
```

On the difficult strip `r>=19/10`, the exact comparison

```text
(237/250)^2 = 56169/62500 <= 9/10 <= r-1
```

and (3.6) imply `d<=1-237/250=13/250`.  For `0<=u<=5/6`, set

```text
x=u^2,
M_R=cos u+d(u sin u+u^2),
M_I=sqrt(2d)|sin u-u cos u|+d u^2,
P(x)=1-(99/250)x+(1/24-13/1500)x^2+(13/30000)x^3.
```

The alternating Taylor bounds for sine and cosine, together with
`d<=13/250`, give

```text
0<=M_R<=P(x),             0<=M_I<=(71/500)x.               (3.6b)
```

Here `sin u>=0` on the stated interval, and
`Re f(u)>=1-u^2/2>=47/72>0` by (3.3).  Hence (3.1)--(3.3) and (3.6b) give the
componentwise square comparison

```text
|f(u)|^2=(Re f(u))^2+(Im f(u))^2
        <=M_R^2+M_I^2<=P(x)^2+((71/500)x)^2.               (3.6c)
```

Exact rational polynomial comparison on `0<=x<=25/36`, followed by the
alternating lower Taylor bound for the exponential, yields

```text
P(x)^2+((71/500)x)^2
 <= 1-(39/50)x+((39/50)x)^2/2-((39/50)x)^3/6
 <= exp(-(39/50)x).                                        (3.6d)
```

Consequently `|f(u)|^2<=exp(-(39/50)u^2)`, and taking the nonnegative square
root gives

```text
|f(u)| <= exp(-(39/100)u^2).                              (3.7)
```

For a directly checkable proof of the first inequality in (3.6d), its
right-hand side minus its left-hand side is exactly `x q(x)`, where

```text
q(x)=3/250+(3061/50000)x-(40367/750000)x^2
     -(3729/5000000)x^3-(143/5000000)x^4
     -(169/900000000)x^5.
```

Direct differentiation gives

```text
q''(x) = -40367/375000 -(11187/2500000)x
         -(429/1250000)x^2 -(169/45000000)x^3 < 0
```

on `[0,25/36]`, while
`q(0)=3/250>0` and
`q(25/36)=98569207799/3482851737600>0`.  A concave function lies above its
endpoint chord, so `q>=0` throughout the interval.  This proves (3.6d) without
a floating-point sign check.  Lean kernel-elaborates the Taylor envelopes, the
equivalent polynomial-gap inequality, and the final rate from the unchanged
moment assumptions; the displayed `q` expansion is the independently
exact-rational-audited human derivation of that same gap.
The corresponding source chain is
`d_le_thirteen_over_250`,
`low_frequency_le_five_sixths`,
`exp_polynomial_gap_nonneg`,
`rectangular_sq_le_exp`, and finally
`complex_norm_le_exp`; the last theorem converts the separate real and
imaginary bounds into the characteristic-function norm bound (3.7).

## 4. The variable telescoping exponent

The numerical improvement over the fixed 0.45 large-`n` envelope is the
following exact lemma.  For `n>=100`, define

```text
a(L) = max(99/100, 1-L^2).
```

Since `nL^2=rho^2` and `rho>=1`,

```text
n(1-L^2)=n-rho^2 <= n-1.
```

Also `(99/100)n<=n-1`.  Hence

```text
a(L)n <= n-1.                                             (4.1)
```

Here `a(L)>=99/100>0`.  If `x>=0`, `H>=0`, and the one-factor
comparison gives `H<=exp(-x)`, then monotonicity of natural powers gives

```text
H^(n-1) <= exp(-(n-1)x)
          <= exp(-a(L)n x).                               (4.2)
```

The direction of the second inequality follows from (4.1), `x>=0`, and
monotonicity of the real exponential.  Substituting the exact strong quantity
`Q=nx` yields `exp(-a(L)Q)`. In the accepted certificates the variable
coefficient is used in the strong small-`L` branch (`L<=1/16`). The direct
middle and upper branches retain `99/100`; their improvement comes from the
feasible disk and the stronger modulus rate. The general inequality (4.2)
is valid on the larger domain but is not asserted to be used by every checker.
In the application, `H` is the maximum of the nonnegative modulus and
Gaussian envelopes, so the omitted-sign case cannot occur.  No probability
assumption and no `n` value is removed.

More explicitly, let `q` be the 0.45 convex minorant and put
`Q_old=(2*pi*t)^2*q(2*pi*t)/(r^2*L^2)`.  On `r>=19/10` and the low-frequency part `t<=1/4`,
(3.7), with `u=2 pi t/(r rho)`, gives the additional exact exponent

```text
Q_rate=(39/100)(2 pi t)^2/(r^2 L^2).
```

Both exponential bounds hold there, so a case split gives the stronger
`Q_strong=max(Q_old,Q_rate)`.  Outside that part of the integral,
`Q_strong=Q_old`.  Hence selecting the maximum strengthens the decay without
discarding the old valid branch.

For a closed dyadic `L` interval, outward squaring and subtraction enclose
`1-L^2`; componentwise interval maximum with the exact enclosure of `99/100`
therefore encloses `a(L)`.  Multiplication by the nonnegative strong-`Q`
interval and the outward `exp(-x)` routine encloses the right side of (4.2);
both the alpha and strong-`Q` intervals are nonnegative.
The variable-alpha cell, Darboux integral, endpoint functional, and
box-to-law implications have all kernel-elaborated.  This is an analytic
improvement, not a smaller number obtained solely by subdividing boxes.

The computed object is fixed at the definition level as well.  In
`BerryEsseen.Interval.VariableExponent.lean`, `largeVariableAlpha` is the
componentwise dyadic maximum of the exact `99/100` enclosure and the outward
enclosure of `1-L^2`; `certifiedLargeSmallVariableAlphaExp` applies the
proved outward `exp(-x)` evaluator to its product with the strong-`Q` hull.
`certifiedLargeSmallVariableAlphaF1`, the complete cell value, the
Darboux sum, and the omission-added bound then use only outward dyadic
operations.  `BerryEsseen.Smoothing.VariableExponentBoundary.lean` accepts a box
exactly when that bound's integer upper numerator is strictly below the integer
lower numerator of `bound4395Threshold` and the complete box-and-cell
admissibility proposition is true.  The threshold itself is
`DyadicInterval.ofRat 879 2000`.  Thus neither a different alpha formula, a
weaker target comparison, nor an omitted side condition is hidden behind the
concrete Boolean.

The exact Lean source chain is
`routeBSmoothingScale_sq_mul_nat`,
`largeVariableAlpha_mul_nat_le_sub_one`,
`routeBMaxEnvelope_pow_le_variableAlpha_largeN_exp`,
`routeBMaxEnvelope_pow_le_variableAlpha_largeQ_exp`,
`max_pow_le_variable_rate_exp`,
`scalarMaxPower_le_large_old_variable_exp`,
`scalarMaxPower_le_large_rate_variable_exp`, and
`scalarMaxPower_le_large_strong_variable_exp`.  The last theorem
case-splits at `t=1/4` and selects `max(Q_old,Q_rate)` only after both
branchwise exponential bounds are available.  The exponent direction in
(4.2) is discharged explicitly by `Real.exp_le_exp` from
`a(L)n<=n-1` and `x>=0`; it is not inferred by the numerical checker.

The endpoint certificate then transports this analytic inequality to the law
without adding a hypothesis.  The exact chain is
`scalar_normalizedDifference_le_large_variable_telescoping`,
`lawNormalizedDifferenceIntegrand_le_large_variable_telescoping`,
`certifiedLargeSmallVariableAlphaF1_sound`,
`lawNormalizedDifference_mul_scale_le_smallVariableF1_upper`, and
`lawNormalizedLargeSmallIntegrand_le_variable_cell_upper`.  The Darboux
and change-of-variable steps are
`intervalIntegral_lawNormalizedLargeSmallIntegrand_le_variable_sum` and
`lawNormalizedEndpointIntegrals_le_variable_sum_upper`; the omitted low,
middle, high-endpoint, and Gaussian-tail pieces are inserted by
`lawNormalizedPrawitzFunctional_le_variable_smallBound_upper` using the
unchanged analytic Route B estimates
`refinedRouteBNormalizedLow_omission_le`,
`refinedRouteBNormalizedHigh_middle_omission_le`,
`refinedRouteBNormalizedHigh_endpoint_omission_le`, and
`refinedRouteBNormalizedE1Tail_small_le`.  Their exact upper bounds are
respectively `13/10^12`, `1/10^12`, `1/10^12`, and `1/10^12`, so their total
`16/10^12` is below the outward dyadic omission allowance `3/10^11`.
`expNegThirtyTwoLe` supplies the common analytic endpoint estimate
`exp(-32)<=1/(7*10^13)` from `exp(1)>=65/24`; no native computation or
floating-point value is used in these four estimates.  The companion theorem
`refinedRouteB_normalizedRouteBU_le_dyadicRouteBLargeSmallBound_upper` checks the
same adjacent-interval recombination for the old-envelope fallback.  Finally,
`lawNormalizedPrawitzFunctional_lt_879_2000_of_variable_box` and
`normalizedKolmogorovDistance_lt_879_2000_of_variable_box` turn an exact box
Boolean into the normalized law bound.  The hybrid checker uses this branch
only when the entire `r` box lies above `19/10`; otherwise
`lawNormalizedPrawitzFunctional_lt_879_2000_of_variable_old_box` retains
the old valid envelope.  That theorem derives `rho>=1`,
`1<=r<=1+1/rho`, and `0<=eta=rho(r-1)<=1` from the unchanged moment lemmas,
then composes
`refinedRouteB_normalizedRouteBU_le_dyadicRouteBLargeSmallBound_upper` with
`lawNormalizedPrawitzFunctional_le_routeB` before the strict target
comparison.  `variableAlphaSmallCoverVerify_sound` and
`variableAlphaSmallVerifyLeafTreeWithRefinement_sound` propagate the
result across both closed halves of every recursive split.
`normalizedKolmogorovDistance_lt_879_2000_of_variable_smallSplit` then uses the
lower-root certificate when `w` is at or below the shared exact dyadic seam and
the upper-root certificate otherwise, so the final assembly consumes the two
roots without an uncovered point.

## 5. Prawitz reduction and exact certificates

The proved finite-first-moment Prawitz smoothing inequality is reused without
change.  For `0<t<1`, put

```text
K(t)=(1-t)/2+i*((1-t)cot(pi*t)+1/pi)/2,
K_c(t)=K(t)-i/(2*pi*t),
```

with the removable values `K(1)=0` and `K_c(0)=1/2`.  If `Y` is integrable,
`h` is its characteristic function, `T>0`, and `0<t_0<1`, then

```text
Delta(Y,N(0,1))
 <= 2 integral_[0,t_0] |K(t)| |h(Tt)-exp(-T^2 t^2/2)| dt
  + 2 integral_[t_0,1] |K(t)| |h(Tt)| dt
  + 2 integral_[0,t_0] |K_c(t)| exp(-T^2 t^2/2) dt
  + (1/pi) integral_[t_0,infinity] exp(-T^2 t^2/2) dt/t.   (5.0)
```

The third-moment assumption makes the standardized sum integrable, so this
introduces no new hypothesis.  Apply (5.0) to `Y=S_n`, write `h_n` for its
characteristic function, and choose

```text
L=rho/sqrt(n),        T=2*pi/(r*L),        t_0=19/50,
u(t)=Tt/sqrt(n)=2*pi*t/(r*rho).
```

For each numerical regime, let `H_0(t)` and `H_1(t)` denote the nonnegative
envelopes constructed by the corresponding checker.  The law-level soundness
lemmas prove, on the full displayed intervals,

```text
|h_n(Tt)-exp(-T^2 t^2/2)| <= H_0(t)       (0<=t<=t_0),
|h_n(Tt)|                    <= H_1(t)       (t_0<=t<=1).
```

Multiplying the original law-dependent right side of (5.0) by the positive
factor `sqrt(n)/rho` gives exactly `lawNormalizedPrawitzFunctional`;
`normalizedPrawitzFunctional_eq_law` proves this identity. Substituting
upper envelopes `H_0,H_1` then gives an upper bound on that functional, not
an equality with it.  The finite branch obtains
`H_0,H_1` from the pointwise minimum of the disk, trivial, and Rademacher
envelopes in Section 3.  The large branch uses the feasible-disk comparison and (3.7), with fixed
coefficient `99/100` for the direct regions and (4.2) for the strong
small-`L` endpoint branch.  The correction and infinite-tail terms, together with all
kernel estimates, are unchanged 0.45 inequalities.  Thus the
certificate bounds the exact right side of the smoothing theorem rather than
a discretized surrogate.


For precision, the finite envelopes just mentioned are the following explicit
functions. For `t>=0`, write `c=2*pi*t/r`, `u=c/rho`,
`dbar=min(1-1/rho,1-eta)`, `B=exp(-u^2/2)`, and `N=B^n`. Set

```text
A = dbar (|u sin u|+u^2),
a = max(-1, cos u-A, 1-u^2/2),
b = min( 1, cos u+A, 1-u^2/2+kappaPlus rho u^3),
j = min(sqrt(2dbar)|sin u-u cos u|+dbar u^2,
        u^3 sqrt(rho^2-eta^2)/6),
F = min(1, sqrt(max(0,1-2u^2 q(2*pi*t))),
           sqrt(max(|a|,|b|)^2+j^2)),
e = min(A, max(|a-cos u|,|b-cos u|)),
E = sqrt(e^2+j^2),
H_0 = min(n rho u^3 D(rho,r,c) max(F,B)^(n-1),
          F^n+N,
          n E max(F,|cos u|)^(n-1)+|cos(u)^n-N|),
H_1 = F^n.
```

The feasible moment bounds ensure `dbar>=0` and `rho^2-eta^2>=0`;
the interval `[a,b]` is nonempty at every admissible law point because it
contains `Re f(u)`. Every branch is nonnegative there. The formulas also
apply at `u=0`, with all difference terms zero. At `n=1`, each exponent
`n-1` is zero and the telescoping identity remains valid.

Here `q` is the baseline piecewise function
`1/2-kappa*v` on `[0,theta]`, `(1-cos v)/v^2` on
`(theta,2*pi]`, and zero afterwards. The 0.45 breakpoint
certificate proves its convexity, monotonicity and minorant property.
The disk is fully specified by

```text
epsilon_rho(c) = rho^2/c^3 * (exp(-c^2/(2rho^2))-1+c^2/(2rho^2)), c>0,
epsilon_rho(0) = 0,
beta(r) = sqrt(1-(r-1)^2)/6,
Xi(r) = {0,kappa} union ({(r-1)/6} intersect [0,kappa]),
D(rho,r,c)^2
  = max_(x in Xi(r)) [(x-epsilon_rho(c))^2
                      +min(beta(r)^2,1/36-x^2)].
```

The normalized one-factor Taylor remainder lies in
`0<=Re z<=kappa`, `|Im z|<=beta(r)`, `|z|<=1/6`.
For a fixed real part `x`, its maximal squared distance from the real
Gaussian offset is the displayed score. On each side of
`x=(r-1)/6` the maximum is at an endpoint, giving `Xi(r)`.
This proves `|f(u)-exp(-u^2/2)|<=rho|u|^3 D(rho,r,rho|u|)`;
the case `u=0` is checked directly before division. Thus the first
finite branch is precisely the shared-parameter disk, with the new
smaller power factor `F`.

The finite law-to-functional source chain is
`scalar_modulus_actual`,
`scalar_disk_difference_actual`,
`scalar_trivial_difference_actual`,
`scalar_rademacher_difference_actual`,
`scalar_power_difference_actual`,
`standardizedSum_charFun_norm_le`,
`standardizedSum_charFun_difference_le`,
`prawitzFunctional_standardizedSum_le_scalar`, and
`kolmogorovDistance_standardizedSum_le_scalar`.  In particular,
`scalarPowerDifference` is definitionally the nested minimum of the
three proved nonnegative candidates, so no unproved branch selector is used.
The added dyadic components are linked to their real expressions by
`rectangularEnvelope_sound`, `errorToCosEnvelope_sound`,
`rademacherDifferenceIntervals_sound`, and
`minModulusEnvelope_sound` before the recursive cover is invoked.

The finite evaluator then closes the remaining law-to-number steps.
`certifiedCellEnvelope_sound` encloses the actual characteristic-function
and Gaussian terms on a whole parameter/frequency cell.  The certified high,
correction, Rademacher, trivial, telescoping, and low-integrand lemmas turn
that enclosure into pointwise upper bounds.  The low-frequency Darboux result
is `lawNormalizedLowIntegral_le_certifiedLowSum_upper`; the separate
high-integral module proves
`lawNormalizedHighIntegral_le_certifiedHighSum_upper` and combines
the two pieces in
`lawNormalizedFiniteIntegrals_le_certifiedFiniteBound_upper`.
`lawNormalizedPrawitzFunctional_le_certifiedFullBound` adds the proved
Gaussian-tail enclosure, and
`normalizedKolmogorovDistance_le_certifiedFullBound` composes this exact
functional bound with Prawitz smoothing.  Finally,
`CertifiedCachedFullAdmissible.toCanonical` transports every cached cell
side condition back to those canonical theorems before a strict target-aware
endpoint comparison is allowed.  Thus cache lookup changes evaluation cost,
not the function or law domain being certified.


The feasible-disk replacement also has a direct scalar description.
For `r>1`, feasibility gives `1<=rho<=1/(r-1)`.
For fixed `c>=0`, the function `epsilon_rho(c)` decreases with
`rho`: for `c>0`, it equals
`[exp(-y)-1+y]/(2*c*y)`, where `y=c^2/(2rho^2)`, and the derivative
of `[exp(-y)-1+y]/y` is
`[1-(1+y)exp(-y)]/y^2>=0` by `exp(y)>=1+y`.
The value at `c=0` is zero. Therefore

```text
epsilon_(1/(r-1))(c) <= epsilon_rho(c) <= epsilon_1(c).
```

For each fixed `x`, the squared disk score is convex in its offset.
Its maximum over the finite set `Xi(r)` is also convex, so its maximum
over this interval is at one of the two endpoints. Consequently

```text
D(rho,r,c) <= Dstar(r,c)
 := max(D(1/(r-1),r,c), D(1,r,c)).
```

This improves the older interval `[0,epsilon_1(c)]`. It is used only
on the strong strip `r>=19/10`, so no division by `r-1=0` is involved.
The other boxes retain the proved baseline envelope.

The large-`n` law-to-functional chain is equally explicit.  First,
`routeBEpsilon_antitone_rho`,
`refinedRouteBDiskBoundSqAtEpsilon_le_endpoints`, and
`refinedRouteBDiskBound_le_diskStar` replace the unknown feasible offset by the
two exact endpoint disks under only `rho>=1`, `r>1`, and
`rho*(r-1)<=1`.  Next, `scalarModulus_le_large_rate` instantiates (3.7),
`scalarMaxPower_le_large_strong_exp` takes the pointwise stronger of the
old and radial-rate exponents on `t<=1/4`, and
`scalar_normalizedDifference_le_large_telescoping` combines that power
bound with the feasible disk and the exact smoothing-scale identity.  Finally,
`lawNormalizedDifferenceIntegrand_le_large_telescoping` derives the
feasibility inequality from `symmetrizationRatio_upper` and transports the
scalar inequality to every admissible centered variance-one law.  The other
large-`n` terms are supplied by
`lawNormalizedDifferenceIntegrand_le_large_old`,
`lawNormalizedHighIntegrand_le_large`, and
`lawNormalizedCorrectionIntegrand_le_large`.  Thus neither the feasible
disk nor the strengthened exponent is merely a checker-side ansatz.

At the direct large-interval layer,
`certifiedLargeDirectStrongQ_sound`,
`certifiedLargeDirectTelescoping_sound`, and the certified direct
low/high cell theorems enclose those real expressions on each entire dyadic
cell.  `lawNormalizedLowIntegral_le_directSum_upper` and
`lawNormalizedHighIntegral_le_directSum_upper` give the two Darboux
pieces; `lawNormalizedPrawitzFunctional_le_largeDirectFullBound` adds
the tail, and
`normalizedKolmogorovDistance_le_certifiedLargeDirectFullBound` applies
the smoothing inequality.  Cache equality plus
`CertifiedLargeDirectCachedFullAdmissible.toCanonical` transports every
cached side condition to this canonical chain.  On a box not wholly above
`r=19/10`, the fallback proof instead invokes the unchanged
`routeB_normalizedRouteBU_le_dyadicRouteBLargeFullBound_upper_of_admissible`
and `kolmogorovDistance_standardizedSum_le_exactRouteBU`, then compares that
outward upper bound with the same `879/2000` threshold.  The fallback therefore
retains a proved 0.45 envelope; it is not an unchecked numerical default.

For the direct middle and upper certificates, the Boolean-to-law implication
is `normalizedKolmogorovDistance_lt_879_2000_of_post044LargeDirectBox`; it
first checks cache validity and recovers the canonical full-bound theorem.
`normalizedKolmogorovDistance_lt_879_2000_of_post044LargeHybridBox` uses that
direct branch only when the complete dyadic `r` box is above `19/10`, and uses
`normalizedKolmogorovDistance_lt_879_2000_of_post044LargeOldBox` otherwise.
`bound4395LargeCoverVerify_sound` and
`bound4395LargeVerifyLeafTreeWithRefinement_sound` lift the box implication
through every closed recursive half, while
`normalizedKolmogorovDistance_lt_879_2000_of_post044LargeCode` makes malformed
topology input fail closed.  The two concrete premises are exactly
`bound4395LargeMiddleFuel5ConcreteCertificate_checked` and
`bound4395LargeUpperFuel8ConcreteCertificate_checked`. The upper theorem
is a native witness. The middle theorem is a kernel-checked alias of
`bound4395LargeMiddleFuel5ShardedFullCertificate_checked`, which composes
four disjoint numerical batches with a separately checked complete topology
parse; it is not an additional native numerical computation.  Finally,
`targetAware_normalizedKolmogorovDistance_lt_879_2000` applies the
coordinate inverse theorems and assembles the finite, small, middle, and upper
regions.  Thus the expensive native evaluations are neither standalone sampled
claims nor substitutes for the analytic box-soundness proof.

Every remaining parameter rectangle is covered by recursive bisection into
closed boxes.  All inputs use outward 48-bit dyadic intervals.  Addition,
multiplication, division, square root, exponential, and trigonometric Taylor
operations round outward; integral terms use proved upper Darboux sums at
resolutions `256`, `1024`, `2048`, `4096`, or `8192`; the last resolution is
available only in the small-`L` variable-alpha adaptive evaluator.  Each
resolution branch supplies the corresponding positive integer `N` to the
integral theorem.  A leaf returns `true` only if

```text
the outward functional upper endpoint is strictly below 879/2000,
every interval is ordered,
the box and tail side conditions hold, and
all low- and high-frequency analytic preconditions hold.
```

Here is the exact real semantics behind that Boolean.  A dyadic interval is
an integer pair `I=(lo,hi)` representing the closed real interval

```text
[I] = [lo/2^48, hi/2^48].
```

For each interval operation used by the evaluator, its Lean containment
theorem has the form

```text
x in [I], y in [J]  ==>  f(x,y) in [F(I,J)],                 (5.1)
```

with the stated positivity hypotheses for division and the stated ordered,
nonnegative hypotheses for square root.  Rational endpoints use integer floor
for the lower endpoint and integer ceiling for the upper endpoint;
multiplication takes the outward four-corner hull.  The exponential evaluator
combines proved alternating Taylor bounds with exact interval halving and
squaring, so (5.1), rather than a floating-point approximation, is the
invariant propagated through the functional.

The elementary-function bridge is equally explicit.  On a nonnegative input,
the exponential checker halves until the interval upper endpoint is at most
`1/8`, brackets `exp(-x)` between the degree-13 and degree-12 alternating
Taylor sums, and reverses the range reduction by outward squaring; this is the
statement proved by `dyadicExpNeg_sound`.  Trigonometric constants and terms
do not enter as machine decimals: `checkerPi_contains_pi` encloses `pi`
between consecutive precision-48 dyadics, the sine and cosine alternating
series have proved lower and upper bounds, and
`dyadicCosineLossTaylor12_sound`, `dyadicCotGapLower_lower_le`, and
`cotGap_le_dyadicCotGapUpper_upper` connect the exact polynomial evaluators to
the real cosine and cotangent expressions used by the Prawitz kernel.

The full-cell sine/cosine evaluator used in the finite characteristic-function
envelope has a separate source-level soundness proof.  At a nonnegative dyadic
cell midpoint it evaluates the cosine polynomial through degree `32` and the
sine polynomial through degree `33` by outward Horner arithmetic.  Lagrange
remainders give `x^33/33!` and `x^34/34!`; the global inequalities
`|sin(x)-sin(m)|<=|x-m|` and `|cos(x)-cos(m)|<=|x-m|` then expand the midpoint
hulls by the exact dyadic cell radius.  Intersecting with `[-1,1]` preserves
containment.  The theorem `trigSinCos_sound` therefore encloses both real
functions on the entire closed cell, including its endpoints, and
`certifiedCellEnvelope_sound` invokes it only after proving the input
cell's lower endpoint is nonnegative.

The remaining special function is the exponential integral.  For `x>0`, write

```text
E_1(x) := integral_x^infinity exp(-s)/s ds
        = exp(-x) * integral_0^infinity exp(-y)/(x+y) dy.    (5.1a)
```

For fixed positive `x`, the shifted integrand is nonnegative, decreasing, and
convex on `[0,infinity)`.  Consequently its composite trapezoidal rule on
`[0,24]`, with `24*32=768` intervals, step `1/32`, and all 769 grid values
(the two endpoints carrying half weight), is an upper bound.  The omitted tail
is bounded by

```text
integral_24^infinity exp(-y)/(x+y) dy <= exp(-24)/(x+24).    (5.1b)
```

Moreover `E_1` is decreasing on the positive half-line.  Thus, for a positive
parameter interval, replacing `x` by its exact lower endpoint is in the upper
direction.  The theorem `routeBE1_le_dyadicE1Up_upper` combines this
monotonicity, the convex trapezoidal bound, (5.1b), and outward dyadic
exponential, division, multiplication, and summation.  Hence the checker
upper-bounds `E_1(x)` for every real `x` in the full parameter interval; the
769 grid evaluations are a proved quadrature bound, not sampling evidence.
The change of variables is also part of the theorem chain:
`routeBE1_eq_integral_Ioi` proves (5.1a), while the quadratic substitution
`u=a*t^2` in `routeBPowerGaussianTail_eq_routeBE1` identifies the fourth
Prawitz term as `E_1(routeBTailArgument)/(2*pi)`.  Finally,
`routeB_normalizedGaussianTail_le_dyadicRouteBTailValue_upper` inserts the
outward `E_1` enclosure into the complete normalized functional.  Thus no
improper Gaussian tail is silently dropped or replaced by an equality that
has only been checked numerically.

For a monotone partition `p_0<=...<=p_N`, let `E_k` enclose the integrand on
the full closed cell `[p_k,p_(k+1)]` and let `W_k` enclose its exact width.
The proved Darboux kernel gives

```text
integral_(p_0)^(p_N) g(t) dt
  <= upper(sum_(k=0)^(N-1) W_k E_k),                        (5.2)
```

where every product and sum on the right is again outward rounded.  Thus a
strict comparison of that upper endpoint with `879/2000` proves the strict
real inequality on the whole cell, including its endpoints.

Finally, the recursive cover has the semantic implication

```text
Cover(fuel,I,J)=true
  ==> every admissible law coordinate in [I]x[J]
      satisfies sqrt(n)/rho * Delta_n < 879/2000.            (5.3)
```

The proof is induction on the fuel and then on the parsed prefix tree.  An
accepted parent invokes the leaf soundness theorem.  Otherwise both child
Booleans must be `true`; the two closed dyadic halves have union equal to the
parent and share their midpoint, so membership passes to at least one child.
This is why neither a rounding gap nor a missed bisection boundary can be
hidden by the finite topology.

A missing or malformed topology code, failed side condition, or failed child
returns `false`.  Prefix codes recovered from the 0.45 bound propose subdivisions
only; Lean reparses them and recomputes every target-aware inequality.  The
kernel-checked cover theorem proves the entire continuous closed rectangle,
including every shared bisection boundary, rather than a finite sample.

## 6. Exhaustive numerical domain

First consider the closed numerical certificate domain

```text
rho/sqrt(n) <= 56/45.                                     (6.1)
```

The final universal-complement branch lies strictly inside (6.1), while the
certificate proves the slightly larger closed domain.  It is partitioned
without a gap as follows.

1. For `1<=n<100`, cover
   `rho in [1,(56/45)sqrt(n)]` and `z=rho(r-1) in [0,1]`.
   The target-aware finite selector tries the proved `256`, `1024`, and
   `2048`-cell evaluators.  The final witness uses recursion fuel `6` for
   `n=1,...,10` and fuel `5` for `n=11,...,99`.
2. For `n>=100` and `L<=1/16`, use the two variable-alpha endpoint roots.
   Here the unit-square second coordinate is
   `w=eta/rho=r-1`, not the finite-branch parameter
   `z=eta=rho(r-1)`.  The two closed `w` ranges meet at the exact
   outward-dyadic seam
   `253327479039591/2^48 = 9/10+3/(5*2^48)` and cover the full endpoint
   rectangle; equality at the seam is sent to the lower root.
3. For `n>=100` and `1/16<L<=1/10`, use the direct middle closed unit square,
   whose second coordinate is again `w=eta/rho=r-1`.
4. For `n>=100` and `1/10<L<=56/45`, use the direct upper closed unit square,
   whose second coordinate is `v=10 eta/sqrt(n)`.  The exact affine first
   coordinates rescale the displayed `L` intervals to `[0,1]`.

The weak boundary at each internal large-regime split belongs to the lower
branch, so `L=1/16` and `L=1/10` are covered; the closed upper certificate
also covers `L=56/45`.  Coordinate inverse lemmas put every admissible law
point in the corresponding closed root.

Finite-cover monotonicity is proved structurally:

```text
C_f(n;I_rho,I_z)=true  ==>  C_(f+1)(n;I_rho,I_z)=true.    (6.2)
```

If the parent is accepted, every larger-fuel call returns immediately.  If
not, both fuel levels take the same deterministic split and induction applies
to the two closed children.  The theorem is lifted through the complete old
leaf tree and the fail-closed parser.  The execution optimization is separately proved equal to the canonical
checker for all inputs, including its cache and admissibility tests. For
`n=1,...,10,21,...,99`, the exact original prefix trees are partitioned into
2309 independently checkable numerical subtrees. Each of the 89 per-`n`
assemblies checks its complete parsed topology and composes every subtree;
the old exported finite-batch theorem statements are unchanged. The
`n=11,...,20` batch is reused as one accepted original witness. This
changes the size of executable proof units, not the numerical proposition.
The accepted leaves include all of the difficult `n=3,4` domains; no
discovery-range verdict is substituted for a final theorem.

Instantiating the four concrete certificate families, the kernel theorem

```text
targetAware_normalizedKolmogorovDistance_lt_879_2000
```

therefore proves

```text
sqrt(n)/rho * Delta_n < 879/2000                           (6.3)
```

for every point in (6.1), every admissible law, and every `n>=1`.

## 7. Universal branch and final assembly

Set

```text
C = 879/2000,              R = 1090/879.
```

Exact rational arithmetic gives

```text
C R = 109/200,
R < 56/45,
56/45-R = 58/13185 > 0.                                  (7.1)
```

For any `n>=1`, split on `R<=rho/sqrt(n)`.

The existing standardized-sum moment lemmas apply under the original
`MemLp 3`, centering, variance, independence, and identical-distribution
hypotheses: the law of `S_n` is a probability measure, its identity map is in
`L^2`, its mean is zero, and its variance is one.  It therefore satisfies all
hypotheses of the distribution-free `109/200` estimate used below.

For completeness, write `F` for the CDF of an arbitrary centered variance-one
law and `Phi` for the standard-normal CDF.  One-sided Chebyshev--Cantelli gives,
for every `a>0`,

```text
P(Y<=-a) <= 1/(1+a^2),       P(Y>=a) <= 1/(1+a^2).
```

The point `x=0` is separate: `Phi(0)=1/2` and `0<=F(0)<=1`, hence
`|F(0)-Phi(0)|<=1/2` without invoking Cantelli.  If `x<0`, put `a=-x>0`.
Then `Phi(x)<=1/2`, so the lower signed error is at least `-1/2`.  If also
`a<=1`, the certified bound `Phi(-a)>=1/2-2a/5` reduces the upper signed error
to

```text
1/(1+a^2)-1/2+2a/5 <= 109/200.                           (7.2)
```

If instead `a>=1`, Cantelli gives `F(x)<=1/2`, so the upper signed error is at
most `1/2` as well.

If `x>0`, put `a=x`.  Since `Phi(x)>=1/2`, the upper signed error is at most
`1/2`.  Moreover

```text
Phi(x)-F(x)=(1-F(x))-(1-Phi(x)),
1-F(x)=P(Y>x)<=P(Y>=x)<=1/(1+a^2).
```

For `a<=1`, the certified normal-tail bound
`1-Phi(a)>=1/2-2a/5` again reduces the remaining signed error to (7.2).  For
`a>=1`, Cantelli bounds `1-F(x)` by `1/2`, while `1-Phi(x)>=0`, so that signed
error is at most `1/2`.  Thus only (7.2) remains in either central half-line.

After multiplying by the positive denominator `200(1+a^2)`, (7.2) is
equivalent to

```text
p(a)=9-80a+209a^2-80a^3 >= 0.
```

If `0<=a<=1/4`, then

```text
p(a)=20a^2(1-4a)+(189a-40)^2/189+101/189 >= 0.
```

If `1/4<=a<=1`, then

```text
p(a)=13/16+(a-1/4)q(a),
q(a)=(a-1/4)(169-80a)+19/2 >= 0.
```

The Lean source mirrors these exact steps.  The lemmas
`standardNormalCDF_neg_linear_lower` and
`standardNormalUpperTail_linear_lower` supply the two normal-tail inequalities;
`refinedUniversalRationalEnvelope_le` is (7.2), and
`refinedUniversal_kolmogorov_bound` performs the negative/zero/positive signed
CDF split.  At the regime boundary,
`bound4395Target_mul_universalCutoff` proves `C*R=109/200`, while
`bound4395UniversalCutoff_lt_routeBCutoff` and
`bound4395_complement_inside_routeB` prove that the complementary branch is
strictly inside the numerical domain.  These are exact real inequalities, not
decimal comparisons performed by the certificate search.

Since `1/2<=109/200`, the zero case, both easy signed errors, the two outer
regions, and (7.2) together show
`|F(x)-Phi(x)|<=109/200` for every real `x`.  This proves the claimed
distribution-free bound without extending the `a>0` Cantelli statement to
`a=0`.

- In that branch, the proved distribution-free estimate
  `Delta_n<=109/200` and (7.1) give
  `Delta_n<=C rho/sqrt(n)`.
- In the complementary branch,
  `rho/sqrt(n)<R<56/45`; (6.3), positivity of `rho` and `sqrt(n)`, and weak
  closure of the strict bound give (1.1).

This proves (1.1) for every positive integer and every law satisfying the
original assumptions using the four instantiated exact numerical certificate families: finite, the paired small-endpoint roots, middle, and upper.  The
internal numerical proposition is discharged by those certificates and is not
a hypothesis of the public theorem.

## 8. Exact differences from the 0.45 bound

The comparison baseline is the proved 0.45 theorem at `9/20=0.45`, not its
internal strict certificate threshold `4495/10000`.  The new theorem
constant improves the theorem by

```text
9/20-879/2000 = 21/2000 = 0.0105,
(9/20-879/2000)/(9/20) = 7/300.
```

Thus the absolute improvement over the current theorem is `0.0105` (a
`7/300` relative reduction).  The smaller number `1/2000=0.0005` is only the
margin by which `879/2000` lies below the requested `0.44` milestone.

| Component | the 0.45 bound (`0.45`) | the 0.4395 bound (`879/2000`) |
| --- | --- | --- |
| Public theorem interface | Classical i.i.d., centered, variance one, `MemLp 3`, every `n>=1` | Byte-for-byte the same binders and assumptions after renaming only the conclusion; the all-`n` definition also differs only in the target name |
| Public target | `9/20` | `879/2000`, with exact dominance proofs over both `11/25` and `9/20` |
| Universal branch | Distribution-free constant `14/25` and cutoff `56/45` | New distribution-free constant `109/200` and cutoff `1090/879`; the complementary branch lies inside the unchanged numerical ceiling `56/45` by `58/13185` |
| One-factor characteristic comparison | Shared-`r` disk and trivial bound | Retains those bounds, strengthens their modulus factor by the radial real/imaginary rectangle, and adds the Rademacher comparison |
| Difficult-strip modulus rate | No radial `39/100` exponent | On `r>=19/10` and the proved frequency range, `|f(u)|<=exp(-(39/100)u^2)` from the same law hypotheses |
| Large-`n` telescoping loss | Fixed coefficient `99/100` applied to the 0.45 convex-minorant exponent | Strong small-`L` branch uses `a(L)`; direct middle/upper keep `99/100`. Strong branches use `max(Q_old,Q_rate)` only at `t<=1/4` and retain `Q_old` elsewhere |
| Numerical threshold and witnesses | Strict `4495/10000` certificate feeding the weak `0.45` theorem | Strict `879/2000` target-aware leaves on the same full continuous law domain; finite fuels `6/5`, small-endpoint fuels `4/8`, middle fuel `5`, and upper fuel `8` |
| Verification boundary | Original 0.45 release and its accepted certificate | Accepted 2480-module closure: 2407 precisely named native witnesses and 73 non-native modules; the exact theorem audit has these 2407 witnesses plus 3 standard axioms. The 0.45 bound proof sources and release remain unchanged |

The improvement is therefore not obtained by changing the law class, omitting
small `n`, shrinking the continuous parameter domain, or merely subdividing
the old boxes more aggressively.  Its analytic inputs are the radial modulus
rate, variable telescoping coefficient, strengthened pointwise exponent, and
the sharper distribution-free branch; the new exact boxes certify the
resulting lower target.

## 9. Concrete evidence and trust boundary

The accepted immutable source manifest has SHA-256
`9c1e559233d9df46fffb39e0e4171ffaa2a89d1ea954ab816f7fa9844fbee546`.
It refines the original proof snapshot
`76120b0d7d0b926c9c92f1e606ab9da45dd18ac62f9cb2a560b2299c8f785534`
by replacing nine monolithic finite batches with exactly equivalent
subtree assemblies. The source manifest, module dependency order and
native theorem names are carried in the portable evidence bundle and
its `plan.json`.

The final native inventory is:

| Kind | Exact number | Mathematical role |
| --- | ---: | --- |
| Finite numerical subtrees | 2309 | Recompute every assigned target-aware continuous leaf certificate |
| Per-`n` parsed topologies | 89 | Establish that the subtrees reconstruct the complete original tree |
| Reused original witnesses | 8 | One finite batch (`11..20`), two small endpoints, four middle batches, one upper root |
| Middle topology parse | 1 | Connect the four disjoint middle batches to the complete middle domain |
| Total named native witnesses | 2407 | All occur in the exact final theorem axiom inventory |
| Non-native modules | 73 | Analytic bounds, checker soundness, compositions, interface and final audits |

All 2480 main-environment module records passed. In the fresh environment
all 73 non-native modules were re-elaborated against the exact successful
native witnesses; every source, direct import and object hash was checked.
The final theorem in that execution was named
`BerryEsseen.iidBerryEsseen879_2000_targetAware`; its publication name is
`BerryEsseen.iidBerryEsseen879_2000`. The executed axiom set consists of the 2407 individually enumerated
`_native.native_decide.ax_1_1` witnesses and only
`propext`, `Classical.choice`, `Quot.sound`: 2410 entries in total.

The 102 `include_str` inputs are unchanged, manifest-bound 0.45 Lean
files read as literal data. They are included in the fresh compilation
tree and in the portable archive; the parser and checkers still establish
their mathematical meaning. The executor identity is
`9b9cd394df4899a99510a71b7e52b08d0bd934824712f05b21309a79d9f79587`.

The portable bundle `subtree-final-evidence.tar.gz` has SHA-256
`fc8fc61454025e27ae5508ec438ecc56c5f6318d35b0b20f94b14783e7d9f84f`
and 22,729 inventoried artifacts. Safe extraction followed by the
independent verifier passed on 2026-09-06 at 05:53:32 UTC.
The verifier checks the complete archive inventory, source and dependency
identity, successful records, fresh replay, literal inputs, and the exact
axiom set; it does not merely accept a server-written success flag.
The dependency pins are Lean 4.29.1, Mathlib v4.29.1, and StatLean
`e1ef06bf52d2a8896439c5b59d982d9aad28a254`.

Lean kernel checking proves the analytic implications, interval containment,
closed-domain coverage, and composition. The concrete Boolean facts use
Lean's native evaluation trust boundary; their computations are not
kernel-only reductions. Python discovers partitions, schedules work, and
checks evidence identity, but its numerical verdicts are not premises
of the Lean theorem. Reusing a hash-identical accepted native witness is
different from repeating its expensive computation in the fresh environment;
the evidence records this distinction explicitly.

The source-facing review locators are:

- moment geometry and radial bounds:
  `BerryEsseen.Moments.FirstAbsoluteMoment`, `BerryEsseen.CharacteristicFunctions.TwoPointComparison`,
  `BerryEsseen.CharacteristicFunctions.ComponentBounds`;
- finite semantics, exact evaluator equality and subdivision soundness:
  `BerryEsseen.Smoothing.FiniteEnvelope`, `BerryEsseen.Interval.Finite.AdaptiveFullCover`,
  `BerryEsseen.Interval.Finite.FastEvaluator`, `BerryEsseen.Interval.Finite.FastCover`,
  `BerryEsseen.Interval.Finite.Subtree`;
- feasible disk, radial rate and variable coefficient:
  `BerryEsseen.CharacteristicFunctions.GaussianCorrection`, `BerryEsseen.CharacteristicFunctions.ExponentialModulus`,
  `BerryEsseen.Smoothing.VariableExponentComparison`,
  `BerryEsseen.Interval.Small.IntegralSoundness`;
- all-regime and universal assembly:
  `BerryEsseen.Theorems.NumericalAssembly`,
  `BerryEsseen.Smoothing.UniversalSplit`;
- final theorem and trust checks:
  `BerryEsseen.Theorems.Bound04395`,
  `BerryEsseen.Verification.FinalAxiomAudit`,
  `BerryEsseen.Verification.Comparisons.ConclusionMonotonicity`.
