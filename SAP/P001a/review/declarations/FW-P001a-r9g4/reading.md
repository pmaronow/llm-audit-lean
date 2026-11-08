# Blind reading

Saved before opening `claims.json` or `record.json`. The source statements,
docstrings, and every entry of `closure.json` were read. Compiler-generated
entries were inspected with `scratch/ClosurePrint.lean`; its successful output
is in `scratch/closure-print.log`. No Solution or other review was consulted.

## SAP.P001a.T16

The Challenge declaration at `SAP/P001a/Challenge/Part1.lean:122` asserts
`T16Statement`, defined at `SAP/P001a/Defs/Part4.lean:214`. It is a conjunction
of five assertions. Its docstring describes a restricted matching example,
with an estimated additive score, bootstrap failure, and a conditional variance
identity, and explicitly lists several omissions.

Here are all the underlying mathematical definitions. A unit is a triple
`(p,d,e)` in `ℝ × Bool × Bool`. Write `η(e)=1` for true and `−1` for false.
For a finite array with index set `Fin n={0,…,n−1}`, scores `p_i`, donor flags
`r_i`, and target index `i`, `nearestDonor p r i` is `some j` for a classically
chosen donor satisfying `r_j=true` and
`|p_j−p_i|≤|p_k−p_i|` for every donor `k`. It is `none` if no minimizer exists.
Finite nonempty donor sets have a minimizer. Ties have an arbitrary fixed
choice; no additional ordering rule is specified.

`causalMatch(s)` is minus the following sum divided by the real number `n`:
for each treated unit (`d_i=true`), use the sign of its nearest control
(`r_j=not d_j`), or zero if no such control exists; for each control, use its
own sign. Thus it is `−n⁻¹ Σ_i η(e_{j(i)})` with the stated control and
missing-donor conventions. Define

* `δ(s)=max(1/8,min(3/8,n⁻¹ Σ_i [1_{d_i=true}−(p_i−1/4)]))`;
* estimated score `p̂_i=δ(s)+p_i−1/4`;
* `causalMatchEstimated(s)` by applying the same causal statistic to
  `(p̂_i,d_i,e_i)`, re-estimating `δ` whenever the statistic is evaluated;
* `resample(s,a)=s∘a`, for every function `a:Fin n→Fin n`;
* `bootMean(T,s)=n^(−n) Σ_a T(s∘a)` and
  `bootVar(T,s)=n^(−n) Σ_a [T(s∘a)−bootMean(T,s)]²`.

For positive `n` this is the complete distribution of an ordinary size-`n`
bootstrap with independent uniform draws of indices. The conditional donor
reuse weight is zero for a nondonor, and for a donor `j` it is one plus the
number of nondonor targets whose chosen nearest donor is `j`. The sign law is
the product over `Fin n` of `(δ_true+δ_false)/2`.

The unit law is Lebesgue measure in `p` times counting measure on both Boolean
coordinates, with density `p` if `p∈[1/4,3/4]` and `d=true`, density `1−p`
there if `d=false`, and zero outside that interval, for each sign. Equivalently
`p` is uniform on that interval, `d|p` is Bernoulli(`p`), and `e` is an
independent fair sign. Its total mass is one: summing over signs supplies the
factor two missing from the interval length `1/2`.

For a measure `μ`, `prob μ A=(μ A).toReal`, `mean μ f=∫f dμ`, and
`var μ f` is Mathlib's real variance: the `toReal` of
`∫⁻ω ‖f(ω)−∫f dμ‖ₑ² dμ`.
`CP μ Z c` means, for every real `ε>0`,
`(μ{ω:ε≤dist(Z_n(ω),c)}).toReal→0`.
`IID μ Z` means each `Z_i` is measurable, the indexed family is independent,
and every `Z_i` is identically distributed with `Z_0` under `μ`.
`firstSample Z n ω` is the array `i↦Z_i(ω)` for `i:Fin n`.

Write `s=1−exp(−1)`, `A=2/s−s/(2−s)`,
`B=3/(2s)−(4−s)/(2(2−s))`,
`V=3 log 3−1/4`, and `VB=1/2+A/2+B(2 log 3−3/2)`.
The quantifiers and conclusions of the five assertions are:

1. For every type `Ω` in the first universe, measurable structure, probability
   measure `μ`, and sequence `Z:ℕ→Ω→ℝ×Bool×Bool`, assume `IID μ Z`,
   `μ.map(Z_0)=matchingUnitLaw`, and, for every natural `n`, membership in
   `L²(μ)` both of the estimated matching statistic and of its bootstrap
   variance. Then for every positive `n` the statistic has expectation zero;
   `n Var(T̂_n)→V`; `E[n bootVar(T̂,s_n)]→VB`; `0<VB<V`; and the sequence
   `n bootVar(T̂,s_n)` does not converge in probability to `V`.
2. Independently, for every probability space in the second universe and every
   iid sequence with that same unit law, `δ(s_n)→1/4` in probability. No `L²`
   premises are imposed in this conjunct.
3. For every natural `n`, every finite array `s`, every Boolean donor vector
   `r`, and every `i:Fin n`, the chosen nearest donor computed from `p̂` equals
   the chosen nearest donor computed from the original `p` (equality of
   `Option (Fin n)`, including its chosen tie).
4. For every natural `n` and every array `s`, the estimated and original causal
   matching statistics agree. This also applies to every resampled array,
   although resamples are not separately quantified in this conjunct.
5. For every positive natural `n`, arbitrary real scores `p` and Boolean
   treatment flags `d`, and then every sign vector `e`, the causal statistic is
   `−Σ_j w_j η(e_j)/n`, where `w` uses the control donor flags `not d`.
   The product sign measure is a probability measure; the conditional mean is
   zero; its variance is `Σ_j w_j²/n²`.

All SAP definitions in this closure have thus been expanded, including `clip`,
`noise`, `resample`, `firstSample`, the bootstrap averages, and the constants.
The closure's `hotDeck.match_1` is only the `Option` case splitter used to
implement a missing-donor branch. Its appearance adds no hot-deck assumption.

Junk and boundary conventions:

* Real division by zero gives zero. At `n=0`, both matching statistics are zero,
  the empty empirical intercept before clipping is zero, and `δ=1/8`.
  The bootstrap index type then has one function and its denominator is
  `0^0=1`; its mean and variance of this statistic are zero. Positive-`n`
  clauses and limits at infinity do not use an empty-sample inference.
* No-control arrays return zero, and the reuse weights then are all zero.
  This agrees with the displayed identity. No partial function is called on
  an invalid index. For positive `n`, `n^n` and `n²` are positive.
* `Classical.choose` implements a possible tied minimizer, not a dummy donor.
  Equality after score translation is a substantive assertion about this
  definition. Under the continuous iid law, original distinct-score distance
  ties have probability zero; bootstrap duplicates carry the same sign.
* Nonintegrable Bochner integrals default to zero; infinite extended variance
  defaults to zero after `toReal`. The `L²` premises exclude these failures in
  the limiting-statistic conjunct. Conditional sign variables are finite.
  `prob` cannot send an infinite measure value to zero here because the
  measures under discussion are probability measures.
* The logarithm is only `log 3`. The denominators `s` and `2−s` are nonzero
  because `0<1−exp(−1)<1`. There is no square root, real power, truncated
  subtraction, infimum, supremum, limsup, or liminf in this closure.
* Natural sample sizes and finite cardinalities are cast into `ℝ`; no lossy
  cast or integer division is used in the matching formulas.

## SAP.P001a.T17

The Challenge declaration at `SAP/P001a/Challenge/Part1.lean:127` asserts
`T17WholeStatement` (`Defs/WholeW2.lean:288`), which includes
`T17Statement` (`Defs/Part5.lean:18`). Its docstring claims an actual causal
null law, population calculations, almost-sure divergence, test rejection,
an actual 240-row sample, and existence of an infinite iid experiment.

The finite probability space has indices `i:Fin 12`. Set
`x_i=−1,0,1` according as `i.val/4=0,1,2`,
`z_i=−1` if `i.val%4<2` and `1` otherwise,
`d_i=1` if `i.val%2=1` and `0` otherwise, and `w_i=x_i²+z_i/2`.
For `x_i=0`, odd indices have mass `1/24` and even indices `1/8`;
for `x_i=±1`, odd indices have mass `1/8` and even indices `1/24`.
`FiniteLaw 12` packages these nonnegative weights with the proof that their
sum is one. Its constructor and `weight` projection carry no further data.
`fmean(P,f)=Σ_i P_i f_i` and `fprob(P,A)=Σ_{i:A(i)} P_i`.
`finiteLawMeasure(P)=Σ_i ofReal(P_i) δ_i`.
`fcond(P,Y,X,x)=Σ_{i:X_i=x} P_iY_i / fprob(P,{X=x})`.
`FCondIndep(P,Y,Z,X)` quantifies, in order, every value `x`, `y`, `z`;
if `P(X=x)>0`, it asserts
`P(X=x,Y=y,Z=z)P(X=x)=P(X=x,Y=y)P(X=x,Z=z)`.
This is conditional independence on a finite law, also when `Y` is a pair.

The regressor is `q_i=(1,x_i,w_i)`, its moment matrix is
`M_jk=Σ_i P_i q_ij q_ik`, and the population risk is
`r(a,b,c)=Σ_i P_i(d_i−a−b x_i−c w_i)²`.
For any finite design matrix `H` and response `y`, the coefficient is
`β(H,y)=(HᵀH)⁻¹Hᵀy`; residual sum of squares is `Σ_i(y_i−(Hβ)_i)²`.
HC0 is `(HᵀH)⁻¹Hᵀ diag(e_i²) H(HᵀH)⁻¹` with actual fitted residuals.
The partial F statistic for `K` baseline and `L` added columns is
`[(RSS_R−RSS_F)/L]/[RSS_F/(n−(K+L+1))]`, with an intercept in both matrices.
The sample statistics here use `K=L=1` and the first `n` atoms of `Z`:
`F_n` is that F statistic, and `Wald_n=β̂_2²/HC0_22`.
The reference `F(k,v)` is the distribution of the ratio of the mean of `k`
independent squared `N(0,1)` coordinates to the mean of `v` further independent
squared `N(0,1)` coordinates. `prob` and `IID` have exactly the meanings
expanded in T16.

The full assertion is the conjunction of the following:

1. For every measurable type `Ω`, probability measure `μ`, and
   `Z:ℕ→Ω→Fin 12`, if `Z` is iid and `Z_0` has the displayed finite law, then:
   `w ⟂ d | x` and `(2+z,3+z) ⟂ d | x`; `det M=17/54`;
   `(29/68,0,4/17)` is the unique minimizer of `r` over all real `a,b,c`;
   almost surely `F_n/n→64/531` and `Wald_n/n→18496/135315`;
   for every `α∈(0,1)` and every sequence of real critical values satisfying
   `P(F(1,n−3)≤critical_n)=1−α` for all `n>3`,
   `P(F_n>critical_n)→1`; for every fixed real `c`,
   `P(Wald_n>c)→1`. It also asserts the numerical identities
   `240 r(7/12,0,0)=175/3`, `240 r(29/68,0,4/17)=885/17`, and the resulting
   F ratio `5056/177`.
2. Independently of that conditional universal, the finite law has both
   conditional independences; at every atom's `x`, its conditional treatment
   mean lies strictly between `1/8` and `7/8`; its conditional variance of
   `w` is `1/4`; `det M=17/54`; its unique full minimizer is as above and
   its unique restricted minimizer is `(a,b)=(7/12,0)`.
   The restricted and full risks are respectively `35/144` and `59/272`,
   the latter is strictly smaller, and `4/17≠0`.
3. For every real `x,z,d`, its joint mass equals
   `1_{x∈{−1,0,1}}/3 × 1_{z∈{−1,1}}/2 × Bern(1/4+x²/2,d)`.
   Here `Bern(p,d)=p` at `d=1`, `1−p` at `d=0`, and zero otherwise.
   For every `x` in the three-point support and every real `w,d`, the
   conditional joint mass of `(w,d)|x` is `Bern(1/4+x²/2,d)/2` at either
   `w=x²−1/2` or `w=x²+1/2`, and zero otherwise.
4. A structural space `((Fin 3×Bool)×Fin 4)` has the product of uniform
   baseline mass `1/6` and uniform seed mass `1/4`. Its atom map is
   `4b_x+2·1_{b_z=true}+1_{seed<t(b_x)}`, where `t(1)=1` and otherwise `t=3`.
   This is a valid `Fin 12` value, its pushforward is the finite law, and
   `x=b_x−1`, `z=η(b_z)`,
   `W(b,d)=(b_x−1)²+η(b_z)/2`,
   `Y(b,false)=2+η(b_z)`, `Y(b,true)=3+η(b_z)`.
   `W(b,false)=W(b,true)` for every baseline. The structural measure is a
   probability measure.
5. The eight asserted moments are `Ex=0`, `Ex²=2/3`, `Ed=7/12`, `Exd=0`,
   `Ew=2/3`, `Exw=0`, `Var(w)=17/36`, and `Cov(w,d)=1/9`.
6. There exists an array `s:Fin 240→Fin 12` with exactly 30 copies of each
   mass-`1/8` atom and 10 copies of every other atom. For every such array,
   restricted OLS coefficients are `(7/12,0)`, full OLS coefficients are
   `(29/68,0,4/17)`, the two RSS values are `175/3` and `885/17`, and the
   actual F statistic is `5056/177`. The asserted rounding error from 28.6
   is less than 0.05. The statement does not use the separately defined
   `W2PlaceboSample240` function as a witness; that function is not in the
   elaborated closure.
7. For every probability space and iid realization with that law, almost
   surely `F_n→+∞` and `Wald_n→+∞` (separate almost-sure assertions).
8. There exists a probability measure on `ℕ→Fin 12` for which the coordinate
   maps are iid and coordinate zero has the displayed law.

Junk and boundary conventions:

* Finite weights are all strictly positive, so all conditional divisions at
  the three stated `x` values have denominator `1/3`. `fcond` returns zero
  off the support, but these off-support values are not asserted to be
  conditional expectations. `FCondIndep` guards zero conditioning mass.
* Sample Gram inverses are zero matrices when singular. Consequently the
  displayed formula is a totalized statistic on rank-deficient samples;
  likewise division by a zero RSS or zero HC0 entry returns zero. Small
  samples, including `n=0`, can use these conventions. The full-rank finite
  sample has neither problem. Positive definite population moments and the
  positive asymptotic variances make these bad events asymptotically
  irrelevant, rather than serving as an asserted test calibration there.
* The F formula subtracts degrees of freedom in `ℝ`, so this is not truncated
  subtraction. The reference has a natural `n−3`, which is truncated, but
  its critical-value hypothesis is required only for `n>3`. Its numerator
  degree is one and its denominator degree is then positive. A zero Gaussian
  denominator is null for those degrees; the real-valued ratio is totalized
  to zero on that null set. No inference uses an F law with zero degrees.
* All finite means and risks exist. All probability values used with
  `toReal` are finite. The iid sample statistics are finite-valued functions
  on finite sets for each `n`; no nonintegrability convention is exploited.
* Integer quotient/remainder in atom labels and finite-cardinality counts
  encode the stated table exactly. All sample-size casts are exact.
  Empty finite sums are zero and empty products one. There are no logarithms,
  roots, real powers, infima, suprema, limsups, or liminfs in this assertion.

## SAP.P001a.T18

The Challenge declaration at `SAP/P001a/Challenge/Part1.lean:140` asserts
`T18WholeStatement` (`Defs/WholeW1.lean:461`), not the older `T18Statement`
in Part5. Its docstring asserts a conditional-mean implication, population
linear projection, actual OLS and HC0 asymptotics, null Wald inference,
and an interpretation without the conditional-mean specification.

For finite natural dimensions `K,L`, set `p=K+L+1`. Baseline and placebo
vectors have types `Fin K→ℝ` and `Fin L→ℝ`; the intercept is always present.
Write `z=(1,x,w)`, `b₀=(γ_0,γ_1,…,γ_K,0,…,0)`, and let `R_W` select the
last `L` coordinates. These are respectively `wholeDesign`, `wholeNullCoef`,
and `wholePlaceboSelector`.

For any measure, `IsCEF μ X D m` means `m` is measurable, `D` and `m∘X`
are integrable, and for every measurable `A` in the covariate space,
`∫_{X⁻¹A} D dμ=∫_{X⁻¹A} m(X) dμ`. In particular
`linearPredictor γ x=γ_0+Σ_k γ_{k.succ}x_k`.
`CI μ X hX W D` means that for every measurable set `A` of placebo values and
`B` of treatment values,
`E[1_{W∈A,D∈B}|σ(X)] = E[1_{W∈A}|σ(X)]E[1_{D∈B}|σ(X)]` almost surely.
This uses Mathlib conditional expectation for the comap sigma algebra of `X`.

`WholePlaceboDesign μ X W D` consists exactly of measurability of `X,W,D`,
`D∈{0,1}` almost surely, `0<P(D=1)<1`, `L²` membership of each coordinate
of `X` and `W`, and nonzero determinant of `Q=E[zzᵀ]`.
`WholePlaceboNull μ X W D γ` consists of all these conditions, the above
conditional independence, and `IsCEF μ X D (linearPredictor γ)`.
`IsUnit det Q` means `det Q≠0` over the real numbers.

For arbitrary coefficient vector `b`, the risk is `r(b)=E[(D−zᵀb)²]`,
residual `u=D−zᵀb`, moment matrix `Q=E[zzᵀ]`, score covariance
`Ω=E[u²zzᵀ]`, and sandwich `S=Q⁻¹Ω(Q⁻¹)ᵀ`.
The fitted matrix has rows `z_0,…,z_{n−1}`, and the actual OLS estimate
is `(AᵀA)⁻¹AᵀD`. `wholeHC0` uses these fitted residuals in
`(AᵀA)⁻¹Aᵀdiag((D_i−z_iᵀβ̂)²)A(AᵀA)⁻¹`.
The root error is `sqrt(n)(β̂_n−b)`.

`WeakLimit μ U ν` means convergence of `∫f(U_n)dμ` to `∫f dν` for every
continuous real-valued bounded function `f` (bounded by some real constant).
`normalVectorLaw(S)` is Mathlib's centered multivariate Gaussian, mapped from
Euclidean coordinates to `Fin p→ℝ`. `CP` has the tail-probability definition
given under T16, using the finite-product metric also for matrices.
`CD μ U ν` means CDF convergence at every point where the target CDF is
continuous. Its CDF is `(μ{U≤x}).toReal`.
`wholeChiSquare(m)` is the pushforward of `m` independent standard Gaussian
coordinates under `Σ_j z_j²`.
For an `m×p` real matrix `R`, Wald is
`(Rβ̂)ᵀ(R C Rᵀ)⁻¹(Rβ̂)` when supplied covariance `C`; the joint region
is the set of `t:Fin m→ℝ` satisfying
`(Rβ̂−t)ᵀ(R C Rᵀ)⁻¹(Rβ̂−t)≤q`.

The theorem is the conjunction of these four quantified assertions:

1. For every measurable type, probability measure, finite `K,L`, functions
   `X,W,D`, coefficient vector `γ`, and proof of `WholePlaceboNull`, the same
   linear baseline predictor is a CEF of `D` given `(X,W)`. For every real
   coefficient vector `b`, `r(b₀)≤r(b)` and `r(b)=r(b₀)` iff `b=b₀`.
2. For every probability space and design satisfying only
   `WholePlaceboDesign`, let `b=Q⁻¹E[zD]`. For every coefficient vector `a`,
   `r(a)=r(b)+(a−b)ᵀQ(a−b)`. There exists a baseline-only coefficient
   vector `γ` attaining this unrestricted risk iff `R_W b=0`.
   There is no conditional independence or CEF premise in this conjunct.
3. For every probability space, finite dimensions, sequences `X,W,D`,
   joint iid hypothesis on `i↦(X_i,W_i,D_i)`, vector `γ`, and
   `WholePlaceboNull` for index zero, actual OLS converges in probability to
   `b₀`; its centered root-`n` error converges weakly to `N(0,S)`; and
   `n HC0_n→S` in probability. Then, in order, for every positive natural
   `m`, real `m×p` matrix `R` with `Rb₀=0` and `det(RSRᵀ)≠0`, and
   `α∈(0,1)`, there exists a real `q` with
   `P(χ²_m≤q)=1−α`, CDF convergence of the feasible Wald statistic to
   `χ²_m`, rejection probability `P(Wald_n>q)→α`, and probability
   `P(0∈jointRegion_n(q))→1−α`. The region coverage in the statement is
   explicitly for zero under `Rb₀=0`, not a separately quantified nonzero
   coefficient target. These are tests of arbitrary zero linear restrictions,
   not only of the placebo selector.
4. For the precise twelve-atom law unfolded under T17,
   `w ⟂ d | x`, `4/17≠0`, and the unique full linear risk minimizer is
   `(29/68,0,4/17)`.

The hypotheses do not take OLS convergence or covariance convergence as inputs.
The other structures appearing nearby in WholeW1, `WholeScoreMoments` and
`WholeGramLimits`, are not dependencies of the elaborated target statement.

Junk and boundary conventions:

* Bochner integrals and conditional expectations have a zero default on
  nonintegrability. Conditional expectation also defaults to zero if its
  sigma algebra is not a subalgebra or the trimmed measure is not sigma
  finite. Measurability of `X`, bounded indicators, and the probability
  measure exclude these cases. Finite second moments and binary `D`,
  together with a genuine CEF in the null conjuncts, make all population
  risks, cross moments, and sandwich quantities well defined. In particular
  the true residual is bounded by one almost surely, and its score has a
  second moment without an extra fourth-moment hypothesis.
* Singular real matrices have inverse zero. The population Gram rank
  hypothesis excludes that value for `Q`; the tested limiting covariance
  rank excludes it for `RSRᵀ`. Sample matrices can be singular at finite `n`;
  OLS, HC0, Wald, and the inverted region use the totalized inverse there.
  These are asymptotic statements under a nonsingular population Gram and,
  for Wald inference, nonsingular limiting tested covariance. Such singular
  sample events disappear asymptotically and are not used as a source of
  calibration. The region can be the whole space for a zero sample
  covariance; this is subject to the same observation.
* Mathlib's multivariate Gaussian defaults to a point mass if the supplied
  covariance is not positive semidefinite. Here `Ω` is an integrable
  expectation of positive semidefinite matrices and `S` its congruence, so
  this default is not used. `S` itself may be singular; the corresponding
  degenerate Gaussian is a legitimate limit.
* `sqrt(n)` only sees nonnegative real casts of naturals; `sqrt(0)=0` is
  harmless at the empty sample. No negative root occurs. `K` or `L` may be
  zero; their sums then vanish, while the intercept leaves `p≥1`. Tests
  separately require `m>0`; the empty chi-square law is not used for them.
* All `toReal` calls are on probability values, not infinity. There is no
  truncated subtraction, logarithm, real power, supremum, infimum, limsup,
  liminf, or partial-function default elsewhere in this closure.

## SAP.P001a.T19

The Challenge declaration at `SAP/P001a/Challenge/Part1.lean:152` asserts
`T19Statement` (`Defs/Part5.lean:81`). Its docstring labels the printed claim
false and describes a restricted positive-countable-mass witness to the
absence of a uniform positivity margin, with a stated omission of a different
explicit propensity rate and a selected covariate.

There are no external objects or hypotheses. For every natural number `k`,
define `t_k=(1/3)^(k+1)`, `c_k=(1/2)^(k+2)`, and
`p_k=t_k/(t_k+c_k)`. The theorem says that both real series are summable,
their respective sums are `1/2`, for every `k` both masses are strictly
positive and `0<p_k<1`, and there does not exist a real `ε>0` such that for
every `k`, `ε<p_k<1−ε`. These are all the conjuncts and quantifiers.

If interpreted as joint masses of `X=k` with the two binary treatment arms,
the total mass is one, both arm probabilities are `1/2`, both conditional
discrete supports are all of `ℕ`, and `p_k` is the conditional treatment
probability. This interpretation is provided by the numbers; no measure,
random variable, support predicate, selected `k`, or limit of `p_k` is an
explicit object or conclusion of the theorem. Directly,
`t_k/c_k=(4/3)(2/3)^k`, so the propensity decreases to zero.

Junk and boundary conventions:

* Every denominator `t_k+c_k` is strictly positive. Natural exponents have
  positive real bases and positive exponents; there is no `0^0`, real-power
  extension, or truncated subtraction. Casts in this definition are just
  rational constants, and there is no cast of an unbounded index in the
  propensity formula.
* A real `tsum` defaults to zero for a nonsummable series, but both
  `Summable` assertions exclude that case. These positive geometric series
  have their ordinary sums `1/2`.
* There are no integrals, real logarithms or roots, `toReal`, empty index
  types, infima, suprema, limsups, liminfs, or partial choices in this closure.

## Compiler-generated closure entries

All 63 distinct entries whose source location is line zero were printed and
their types inspected. Except as noted next, they are proofs of the
`AtLeastTwo` property of explicit positive numerals, proofs that `K+1` or `3`
is nonzero for finite indexing, or the scalar-tower instance for extended
nonnegative reals. These encode numeral and indexing elaboration only. This
includes every numbered auxiliary of `T17Statement`, `T18WholeStatement`,
`W2PlaceboMoments`, `W2PlaceboSampleFacts`, `estimatedMatchIntercept`,
`matchingUnitLaw`, and the other numerically named ancestors in the closures.
`placeboLaw._proof_3` proves exactly weight nonnegativity, and
`placeboLaw._proof_4` proves exactly that its twelve weights sum to one.
`W2PlaceboStructuralAtom._proof_9` proves that the displayed structural atom
index is less than twelve. `hotDeck.match_1` is the ordinary `Option`
eliminator described under T16. None introduces a hypothesis or an alternative
mathematical definition. The closure file and successful #print transcript
retain the individual names rather than substituting a guessed dependency
list.
