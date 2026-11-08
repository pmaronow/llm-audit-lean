# Blind reading of the P046 statements

This file was written after reading only `SAP/P046/Defs.lean`, its four parts,
`SAP/P046/Challenge.lean`, its part, and the Mathlib definitions cited below.
Neither `claims.json` nor `record.json` has been opened at this stage. The
mathematics below describes the actual propositions, independently of their
names and explanatory docstrings. Every quantifier below is universal unless
explicitly existential.

## Common objects and conventions

A full observation is an element of the Borel measurable space
`R × (Bool × (Bool × Bool))`, written `(W,X,Y0,Y1)`, where each Boolean is
converted into the real number 0 or 1. Thus the covariate is scalar and real,
treatment and both potential outcomes are binary. The observed outcome is
`Y=(1-X)Y0+XY1`. The observed triple is `(W,(Y,X))`; no potential outcome is
included separately in this triple.

A study `M` supplies a measure `P`, two everywhere real-valued functions
`pi,m : R → R`, and a real number `delta`. `ValidStudy M` means all of:

1. `P` is a probability measure.
2. For every real `w`, `P(W=w)=0` (an atomless covariate marginal).
3. Both `pi` and `m` are Borel measurable.
4. `delta>0`.
5. `delta<pi(W)<1-delta`, almost surely under `P`.
6. `E[X | sigma(W)]=pi(W)`, almost surely.
7. `E[Y1 | sigma(W)]=m(W)`, almost surely.
8. `0≤m(W)≤1`, almost surely.
9. `Y0` and `X` are conditionally independent given `sigma(W)`.
10. `Y1` and `X` are conditionally independent given `sigma(W)`.

The last two conditions are separate conditional independence assertions; they
do not assert joint independence of `(Y0,Y1)` and `X`. There are no other
restrictions on `pi,m` off the covariate law's support. Define `mu=E_P[Y1]`.

For a natural number `n`, a sample `a` is a function from `Fin n` into the full
observation space, with law `P_n=P^n`, Mathlib's finite product measure. All
sample probabilities and expectations below use this law, including randomness
in the training observations. Write `W_i,X_i,Y_i` for the coordinates. Define

```
H_n(a)       = (sum_i X_i Y_i / pi(W_i))/n,
xi_n(a)      = (sum_i pi(W_i)^(-2))/n,
muW_n(a)     = (sum_i m(W_i))/n,
r_n(alpha,a) = sqrt(xi_n(a) log(2/alpha)/(2n)),
c_n(alpha,a) = (sqrt(xi_n(a))+1) sqrt(log(4/alpha)/(2n)),
A_n(g,a)     = (sum_i [X_i (Y_i-g(W_i))/pi(W_i)+g(W_i)])/n.
```

The divisions are real divisions, with `n` coerced to a real. Lean sets a real
inverse of zero to zero, and `Real.sqrt` is zero on negative inputs. The stated
positive sample sizes, positive significance levels and positivity hypotheses
are consequently material. `tailProb M est radius` is
`P_n(radius(a) ≤ |est(a)-mu|)`, with the boundary **included**.
`strictNoncoverage M n alpha` instead uses `r_n(alpha,a)<|H_n(a)-mu|`.

A `CrossFit n` consists of a deterministic function `fold : Fin n → Bool` and
functions `g_j(a,w)` for `j=false,true`. For each `j`, `g_j` is jointly Borel
measurable in `(a,w)`. For every `j,a,b`, if the observed triples of `a_i,b_i`
agree for every `i` with `fold(i) != j`, then the entire functions `g_j(a,·)`
and `g_j(b,·)` agree. Thus the prediction for fold `j` depends only on observed
data in the opposite fold. There is no bound on fitted values and no
correctness requirement on the fit. Let

```
A_n(F,a) = (sum_i [X_i (Y_i-g_fold(i)(a,W_i))/pi(W_i)
                   +g_fold(i)(a,W_i)])/n.
```

A sequence `F=(F_n)` is `Balanced` if, for each Boolean `j`,
`#{i : fold_n(i)=j}/n → 1/2` as `n→infinity`. This imposes no requirement on
an individual small sample size, including `n=0`.

Further notation (all population integrals are over the **full** observation
law, with the displayed functions depending only on the indicated coordinates):

```
q(w)       = (1-pi(w))/pi(w),
R(g)       = E[q(W)(Y1-g(W))^2],
||g||q^2   = E[q(W)g(W)^2],
||g||2^2   = E[g(W)^2],
V(g)       = Var(Y1)+R(g),
B          = E[m(W)(1-m(W))/pi(W)]+Var(m(W)),
Q_T(g,a)   = sum_{i in T} X_i(1-pi(W_i))/pi(W_i)^2 (Y_i-g(W_i))^2.
```

`ZeroBenchmark M G` means either the everywhere zero function belongs to `G`,
or there exists a sequence `h_k` of members of `G` with `||h_k||q^2 → 0`.
This definition alone does not assert any integrability of its members.

`L2InProbability M F j g` means, for every real `eps>0`,
`P_n(eps < ||g_{n,j}(a,·)-g||2^2) → 0`. `L2InMeanSquare M F j g` means
`E_{P_n}[||g_{n,j}(a,·)-g||2^2] → 0` **and**, for every natural `n`, this
sample-dependent squared error is integrable under `P_n`.

`RootN M est` means: for every real `eps>0`, there exist real `C>0` and natural
`N` such that, for every natural `n≥N`,
`P_n(C < sqrt(n)|est_n-mu|)≤eps`. The constants may depend on the fixed study
and on the estimator sequence.

`NormalLimit M est v` asserts `v≥0`, existence of a probability-measure
certificate for `P`, and weak convergence of the laws of
`sqrt(n)(est_n-mu)` under `P_n` to `N(0,v)`. It includes almost-everywhere
measurability of every member of the sequence, even at `n=0`.
For `v=0` the Gaussian law is the point mass at zero.

`UniformRootN delta` means: for every real `eps>0`, there exists a real `C>0`
such that for **every** study `M` satisfying `ValidStudy M` and
`M.delta=delta`, and **every** natural `n>0`,
`P_n(C < sqrt(n)|H_n-mu|)≤eps`. Here `C` precedes both the study and sample
size quantifiers.

### Mathlib meanings followed

- `IsProbabilityMeasure` is `P(univ)=1`:
  `MeasureTheory/Measure/Typeclasses/Probability.lean:64`.
- `MeasurableSpace.comap` is the sigma algebra of inverse images; here it
  generates exactly `sigma(W)` or `sigma((W_i)_i)`:
  `MeasureTheory/MeasurableSpace/Basic.lean:84`.
- `condExp` is the integrable conditional expectation for a sub-sigma algebra
  and sigma-finite trimmed measure. It is defined as zero if these conditions
  fail: `MeasureTheory/Function/ConditionalExpectation/Basic.lean:102`.
  The variables being conditioned in these statements are bounded, and the
  measures are probabilities where validity is assumed.
- `CondIndepFun` is conditional-kernel independence; for measurable functions
  its characterization is factorization of conditional probabilities for every
  pair of measurable inverse-image events:
  `Probability/Independence/Conditional.lean:155,358,660`.
- `Measure.pi` is finite product measure, `Measure.prod` binary product,
  `Measure.map` pushforward for almost-everywhere measurable maps, and
  `Measure.restrict E` the measure restricted to `E` (not normalized):
  `MeasureTheory/Constructions/Pi.lean:210`,
  `MeasureTheory/Measure/Prod.lean:171`, `Map.lean:99`, `Restrict.lean:50`.
  Nonmeasurable maps have a fallback value in Mathlib; all concrete generators
  here are built from Borel threshold tests and projections.
- `Integrable` includes almost-everywhere strong measurability and finite
  integral of absolute value:
  `MeasureTheory/Function/L1Space/Integrable.lean:59`.
- `MemLp f 2 P` means almost-everywhere strong measurability and finite
  squared integral: `MeasureTheory/Function/LpSeminorm/Defs.lean:152`.
- Real-valued `integral` is the Bochner integral and is **zero** if its
  integrand is not integrable:
  `MeasureTheory/Integral/Bochner/Basic.lean:158,204`. In particular, the bare
  definitions of `R`, the two squared norms and mean-square convergence cannot
  alone be read as extended-valued integrals.
- `variance f P` is `toReal` of the nonnegative Lebesgue integral of
  `|f-E[f]|^2`; infinite variance becomes zero:
  `Probability/Moments/Variance.lean:57,64`.
- `TendstoInDistribution` is weak convergence of pushforward probability
  measures, with explicit almost-everywhere measurability conditions:
  `MeasureTheory/Function/ConvergenceInDistribution.lean:64`.
  `gaussianReal 0 v` uses variance `v` and is a Dirac mass when `v=0`:
  `Probability/Distributions/Gaussian/Real.lean:222,229`.
- `toReal` of a finite nonnegative measure value is its ordinary real value;
  infinity is instead sent to zero. Probabilities in these statements are
  finite under `ValidStudy`. `v.toNNReal` clips negative values to zero, but
  `NormalLimit` separately requires `v≥0`.
- `Tendsto ... atTop (nhds x)` is ordinary convergence as natural sample size
  tends to infinity. `∀ᵐ` and `=ᵐ` mean outside a measure-zero set. An
  almost-everywhere statement for `P_n.restrict E` means it holds for almost
  every sample in `E`; it does not condition by renormalizing the measure.

## SAP.P046.T1

This theorem has no external parameters or hypotheses. Let `W,U` be
independent uniform `[0,1]` real variables, put
`pi(w)=13/20` for `w≤3/5` and `pi(w)=99/100` otherwise, and set
`X=1{U≤pi(W)}`, `Y0=0`, `Y1=1{W≤3/5}`. Use
`m(w)=1{w≤3/5}`, `delta=1/200` for the resulting study. The theorem is the
conjunction of these assertions:

1. This study is valid in all ten senses above.
2. Its `W` marginal is uniform `[0,1]`.
3. `mu=3/5`.
4. At `n=100, alpha=1/10000000`, strict noncoverage of the printed-radius
   interval equals `N/100^100`, where the natural number `N` is defined below.
5. `N` equals the following natural number:
   `11979291069795625472576722625601454579193931030581441019247695948117336197717708252113744670235734049700195915329948439938976976688794607547282140972800735873954434550061258658968400997158933003`.
6. The strict noncoverage probability is greater than `119/1000000000`.
7. `1/10000000 < 119/1000000000`.
8. Exactly 1946 pairs of natural numbers `0≤s≤k≤100` satisfy
   `xiK(k) log(20000000)/200 < (s-39)^2/65^2`, with the subtraction in this
   last expression performed in the reals.

Here

```
xiK(k) = [400k/169 + 10000(100-k)/9801]/100,
mass(k,s) = choose(100,k) choose(k,s) 39^s 21^(k-s) 40^(100-k),
cut(k,s) iff
  200*7840800*absNat(s-39)^2 >
    3363*(3920400*k + 1690000*(100-k)),
N = sum_{k=0}^{100} sum_{s=0}^{k} [if cut(k,s) then mass(k,s) else 0].
```

`absNat(s-39)` is implemented as `39-s` if `s≤39`, else `s-39`.
The other subtractions in `mass` and `cut` are natural subtractions; the
summation bounds ensure `s≤k≤100`. In `xiK` subtraction is real. The
statement does not introduce sample random variables corresponding to `k,s`
or assert their laws or a pointwise reduction of the sample statistics.

## SAP.P046.T2

This is another closed conjunction, with no outside hypotheses. Let `W,U` be
independent uniform `[0,1]`, `X=1{U≤9/10}`, `Y0=0`,
`Y1=1{W≥1/2}`, `pi=9/10`, `m(w)=1{w≥1/2}`, and `delta=1/20`.
For samples of size 100 define `E={a : for every i, W_i<1/2}`. The theorem says:

1. This study is valid, its covariate marginal is uniform `[0,1]`, and `mu=1/2`.
2. `P_100(E)=ofReal((1/2)^100)` and `P_100(E)>0`.
3. For every full sample `a`, including samples outside the law's support,
   `xi_100(a)=100/81` and `r_100(1/20,a)=sqrt(log(40)/162)`.
4. `log(40)/162<1/4`, `sqrt(log(40)/162)<1/2`, and
   `2 exp(-log(40))=1/20`.
5. For `P_100.restrict E`-almost every `a`,
   `E[1{r_100(1/20,b)≤|H_100(b)-mu|} | sigma((W_i)_i)](a)=1`
   and `1>1/20`.

The conditional expectation in the last clause is with respect to the
**unrestricted** full sample law; restriction affects where its equality is
asserted, not the law used to define that conditional expectation.

## SAP.P046.T3

For every study `M`, if `ValidStudy M`, the following two conclusions hold.

First, for every real `alpha` with `0<alpha<1`, all three assertions hold:

1. For every natural `n>0`,
   `P_n(c_n(alpha,a)≤|H_n(a)-mu|)≤alpha`.
2. For every natural `n>0`, for `P_n`-almost every `a`,
   `c_n(alpha,a)<(delta^(-1)+1)sqrt(log(4/alpha)/(2n))`.
3. There exists a real `C>0` such that, for every natural `n>0`, for
   `P_n`-almost every `a`, `2 c_n(alpha,a)≤C/sqrt(n)`.
   This `C` may depend on the study and on `alpha`, but precedes `n,a`.

Second, for every real `b>0` satisfying `b≤pi(W)` almost surely, for every
natural `n>0` and every real `alpha` with `0<alpha<1`,
`P_n(b^(-1)sqrt(log(2/alpha)/(2n))≤|H_n(a)-mu|)≤alpha`.

## SAP.P046.T4

This is a closed conjunction about the following explicit study and fits.
Let `W,U,V` be three independent uniform `[0,1]` variables. Set
`L=1{W≤1/2}`, `Z=1{U≤1/10}`, `Y0=Y1=LZ`, and
`pi(W)=1/4` on the lower half, `3/4` on the upper half.
Set `X=1{V≤pi(W)}`, `m=1/10` on the lower half and zero otherwise,
and `delta=1/8`. The working predictions are
`p_theta(w)=1/2` on the lower half and `theta` on the upper half, for every
real parameter `theta`. For each natural `n`, set
`fold_n(i)=1{floor(n/2)≤i.val}` and use the deterministic fit `p_0` for both
folds, independent of the data.

The conjunction asserts:

1. The study is valid, its covariate marginal is uniform `[0,1]`, and `mu=1/20`.
2. The fit sequence is balanced.
3. For each Boolean `j`, its fitted prediction converges in the defined L2
   probability sense to `p_0`.
4. For every natural `n` and every Boolean `j`, for `P_n`-almost every sample
   `a`, **for every real `theta`**,
   `Q_{opposite fold j}(p_0,a)≤Q_{opposite fold j}(p_theta,a)`.
   The full set of parameters is compared on a common full-measure sample set.
5. For every natural `n>0`, both `E[H_n]` and `E[A_n(F_n)]` equal `mu`,
   `Var(H_n)=79/(400n)`, and `Var(A_n(F_n))=169/(400n)`.
6. For every natural `n` and every full sample `a`,
   `A_n(F_n,a)=A_n(p_0,a)` (the fixed-function estimator).
7. `sqrt(n)(H_n-mu)` converges weakly to `N(0,79/400)` and
   `sqrt(n)(A_n(F_n)-mu)` to `N(0,169/400)`.
8. `79/400<169/400`, `169/400-79/400=9/40`, and their ratio is `169/79`.
9. For every real `theta`, `||p_theta||q^2=3/8+theta^2/6`.
10. `R(0)=3/20` and `R(p_0)=3/8`.

No general efficiency inequality is asserted by this theorem.

## SAP.P046.T5

This theorem conjoins two universal implications.

For the first: choose, in order, a study `M` with `ValidStudy M`, a natural
number `d`, a family `family : R^d → (R → R)`, and a sequence of cross-fits
`F`. Assume:

1. `F` is balanced.
2. For every real parameter vector `theta`, `family(theta)(W)` is in `L2(P)`.
3. The zero function is in the family's range, or there exists a sequence of
   family members whose squared weighted norms tend to zero.
4. For every natural `n` and Boolean `j`, for `P_n`-almost every sample `a`,
   there exists a parameter vector `theta` such that
   `g_{n,j}(a,·)=family(theta)` everywhere, and for **every** parameter vector
   `eta` the opposite-fold empirical risk of `family(theta)` is at most that
   of `family(eta)`.

Then choose any deterministic function `gstar : R → R`. If it is a member of
the family, if for every `theta` it satisfies
`R(gstar)≤R(family(theta))`, and if both fitted folds converge to `gstar` in
the defined L2 probability sense, the conclusion is all of:

- `sqrt(n)(A_n(F_n)-mu)` converges weakly to `N(0,V(gstar))`;
- `sqrt(n)(H_n-mu)` converges weakly to `N(0,V(0))`;
- `V(gstar)≤V(0)`.

In the second implication: choose a valid study `M`, a balanced sequence of
cross-fits `F`, and a deterministic function `gstar`. Assume
`gstar(W)∈L2(P)`, convergence of each fitted fold to `gstar` in the defined
L2 probability sense, and, for every natural `n` and Boolean `j`,
`g_{n,j}(a,W)∈L2(P)` for `P_n`-almost every training sample `a`.
Finally assume `R(gstar)≤R(0)`. The same three conclusions follow. There is
no working-family membership or empirical-minimization condition in this
second implication. Its risk comparison is an explicit premise.

## SAP.P046.T6

This closed theorem negates the following universal assertion:
for every study `M`, if `ValidStudy M`, then for every natural `n>0` and real
`alpha` with `0<alpha<1`,
`P_n(r_n(alpha,a)≤|H_n(a)-mu|)≤alpha`.
Equivalently, classically, it asserts existence of a valid study, a positive
sample size and an `alpha` strictly between zero and one with the displayed
tail probability strictly greater than `alpha`. It does not assert failure
for every study or for every sample size/significance level.

## SAP.P046.T7

The first conjunct says: for every real `delta>0`, `UniformRootN delta` holds,
with the nested quantifiers spelled out above. The constant is common to all
valid studies with that **specified** positivity constant and all `n>0`.

The second conjunct says: for every study `M` with `ValidStudy M`, all of:

1. For every natural `n>0`, `H_n` is integrable under `P_n` and `E[H_n]=mu`.
2. The single-observation summand `Z=X Y/pi(W)` has variance
   `v=E[m(W)/pi(W)]-mu^2` under `P`.
3. `sqrt(n)(H_n-mu)` converges weakly to `N(0,v)`, including the assertion
   that `v≥0` and the point-mass interpretation if `v=0`.

## SAP.P046.T8

For every study `M` with `ValidStudy M`, every natural `n>0`, and every
`CrossFit n` object `F`, assume that for **every** sample index `i` the random
variable `a ↦ g_fold(i)(a,W_i)` is integrable under the full sample law `P_n`.
Then `E_{P_n}[A_n(F)]=mu`. There is no balance requirement and no consistency,
correct-regression or working-family assumption. Integrability is imposed on
the individual evaluated predictions, rather than only on their final sum.

## SAP.P046.T9

This theorem conjoins two implications.

First: for every valid study `M`, every balanced sequence of cross-fits `F`,
and every pair of deterministic functions `g_false,g_true`, suppose each
`g_j(W)` belongs to `L2(P)`, each fold converges to its own `g_j` in the
defined mean-square sense (including the finite-sample integrability of its
scalar squared-error integral), and, for every natural `n` and Boolean `j`,
the fitted function belongs to `L2(P_W)` for `P_n`-almost every training
sample. Then `RootN M (A_n(F_n))`. The two fold limits may differ. No normal
limit is asserted in this first implication.

Second: for every valid study `M` and every balanced sequence of cross-fits
`F`, suppose each fold converges in the defined L2 probability sense to the
stored true regression `m`, and, for every natural `n` and Boolean `j`, the
fitted function is in `L2(P_W)` for `P_n`-almost every training sample. Then
`sqrt(n)(A_n(F_n)-mu)` converges weakly to `N(0,B)`, with
`B=E[m(W)(1-m(W))/pi(W)]+Var(m(W))`. This is a numerical normal-limit
statement, without a formal definition or proof of a semiparametric lower
bound or optimality over other estimators.

## SAP.P046.T10

For **every** estimator sequence `est_n : (Fin n → (R × (R × R))) → R`
such that each `est_n` is Borel measurable, there exist real `eps>0` and real
`c>0` such that, for every natural `N`, there exist a natural `n≥N` with
`n>0` and a study `M` satisfying `ValidStudy M` for which

`P_n(eps < |est_n((W_i,Y_i,X_i)_i)-mu(M)|)≥c`.

The estimator is chosen before `eps,c,N,n,M` and cannot receive the study,
its propensity, its regression, its positivity constant or potential outcomes
as additional inputs. The adverse study may vary with `n,N` and the
estimator. No common positive lower bound for the studies' `delta` values is
specified in this proposition. Estimators are formally defined also on triples
with nonbinary outcome/treatment, but evaluated only on observed sample
triples from the study law.
