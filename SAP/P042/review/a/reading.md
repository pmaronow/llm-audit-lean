# Blind mathematical reading

This file was written and saved after reading only `SAP/P042/Defs*.lean`,
`SAP/P042/Defs/*.lean`, `SAP/P042/Challenge*.lean`,
`SAP/P042/Challenge/*.lean`, and the relevant Mathlib definitions. Neither
`claims.json` nor `record.json` has been opened at this stage. The readings below
describe the theorem types, not what their comments say they establish.

## Shared definitions and Mathlib semantics

`Fin J` is the ordered set `{0,...,J-1}`. Sums over a finite type use every
element, once. A `Finset` is a finite set, without multiplicities. Real and
rational division are field division, including the convention `x/0 = 0`.
Natural subtraction is truncated: `u-v = max(u-v,0)`. These conventions are
relevant to the raw definitions even when the theorem hypotheses prevent the
degenerate cases.

For real numbers `v_j`, define

* `w_j = 1/v_j`, `W = sum_j w_j`, and `a_j = w_j/W`;
* `P(a,D)(omega) = sum_j a_j D_j(omega)`;
* `Vdiag(v) = sum_j a_j^2 v_j`;
* `Q(a,Sigma) = sum_j sum_k a_j a_k Sigma_jk`;
* `O(a,Sigma) = sum_{j<k} a_j a_k Sigma_jk` for indices `Fin J`;
* for a finite subset `E`, `a^E_j = (1/v_j)/(sum_{k in E}1/v_k)` when
  `j in E`, and zero otherwise.

On a measurable space with probability measure `mu`, write `E X` for the
Mathlib Bochner integral, `Var X` for `ProbabilityTheory.variance X mu`, and
`Cov(X,Y)` for `ProbabilityTheory.covariance X Y mu`. The definitions followed
are:

* `IsProbabilityMeasure mu`: `mu(univ)=1`
  (`Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`).
* `MemLp X 2 mu`: the extended L2 seminorm is finite; its definition includes
  almost everywhere strong measurability through `eLpNorm`. For real functions
  this gives square integrability and, on a probability space, integrability
  (`Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`).
* The Bochner integral is the L1 integral when integrable, and zero otherwise
  (`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:158`).
* `Var X = (integral_nonnegative |X-E X|^2).toReal`, with `toReal(infinity)=0`
  (`Mathlib/Probability/Moments/Variance.lean:58,64`).
* `Cov(X,Y) = E[(X-E X)(Y-E Y)]`
  (`Mathlib/Probability/Moments/Covariance.lean:44`).
* The L2 hypotheses in the probabilistic assertions make all these moments
  finite and make the ordinary variance/covariance interpretation valid.
* `IndepFun X Y mu` means independence of their generated sigma algebras
  (`Mathlib/Probability/Independence/Basic.lean:144`, through the corresponding
  kernel definition). `Pairwise` asks for this for every two distinct indices,
  not mutual independence of the whole family.
* `f =^ae[mu] g` means equality outside a set of measure zero. `Real.sqrt` is
  the nonnegative square root on nonnegative inputs, and zero on negative
  inputs.

For a finite set `S`, `E_S f = (sum_{s in S} f(s))/|S|` and
`Cov_S(f,g)=E_S[(f-E_S f)(g-E_S g)]`. Rational versions have exactly the same
definitions in Q; `Var_S f=E_S[(f-E_S f)^2]`. Thus finite covariance uses a
probability denominator `|S|`, not the sample denominator `|S|-1`.
For `N` population values, `bar Y=(sum_i Y_i)/N` and
`S(Y,V)=(sum_i (Y_i-bar Y)(V_i-bar V))/(N-1)`, where `N-1` is natural
subtraction before the cast to R.

## `SAP.P042.T1`

There are no input parameters or hypotheses. The theorem asserts both of the
following fully specified witness propositions.

### Six-unit finite witness

There are six labelled units, three labelled arms, and outcomes
`Y_i(g)=1` for `i=0,1,2` and `Y_i(g)=0` for `i=3,4,5`, for every arm `g`.
An allocation is an ordered pair `(A,B)` of disjoint two-element subsets of
the six units. Its control set is `C=all units \ (A union B)`. Each arm mean
is its sum of outcomes divided by 2. Set `D1=mean(A)-mean(C)` and
`D2=mean(B)-mean(C)`. All means, variances and covariances here are rational
uniform finite-set moments over the set of allocations. The assertion is the
conjunction of:

1. Every unit has identical potential outcomes in every arm and in arm zero.
2. The allocation set has size 90, and `choose(6,2) choose(4,2)=90`.
3. Every allocation has `|A|=|B|=|C|=2` and disjoint `A,B`.
4. `E D1=E D2=0`, `Var D1=Var D2=3/10`, and `Cov(D1,D2)=3/20`.
5. For the two real variances both equal to `3/10`, both normalized precision
   weights are `1/2`, the diagonal variance is `3/20`, and `1/W=3/20`.
6. `Var((D1+D2)/2)=9/40`, `E[((D1+D2)/2)^2]=9/40`, this variance equals
   `(3/2)(3/20)`, and it is strictly greater than `3/20`.

### Binomial witness

For `x in {0,...,100}`, `p(x)=choose(100,x)/2^100` in Q. The expectation of
a function of `x0,x1,x2` is the nested finite sum with product weights
`p(x0)p(x1)p(x2)`. Variance and covariance use that expectation and centering.
Define `D1=(x1-x0)/100`, `D2=(x2-x0)/100`, and `T=(D1+D2)/2`.
Define

`C_r = 2^(-300) sum_{x=0}^{100} choose(100,x)
       sum_{t=max(0,2x-r)}^{min(200,2x+r)} choose(200,t)`.

The lower limit is precisely the natural subtraction in `coverageCount`.
`coversZero(t,h)` means the two inequalities `t-h <= 0 <= t+h`.
The assertion is the conjunction of:

1. `p(x)>=0` for every x and `sum_x p(x)=1`.
2. `E D1=E D2=0`, `Var D1=Var D2=1/200`,
   `Cov(D1,D2)=1/400`, and `Var(x0/100)=1/400`.
3. For two real variances `1/200`, both precision weights are `1/2`,
   `Vdiag=1/400`, and `1/W=1/400`.
4. For every triple, `T=(x1+x2-2x0)/200`; `E T=0`, `Var T=3/800`, this
   variance is `(3/2)(1/400)`, and it is strictly greater than `1/400`.
5. `(49/25)sqrt(1/400)=49/500` in R.
6. For every triple and the integer `q=x1+x2-2x0`, the interval with center
   `T` and radius `49/500` covers zero iff `|q|<=19`; the interval with radius
   `(49/25)sqrt(3/800)` covers zero iff `|q|<=24`.
7. `24^2 < 200^2(49/25)^2(3/800) = 14406/25 < 25^2` in R.
8. The product-weight expectation of the indicator of coverage for radius
   `(49/25)sqrt(1/400)` equals `C_19`, and that for radius
   `(49/25)sqrt(3/800)` equals `C_24`.
9. With
   `b=56571224212801903286613058436266763680981055287737934836552182663205237639665445537726383`,
   `C_19=b/2^295`, and the natural numbers `b` and `2^295` are coprime.
10. `888/1000 < C_19 < 889/1000 < 95/100 < C_24`.

The separately defined `binomialCountEvent` is not used directly by this
theorem type. No assertion involves a standard-normal quantile.

## `SAP.P042.T2`

There are no outer hypotheses. The theorem asserts eight universally
quantified laws. Except for the last, each first quantifies, in order, over a
type `Omega`, its measurable-space structure, a measure `mu`, and a proof that
`mu` is a probability measure. Every random variable below is real valued.

### 1. Linear pooling

For every natural `J`, every real coefficient vector `a` on `Fin J`, and every
family `D_j`, if every `D_j` is L2, then all three equalities hold:

`E P(a,D) = sum_j a_j E D_j`,

`Var P(a,D) = Q(a,Cov(D_j,D_k))`,

`Q(a,Cov(D_j,D_k)) = sum_j a_j^2 Var D_j + 2 O(a,Cov(D_j,D_k))`.

No positivity, normalization, or independence is required. `J=0` is included.

### 2. Precision pooling

For every natural `J>0`, every family `D_j` with each member L2 and
`v_j=Var D_j>0`, let `a` be the normalized precision weights and
`Sigma_jk=Cov(D_j,D_k)`. The following all hold:

* `W>0`, every `a_j>0`, and `sum_j a_j=1`.
* `Vdiag(v)=1/W` and `Var P(a,D)=1/W+2 O(a,Sigma)`.
* `Var P(a,D)=1/W` iff `O(a,Sigma)=0`.
* If all distinct-index covariances are zero, then `Var P(a,D)=1/W`.
* If all distinct-index covariances are nonnegative and there exist indices
  `j<k` with positive covariance, then `1/W < Var P(a,D)`.
* For every real `z`, `z sqrt(Var P(a,D))=z sqrt(Q(a,Sigma))`.
* For every real `z>0`, `z sqrt(Var P(a,D))=z sqrt(1/W)` iff `O(a,Sigma)=0`.

### 3. Shared control

For every `A,B,C` in L2 with `Cov(A,B)=Cov(A,C)=Cov(B,C)=0`,
`Cov(A-C,B-C)=Var C`. Neither independence nor positive variance is assumed.

### 4. Independent individual observations

For every three positive naturals `n0,n1,n2`, every family `X` indexed by
the disjoint sum of `Fin n0`, `Fin n1`, `Fin n2`, suppose every `X_i` is L2
and distinct `X_i,X_j` are independent. For every real `sigmaSq>0`, if every
`Var X_i=sigmaSq`, form the three sample means `C,A,B` by summing each arm
and dividing by its sample size, and set `D1=A-C`, `D2=B-C`. Then

`Var D1=sigmaSq(1/n1+1/n0)`,

`Var D2=sigmaSq(1/n2+1/n0)`,

`Cov(D1,D2)=sigmaSq/n0`,

`Cov(D1,D2)/(sqrt(Var D1)sqrt(Var D2))
 = sqrt(n1 n2/((n1+n0)(n2+n0)))`.

All sizes in these equations are cast into R. Equal means and identical
distributions are not required. The independence hypothesis is pairwise.

### 5. Covariance bound

For every natural `J`, coefficient vectors `a,s`, and family `D`, if every
`D_j` is L2, every `a_j>=0`, every `s_j>0`, and `Var D_j=s_j^2`, then

* for every `j,k`, `|Cov(D_j,D_k)|<=s_j s_k`;
* `Var P(a,D) <= (sum_j a_j s_j)^2`;
* for every real random variable `Z`, if `Z` is L2, `E Z=0`, `Var Z=1`, and
  for every j the centered variable `D_j-E D_j` equals `s_j Z` almost
  everywhere, then equality holds in the preceding bound.

`J=0` is allowed. The last clause is conditional on such a `Z` and such a
representation for the already specified `D`; it does not existentially
construct a factor or a coupling.

### 6. Difference of two pools

After the common probability-space quantifiers, quantify over a finite type
`I` with decidable equality and two finite subsets `N,A` of it. If `N` and
`A` are both nonempty and disjoint, then for every family `D` on all of `I`
whose members are L2 and have strictly positive variance, define
`v_j=Var D_j`, the subset precision weights `aN,aA`, and `b_j=aN_j-aA_j`.
Both equalities hold:

`Var(P(aN,D)-P(aA,D))=Q(b,Cov(D_j,D_k))`,

`Var(P(aN,D)-P(aA,D))=Var P(aN,D)+Var P(aA,D)
                     -2 Cov(P(aN,D),P(aA,D))`.

The L2 and positive-variance assumptions apply even to indices outside the
two subsets. No independence or zero-covariance hypothesis is imposed.

### 7. A three-contrast covariance block

For every natural `J>0` and L2 family `D` with strictly positive variances,
for every injection `e:Fin 3 -> Fin J` and every four real numbers
`a,c12,c13,c23`, suppose each selected index has normalized precision
weight `a`. Suppose also that for every pair `j != k` its covariance is
`c12` on the two orientations of `(e0,e1)`, `c13` on `(e0,e2)`, `c23` on
`(e1,e2)`, and zero for all other pairs. Then

`Var P(normalizedWeight(v),D)=1/W+2 a^2(c12+c13+c23)`;

if additionally `c12=c13` and `c13=c23`, then this variance is
`1/W+6 a^2 c12`.

The injection enforces at least three distinct indices; the covariance
assumption includes every pair involving any remaining indices.

### 8. Finite-population randomization

For every natural `N>=2`, every three positive natural sizes `n_g` whose sum
is at most N, and every fixed real array `Y_i(g)` for `N` units and three
arms, form the finite set S of **all** maps from `Fin N` to `Fin 4` having
exactly `n_g` units labelled g for each `g=0,1,2`. Label 3 is a residual
unobserved group of size `N-sum_g n_g`; it is not required to be empty.
Use uniform finite-set averaging on S. An arm mean is its assigned sum of
`Y_i(g)` divided by `n_g`. Let `D1=mean_1-mean_0`,
`D2=mean_2-mean_0`, `tau1_i=Y_i(1)-Y_i(0)`, and
`tau2_i=Y_i(2)-Y_i(0)`. Then S is nonempty and

`Cov_S(D1,D2)=S(Y(0),Y(0))/n0 - S(tau1,tau2)/N`;

`S(tau1,tau2)=S(Y(1),Y(2))-S(Y(1),Y(0))
              -S(Y(0),Y(2))+S(Y(0),Y(0))`;

if for every unit `Y_i(1)=Y_i(0)` and `Y_i(2)=Y_i(0)`, then
`Cov_S(D1,D2)=S(Y(0),Y(0))/n0`.

There are no measurability or stochastic hypotheses here because the outcomes
and allocation sets are finite. All covariance denominators are positive.

## Numerical definitions used by `SAP.P042.T3` and `SAP.P042.T4`

There are two fixed effects and standard errors, all real:

`d=(58247/25000,21649/25000)`,

`se=(1741/3125,40891/50000)`, `v_j=se_j^2`.

Set `M=sum_j (1/v_j)d_j/W`, `V=1/W`,
`Q=sum_j (1/v_j)(d_j-M)^2`,
`C=W-(sum_j (1/v_j)^2)/W`, `tau2=max(0,(Q-1)/C)`,
`vR_j=v_j+tau2`, `MR=sum_j normalizedWeight(vR)_j d_j`,
and `VR=1/totalWeight(vR)`.

`RoboFixedExact` abbreviates the five equalities

`v0=3031081/9765625`, `v1=1672073881/2500000000`,

`W=23906548994140625/5068191371295361`,

`M=114191974724271/61200765425000`,

`V=5068191371295361/23906548994140625`.

`RoboRandomExact` abbreviates all the following:

`Q=(d0-d1)^2/(v0+v1)=5357654416/2448030617`, `Q>1`,

`C=2/(v0+v1)=5000000000/2448030617`,

`tau2=2909623799/5000000000`,

`1/vR0=5000000000/4461537271`,

`1/vR1=5000000000/6253771561`,

`MR=12592252377/7319600000`,

`VR=27901434903721350031/53576544160000000000`.

`RoboRandomRounding` means `1.7195<=MR<1.7205`, and, **for every real z**,
if `1.9599<=z<=1.96`, then
`0.3055<=MR-z sqrt(VR)<0.3065` and
`3.1345<=MR+z sqrt(VR)<3.1355`.

All decimals in this reading are exact terminating rationals. No theorem
identifies z with a normal quantile or proves any normal approximation.

## `SAP.P042.T3`

There are no parameters or hypotheses. The theorem is the conjunction of:

1. `RoboFixedExact` with exactly the equalities just written.
2. `1.8655<M<1.8665` and `1.7205<M`.
3. For every real z satisfying `1.9599<=z<=1.96`,
   `0.9625<M-z sqrt(V)`, `0.3065<0.9625`,
   `M+z sqrt(V)<2.7685`, and `2.7685<3.1345`.
4. `RoboRandomExact` with exactly the assertions above.
5. `RoboRandomRounding` with its universal z quantifier above.

This type establishes separation from the alternative rounding bins and the
alternative calculation's membership in them; it does not itself connect the
input constants to a data file or historical rows.

## `SAP.P042.T4`

There are no parameters or outer hypotheses. The theorem is the conjunction
of:

1. `RoboFixedExact`.
2. `1.8655<=M<1.8665`.
3. For every real z satisfying `1.9599<=z<=1.96`,
   `0.9625<=M-z sqrt(V)<0.9635` and
   `2.7675<=M+z sqrt(V)<2.7685`.
4. For every real z with `0<=z<=1.96`, `0<M-z sqrt(V)`.
5. For every type Omega, measurable-space structure, probability measure mu,
   and pair of real L2 random variables D, if `Var D_j=v_j` for both j and
   `Cov(D0,D1)=0`, then
   `Var P(normalizedWeight(v),D)=V`.
6. `RoboRandomExact` and `RoboRandomRounding`.

The only probabilistic claim is conditional on the specified marginal
variances and zero covariance. No data provenance, analysis command, or
editing instruction is part of the type.

## `SAP.P042.T5`

There are no parameters or hypotheses. The type is the conjunction of two
negated universal assertions:

1. It is false that, for every type Omega, measurable-space structure,
   probability measure mu, positive natural J, and L2 family `D` on `Fin J`
   with every `Var D_j>0`,
   `Var P(normalizedWeight(Var D),D)=1/totalWeight(Var D)`.
2. It is false that, for every such probability space, finite type I with
   decidable equality, nonempty disjoint finite subsets N,A, and L2 family D
   on all of I with every variance positive,
   `Var(P(aN,D)-P(aA,D))
      =1/(sum_{j in N}1/Var D_j)+1/(sum_{j in A}1/Var D_j)`.

Classically these assert existence of a counterexample to each formula, with
all its stated positivity and integrability hypotheses. The two witnesses
need not be the same. There are no claims about any particular historical
estimates, intervals, or designs.

## `SAP.P042.T6`

This is a conjunction of a universal finite-randomization theorem and one
numeric identity.

For every pair of natural numbers N,m, if `N>=2`, `m>=1`, and `m<=N-1`,
then for every fixed potential-outcome array `Y:Fin N -> Bool -> R`, use the
uniform law on all m-element subsets S of the N units. Define the treatment
mean of a vector U as `(sum_{i in S} U_i)/m` and its control mean as
`(sum_{i not in S} U_i)/(N-m)`. All of the following hold:

1. For each Boolean t, the expectation of the treatment mean of `Y_i(t)` and
   that of the control mean both equal `(sum_i Y_i(t))/N`.
2. Let the observed outcome be `Y_i(true)` on S and `Y_i(false)` off S.
   The expected treatment-minus-control observed-outcome contrast equals
   `(sum_i (Y_i(true)-Y_i(false)))/N`.
3. For every fixed contact/compliance indicator `c:Fin N -> Bool`, if its
   number `K` of true values is positive, define
   `pi=K/N`,
   `theta=(sum_{c_i=true}(Y_i(true)-Y_i(false)))/K`,
   `ITT=(sum_i (Y_i(c_i)-Y_i(false)))/N`.
   For allocation S the contacted outcome is `Y_i(c_i)` on S and
   `Y_i(false)` off S. Let `diff(S)` be the treatment-minus-control contrast
   in those outcomes, and
   `contact(S)=(sum_{i in S} 1_{c_i=true})/m`. Then
   `ITT=pi theta`, `E_S diff=ITT`, `E_S contact=pi`,
   `E_S contact>0`, and `theta=E_S diff/E_S contact`.

The final numeric assertion is `((9.4-7.0)/(1/2))=4.8` in R. The ratio above
is a ratio of expectations, not an expectation of allocation-level ratios.
Fixed Y and c do not depend on S, no unit outside S is contacted, and each
outcome depends only on that unit's own contact status. No distributional
independence assertion appears separately in the type.
