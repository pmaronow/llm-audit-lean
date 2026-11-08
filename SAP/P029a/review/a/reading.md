# Blind mathematical reading

Saved before opening `claims.json` or `record.json`. This reading uses only the
Defs, Challenge, and Mathlib sources. The Challenge has thirteen closed theorem
stubs, `SAP.P029a.T1` through `SAP.P029a.T13`. Their universe parameters quantify
over the types described below; they do not supply mathematical assumptions.
All premises are inside the expanded propositions.

## Shared objects and conventions

A potential response is a tuple `(X,D0,D1,Y0,Y1)`, where `D0,D1` are Boolean
and `Y0,Y1` are real. Write `tau=Y1-Y0`, `C={D0=0,D1=1}` and
`F={D0=1,D1=0}`. At Boolean assignment `Z`, treatment is `D=DZ`, and the
observed outcome is `Y=Y1` if `D=1`, otherwise `Y0`. Thus exclusion and
consistency are built into the definition of the observed outcome.

For a finite type L, a finite law means real masses `p_i>=0` with
`sum_i p_i=1`. `E_p v=sum_i p_i v_i`, `P_p(A)=sum_{i in A}p_i`,
`E_p[v|A]=E_p[v 1_A]/P_p(A)`, `Cov_p(u,v)=E_p(uv)-E_pu E_pv`,
`Var_p(v)=Cov_p(v,v)`, and `Corr_p(u,v)=Cov_p(u,v)/sqrt(Var_pu Var_pv)`.
Finite independence means `P(U=a,V=b)=P(U=a)P(V=b)` for every a,b in the
respective entire codomains. Finite conditional independence given X means
the corresponding product formula for every x,a,b, subject to `P(X=x)>0`.
The auxiliary Bernoulli product construction gives `(i,z)` mass
`p_i e^z(1-e)^(1-z)`.

For a measure mu on a measurable space Omega, `P(A)=(mu A).toReal`, and
`E[v|A]=(integral_A v dmu)/P(A)`. Every general IV statement separately
requires mu to be a probability measure. Consequently `.toReal` is ordinary
finite measure conversion there. The following IV bundle means:

* X,D0,D1,Y0,Y1,Z are measurable; Y0,Y1 are integrable;
* Z is independent of the joint tuple `(X,D0,D1,Y0,Y1)`;
* `0<P(Z=1)<1`, `P(F)=0`, and `E[D|Z=1]-E[D|Z=0] != 0`.

The finite IV bundle uses the analogous finite law, independence, overlap,
no-defiers and nonzero first stage; no measurability or integrability is
needed on finite sums. For a profile x write
`pi(x)=P(C,X=x)/P(X=x)` and `tau_C(x)=E[tau|C,X=x]`. Latent mean equality
at x is `E[tau|X=x]=tau_C(x)`; finite latent ignorability requires this for
all positive-mass profiles. Receipt mean equality at x is the pair of
equalities `E[Yd|D=1,X=x]=E[Yd|D=0,X=x]`, d=0,1. It is a mean condition,
not by definition full conditional independence.

For weights w, define
`m_w(v,z)=E[wv|Z=z]/E[w|Z=z]`,
`Delta_w(v)=m_w(v,1)-m_w(v,0)`, and
`W(w)=Delta_w(Y)/Delta_w(D)`. This is exactly the finite and population
Wald notation below. Population covariance is `integral uv - integral u
integral v`.

Mathlib operations are total: real division by zero is zero; `Real.log 0=0`
and log of a negative argument is log of its absolute value; real sqrt is
zero for negative arguments; a Bochner integral of a nonintegrable function
is zero; an infinite ENNReal has `toReal=0`; the nonsingular matrix inverse
is zero if its determinant is not a unit. These conventions must be checked
against the premises rather than silently interpreted as partial operations.
The extended negative log used here explicitly returns `+infinity` at zero
and otherwise embeds `-Real.log(x)` in EReal. Natural powers use `0^0=1`.

The relevant Mathlib definitions were followed in
`Probability/Independence/Basic.lean` (independence of generated sigma
algebras), `Probability/ConditionalProbability.lean` (normalized restricted
measure), `MeasureTheory/Integral/Bochner/Basic.lean`,
`MeasureTheory/Function/LpSeminorm/Defs.lean`,
`Analysis/SpecialFunctions/Log/Basic.lean`, `Analysis/Real/Sqrt.lean`,
`Analysis/Convex/Function.lean`, `Analysis/Calculus/Deriv/Basic.lean`, and
`LinearAlgebra/Matrix/NonsingularInverse.lean`. `MemLp f 2 mu` means a.e.
strong measurability and a finite second moment. `StrictConcaveOn` includes
convexity of the domain and the strict Jensen inequality for distinct
points and strictly positive coefficients summing to one. `HasDerivAt f a x`
is the ordinary derivative assertion at x. `IsUnit` of a real determinant
means that determinant is nonzero. Finite matrix operations, sums and
products are ordinary finite operations.

## T1

There are no hypotheses. The specified six-atom population has constant X,
a type T independent of fair Z, and this table:

|T|mass|D0|D1|Y0|Y1|
|---|---:|---:|---:|---:|---:|
|complier|1/2|0|1|0|1|
|always taker|1/4|1|1|0|0|
|never taker|1/4|0|0|0|0|

The assertion is the conjunction of all of the following:

* This is a finite IV law and satisfies receipt mean equality at its sole
  profile. The joint potential outcome pair `(Y0,Y1)` is independent of D.
* `P(D=1)=P(D=0)=1/2`; `P(C|D=1)=P(C|D=0)=1/2`;
  `E tau=1/2`, `E[tau|C]=1`, `pi=1/2>1/4`.
* `W(1)=1` and `W(1/pi)=1`; every record's inverse score is 2.
* `P(Z=1)=1/2`, `E[D|Z=1]=3/4`, `E[D|Z=0]=1/4`;
  for each Boolean d, `E[Y1|D=d]=1/2` and `E[Y0|D=d]=0`;
  `E[Y|Z=1]=1/2`, `E[Y|Z=0]=0`.
* Finite latent ignorability fails.

## T2

First it asserts both explicit directions of incomparability. The T1 law
satisfies finite IV and receipt mean equality and fails latent ignorability.
The second law uses the same T,Z masses and D0,D1 as T1 but
`Y0=1_{T=always}`, `Y1=Y0+1`. It satisfies finite IV and latent
ignorability and fails receipt mean equality. In this second law every
tau is 1, ATE=LATE=1, and the receipt-group means of Y0 are 1/2 and 0
for D=1 and D=0, respectively; the corresponding Y1 means are 3/2 and 1.

Finally, universally quantify in order: arbitrary types Omega and X;
measurable structures on both with measurable singletons in X; a measure
mu on Omega and a proof it is a probability measure; a response function U;
a Boolean assignment function Z; the full general IV bundle; the additional
premise `D0=0` mu-almost everywhere; a profile x; `P(X=x)>0`;
`pi(x)>0`; receipt mean equality at x. The conclusion is latent mean
equality at x. No other profiles are required to have positive compliance.

## T3

There are no premises. Two fully specified 32-atom laws are asserted.
Both have Boolean variables `(c,t,x,b,z)`, with b,z independent fair coins
independent of `(c,t,x)`; set `D0=(not c) and b`, `D1=D0 or c`,
`Y0=0`, `Y1=t`, and `X=x`. Thus c is the complier indicator.

In the marginal law, each pair (c,t) has mass 1/4, and
`P(x=1|c,t)=3/4` if `c=t=1`, otherwise 1/4. It satisfies finite IV and
t is independent of `(D0,D1)`. The assertions are:

* `P(t=1)=P(t=0)=1/2`, `P(x=0)=5/8`, `P(x=1)=3/8`;
  `pi(0)=2/5>1/3`, `pi(1)=2/3>1/3`;
  `E[tau|x=0]=2/5`, `tau_C(0)=1/4`,
  `E[tau|x=1]=2/3`, `tau_C(1)=3/4`.
* ATE=LATE=1/2, `P(C)=1/2`, `E[1_C tau]=1/4`, `W(1)=1/2`;
  `E[1/pi(X)]=17/8`, `W(1/pi)=7/16`;
  `Delta_{1/pi}(Y)=7/34`, `Delta_{1/pi}(D)=8/17`;
  inverse scores at x=0,1 are 5/2,3/2;
  `Delta_1(Y)=1/4`, `Delta_1(D)=1/2`.
* `E[D1|x=0]=7/10`, `E[D1|x=1]=5/6`,
  `E[D0|D1=1,x=0]=3/7`, `E[D0|D1=1,x=1]=1/5`;
  `(5/8)(1/4)+(3/8)(3/4)=7/16`.

In the conditional law, `P(c,t,x)=9/32` when c=t=x, `1/32`
when c=t differs from x, and `3/32` when c differs from t. It satisfies
finite IV, conditional independence `t independent (D0,D1) given X`,
latent ignorability, and fails unconditional independence of t and
`(D0,D1)`. Further:

* For each Boolean x, `P(X=x)=1/2`; `pi(0)=1/4>1/8`,
  `pi(1)=3/4>1/8`; inverse scores are 4 and 4/3;
  `E[tau|X=0]=1/4`, `E[tau|X=1]=3/4`.
* `P(t=1)=P(t=0)=1/2`, `P(C)=1/2`, ATE=1/2,
  `E[1_C tau]=5/16`, LATE=5/8, `W(1)=5/8`, `W(1/pi)=1/2`;
  `Delta_{1/pi}(Y)=3/16`, `Delta_{1/pi}(D)=3/8`.

## T4

Universally quantify in order: types Omega,X; measurable structure on
Omega; a finite type X with a measurable structure and measurable
singletons; probability measure mu; U,Z; the complete IV bundle;
`pi(x)>0` at every positive-mass profile; a real function w on X;
`w(x)>0` for every x, including zero-mass profiles. Then:

1. `W(w(X))=E[w(X)1_C tau]/E[w(X)1_C]`.
2. The same ratio is
   `sum_x P(X=x)w(x)pi(x)tau_C(x) / sum_x P(X=x)w(x)pi(x)`.
3. `W(1)=LATE` and `W(1/pi(X))=sum_x P(X=x)tau_C(x)`.
4. `W(1)-W(1/pi(X))=Cov(pi(X),tau_C(X))/P(C)`.
5. If LATE=ATE, then `W(1)=ATE`.
6. If latent mean equality holds at every positive-mass profile, then
   `W(1/pi(X))=ATE`.

In a second universally quantified proposition, the same types, spaces,
mu,U,Z, IV bundle and positive-profile compliance are followed by the
premise that either `tau independent (1_C,X)` or
`1_C independent (tau,X)`. The conclusions are LATE=ATE, latent mean
equality at every positive-mass profile, and both Wald ratios equal ATE.

T4 additionally asserts the marginal and conditional witness fact bundles
of T3, including both IV laws, their independence assertions, the
conditional-law latent ignorability, all numerical conclusions listed in
those fact bundles, and all conclusions in `IndependenceWitnessMeans`:
P(C), LATE, marginal `E[1_C tau]`, conditional profile masses and the four
inverse-score arm differences. It does not assert sampling convergence.

## T5

There are no external hypotheses. The design has 500 rows
`(r,k,z) in Fin 50 x Fin 5 x Bool`, and columns `(1,z,x1,x2,x3)`,
where the five covariate profiles are `(0,0,0)`, `(1/2,0,0)`,
`(0,1/2,0)`, `(0,0,1/2)`, `(-1/2,-1/2,-1/2)`. Its Gram matrix is

```
[500 250  0  0  0]
[250 250  0  0  0]
[  0   0 50 25 25]
[  0   0 25 50 25]
[  0   0 25 25 50]
```

For every Boolean opposite and every row, `D0=0,D1=1`,
`Y0=5+opposite*z`, `Y1=Y0+5`; consequently tau=5, D=z, and
`Y=5+(if opposite then 6 else 5)z`. All profile coordinates and 1/5
are strictly between -1 and 1, and exactly 250 rows have z=1.
The latent index construction `AC=1_{indexAC>0}`,
`A=1_{indexA>0} AC`, `C=AC-A`, `D=Cz+A` evaluated at indices
2,-2 gives AC=C=1,A=0,D=z for every z.

The Gram matrix is exactly the matrix displayed and has determinant
3906250000. Its inverse times its product with `(5,5,0,0,0)` and
`(5,6,0,0,0)` gives those vectors. Actual outcome cross-products
are `(3750,2500,0,0,0)` and `(4000,2750,0,0,0)`, and multiplication
by the inverse Gram matrix gives the corresponding coefficient vectors.

For every row-weight function w with every w_i>0, and then every real
coefficient vector b of length five, `G=X' diag(w) X` has nonzero
determinant and `G^{-1} X' diag(w) X b=b`.

Define `B_n(x)=n^{-1}sum_i 5(1+x_i1+x_i2+x_i3)`. The separately
specified 500-row constant profile `(1/5,0,0)` gives B=6.
The four squared errors are `(5-6)^2=1`, `(5-5)^2=0`,
`(6-6)^2=0`, `(6-5)^2=1`. For every positive natural R, the same
four RMSEs for the constant runs are 1,0,0,1 respectively. Here
`RMSE(t,B)=sqrt(sum_{r in Fin R}(t_r-B_r)^2/R)`.

## T6

This is a conjunction of universal assertions and the T5
`NoiseScoringWitnessFacts` and `NoiseWitnessAdmissibility` bundles:

* For every real y, `(y+5)-y=5`. For every natural n>0 and every
  `Y0:Fin n -> R`, its sample average effect is 5. For every measurable
  Omega, probability mu, arbitrary real function Y0, measurable set C
  with P(C)>0, both the integral of `(Y0+5)-Y0` and its event mean on C
  are 5. There is no measurability premise on Y0 itself; the difference
  is pointwise constant.
* For every natural R>0 and every run t of length R, the corrected
  RMSE is `sqrt(sum_r(t_r-5)^2/R)`.
* The measure `uniformCovariateLaw=(volume(-1,1))^{-1} volume|(-1,1)`
  has first moment 0 and second moment 1/3.
* Universally, for any measurable Omega, probability mu, n>0, family
  `X:Fin n -> Fin 3 -> Omega -> R`, measurable coordinates, joint
  independence of the entire n-by-3 family, and each coordinate's
  pushforward equal to this uniform measure: `E B_n=5` and
  `Var(B_n)=25/n`.
* For every real t,B,
  `(t-B)^2-(t-5)^2=(B-5)^2-2(t-5)(B-5)`.
* For every natural R, then runs t,B of length R, subject to R>0,
  `sum(t-B)^2/R-sum(t-5)^2/R`
  `=sum(B-5)^2/R-(2/R)sum(t-5)(B-5)`.
* For every finite type L, then real arrays p,t,B, a finite law p, and
  E_p B=5, `E_p(t-B)^2-E_p(t-5)^2=Var_p(B)-2Cov_p(t,B)`.
* For every measurable Omega, probability mu, real functions t,B,
  `t,B in L2(mu)` and E B=5, the same expected-error identity holds
  with integrals and population covariance.

The retained noise bundles include the design equality, response formulas,
two coefficient recovery equalities against the Gram matrix, B=6 at the
separately specified constant profile, the four squared errors, profile
support bounds, all-complier latent indices and the 250 assignment count.

## T7

For a finite observation type I write `Qin(L,w)=-sum_i log(L_i w_i)`
and `Qout(L,w)=-sum_i w_i log L_i`. A global minimum at theta means
`Q(theta)<=Q(t)` for every parameter t in the entire parameter type.

T7 universally asserts:

* For any finite I, arrays L,w with every L_i,w_i>0,
  `Qin(L,w)=Qin(L,1)-sum log w_i`.
* For any finite I, arbitrary parameter type Theta, likelihood family
  L(theta,i)>0 for all theta,i, positive w, and theta,
  theta globally minimizes Qin iff it globally minimizes Qout with
  unit weights. No existence of a minimizer is asserted.
* For every real L, `L*0=0` and its extended negative log is infinity.
  For every finite I, arrays `0<L_i<=1`, a selected i with w_i=0,
  and w_j>0 for all j != i, the sum of extended negative logs of
  L_j w_j is infinity.

The numerical witness uses uniform mass 1/16 on `(x,z,k) in
Bool x Bool x Fin 4`, D0=0, `D1=1_{k<1}` at x=0 and
`D1=1_{k<3}` at x=1, Y0=0,Y1=1+x. Put weight a=9 if
observed D=1, otherwise 1. The *specified* arrays are
`p=(1/4,3/4)` and `pW=(3/4,27/28)`. The conclusions are
`9/(9+3)=pW(0)`, `27/(27+1)=pW(1)`,
`W(a/p(X))=3/2`, `W(a/pW(X))=17/10`, and these are unequal.

For four cells `(x,z)`, success counts out of four are 1,2,1,3
in order `(0,0),(0,1),(1,0),(1,1)`. Specified unweighted rates
are 1/4,1/2,1/4,3/4, and specified weighted rates are
3/4,9/10,3/4,27/28. Each array has `0<q(x,0)<q(x,1)<1` for
every x. For `L4(q)=product_cells q^successes (1-q)^(4-successes)`,
`L4(qW)/L4(q)=729/1500625<1`; the weighted differences at x=0,1
are 3/20,3/14.

For every real t>0 change only the weight of `(x=0,z=1,k=1)` to t,
leaving all other weights 1. Define specified perturbed scores
`p_t(0)=1/(3+t)`, `p_t(1)=3/4`. The conclusion is
`W(a_t/p(X))=3/2`, `W(a_t/p_t(X))=(t+11)/(t+7)`, together
with the two score formulas. The rational function has derivative -1/16
at t=1, and the constant function 3/2 has derivative 0 there.
T7 does not assert any of these score arrays are likelihood fits.

## T8

This conjoins the T7 numerical score/Wald, four-cell, and positive-t
perturbation assertions with the following fitting propositions:

* For every finite I and array `0<L_i<=1`, each `0*log L_i=0`,
  and Qout(L,1)=Qin(L,1).
* For every finite I, positive L, natural-valued weights w,
  `exp(-Qout(L,w))=product_i L_i^(w_i)`.
* For every S,F>0, `ell(q)=S log q+F log(1-q)` is strictly concave
  on (0,1). Its qhat=S/(S+F) lies in (0,1), and for every q in
  (0,1), ell(q)<=ell(qhat), with equality iff q=qhat.
* Universally quantify finite types I,C; cell:I->C; D:I->Bool;
  real weights w; w_i>=0 for all i; and positive weighted success
  and failure totals S_c,F_c for every c. Define
  qhat_c=S_c/(S_c+F_c). Then every qhat_c is interior. For every
  q:C->R with all q_c interior, Qout for the individual Bernoulli
  factors at qhat is <= its value at q, with equality iff q=qhat.
  No assumption of independence or random sampling is attached to this
  deterministic optimization assertion.
* The same uniqueness assertion, including interiority, holds for
  three explicit datasets: the eight treated records `(x,k)` of the
  T7 witness with receipt weight 9 or 1 and qhat=pW; those records
  with a_t and qhat=p_t for every t>0; and the sixteen records in
  the four T7 cells, receipt `k<successCount`, weights 9 or 1,
  and qhat the specified weighted four-cell rates.
* Universally, for finite I, arbitrary Theta, L(theta,i)>0 for every
  theta,i, k>0, and theta, theta globally minimizes Qin at constant
  weight k iff it globally minimizes Qout at constant weight k.

The free-cell fits have no probit or coefficient parametrization.

## T9

The finite record type is the disjoint union of nine cells of sizes
`602,768,2514,160,155,461,1789,5247,7237`. Race is recorded true
in the first three, false in the next three and missing in the last
three. In each triple, assignment is true in the first two cells,
and contact is true only in the first cell. Every record has mass
1/18933. Completion A labels only the first triple true; completion B
labels the first and last triples true.

For every real outcome vector Y on these records:

* There are 18933 records, their masses form a finite law, and both
  completions agree with every recorded binary label.
* With constant X, D0=0,D1=contact,Y0=Y1=Y, every observed treatment
  equals recorded contact, every observed outcome equals Y, and
  no record is a defier.
* `P(contact)=2551/18933`; true-race masses in completions A,B are
  3884/18933 and 18157/18933; joint true-race/contact masses are
  602/18933 and 2391/18933.
* The integer cross-products are
  `18933*602-2551*3884=1489582` and
  `18933*2391-2551*18157=-1049704`.
* `E[contact|A=1]-E[contact|A=0]=744791/29225158>0`;
  `E[contact|B=1]-E[contact|B=0]=-131213/1761229<0`.

For every raw-code array R taking values in optional strings, subject to
the premise that `R_i=some code` implies the recorded binary race at i
is `some(code="W")`, appending either completion preserves every R_i
exactly, and every present code agrees with both appended binary labels.
In particular the premise forces R to be missing in the last three cells.

For every e with 0<e<1, the product over all records of e if assigned
and 1-e otherwise is positive. Finally
`E[A|contact=1]>E[A|contact=0]` and
`E[B|contact=1]<E[B|contact=0]`.

## T10

For every n, binary arrays C,W on `Fin(n+1)`, then premises
`0<count(W)<n+1` and `0<count(C)<n+1`, put N=n+1,
nW=count(W), nC=count(C), n11=count(C and W), and uniform p=1/N.
The conclusions are

* `Cov(C,W)=(N*n11-nC*nW)/N^2`;
* `E[C|W=1]-E[C|W=0]=(N*n11-nC*nW)/(nW*(N-nW))`;
* `E[W|C=1]-E[W|C=0]=(N*n11-nC*nW)/(nC*(N-nC))`;
* each of the corresponding two strict-positive comparisons holds
  iff `nC*nW<N*n11`.

The exact Raleigh comparisons are
`602/1370-160/315=-2957/43155<0` and
`602/1370-155/308=-13467/210980<0`.
T10 also includes T9's entire universally quantified RaceCompletionFacts
bundle and assignment-product support assertion, but not its raw-code
preservation proposition or its two explicit reverse comparisons.

Finally quantify n, a finite group type G, real arrays s,A on
`Fin(n+1)`, and group:Fin(n+1)->G. Let p=1/(n+1),
sbar_g=E[s|group=g], Abar_g=E[A|group=g]. Then

`Cov(s,A)=E[(s-sbar_group)(A-Abar_group)]`
`+E[(sbar_group-E s)(Abar_group-E A)]`.

For every g, subject first to P(group=g)>0, and then to the premise
that for every i outside g and every j in i's group one has A_j=A_i,
the within-group term equals
`count(group=g)/(n+1) * E[(s-sbar_g)(A-Abar_g)|group=g]`.

## T11

There are no hypotheses. First witness: t is Boolean with P(t=1)=1/4,
Z independently has P(Z=1)=1/4; set X constant, D0=t,D1=1-t,
u=t-1/4,Y0=u,Y1=u+1, and v=D-1/4-Z/2. It is a finite
law, and Z is independent of the joint potential response tuple.
For every record, tau=1, Y=D+u, D=1/4+Z/2+v. For each z,
E[v|Z=z]=0. The other asserted values are:

`E Z=1/4`, `Var Z=3/16`, `E u=0`, `Var u=3/16`,
`Cov(Z,u)=Corr(Z,u)=0`, `Cov(Z,D)=3/32`,
`Cov(D,u)=3/32`, `P(defier)=1/4`,
`E[D|Z=0]=1/4`, `E[D|Z=1]=3/4`,
and `Cov(Z,Y)/Cov(Z,D)=1`.

Second witness: four equal-mass records u=-2,-1,1,2; Z=1 on
u=-2,2 and 0 on u=-1,1; X constant, D0=1_{u>0},D1=1,
Y0=u,Y1=u+1, v=D-1/2-Z/2. This is a finite law and for each
record tau=1, Y=D+u, D=1/2+Z/2+v. For each z,
E[v|Z=z]=E[u|Z=z]=0. Further:

`Var Z=1/4`, `Var u=5/2`, `Corr(Z,u)=Cov(Z,u)=0`,
`Cov(Z,D)=1/8`, `Cov(D,u)=1/4`, P(defier)=0,
u and Z are not independent,
`E[D|Z=0]=1/2`, `E[D|Z=1]=1`,
`Cov(Z,Y)/Cov(Z,D)=1`,
`P(|u|=2|Z=1)=1`, `P(|u|=2|Z=0)=0`.

## T12

T12 includes both complete T11 finite-law fact bundles SEMDefierFacts
and SEMDependenceFacts (their law, equations, zero conditional means,
variances, correlations, relevance/endogeneity covariances, defier and
independence conclusions). It does not include the separate
SEMWitnessMeans bundle of extra receipt rates and |u| probabilities.

It also quantifies arbitrary types I,K with K finite, arrays Y0,Y1,u on
I, Q:I->K->R, beta0,beta1 and coeff:K->R. Subject in order to
`Y0_i=beta0+sum_k coeff_k Q_ik+u_i` for every i and
`Y1_i=beta0+beta1+sum_k coeff_k Q_ik+u_i` for every i, it concludes
`Y1_i-Y0_i=beta1` for every i.

Finally, an equal-probability Boolean h independent of fair Z defines
X constant, D0=0,D1=1,Y0=0 and Y1=1 if h=0, 2 if h=1.
This law satisfies finite IV; its two effects are 1 and 2 and no
single real beta is their common effect; ATE=LATE=W(1)=3/2;
`Cov(Z,D)=1/4`, first stage=1, and for each Boolean t the effect
`if t then 2 else 1` occurs with probability 1/2.

## T13

There are no hypotheses. Start with the constant-X law on independent
T,Z with T masses 1/2,1/4,1/4 and fair Z, D0,D1 as in T1,
Y0=0,Y1=1. It satisfies finite IV and latent ignorability,
`pi=1/2>1/4`, `E[D|Z=1]=3/4`, `E[D|Z=0]=1/4`.

Separately sample two independent receipts d1~Bernoulli(3/4) and
d0~Bernoulli(1/4), so masses of `(0,0),(0,1),(1,0),(1,1)` are
3/16,1/16,9/16,3/16 and form a finite law. On the closed triangle
`0<=q<=p<=1`, likelihood is `p^d1(1-p)^(1-d1)` times
`q^d0(1-q)^(1-d0)` with natural Boolean exponents. The selected
fits in that order are `(0,0),(1/2,1/2),(1,0),(1,1)`.
For every d the selected fit lies in the triangle and dominates the
likelihood at every point in the triangle. Its likelihood is 1/4 for
d=(0,1), otherwise 1. The fitted difference is 1 exactly at (1,0),
otherwise zero; its mean is 9/16, not pi=1/2, with bias 1/16.
The raw difference d1-d0 has expectation 1/2. The nested probability
formula `a(1-b)z+ab` at `(a,b)=(3/4,1/3)` gives arm rates 3/4,1/4.

For independent binomial counts K1~Binomial(5,1/2),
K0~Binomial(5,3/10), using the explicitly defined binomial masses
`choose(n,k)p^k(1-p)^(n-k)`, the conclusions are
`E max(K1/5-K0/5,0)=15659/64000`, its difference from 1/5 is
2859/64000, and `P(K1<K0)=257079/1600000`. Here n-k is natural
subtraction, but k belongs to Fin(n+1), so k<=n.

For every pair of real p,q, four polynomial certificates hold:

```
1-(1-p)(1-q) = p+(1-p)q
1/4-(1-p)q = (p-1/2)^2+(1-p)(p-q)
1-p(1-q) = (1-p)+pq
1-pq = (1-p)+p(1-q).
```

No finite-coefficient probit maximum, asymptotic sampling statement or
validation of an external dataset is asserted by any of these last
finite arithmetic statements.
