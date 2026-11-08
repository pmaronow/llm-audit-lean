# Blind reading of SAP.P020.T1–T5

This file was saved before opening either `claims.json` or `record.json`.
The inputs at this stage were `closure.json`, the Challenge statements and
docstrings, their definition sources, and the generated proof declarations
printed in `scratch/ClosurePrint.log` (successful Lean compilation).

## SAP.P020.T1

### Objects and definitions, unfolded

The theorem has no hypotheses or arguments: it asserts the conjunction called
`T1Statement` in `Defs/Part3.lean:12–83`.

A cluster population consists of natural numbers M and m_t with
0 < m_t < M, positive natural sizes n_j indexed by `Fin M` (the integers
0,...,M-1), and real potential cluster totals y_0j,y_1j. Thus M >= 2.
The constructor and all projections listed in the closure have exactly these
types; the positivity proofs are fields, not independent assumptions about
outcomes. Put m_c=M-m_t and N=sum_j n_j. Assignments are all subsets s of
`Fin M` with cardinality m_t, obtained by `Finset.univ.powersetCard m_t`;
the control set is the complement of s in `Finset.univ`. This set of
assignments is nonempty because m_t <= M. The randomization law is uniform
on it, with weight 1/(number of assignments).

More generally, a `FiniteLaw Ω` is a finite set S of elements of an arbitrary
type Ω and a function w:Ω -> R satisfying w(ω)>=0 for ω in S and
sum_{ω in S} w(ω)=1. Values of w outside S are irrelevant.
`uniformLaw` takes a nonempty S and sets w(ω)=1/|S| for every ω.
Expectation is the real finite sum E[X]=sum_{ω in S} w(ω)X(ω).
Bias at target d is E[X]-d; MSE is E[(X-d)^2]; error probability at
tolerance ε is sum_{ω in S, ε<|X(ω)-d|} w(ω). In particular the error
event uses a strict inequality.

For an arm a, let A_1(s)=s, A_0(s)=s^c, m_1=m_t, m_0=m_c,
S_a(v,s)=sum_{j in A_a(s)} v_j, and n_a(s)=S_a(n,s).
The ATE is Δ=(sum_j y_1j-sum_j y_0j)/N. The difference in means is
D(s)=S_1(y_1,s)/n_1(s)-S_0(y_0,s)/n_0(s).
HT arm totals are H_a(s)=(M/m_a)S_a(y_a,s), and HT(s)=(H_1-H_0)/N.
For a real vector v on `Fin M`, its cluster mean is sum_j v_j/M,
its variance is sum_j(v_j-mean(v))^2/M, and its covariance with u is
sum_j(v_j-mean(v))(u_j-mean(u))/M. These use divisor M, not M-1.
The differenced potential is y'_aj(k)=y_aj-k(n_j-mean(n)).
Raj arm totals are R_a(k,s)=(M/m_a)sum_{j in A_a(s)} y'_aj(k),
and R(k,s)=(R_1-R_0)/N. The arm optimal coefficient is
cov(n,y_a)/var(n); the common coefficient is
(m_t/M)cov(n,y_0)/var(n)+(m_c/M)cov(n,y_1)/var(n).
An individual cluster total is just a finite sum over its individuals.

The fixed `efficiencyPopulation` is M=3, m_t=1,
n=(1,2,4), y_0=(0,1,1), y_1=(0,0,0). Its assignments are the three
singletons, each of probability 1/3. For any positive natural h,
`replicateWithin P h` keeps M and m_t fixed and replaces n by hn and
both potential-total vectors by hy_a. It does not introduce new clusters
or independent assignments.

`DesignConsistent L X d` means: for every real ε>0, as the natural index
r tends to infinity, sum_{ω in support(L_r), ε<|X_r(ω)-d_r|}w_r(ω)
tends to 0 in the usual real topology. `WithinReplicationConsistent P`
uses this definition with population `replicateWithin P (r+1)` at index r,
its uniform cluster law, its difference in means, and its ATE.

### Exact conjunction and quantifier order

The theorem asserts all of the following.

1. For every j in `Fin 3`, the individual control outcomes given by
   zero if j=0, otherwise one at individual i=0 and zero elsewhere, sum
   to y_0j. The all-zero treated outcomes sum to y_1j.
2. For this fixed population: N=7, Δ=-2/7;
   D({0})=-1/3, D({1})=-1/5, D({2})=-1/3;
   HT({0})=-3/7, HT({1})=HT({2})=-3/14;
   E[D]=-13/45, bias(D)=-1/315, MSE(D)=131/33075;
   E[HT]=Δ and MSE(HT)=1/98.
3. For every real k, simultaneously:
   R(k,{0})=-3/7+(6/7)k,
   R(k,{1})=-3/14+(3/14)k,
   R(k,{2})=-3/14-(15/14)k;
   E[R(k)]=Δ;
   MSE(R(k))=1/98-(6/49)k+(9/14)k^2
   =3/686+(9/14)(k-2/21)^2;
   MSE(R(k))=3/686 iff k=2/21;
   MSE(R(k))>=3/686; and
   131/33075<3/686<1/98 with MSE(D)<MSE(R(k)).
4. The size variance is 14/9; its covariances with y_0 and y_1 are
   4/9 and 0, respectively; the common optimal coefficient is 2/21.
5. P(|D-Δ|>1/25)=1.
6. For every natural h, every proof hh of h>0, and every real k,
   in that order: the replicated N is 7h, its ATE is -2/7; for every
   assignment s belonging to the base assignment set, replicated D,
   HT and R(k) equal their base values; replicated bias(D)=-1/315;
   replicated P(|D-Δ|>1/25)=1; and replicated MSE(D)<MSE(R(k)).
7. The natural sequence h -> 7h tends to infinity; the constant sequence
   of base laws/estimators/targets is not design consistent; the positive
   within-cluster replication sequence is not design consistent;
   base bias(D) is nonzero; and base MSE(D)<MSE(HT).

The k in item 6 is the numerical coefficient for the already replicated
cluster totals and sizes. The theorem compares every fixed coefficient;
it does not quantify over an assignment-dependent fitted coefficient.

### Junk values and boundary cases

Real division uses inverse(0)=0. All actual experiment denominators here
are positive: M=3, m_t=1, m_c=2, N=7h with h>0, and both realized arm
sizes on the three supported assignments. The size variance used in the
coefficient is 14/9. Rational constants have nonzero denominators.
The general D definition can evaluate an empty arm to zero on unsupported
assignments, but all pointwise assertions in this theorem use supported
singletons and all expectations sum only over the support. That totalized
extension therefore has no effect. `clusterMean` at M=0 would be zero;
M=0 never occurs here. Natural subtraction M-m_t is truncated, but
m_t<M makes it the ordinary positive difference. All casts of natural
numbers to reals preserve their values and are exact. Finite individual
types are nonempty because sizes are positive. Positive replication
excludes h=0; the growth assertion alone includes h=0 without dividing
by h. The law support cannot be empty because weights sum to 1.
No integral, extended-real conversion, log, sqrt, rpow, extrema, limsup,
liminf, or partial-function default appears in this closure.

## SAP.P020.T2

### Objects, definitions and exact statement

This is another closed conjunction, `T2Statement` (`Part3.lean:86–114`).
The finite laws, finite expectation, bias, MSE, strict error event,
cluster populations, uniform complete randomization, population size,
arm sums and sizes, ATE, difference in means, centered Raj totals,
positive within-cluster replication, and the explicit population have
exactly the finite-sum meanings expanded in the preceding section.
In this section, additionally, Var_L(X) means
sum_{ω in S}w(ω)(X(ω)-sum_{ν in S}w(ν)X(ν))^2.
These expansions define every statistical quantity used here; no measure
integral or limiting definition of variance is involved.

The clauses, with their quantifiers, are:

1. For every type Ω, finite probability law L on Ω, real function T on Ω,
   and real d: MSE_L(T,d)=Var_L(T)+(E_L[T]-d)^2, and
   (E_L[T]-d)^2<=MSE_L(T,d).
2. For every family of types Ω_h indexed by naturals, laws L_h on Ω_h,
   real functions T_h,U_h, real targets d_h, real b and proof b!=0,
   if E[T_h]-d_h tends to b and MSE(U_h,d_h) tends to 0, then there is
   a natural h_0 such that, for every natural h>=h_0,
   MSE(U_h,d_h)<MSE(T_h,d_h). The order is universal data and limit
   hypotheses first, then the existential cutoff and universal tail.
3. For every type Ω, finite law L, real function T, reals d,ε with
   ε>0: sum_{ω in S, ε<|T(ω)-d|}w(ω)<=MSE_L(T,d)/ε^2.
4. For every family Ω_h,L_h,U_h,d_h, if MSE(U_h,d_h) tends to 0,
   then for every real ε>0 its strict-error probabilities tend to 0.
5. For every natural h and proof h>0, the population with M=3,m_t=1,
   sizes (h,2h,4h), control totals (0,h,h) and treated totals zero has
   difference-in-means bias -1/315 and its MSE is strictly smaller than
   that of R(0), where R(0) is HT.
6. The natural sequence 7h tends to infinity.

`DesignConsistent` places no separate population-growth requirement on
clause 4; it is the usual epsilon definition of convergence in probability
for varying finite spaces. The only population-growth conclusion here is
the explicit final clause for the counterexample.

### Junk values and boundary cases

The finite law conditions imply a nonempty support and normalized genuine
probabilities, even if Ω is infinite or nonempty points have zero weight.
An empty Ω admits no such law. Real functions on the finite support have
finite moments. The only new division in clause 3 is by ε^2, which is
positive by its hypothesis. All denominators for the explicit replicated
experiment are positive by the same checks as T1. Its k=0 involves no
regression-variance division. Natural subtraction, casts, and values at
unsupported assignments are as in T1. The general limit clauses allow
h=0, but have no division by the index and impose no growth or positivity
assumptions on the targets. There are no extended-real, integral,
log/sqrt/rpow, empty-extremum, limsup/liminf, or partial-default operations.

## SAP.P020.T3

### Objects, definitions and exact statement

This closed theorem uses `T3WholeStatement_W2`
(`WholeW2.lean:21–37`), not the older T3 statement elsewhere in Defs.
The only non-propositional SAP notion in its closure is
L(x)=`logistic x`=1-(1+exp(x))^(-1), using Mathlib's real exponential.
All arithmetic, order, finite sums and limits of types are ordinary
Mathlib notions; no cluster-population structure is used.

The theorem asserts this conjunction:

1. L is strictly increasing: for all real x<y, L(x)<L(y).
2. For every real n with n>=1, 2/5-(9/10)n<=-1/2.
3. For every real base and then every real n>=1,
   L(base+2/5-(9/10)n)-L(base)<0.
4. For every natural N>0, every pair of functions base,size:`Fin N`->R,
   if size(i)>=1 for every i, then
   sum_i[L(base(i)+2/5-(9/10)size(i))-L(base(i))]/N<0.
5. With exactly the same universal quantifiers and hypotheses, that
   average is different from 7/1000.
6. L(0)=1/2, L(0+2/5-(9/10)*1)=L(-1/2), and L(-1/2)<1/2.

The base is arbitrary. No relation among individuals' bases or sizes is
required. Sizes in these assertions are real, not necessarily integer.
The final clause is a scalar numerical example; the docstring explicitly
says it does not specify a randomized cluster experiment. There is no
existence claim about a one-person experiment or conditional probability
space. The docstring assumes the usual measure-theoretic conditions.

### Junk values and boundary cases

The inverse in L never receives zero since exp(x)>0 for all real x.
It is thus the ordinary logistic probability for every real input.
All rational denominators (2,5,10,1000) are positive.
The average denominator N is positive under N>0, so its `Fin N` index
type is nonempty and its natural-to-real cast is exact. The nonintegral
real sizes do not invoke truncation or rounding. There is no other
division, natural subtraction, integral, extended real, log, sqrt, rpow,
extremum, limsup/liminf, or partial function in the statement's closure.

## SAP.P020.T4

### Objects, definitions and exact statement

This closed theorem asserts `T4Statement` (`Part3.lean:133–151`).
Its SAP notions are the same L(x)=1-1/(1+exp(x)) and
q(n)=`repairedContrast n`=2/5-(9/10000)n for real n.

It states the following conjunction:

1. For every real alpha,block,n,t, in that order,
   alpha+(2/5)t+(7/5)(n/1000)-(9/10)(n/1000)t+block
   =alpha+(2/5)t+(7/5000)n-(9/10000)nt+block.
   There is no assumption that t is binary or n positive in this
   algebraic identity.
2. For every real n: q(n)>0 iff n<4000/9, and q(n)<0 iff
   4000/9<n. At equality these statements simply leave q(n)=0.
3. For every natural n: q(n)>0 iff n<=444, and q(n)<0 iff
   n>=445, with n cast to R when used in q.
4. For every real base, then every natural n:
   L(base)<L(base+q(n)) iff n<=444, and
   L(base+q(n))<L(base) iff n>=445.
5. For every natural N>0, real vector base on `Fin N`, natural vector
   size on `Fin N`, and proof all size(i)>=1:
   if all size(i)<=444, then the real average
   sum_i[L(base(i)+q(size(i)))-L(base(i))]/N is positive;
   and if all size(i)>=445, the same average is negative.

The docstring makes the replacement n -> n/1000 conditional, not an
assertion about the units actually used in a simulation. There is no
numerical ATE asserted for a population with mixed size signs, and no
claim that changing units alone reproduces 7/1000.

### Junk values and boundary cases

All fixed divisors (5,9,10,1000,5000,10000) are positive.
The logistic denominator is positive for every base and shift.
The real threshold is an ordinary rational number, with integer
thresholds obtained on exact natural casts. Natural n=0 is permitted
in clauses 3–4 and causes no undefined arithmetic. The population
average requires N>0 and all sizes positive. No truncated subtraction
is used: differences in q and predictors are real subtraction.
There is no integral, extended-real conversion, log, sqrt, rpow,
extremum, limsup/liminf, or partial default. Generated declarations
whose names happen to refer to other statements are only proofs about
small natural numerals, not additional experimental data or assumptions.

## SAP.P020.T5

### Objects and definitions, unfolded

This closed theorem is `T5WholeStatement` (`WholeW1.lean:39–42`), the
conjunction of `T5Statement` and an additional expectation calculation.
For every cluster population P with natural M,m_t, 0<m_t<M, positive
natural sizes n_j and real potential totals y_0j,y_1j, put
m_c=M-m_t, N=sum_j n_j and bar_n=N/M. The assignments are all
m_t-element subsets s of `Fin M`, with uniform weight 1/binomial(M,m_t).
E is the corresponding finite sum. All these population and law
definitions, constructors and projections are as expanded under T1.

For a Boolean a, m_a=m_t or m_c and A_a(s)=s or its complement.
The realized size mean is bar_n_a(s)=(sum_{j in A_a(s)}n_j)/m_a.
Observed total O_j(s) is y_1j when j belongs to s and y_0j otherwise.
The observed arm mean is bar_O_a(s)=sum_{j in A_a(s)}O_j(s)/m_a.
The parameter khat is an arbitrary function from the finite-subset type
`Finset (Fin M)` to R. It may depend on the assignment without any
independence condition and may be different at every supported assignment.

For a fixed scalar k, the centered potential is
y_aj-k(n_j-(sum_l n_l)/M).
`rajTotal P a k s` is M/m_a times its sum over A_a(s).
In the theorem, k is replaced by khat(s); write this value R_a(s).
The observed version O_Ra(s) is
(M/m_a)sum_{j in A_a(s)}[O_j(s)-khat(s)(n_j-N/M)].
The Raj ATE estimate is (R_1(s)-R_0(s))/N;
Δ=(sum_j y_1j-sum_j y_0j)/N.
For any two real assignment functions X,Z, covariance means the finite sum
E[(X-E[X])(Z-E[Z])], and design bias means E[X]-Δ.

### Exact conjunction and quantifier order

First, for every P and then every assignment function khat, the theorem
asserts these three identities simultaneously:

* E[R_1]=sum_j y_1j-M Cov(khat,bar_n_1).
* E[R_0]=sum_j y_0j-M Cov(khat,bar_n_0).
* E[(R_1-R_0)/N]=Δ+(M/N)[Cov(khat,bar_n_0)-Cov(khat,bar_n_1)].

Next, separately for every P and khat, the bias of that estimate is
(M/N)[Cov(khat,bar_n_0)-Cov(khat,bar_n_1)].

Finally, for every P, then every khat, then every Boolean arm a, the
following entire chain is asserted. Define the following real numbers
locally, after this data is chosen:

* B=(M/m_a){E[sum_{j in A_a(s)}O_j(s)]
  -E[sum_{j in A_a(s)}khat(s)n_j]
  +E[sum_{j in A_a(s)}khat(s)N/M]}.
* C=(M/m_a){E[m_a bar_O_a(s)]
  -E[khat(s)m_a bar_n_a(s)]+E[khat(s)m_a N/M]}.
* D=sum_j y_aj-M{E[khat(s)bar_n_a(s)]-E[khat]E[bar_n_a]}.

For every supported assignment s, R_a(s)=O_Ra(s).
E[bar_n_a]=N/M.
E[m_a bar_O_a]=(m_a/M)sum_j y_aj.
E[R_a]=E[O_Ra]=B=C=D.
Finally D=sum_j y_aj-M Cov(khat,bar_n_a).
The equality R_a=O_Ra is restricted to supported assignments; the
remaining equalities are equalities of finite design expectations.

### Junk values and boundary cases

The hypotheses built into P imply M>=2, m_t,m_c>0 and N>0, so every
divisor in this statement (M,m_a,N and the assignment count) is positive.
Natural M-m_t is not truncated in these admissible populations.
The mean in centered sizes is sum n/M, exactly N/M under the real cast.
`observedTotal` is a total if/else function and uses no default choice.
Unsupported assignments may have a different cardinality from m_a, but
the observed/potential equality is only asserted on the support, and no
expectation sees unsupported values. No ratio involving a size variance
or observed fitted-slope denominator occurs: khat is an arbitrary
real-valued input function. Zero size variance and constant khat are
permitted. The nonempty finite assignment support makes every product
and covariance finite. There are no integrals, infinite extended-real
quantities, log/sqrt/rpow, extrema, limsup/liminf, or partial functions.

## Closure accounting

Every entry in each target's `closure.json` list was read. Structure
constructors and field projections are covered by the full structure
declarations in `Part1.lean`. The definitions used by each target were
read at their listed source locations, including the uniform-support
nonemptiness proof and the positive-size proof for replication.
All 41 distinct generated `._proof_` declarations appearing across the
five closures were additionally printed and read in
`scratch/ClosurePrint.log`: the T1 numeral proofs 1–20; T3 numeral
proofs 1–2; W2 T3 numeral proofs 1–6; T4 numeral proofs 1–3;
`efficiencyPopulation` proofs 1–3; `repairedContrast` proofs 1–3;
`replicateWithin` proof 1; `subscriptPopulation` proof 3; and
`uniformLaw` proofs 1–2. These prove natural numeral typeclass facts,
the witness's arm-count/size positivity, positive replicated sizes,
or normalization/nonnegativity of the uniform finite law. They introduce
no further mathematical hypotheses or hidden definitions.
