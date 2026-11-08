# Blind reading

Saved before opening `claims.json` or `record.json`. This reading uses only the
Defs and Challenge sources and the Mathlib definitions they use. Challenge
docstrings are descriptions, not additional hypotheses or conclusions.

## Shared mathematical definitions

`Bool` has two points, written 0 (false) and 1 (true), and `assignment` is their
real-valued 0/1 coding. `Fin n` is {0,...,n-1}. Finite sums here include every
point of the specified finite type; `range J` is {0,...,J-1}. All fractions,
effects, expectations, and weights below are real, except the IV doses, which
are natural numbers. Real subtraction is ordinary subtraction.

A `Population Ω`, where Ω is a finite type, consists of weights w_i >= 0 with
sum_i w_i = 1. Thus such a population cannot exist on an empty type. Write
E f = sum_i w_i f(i), P(A) = E 1_A, and
E(f | A) = E(1_A f)/P(A), where `indicator` is exactly 1 on a true proposition
and 0 otherwise. The definition of this conditional mean returns 0 if P(A)=0
because real division by zero in Lean is 0; it does not contain a positivity
condition of its own.

For a real p, a_1=p and a_0=1-p. `jointMass` is a_t w_i. For any f(t,i),
`armMean(t,f)` = [sum_i a_t w_i f(t,i)]/a_t, and `contrast(f)` is its value
at t=1 minus its value at t=0. Whenever 0<p<1, armMean(t,f)=E f(t,i).
`designMean(f)`=(1-p)E f(0,i)+p E f(1,i);
`covariance(f,g)`=designMean(fg)-designMean(f)designMean(g);
`variance(f)`=covariance(f,f); and `assignmentSlope(f)`=Cov(T,f)/Var(T).
The finite theorems use p=1/2 or explicitly assume 0<p<1.

A `MediationModel Ω` is any two functions K:{0,1} x Ω -> R and
S:{0,1} x R x Ω -> R. Observed support is Y(t,i)=S(t,K(t,i),i), so consistency
is built into its definition. Its reduced form is RF=contrast(Y). The
mediated effect is M=E[S(0,K(1,i),i)-S(0,K(0,i),i)], and the direct effect is
D=E[S(1,K(1,i),i)-S(0,K(1,i),i)]. There is no restriction on S or K implicit
in this structure. The linear model has K(t,i)=alpha+a t+u1(i) and
S(t,k,i)=sigma+b k+c t+u2(i).

A uniform population on a nonempty finite Ω has w_i=1/|Ω|. A product
population has weights w_(i,j)=w_i w_j.

For the measure-theoretic definitions, Ω is a type with a sigma algebra and μ
is a measure. `IsProbabilityMeasure μ` means μ(Ω)=1. `unitInterval` is the
subtype [0,1] of R. Mathlib's `bernoulliMeasure true false p` assigns mass p
to 1 and 1-p to 0. `randomizedLaw μ p` is the product measure
ν=μ x [p δ_1+(1-p)δ_0] on Ω x Bool. Thus assignment is independent of all
potential functions on Ω. `lawArmMean(t,f)` is
[integral over {(i,z): z=t} of f(z,i) dν]/ν({z=t}).toReal;
`lawContrast`, `lawReducedForm`, `lawMediated`, and `lawDirect` replace the
finite quantities above by this conditional mean and μ-integrals.
`IntegrableMediationPotentials μ m` requires all five functions
K(0), K(1), S(0,K(0)), S(0,K(1)), and S(1,K(1)) to be μ-integrable.
In Mathlib this means almost everywhere strongly measurable with finite
integral of the absolute value. Consequently the differences being integrated
are integrable as well. Mathlib's Bochner integral defaults to 0 outside its
integrability domain, but these five hypotheses avoid using that convention.
The positive assignment probabilities avoid a zero conditioning denominator;
the probability assumption avoids infinite measure converted to a real.

An `IVModel Ω` is K:{0,1} x Ω -> N and R:N x Ω -> R. Its potential support
`ivPotentialSupport(z,k,i)` is R(k,i), independent of z, and its observed
support is Y(z,i)=R(K(z,i),i). Thus exclusion and consistency are built in.
`ivKnowledge` is K cast to R. The first stage F is contrast(K), the reduced
form G is contrast(Y), and the IV ratio is V=G/F. An increaser satisfies
K(0,i)<K(1,i). Its effect C is
E[R(K(1,i),i)-R(K(0,i),i) | K(0,i)<K(1,i)].
The conditional observable mass at (k,y) in arm z is
P(K(z)=k and Y(z)=y). The full observable law at (z,k,y) is a_z times that
mass. In these finite models a point-mass function specifies the full law.

For a natural margin j, Δ_j(i)=R(j,i)-R(j-1,i), with natural subtraction
in j-1. Crossed margins in all sums are j=r+1 >= 1, so the truncated
subtraction is ordinary predecessor there. The upward-crossing indicator is
U_j(i)=1_{K(0,i)<j<=K(1,i)}, and the signed crossing is
Q_j(i)=1_{j<=K(1,i)}-1_{j<=K(0,i)}. Let π_j=P(K(0)<j<=K(1)),
w_j=π_j/F, and e_j=E(Δ_j | K(0)<j<=K(1)).

Mathlib checks used: `Topology/UnitInterval.lean` defines [0,1];
`Probability/Distributions/Bernoulli.lean` defines the two weighted Dirac
measures; `MeasureTheory/Measure/Typeclasses/Probability.lean` defines total
mass one; `MeasureTheory/Measure/Prod.lean` defines the product measure and
proves its rectangle formula; `MeasureTheory/Function/L1Space/Integrable.lean`
defines integrability; `MeasureTheory/Integral/Bochner/Basic.lean` defines the
integral and its out-of-domain zero convention; `Order/Monotone/Defs.lean`
uses the usual order-preserving meaning of `Monotone`; and
`Algebra/GroupWithZero/Basic.lean` supplies `div_zero`.

## SAP.P043.T1

There are no hypotheses or variable objects: this is a conjunction of facts
about two fixed finite models at p=1/2, followed by universal assertions about
their assignment laws.

The linear population has four equally weighted points i=(r,s) in Bool².
u1=1/5 if r=1 and -1/5 otherwise; u2=1/10 if s=1 and -1/10 otherwise.
The model is
K(t,i)=8+(6/5)t+u1(i),
S(t,k,i)=23/10+(k-8)/20-(3/50)t+u2(i).
The theorem asserts all of the following:

1. For every t and i the joint mass is 1/8. For every r,s,
   P(i.1=r and i.2=s)=1/4, and for every r each coordinate has probability
   1/2 of equaling r.
2. For every i, K(1,i)-K(0,i)=6/5 and this difference is positive.
3. For every t,k,h,i, if h>0 then S(t,k+h,i)-S(t,k,i)=h/20 and this
   difference is positive. The quantifiers precede the implication.
4. contrast(K)=6/5, M=3/50, D=-3/50, RF=0, Var(T)=1/4,
   Cov(T,Y)=0, Cov(T,K)=3/10, assignmentSlope(Y)=0,
   assignmentSlope(K)=6/5, (6/5)(1/20)=3/50, and
   (6/5)(1/20)-3/50=0.
5. For every arm t and every real y, its conditional observed support mass
   is 1/4 when y is one of 219/100, 221/100, 239/100, 241/100, and 0
   otherwise. The conditional mass is the armMean of the indicator Y=y.
6. RF<M and M>0.

The integer population is uniform on Fin 5 x Fin 100 (500 points). Write
d(i)=1+1_{i.1=4}, which equals 2 for 1/5 of the points and 1 otherwise.
K(t,i)=8+t d(i),
S(t,k,i)=2+1_{i.2+1 <= 36+5(k-8)-6t}, with the inequality in R.
The auxiliary `integerGeneralKnowledge` is constantly 2. The theorem asserts:

1. For every t,i the joint mass is 1/1000. For every t,i,
   K(t,i) belongs to {8,9,10}, Y(t,i) belongs to {2,3}, and general
   knowledge equals 2.
2. For every t and real k, if k=8 or k=9, then for every i the increment
   S(t,k+1,i)-S(t,k,i) belongs to {0,1}, and its population mean is 1/20.
3. armMean(0,K)=8, armMean(1,K)=46/5, E(K(1)-K(0))=6/5;
   E S(0,K(0))=59/25, E S(0,K(1))=121/50,
   E S(1,K(1))=59/25; M=3/50, D=-3/50, RF=0.
4. For every t and real y, the conditional mass of Y=y is 16/25 at y=2,
   9/25 at y=3, and 0 otherwise.
5. RF<M and M>0.

The outer conjunction repeats RF=0, M=3/50, D=-3/50 separately for each
model. It then states, first for every population predicate A on Bool² and
every arm t, and separately for every population predicate A on
Fin 5 x Fin 100 and every arm t,
sum_i jointMass(t,i) 1_A(i)=a_t P(A). There are no measurability constraints
on these finite predicates.

## SAP.P043.T2

This theorem has two conjuncts. The first universally quantifies, in order:
an arbitrary type Ω in universe u, a measurable space on Ω, a measure μ,
a proof μ is a probability measure, and p in [0,1]. If 0<p<1, then for
every MediationModel m, if its five specified potentials are integrable,
all the following hold (now M,D,RF are the μ/product-law quantities):

1. RF=integral S(1,K(1)) dμ - integral S(0,K(0)) dμ,
   RF=M+D, RF>=M iff D>=0, and RF>M iff D>0.
2. If D>=0 then RF>=M; if D>=0 and RF<=0 then M<=0;
   and if D>=0 and RF=0 then M<=0.
3. For every i, the individual observed outcome difference equals
   [S(1,K(1,i),i)-S(0,K(1,i),i)]
   +[S(0,K(1,i),i)-S(0,K(0,i),i)].
4. For every real alpha,a,sigma,b,c and every pair of functions u1,u2
   on this same Ω, if u1 and u2 are integrable, then for their linear model
   contrast(K)=a, M=ab, D=c, RF=ab+c, and RF>=M iff c>=0.
   For every natural n and d:Fin n -> R, if c=sum_j d(j), then RF>=M
   iff sum_j d(j)>=0.
5. Under the same universal quantifiers and integrability conditions for
   that linear model, if a>0, then RF/a=b+c/a and RF/a>=b iff c>=0.
6. For every natural n and d:Fin n -> R, if each d(j)>=0, then
   sum_j d(j)>=0. There exists d:Fin 2 -> R whose sum is nonnegative but
   for which not every component is nonnegative.

The second conjunct is the fixed linear finite witness of T1: RF=0,
M=3/50, D=-3/50, and M>0. It does not impose that witness's negative direct
effect on the universally quantified models in the first conjunct. No error
centering, error independence, or parametric assumptions are placed on the
general model; the linear models only require the two errors' integrability.

## SAP.P043.T4

There are no hypotheses. There are two groups of fixed IV constructions at
p=1/2. Set H(k)=1_{9<=k} for every natural k.

For the up/down construction Ω=Bool, w_true=2/3, w_false=1/3:

| i | K(0) | K(1) | R(k) |
|---|---:|---:|---|
| true | 8 | 9 | 3+H(k) |
| false | 9 | 8 | 2+2H(k) |

The theorem asserts armMean(0,K)=25/3, armMean(1,K)=26/3, F=1/3 and F>0;
armMean(0,Y)=armMean(1,Y)=10/3; G=0, V=0, Cov(Z,K)=1/12,
Cov(Z,Y)=0, Cov(Z,Y)/Cov(Z,K)=0; P(increaser)=2/3; C=1;
and (2/3)1+(1/3)(-2)=0.
For every i, it additionally asserts:

1. i is an increaser iff i=true; if i is an increaser, K(0)=8,
   K(1)=9 and R(9)-R(8)=1.
2. For every z, K(z) is in {8,9} and K(z)<=18.
3. For every natural k, R(k) is in {2,3,4}, 0<=R(k)<=7.
4. R is nondecreasing on all of N.

Models A and B each have five equiprobable types, numbered 0 through 4:

| type | A:K(0) | A:K(1) | A:R(k) | B:K(0) | B:K(1) | B:R(k) |
|---|---:|---:|---|---:|---:|---|
| 0 | 8 | 9 | 3+H(k) | 8 | 9 | 3+H(k) |
| 1 | 8 | 9 | 3+H(k) | 8 | 9 | 3+H(k) |
| 2 | 9 | 8 | 2+2H(k) | 9 | 8 | 2+2H(k) |
| 3 | 8 | 8 | 2 | 8 | 9 | 2+2H(k) |
| 4 | 9 | 9 | 4 | 9 | 8 | 2+2H(k) |

For each of A and B, the theorem asserts armMean(0,K)=42/5,
armMean(1,K)=43/5, F=1/5, F>0, armMean(0,Y)=armMean(1,Y)=16/5,
G=0 and V=0. Their full observable laws are equal as functions on
Bool x (N x R). C_A=1 and C_B=4/3. For every z,k,y the conditional
observable law of each model equals the following function:

* z=1: (2/5)1_{k=8,y=2}+(3/5)1_{k=9,y=4}.
* z=0: (1/5)1_{k=8,y=2}+(2/5)1_{k=8,y=3}+(2/5)1_{k=9,y=4}.

For every i, in each model separately, every z has K(z) in {8,9} with
K(z)<=18; for every natural k, 0<=R(k)<=7; R is nondecreasing on N;
and being an increaser implies K(0)=8 and K(1)=9.

There does not exist ANY function from full observable-mass functions
(Bool x (N x R) -> R) to R whose value at A's observable law is C_A
and whose value at B's observable law is C_B. Finally P_A(increaser) and
P_B(increaser) are both nonzero; their exact values are not a separate
conjunct. Together with the positive first stages above, all conditional
effect and IV ratio denominators used in these claims are nonzero.

## SAP.P043.T5

Universally quantify, in order, a type Ω in universe u, a finite-type
structure on Ω, a Population P on Ω, and a real p. If 0<p<1, then for
every IVModel m and natural J, suppose

* for every i both K(0,i)<=J and K(1,i)<=J;
* for every i, K(0,i)<=K(1,i) (individual monotonicity);
* E[(K(1):R)-K(0)]>0.

Then the following conclusions all hold:

1. F=E[(K(1):R)-K(0)] and
   G=E[R(K(1,i),i)-R(K(0,i),i)].
2. Cov(Z,K)=p(1-p)F and Cov(Z,Y)=p(1-p)G. If F!=0, then
   Cov(Z,Y)/Cov(Z,K)=V.
3. For every i,
   R(K(1,i),i)-R(K(0,i),i)=sum_{r=0}^{J-1} U_(r+1)(i) Δ_(r+1)(i),
   (K(1,i):R)-K(0,i)=sum_{r=0}^{J-1} U_(r+1)(i).
4. G=sum_{r=0}^{J-1} E[U_(r+1) Δ_(r+1)] and
   F=sum_{r=0}^{J-1} π_(r+1).
5. For every natural j, w_j>=0; sum_{r=0}^{J-1} w_(r+1)=1; and
   V=sum over r in {0,...,J-1} with π_(r+1)>0 of
   w_(r+1) e_(r+1). Conditional effects at zero-probability margins are
   excluded from this final sum. The first stage is positive by 1 and the
   positive mean hypothesis.
6. For every OTHER IVModel m' on the same Ω, every natural J', and every i,
   if both K'(0,i)<=J' and K'(1,i)<=J', then the two signed identities
   R'(K'(1,i),i)-R'(K'(0,i),i)
     =sum_{r=0}^{J'-1} Q'_(r+1)(i) Δ'_(r+1)(i),
   (K'(1,i):R)-K'(0,i)=sum_{r=0}^{J'-1} Q'_(r+1)(i)
   hold. No monotonicity or first-stage condition on m' is added here,
   but the outer premises still have to be satisfied for m.
7. For every i,j, if i is not an increaser in m then U_j(i)=0.
8. For every i,j in m, Q_j(i) belongs to {-1,0,1} and Q_j(i)=U_j(i).
9. For every other IVModel m' on Ω, every i and natural j, if
   K'(1,i)<j<=K'(0,i), then Q'_j(i)=-1.

This theorem has no law-level quantifier over arbitrary probability spaces:
it is a theorem about finite populations with arbitrary nonnegative masses.
The aggregate's monotonicity and positive first stage are outer premises of
the contrast and covariance claims as well as the margin-average claim.

## SAP.P043.T6

For every pair of natural numbers n,q, every stratum assignment
s:Fin n -> Fin(q+1), and every coefficient vector gamma:Fin q -> R,
define D_k(i)=1_{s(i)=k} for k=0,...,q-1. The reference stratum is q,
and A(i)=sum_{k=0}^{q-1} gamma_k D_k(i). Define gamma*(r)=gamma_r for
r<q and gamma*(q)=0. The theorem states the following conjunction:

1. For every i and k in Fin q, if s(i)=k (via castSucc), A(i)=gamma_k.
2. For every i, if s(i)=q, A(i)=0.
3. For every i, sum_{k=0}^{q-1} D_k(i)=1-1_{s(i)=q}.
4. For every X:Fin n -> Fin 2, u,Y:Fin n -> R, and beta0,beta1 in R,
   the assertion that for every i,
   Y_i=beta0+beta1 X_i+A(i)+u_i
   is equivalent to the assertion that for every i,
   Y_i=(beta0+gamma*(s(i)))+beta1 X_i+u_i.

There are no nonemptiness, rank, stratum-occupancy, error, or statistical
assumptions. n=0 is allowed, but the theorem also covers every positive n;
q=0 means the single legitimate reference stratum, with empty gamma vector
and A=0. X_i is the real cast of its value 0 or 1. `Fin.lastCases 0 gamma`
is precisely the coefficient extension with last value zero.
