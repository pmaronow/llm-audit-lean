# Blind reading

This file was completed before opening either `claims.json` or `record.json`.
The source statements and docstrings of T45--T49, every entry of their
`closure.json` closures, and their defining source declarations were read.
The generated closure declarations were also printed with Lean in
`scratch/PrintClosure.lean`. They prove only that numeral bases 2 and 4 have
at least two elements; they impose no mathematical hypothesis.

## Common notation, completely unfolded

These definitions apply separately in every section below. All sums are
Mathlib finite sums and all limits are `Filter.Tendsto`, with the natural-number
filter `atTop` unless another filter is specified.

A study consists of a function N : natural numbers -> natural numbers,
N(t) > 0 for every t, N(t) tending to infinity, and, for every t, an
experiment on n=N(t) units. An assignment is a function z : Fin n -> Bool.
An experiment is a probability mass function p on this entire finite binary
cube, with p(z)>=0 and sum_z p(z)=1, and real potential outcomes
y_i(z) for every unit and every assignment, including assignments of mass zero.
The constructors and projections `Law.mk`, `Law.mass`, `Experiment.mk`,
`Experiment.design`, `Experiment.outcome`, `Study.mk`, `Study.N`, and
`Study.experiment` are precisely these data and proof fields, without further
conditions. The real `size` is the cast of N(t).

Write E[f]=sum_z p(z)f(z), P(A)=sum_z p(z)1_A(z),
E[f|A]=E[1_A f]/P(A), Cov(f,g)=E[(f-E[f])(g-E[g])],
Var(f)=Cov(f,f), and
Cov(f,g|A)=E[(f-E[f|A])(g-E[g|A])|A]. These are definitions,
not measure-theoretic conditional expectations. Let p_ib=P(z_i=b).
Let y_i(b,z)=y_i(z with coordinate i overwritten by b),
tau_i(z)=y_i(true,z)-y_i(false,z),
ATE(z)=(sum_i tau_i(z))/n, EATE=E[ATE], and
ADSE=(sum_i (E[y_i|z_i=true]-E[y_i|z_i=false]))/n.

Define U_b(z)=(sum_i 1_{z_i=b} y_i(z)/p_ib)/n,
M_b(z)=sum_i 1_{z_i=b}/p_ib, and HT(z)=U_true(z)-U_false(z).
Both weighted arms are nonempty precisely when M_true and M_false are
nonzero. An extension H, one real function on assignments for each t,
must satisfy H_t(z)=n U_true(z)/M_true(z)-n U_false(z)/M_false(z)
whenever both arms are nonempty; its other values are arbitrary.

The structural relation I(i,j) holds if i=j, or if there are two full-cube
assignments differing only at coordinate i with different outcomes for j.
D(i,j) holds if there exists a unit l with I(l,i) and I(l,j).
d_ij=1_{D(i,j)}, d_i=sum_j d_ij, dAVG=(sum_i d_i)/n,
dMAX=sSup {d_i : i in Fin n}, and dRMS=sqrt((sum_i d_i^2)/n).
Thus D is symmetric and reflexive; 1<=d_i<=n, and dAVG,dMAX,dRMS
are positive for the studies being quantified over. `Restricted` means
dAVG/n tends to zero. `NoInterference` means y_i(z)=y_i(z') whenever
z_i=z'_i, for every i and every two full-cube assignments.

For finite random variables X,Y (the codomains may be arbitrary types),
alpha(X,Y)=sSup { |P(X in A and Y in B)-P(X in A)P(Y in B)| :
A and B arbitrary subsets of the respective codomains }.
Let Zmask_i(z) be the assignment retaining z_j when I(j,i) holds and
putting false in every other coordinate. ZmaskOther_i is Zmask_i with its
own coordinate i overwritten by false. Define m(a,e)=0 if a=0, and
Real.rpow(a,e) otherwise. Then
alphaEXT(e)=(sum_i sum_j (1-d_ij)m(alpha(Zmask_i,Zmask_j),e))/n,
and alphaINT(e)=sum_i m(alpha(z_i,ZmaskOther_i),e).

A moment index is an element of `WithTop Real`: a real exponent or top,
written infinity. For k>0 a bound at a finite index r is
E[Real.rpow(|X|,r)]<=Real.rpow(k,r); a bound at infinity is
|X(z)|<=k for every z of positive mass. `RegularMix(S,k,q,s)` means
k>0, q>=2, s>=1, all p_i,true in [1/k,1-1/k] uniformly over t,i,
all observed y_i have the q moment bound with k, and all overwritten
y_i(b,z) have the s moment bound with that same k, uniformly over t,i,b.
For finite q, eEXT(q)=(q-2)/q; at infinity it is 1.
For finite s, eINT(s)=(s-1)/s; at infinity it is 1.
`RegularSequence(S,k,q,s)` uses real finite q,s and requires the same
four bounds with finite real powers for every t, with k>0,q>=2,s>=1.
Bernoulli means each treatment marginal is strictly between 0 and 1 and
p(z)=product_i (p_i,true if z_i=true, else 1-p_i,true), at every assignment.

`LittleO(f,g)` means f(t)/g(t) tends to zero (a quotient definition).
`InProbability(S,X)` means for every real epsilon>0,
P(epsilon<|X_t|) tends to zero. `Op(S,X,a)` means for every epsilon>0
there is a real K>0 such that eventually
P(K*a(t)<=|X_t|)<=epsilon. The rate sqrt(dAVG)/sqrt(n) is
`bernoulliRate`. `HTClaims(S,theta,a)` conjoins convergence of HT-theta
to zero in probability and `Op` for HT-theta at rate a.
`WholeEstimatorClaims` conjoins these two HT conclusions with the two
corresponding conclusions for the particular extension H.

The variance definitions used below are
VBER(z)=(sum_i [1_{z_i=true} y_i(z)^2/p_i,true^2
+1_{z_i=false} y_i(z)^2/p_i,false^2])/n^2,
VAVG=dAVG*VBER, VMAX=dMAX*VBER, and
MSQ=(sum_i (E[tau_i])^2)/n.
Set W_i(z)=1_{z_i=true}y_i(z)/p_i,true
-1_{z_i=false}y_i(z)/p_i,false,
sigma_i^2=Var(W_i), barsigma^2=(sum_i sigma_i^2)/n, and
SDsigma=sqrt((sum_i (sigma_i^2-barsigma^2)^2)/n).

`Conservative(S,V)` means there exists a function L : Real -> Real such
that for EVERY epsilon>0 the ordinary real limit
lim_t P((n/dAVG)(V_t-Var(HT_t))<=-epsilon)=L(epsilon) exists,
and L(epsilon) tends to zero as epsilon approaches zero through positive
reals (`nhdsWithin 0 (Set.Ioi 0)`). This includes existence of all positive
epsilon inner limits, not merely an assertion about a limsup.
`PositiveLiminf(a)` is defined without a numerical liminf: there exists
c>0 such that eventually c<=a(t).

## SAP.P009c.T45

Source: `Challenge/Part1.lean:69-77`; body:
`Defs/WholeW1.lean:84-100`.

Quantifier order: for every study S, real k, and moment indices q,s,
assume `RegularMix` as expanded above; dAVG/n -> 0;
alphaEXT(eEXT(q))/n -> 0; and alphaINT(eINT(s))/n -> 0.
Then, for every sequence H of real functions on assignments, if H agrees
with the displayed two-ratio contrast whenever both denominators are
nonzero, BOTH HT and H converge in probability to EATE and BOTH errors
are of stochastic order

    a(t)=sqrt(dAVG)/sqrt(n)
         +sqrt(alphaEXT(eEXT(q)))/sqrt(n)+alphaINT(eINT(s))/n.

The index bounds are uniform moment bounds, not maximality assumptions.
Neither index need be attained as a maximum of any set. There is no
Bernoulli, complete, paired, or supported-arms hypothesis. Quantifying over
every extension is a conclusion about any such real-valued H.

Junk/default audit: All division by n, sqrt(n), q (in the finite branch),
s (in the finite branch), and treatment marginals has nonzero denominators
under these hypotheses. The limits defining little-o divide only by n>0.
Real subtraction in the exponents is not truncated natural subtraction.
The `WithTop.untopD 0` default at infinity occurs only in an inactive branch;
infinity has its explicitly defined exponent 1 and support bound. All
real powers have nonnegative bases and finite real exponents. The explicit
mixing convention m(0,0)=0 differs from Mathlib's Real.rpow(0,0)=1 and
affects the boundary indices q=2 and s=1. It must be checked against the
intended mathematical convention later. No negative-base real power is used.
All sqrt arguments are nonnegative, and the rate is strictly positive
because dAVG>=1 and n>0. `Op`'s non-strict tail event would be problematic
at a zero rate, which cannot occur here. Empty weighted arms can occur;
no claim evaluates the printed contrast there without its guard, and H
may assign any real value there. `alpha` takes a nonempty bounded supremum:
empty events give value 0 and probabilities lie in [0,1]. There are finitely
many effective event pairs since the sample space is finite. Hence no
empty/unbounded `sSup` default is used. Fin n is nonempty in every study.
No integrals, logarithms, `toReal`, numeric limsup/liminf, or partial-function
defaults occur. Finite sums make every expectation finite; null assignments
remain relevant to structural interference, and zero-mass outcomes do not
contribute to moments. Function.update and masking are total operations.

## SAP.P009c.T46

Source: `Challenge/Part1.lean:79-87`; body:
`Defs/WholeW1.lean:102-116`.

Quantifier order: for every study S, real k, and moment indices q,s,
assume `RegularMix`; dAVG/n -> 0; and alphaEXT(eEXT(q))/n -> 0.
For every H as above, if it is an extension of the two-ratio contrast,
BOTH HT and H converge in probability to ADSE, and BOTH errors have order

    a(t)=sqrt(dAVG)/sqrt(n)+sqrt(alphaEXT(eEXT(q)))/sqrt(n).

Every finite or infinite admissible q,s is included. There is no maximality
condition and no assumption on alphaINT, nor any randomization-class or
supported-arms condition. The potential-moment condition is still a hypothesis,
although s does not appear in the rate.

Junk/default audit: As for T45, positive sizes, positive dAVG, interior
marginals, and the finite-index lower bounds guard every relevant division.
ADSE uses the two conditional means for events z_i=true/false; both events
have positive probability, so cmean never uses its totalized value 0 at a
null event. Infinity is handled by an explicit support bound/exponent and
the `untopD` default is inactive. The mixing convention m(0,0)=0 matters at
q=2; all mixing suprema are nonempty and bounded, sqrt bases are nonnegative,
and the rate is positive. The guarded extension imposes no ratio at empty
arms. No unguarded limit/supremum default, infinite integral, `toReal`, log,
negative-base power, truncated subtraction, partial function, or empty unit
type is involved. All remaining finite-sum and null-assignment conventions
are exactly as expanded for T45.

## SAP.P009c.T47

Source: `Challenge/Part1.lean:89-92`; body: `Defs/Part4.lean:12-21`.

For every study S and real k,q,s, assume `RegularSequence(S,k,q,s)`,
q>=4, and Bernoulli randomization at every t. No restricted-interference
condition is assumed. The following three conclusions are conjoined:

1. (n/dAVG)(VBER-Var(HT))-[MSQ/dAVG-B1-B2] -> 0 in probability.
2. If every population has no interference on the full cube, then
   n(VBER-Var(HT))-MSQ -> 0 in probability.
3. MSQ>=0 for every t.

The moving quantities B1,B2 are real numbers recomputed at every t:
let xi_ij(a)=E[y_i(z with i=a, then j=true)
-y_i(z with i=a, then j=false)],
xibreve_ij=(1-p_i,true)xi_ij(true)+p_i,true xi_ij(false), and
ybreve_i=(1-p_i,true)E[y_i|z_i=true]+p_i,true E[y_i|z_i=false].
Then

    B1=(sum_{i,j:j!=i} [xibreve_ij*xibreve_ji
        +2*ybreve_j*(xi_ij(true)-xi_ij(false))])/(n*dAVG),
    B2=(sum_{i,j:j!=i} sum_{a,b in Bool}
        (1-2*bit(a))*(1-2*bit(b))
        *Cov(y_i,y_j | z_i=a and z_j=b))/(n*dAVG).

Here bit(false)=0 and bit(true)=1. Each probability convergence has its
own quantification over every positive real error threshold. The no-
interference condition is an implication only for conclusion 2.

Junk/default audit: n>0 and dAVG>=1 guard all scaling denominators, including
B1 and B2. Interior marginals guard VBER and the single-coordinate conditional
means. For i!=j, Bernoulli factorization and interior marginals make all four
conditioning events in B2 strictly positive. When i=j the entire summand is
defined to be 0, so contradictory events z_i=a and z_i=b cannot affect B2.
The own-coordinate double updates in xi when i=j are total but discarded by
the off-diagonal sums. Finite real q>=4 and s>=1 avoid exceptional powers at
zero exponents in moment bounds; k>0. MSQ uses ordinary real squares, not
square roots or truncated operations. No mixing convention, infinity moment
index, supremum, numerical limsup/liminf, Bochner integral, `toReal`, log,
partial-function default, or empty index type affects this statement.

## SAP.P009c.T48

Source: `Challenge/Part1.lean:94-97`; body: `Defs/Part4.lean:23-28`.

For every study S and real k,q,s, assume `RegularSequence(S,k,q,s)`,
q>=4, Bernoulli randomization for every t, dAVG/n -> 0, and

    SDsigma/(dAVG/dRMS) -> 0.

Then VAVG=dAVG*VBER is conservative: there exists L : Real -> Real,
for every epsilon>0 the probability
P((n/dAVG)(VAVG-Var(HT))<=-epsilon) converges to L(epsilon), and
L(epsilon)->0 as epsilon decreases to 0. The SDsigma and all other
quantities are precisely the finite-sum expressions in the common notation.
The variance-heterogeneity condition is a quotient limit; no separate
positivity-of-variance assumption is present.

Junk/default audit: n>0, dAVG>=1 and dRMS>=1 guard the divisions by n,
dAVG, and dAVG/dRMS. Both sqrt arguments (degree squares, centered variance
squares) are nonnegative. SDsigma may be 0, which is an ordinary zero
numerator. Treatment probabilities and their squares are strictly positive.
All moment powers have nonnegative bases and positive finite exponents.
`Conservative` asks for genuine real limits and never applies a totalized
liminf or limsup. Its existential L is constrained at positive epsilon only;
values at epsilon<=0 are irrelevant to the within-positive limit. There is
no sSup, infinity conversion, integral default, truncated subtraction,
logarithm, partial-function default, or empty unit type in this closure.

## SAP.P009c.T49

Source: `Challenge/Part1.lean:99-102`; body: `Defs/Part4.lean:30-36`.

For every study S and real k,q,s, assume `RegularSequence(S,k,q,s)`,
q>=4, and Bernoulli randomization at every t. Then assume the disjunction

    dMAX/(sqrt(n)*sqrt(dAVG)) -> 0
    OR
    (dAVG/n -> 0 AND there exists c>0 with eventually MSQ>=c).

The conclusion is that VMAX=dMAX*VBER is conservative, with precisely the
existential L, all-positive-epsilon inner limits, and one-sided outer limit
expanded for T48. Restricted interference is explicitly a conjunct of the
second alternative only. The first alternative implies it via the degree
inequalities; it is not a separate antecedent in the Lean syntax.

Junk/default audit: The set whose sSup defines dMAX is a finite nonempty
set of real degrees, bounded between 1 and n, so no empty/unbounded supremum
default is used. n,dAVG,sqrt(n),sqrt(dAVG) are positive; all divisions and
square roots in scaling and in the alternatives are well defined in their
ordinary mathematical sense. MSQ is a finite real nonnegative number.
`PositiveLiminf` uses an eventual positive lower bound and therefore does
not use Mathlib's totalized numeric liminf for unbounded sequences. Marginal
denominators are positive; moments and variance are finite sums. There is
no infinity index/conversion, logarithm, unguarded conditional mean, Bochner
integral, truncated subtraction, or partial-function default involved.
