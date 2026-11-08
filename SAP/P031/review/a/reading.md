# Blind reading of the Challenge

This file was written and saved after reading all five Defs parts, the Defs import,
the Challenge part and its import, and the Mathlib definitions cited below, but
before opening either `claims.json` or `record.json`. It records the mathematical
statements, without comparing them with the intended claims.

## Common finite mathematics

Let I be an arbitrary finite type with decidable equality, N = |I|, and s a subset
of I. Complements are relative to I. Put M = |s|, K = |sᶜ| = N-M. An
**admissible** assignment means M > 1 and K > 1, hence N ≥ 4. All outcomes are
arbitrary real functions on I. All sums here are ordinary finite sums.

For a subset t and vector v, write

* μ_t(v) = (Σ_{i∈t} v_i)/|t| and μ(v) = μ_I(v).
* V(v) = (Σ_i (v_i-μ(v))²)/N.
* C(v,w) = (Σ_i (v_i-μ(v))(w_i-μ(w)))/N.
* S²_t(v) = (Σ_{i∈t} (v_i-μ_t(v))²)/(|t|-1).

Thus V and C use divisor N; S²_t uses divisor |t|-1. Cardinalities are cast to
the reals before real subtraction or division in these definitions.

For potential outcomes y1,y0, the indicator X_i = 1 if i∈s and 0 otherwise gives
Y_i = X_i y1_i + (1-X_i)y0_i. The population effect is τ = μ(y1)-μ(y0).
For any observed vector Y, put b = μ_s(Y)-μ_sᶜ(Y), a0 = μ_sᶜ(Y), and
e_i = Y_i-a0-X_i b. The two-column design has row x_i = (1,X_i). Define

G = [[1/K,-1/K],[-1/K,1/M+1/K]],
h_i = Σ_{j,k∈{0,1}} x_{ij}G_{jk}x_{ik},
w_i = Σ_{j∈{0,1}} G_{1j}x_{ij}.

These are the explicit `gramInverse`, `leverage`, and `coefficientWeight`
definitions; they do not call an abstract regression fitting procedure. On
admissible s, G really is the inverse Gram matrix, h_i is 1/M on s and 1/K off
s, and w_i is 1/M on s and -1/K off s. The estimators are

* Neyman = S²_s(Y)/M + S²_sᶜ(Y)/K.
* HR = Σ_i w_i²e_i².
* HC2 = Σ_i w_i²e_i²/(1-h_i).
* HC1 = N/(N-2) HR.
* HC3 = Σ_i w_i²e_i²/(1-h_i)².
* OLS = (Σ_i e_i²)/(N-2) · G_{11}.

The imputed potential outcomes are z0_i = Y_i-X_i b and
z1_i = Y_i+(1-X_i)b. For any two vectors v,w and real M,K the defined
variance expression is

    F(M,K;v,w) = N/(N-1)·(V(v)/M+V(w)/K)
                 +(2C(v,w)-V(v)-V(w))/(N-1).

CE = F(M,K;z1,z0). This is a plug-in variance formula for the imputed vectors;
it is not by definition an expectation over assignments.

For an integer m, A_m is the set of all m-element subsets of I. The defined
expectation is E_m[f] = (Σ_{s∈A_m} f(s))/|A_m|. Given y1,y0, let
b_s = μ_s(y1)-μ_sᶜ(y0). The randomization variance is
Vtrue_m = E_m[(b_s-E_m[b])²], centered at its actual finite expectation.

Mathlib's `Finset.powersetCard` is precisely the collection of subsets with the
specified size (`Mathlib/Data/Finset/Powerset.lean`, `mem_powersetCard`), whose
cardinality is the binomial coefficient. Outside the admissible domain, real
division is total and division by zero is zero. The universal finite theorems
use admissibility or explicit arm-size bounds, so those cases do not occur
in their hypotheses.

## Common population and limit definitions

A `Population` is a tuple (N,M,y1,y0) with N,M natural numbers, both outcome
vectors on {0,…,N-1}, and proofs 1<M and M<N-1, where N-1 is natural subtraction.
These inequalities imply N≥4 and 2≤M≤N-2. Every random assignment used in a
population probability is sampled uniformly from A_M, a nonempty finite set.
`pointEstimate`, `populationEffect` and `trueVariance` are b_s, τ and Vtrue_M
above. An estimator is a function of a population and an arbitrary assignment;
the seven population estimator definitions evaluate the seven formulas above
on its observed outcome vector.

For each population, Pr(E) = E_M[1_E]. For a sequence P_r, write N_r,M_r,τ_r,
V_r and Pr_r for these objects. Its additional predicates mean:

* Growing: for every integer L, eventually N_r≥L, as r→∞.
* Standardized normal limit: eventually V_r>0, and, for every real x,
  Pr_r((b_s-τ_r)/sqrt(V_r) ≤ x) → Φ(x).
* f_r converges in probability to c: for every real ε>0,
  Pr_r(ε<|f(P_r,s)-c|) → 0.
* A is first-order equivalent to B: for every real ε>0,
  Pr_r(ε|B(P_r,s)|<|A(P_r,s)-B(P_r,s)|) → 0.
  In particular B=0 and A≠0 counts as failure at every ε, and A=B=0 does not.
* Coverage(V,z) = Pr_r(|b_s-τ_r|≤z sqrt(V(P_r,s))). Equality is included even
  for a zero-width interval.
* Conservative coverage(V,z): for each ε>0, eventually
  2Φ(z)-1-ε ≤ Coverage(V,z).
* UnbalancedVarianceLimit(P,a,v): P is growing; N_r≠2M_r at every r; v>0;
  N_r V_r→v; N_r OLS converges in probability to a; and N_r CE converges in
  probability to that same a. No positive lower bound on allocation fractions
  or explicit a>0 is part of this predicate.

Here Φ(x) is Mathlib's CDF of `gaussianReal 0 1`: the actual probability of
(-∞,x] under the Gaussian with mean 0 and variance 1. See
`Mathlib/Probability/CDF.lean` (`cdf_eq_real`) and
`Mathlib/Probability/Distributions/Gaussian/Real.lean` (`gaussianReal`, its
probability measure instance). Its variance parameter is a nonnegative real,
and the chosen value is 1. `Real.sqrt` is the nonnegative square root for
nonnegative inputs and zero for negative inputs
(`Mathlib/Analysis/Real/Sqrt.lean`). `Tendsto` to `nhds` is ordinary real
convergence; `atTop` on natural numbers means eventual tails
(`Mathlib/Order/Filter/Defs.lean`, `Mathlib/Order/Filter/AtTopBot/Defs.lean`).
Thus no unbounded limsup or improper integral is used in the SAP definitions.

## T1 — SAP.P031.T1

For every finite type I with decidable equality, every subset s, every real
observed vector Y, and every proof that M>1 and K>1, HC2(s,Y)=Neyman(s,Y).
There is no potential-outcome, probabilistic, balance or nonconstant-outcome
hypothesis.

## T2 — SAP.P031.T2

For every finite type I with decidable equality, every natural M, subject in
this order to 2≤M, 2≤N-M, and M≤N, and every pair y1,y0 of real potential-outcome
vectors, Vtrue_M ≤ E_M[HC2(s,observed(s,y1,y0))]. Here N-M is natural
subtraction; the additional M≤N bound makes it ordinary nonnegative subtraction.
Expectation and variance are over every M-element subset uniformly.

## T3 — SAP.P031.T3

For every finite I with decidable equality, subset s, real vector Y and
admissibility proof, ((N-2)/(N-1)) OLS(s,Y) = CE(s,Y).

## T4 — SAP.P031.T4

For every finite I with decidable equality, s,Y and admissibility proof,
followed by a balance proof N=2M, all three equalities hold:
((N-1)/(N-2)) CE=OLS, OLS=Neyman, and Neyman=HC2.

## T5 — SAP.P031.T5

This is a conjunction of two assertions, with no external hypotheses:

1. There exists a sequence P_r of populations which is growing, has a
   standardized normal limit, and for which HR is not first-order equivalent
   to HC2 in the relative-event sense above.
2. It is not the case that every population sequence P, if growing and having
   a standardized normal limit, satisfies all of: HR~HC2, HC1~HC2, HC3~HC2,
   and, for every real z>0, conservative coverage for each of Neyman, HC2,
   HR, HC1 and HC3.

The first conjunct already implies the second by logic. Neither conjunct
asserts failure of any individual coverage clause. There is no assumption
that M_r or N_r-M_r tends to infinity or that treatment fractions have an
interior limit. The Challenge docstring describes this as falsifying a
printed normality-only assertion; that description is not a hypothesis.

## T6 — SAP.P031.T6

With no external hypotheses, both existence assertions hold:

1. There exist a population sequence P and real a,v with
   UnbalancedVarianceLimit(P,a,v), a<v, and a standardized normal limit,
   such that for every real z>0 there exists a real q (allowed to depend on z)
   with q<2Φ(z)-1, Coverage(OLS,z)→q, and Coverage(CE,z)→q.
2. There exist a possibly different population sequence P and real a,v with
   UnbalancedVarianceLimit(P,a,v) and v<a.

The second witness need not satisfy any central limit or coverage assertion.
Both witnesses have a positive limit v of N times the actual variance, and
use convergence in probability, rather than expectation alone, for the
scaled variance estimates. No coverage statement about Neyman or HC2 is made.

## T7 — SAP.P031.T7

This is one unconditional conjunction concerning I={0,1,2,3},
s={0,1}, Y=y1=y0=(0,2,5,9). It asserts every following fact:

* s is admissible, |s|=2, there are 6 size-two assignments and s is among them.
* Its observed outcome vector is Y; its treated mean is 1, intercept is 7,
  and estimated effect b is -6.
* z0=(6,8,5,9), z1=(0,2,-1,3), and, for every unit i, z0_i=z1_i-b.
* V(z0)=5/2, V(z1)=5/2, C(Y,Y)=23/2, and V(z1)≠C(Y,Y).

Thus its last comparison concerns the original potential outcomes, not the
covariance of the two imputed vectors. No variables or hypotheses are left
universally quantified outside this explicit example.

## T8 — SAP.P031.T8

For every finite I with decidable equality, s,Y and admissibility proof, let
S=Σ_i e_i². Every equality in the following list holds (the list is a
conjunction, not an implication chain):

1. For every i, z0_i=z1_i-b.
2. V(z0)=V(z1).
3. V(z1)=C(z0,z1).
4. CE=N/(N-1)·N/(MK)·V(z0).
5. S/N=(Σ_i (Y_i-a0-X_i b)²)/N.
6. (Σ_i (Y_i-a0-X_i b)²)/N=(Σ_i (z0_i-a0)²)/N.
7. (Σ_i (z0_i-a0)²)/N=V(z0).
8. (N-2)/(N-1)·OLS=(N-2)/(N-1)·(S/(N-2))·N/(MK).
9. The right side of (8) is N/(N-1)·(S/N)·N/(MK).
10. The right side of (9) is N/(N-1)·N/(MK)·V(z0).
11. The right side of (10) is CE.

## T9 — SAP.P031.T9

For every finite I with decidable equality, s,Y, admissibility proof and then
balance proof N=2M, let S=Σ_i e_i². Every link of this equality chain holds:

    (N-1)/(N-2)·CE = OLS
      = S/[2(M-1)] · (2M/M²)
      = [Σ_{i∈s} e_i²/(M-1)]/M + [Σ_{i∈sᶜ} e_i²/(M-1)]/M
      = S²_s(Y)/M + S²_sᶜ(Y)/M
      = Neyman = HC2.

## T10 — SAP.P031.T10

For a real parameter a and index n≥0, set k=n+2, N=4k, M=k, and define signs
u_i=-1 for i<2k and +1 otherwise. The family P^a_n has y0_i=u_i and
y1_i=a u_i+2. The following package W(a,q) means all of:

* N→∞ and N≠2M at every index.
* At every index, M/N=1/4, μ(y0)=0, μ(y1)=2, τ=2,
  V(y0)=1, V(y1)=a² and C(y1,y0)=a.
* N Vtrue→3a²+2a+1/3.
* N E_M[OLS]→4a²/3+4.
* N OLS converges in probability to 4a²/3+4.
* OLS/Vtrue converges in probability to q.

T10 has no external hypotheses. It asserts W(1,1), W(2,4/7),
W(1/2,52/25), and 4/7≠52/25. It also asserts: for every population P and
every real c,d, if Q has the same N,M, y0'=y0+c and y1'=y1+c+d, then
μ(y0')=μ(y0)+c, τ'=τ+d, Vtrue'=Vtrue, and for every size-M assignment s,
OLS(Q,s)=OLS(P,s). The shifts need not be bounded. No finite-row formula,
28-assignment calculation or CE limit is included in W or the conclusion.

## T11 — SAP.P031.T11

For every population sequence P, if N_n→∞, then for every real p,v1,v0,c,
in that quantifier order, assume 0<p, p<1, M_n/N_n→p, V(y1_n)→v1,
V(y0_n)→v0, and C(y1_n,y0_n)→c. Put

    t = (1-p)/p·v1 + p/(1-p)·v0 + 2c,
    a = v1/(1-p) + v0/p,
    D = (2p-1)(v1-v0)/(p(1-p)) + v1+v0-2c.

All of the following hold:

1. N_n Vtrue_n→t.
2. N_n E_{M_n}[OLS_n]→a.
3. N_n(E_{M_n}[OLS_n]-Vtrue_n)→D.
4. V(y1_n-y0_n)→v1+v0-2c.
5. If there exists one real B bounding both |y1_{n,i}| and |y0_{n,i}| for
   every n and every unit i, then both centered sample-variance errors
   S²_s(y1_n)-V(y1_n) and S²_sᶜ(y0_n)-V(y0_n) converge in probability to zero.
6. If those two sample-variance errors converge in probability to zero, OR
   the uniform bound in (5) exists, then N_n OLS_n converges in probability
   to a; furthermore, if t>0, OLS_n/Vtrue_n converges in probability to a/t.
7. For every real c',d and then every index n, shifting that row's y0 by c'
   and y1 by c'+d changes μ(y0) by c', changes τ by d, preserves Vtrue, and
   preserves OLS on every size-M_n assignment.

There are no additional first-moment-limit, fourth-moment, Gaussian-limit,
positive-t (except for the ratio clause), or balance hypotheses. The two
sample-variance convergence hypotheses in (6) are exactly the defined
`ArmSecondMomentsConverge`; they are not convergence of the estimated
variance itself. The boundedness implication in (5) is part of the conclusion.
