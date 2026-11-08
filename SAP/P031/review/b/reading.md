# Blind reading of the Challenge statements

This file was written after reading only `SAP/P031/Defs*.lean`,
`SAP/P031/Defs/*.lean`, `SAP/P031/Challenge*.lean`,
`SAP/P031/Challenge/*.lean`, and relevant Mathlib definitions. Neither
`claims.json` nor `record.json` has been opened at this stage. The theorem
docstrings are part of the supplied Challenge, but the readings below are
of the actual propositions, not of their descriptions.

## Common finite mathematics

Let I be a finite type with decidable equality, N its cardinality, s a
subset of I, M = |s|, K = |I \ s|, and T_i = 1 if i belongs to s and 0
otherwise. Complements are relative to all of I. An admissible s has M > 1
and K > 1. Thus N >= 4, M,K >= 2, and N = M+K.

For any real vector v and subset A, write

* mean_A(v) = (sum over i in A of v_i)/|A|;
* V(v) = (sum over I of (v_i - mean_I(v))^2)/N;
* C(v,w) = (sum over I of (v_i-mean_I(v))(w_i-mean_I(w)))/N;
* S_A^2(v) = (sum over A of (v_i-mean_A(v))^2)/(|A|-1).

The last subtraction is in the real numbers. These are divisor-N
population moments and divisor-(|A|-1) sample variances. All underlying
Lean divisions are total (division by zero gives zero), but admissibility
excludes zero denominators in these statistics and the estimators below.

For real potential-outcome vectors y1,y0, the observed vector is
Y_i(s) = T_i y1_i + (1-T_i)y0_i and the population effect is
tau = mean_I(y1)-mean_I(y0). For an arbitrary observed vector Y, put
b0 = mean_(I\s)(Y), b1 = mean_s(Y)-mean_(I\s)(Y), and
e_i = Y_i-b0-T_i b1. The design matrix has row (1,T_i). The defined
matrix G has rows (1/K,-1/K) and (-1/K,1/M+1/K).
The leverage is h_i = sum over a,b in {0,1} of X_ia G_ab X_ib;
the coefficient weight is w_i = sum over a in {0,1} of G_1a X_ia.
For admissible assignments these are h_i=1/M, w_i=1/M in s and
h_i=1/K, w_i=-1/K outside s.

The real variance estimators are exactly

* Neyman = S_s^2(Y)/M + S_(I\s)^2(Y)/K;
* HR = sum over I of w_i^2 e_i^2;
* HC2 = sum over I of w_i^2 e_i^2/(1-h_i);
* HC1 = N/(N-2) HR;
* HC3 = sum over I of w_i^2 e_i^2/(1-h_i)^2;
* OLS = (sum over I of e_i^2)/(N-2) times G_11.

Define imputed vectors y0*_i = Y_i-T_i b1 and
y1*_i = Y_i+(1-T_i)b1. For real numbers m,k define

    F(m,k;v,w) = N/(N-1) [V(v)/m + V(w)/k]
                 + [2 C(v,w)-V(v)-V(w)]/(N-1).

CE, the constant-effects imputation variance, is F(M,K;y1*,y0*).

For an integer m, Omega_m is the set of all m-element subsets of I;
E_m(f) = (sum over s in Omega_m of f(s))/|Omega_m|.
Randomization variance is

    Var_m(y1,y0) = E_m((b1(s,Y(s)) - E_m(b1(t,Y(t))))^2).

It is centered at the randomization expectation, not definitionally at tau.
In all uses here m <= N and both arms have at least two units, so
Omega_m is a nonempty finite set and this expectation is an ordinary
uniform average, not an empty-sum convention.

## Common sequence and probability mathematics

A `Population` consists of natural numbers N,M, real vectors y1,y0 on
{0,...,N-1}, and proofs 1<M and M<N-1. Here N-1 is natural subtraction;
the inequalities imply N>=4 and N-M>=2. There are no bounds or
distributional restrictions on the outcomes. Estimators are functions of
a population and an assignment subset, evaluated probabilistically only
over its legal M-element assignments. Write hat_tau_P(s) for its b1,
tau_P for its population effect, V_P for its true randomization variance,
and Pr_P for the uniform probability on legal assignments.

The estimator names followed by `Estimator` mean the corresponding
finite estimator applied to the observed potential outcomes of P.
`eventProbability` is E_M of a 0/1 indicator of the event; every event is
decidable classically and the sample space is finite.

Phi(x) is the actual CDF of Mathlib's `gaussianReal 0 1`, whose
parameters are mean and variance. Mathlib defines its nonzero-variance
Gaussian by the usual Gaussian density with respect to Lebesgue measure;
it is a probability measure and its CDF is its probability of (-infinity,x].
This is the standard normal CDF, not a placeholder function.

For a sequence P_r, all limits below are as the natural index r tends to
infinity. `Tendsto ... atTop (nhds L)` means the usual real limit L,
and `eventually` means for every sufficiently large natural index.

* Growing(P) means N_r tends to infinity.
* Normal(P) means V_(P_r)>0 eventually, and, for every real x,
  Pr_(P_r)((hat_tau-tau)/sqrt(V_(P_r)) <= x) tends to Phi(x).
* f(P_r,s) converges in probability to a real c means: for every real
  epsilon>0, Pr_(P_r)(epsilon < |f(P_r,s)-c|) tends to zero.
* Equivalent(P,A,B) means: for every real epsilon>0,
  Pr_(P_r)(epsilon |B(P_r,s)| < |A(P_r,s)-B(P_r,s)|) tends to zero.
  In particular if B=0 the bad event is exactly A != 0; equal zero
  estimates are accepted, unequal ones are counted. This definition
  makes no pointwise division by B.
* Cov(P,V,z) = Pr_P(|hat_tau-tau| <= z sqrt(V(P,s))). This includes
  zero-width intervals. Mathlib's real square root is zero on negative
  inputs as well; the named estimators on legal assignments are
  nonnegative.
* Conservative(P,V,z) means: for each real epsilon>0, eventually
  2 Phi(z)-1-epsilon <= Cov(P_r,V,z). It is a lower asymptotic coverage
  bound, not an asserted limit.
* Unbalanced(P,a,v) means, in conjunction: Growing(P); for every r,
  N_r != 2 M_r; v>0; N_r V_(P_r) tends to v; N_r OLS(P_r,s)
  converges in probability to a; and N_r CE(P_r,s) converges in
  probability to the same a. Positivity of a is not an explicit
  hypothesis.

For k a natural number the sign vector on {0,...,4k-1} is -1 in the
first 2k positions and +1 elsewhere. The fixed family P^a_n, for every
real a and natural n, has k=n+2, N=4k, M=k, y0=sign and
y1=a sign+2. Its design inequalities are built into the definition.
Shift(P,c,d) leaves N,M unchanged, adds c to every y0 and c+d to
every y1.

Witness(a,q) is the following whole conjunction about that fixed family:

1. P^a grows; N_n != 2M_n for every n.
2. For every n, M_n/N_n=1/4, mean(y0)=0, mean(y1)=2,
   tau=2, V(y0)=1, V(y1)=a^2, and C(y1,y0)=a.
3. N_n V_(P^a_n) tends to 3a^2+2a+1/3.
4. N_n E_(M_n)(OLS(P^a_n,s)) tends to 4a^2/3+4.
5. N_n OLS(P^a_n,s) converges in probability to 4a^2/3+4.
6. OLS(P^a_n,s)/V_(P^a_n) converges in probability to q.

There is no CE limit in Witness. UniformlyBounded(P) means there exists
one real B such that for every n and every unit i of P_n, both
|y1_(n,i)|<=B and |y0_(n,i)|<=B.
ArmMoments(P) means both S_s^2(y1)-V(y1) and
S_(I\s)^2(y0)-V(y0) converge in probability to zero. These are the
centered, traditional arm sample variances, rather than raw second
moments.

## Individual theorem readings

### SAP.P031.T1

For every finite type I (in Lean universe `Type`, with Fintype and
decidable equality), every assignment s, every real vector Y on I, and
every proof that s is admissible, HC2(s,Y)=Neyman(s,Y).
There are no potential-outcome, randomization, or moment assumptions.

### SAP.P031.T2

For every finite I with those instances, every natural M, every proof
2<=M, every proof 2<=N-M (natural subtraction), every proof M<=N,
and then every pair of potential-outcome vectors y1,y0,

    Var_M(y1,y0) <= E_M(HC2(s,Y(s))).

Thus it is a uniform-design expectation inequality for arbitrary fixed
potential outcomes. The M<=N hypothesis prevents the truncated
subtraction from admitting an invalid allocation.

### SAP.P031.T3

For every finite I, every s, every Y, and every admissibility proof,

    (N-2)/(N-1) OLS(s,Y) = CE(s,Y).

### SAP.P031.T4

For every finite I, every s, every Y, every admissibility proof, and
then every proof N=2|s|, the following three equalities hold together:

    (N-1)/(N-2) CE(s,Y) = OLS(s,Y),
    OLS(s,Y) = Neyman(s,Y),
    Neyman(s,Y) = HC2(s,Y).

### SAP.P031.T5

This is a conjunction of two propositions, with no external hypotheses.
First, there exists a sequence P of Populations such that Growing(P),
Normal(P), and NOT Equivalent(P,HR,HC2). Second, it is NOT the case
that for every sequence P, Growing(P) implies Normal(P) implies the
following whole conjunction:

* Equivalent(P,HR,HC2);
* Equivalent(P,HC1,HC2);
* Equivalent(P,HC3,HC2);
* for every real z>0, Conservative(P,V,z) for each V in
  {Neyman,HC2,HR,HC1,HC3}.

The exhibited existential failure concerns HR equivalence; no separate
failure of any coverage assertion is asserted. There is no assumption
that allocation fractions stay bounded away from zero and one or that
both arm sizes tend to infinity.

### SAP.P031.T6

This is another conjunction of two separate existential statements.
There exist, in order, a sequence P and real a,v such that
Unbalanced(P,a,v), a<v, Normal(P), and: for every real z, if z>0,
there exists a real q with

    q < 2 Phi(z)-1,
    Cov(P_r,OLS,z) -> q,
    Cov(P_r,CE,z) -> q.

Thus the same underestimating sequence works for every positive z;
the limiting coverage q may depend on z, and is common to OLS and CE.
Separately there exist a sequence P and reals a,v such that
Unbalanced(P,a,v) and v<a. This second sequence has no stated
normal limit or coverage conclusion. No claims about Neyman or HC2
coverage occur in the proposition.

### SAP.P031.T7

This is a closed finite example on I={0,1,2,3}, with s={0,1} and
Y=(0,2,5,9). All the following are asserted together, in this order:

1. s is admissible, |s|=2, there are six 2-element assignments, and
   s is one of them.
2. Observing identical potential-outcome vectors Y,Y gives Y.
3. mean_s(Y)=1, b0=7, and b1=-6.
4. y0*=(6,8,5,9), y1*=(0,2,-1,3), and for every unit i,
   y0*_i=y1*_i-b1.
5. V(y0*)=5/2, V(y1*)=5/2, C(Y,Y)=23/2, and
   V(y1*) != C(Y,Y).

The original potential outcomes are both Y, so the last covariance is
of original outcomes, while the variances are of imputed outcomes.

### SAP.P031.T8

For every finite I, every s, every Y, and every admissibility proof,
let N,M,K be the real-valued counts above and S=sum e_i^2. The
proposition is the conjunction of every link listed below:

1. For every i, y0*_i=y1*_i-b1.
2. V(y0*)=V(y1*).
3. V(y1*)=C(y0*,y1*).
4. CE=N/(N-1) [N/(MK)] V(y0*).
5. S/N=(sum (Y_i-b0-T_i b1)^2)/N.
6. (sum (Y_i-b0-T_i b1)^2)/N=(sum (y0*_i-b0)^2)/N.
7. (sum (y0*_i-b0)^2)/N=V(y0*).
8. [(N-2)/(N-1)] OLS=[(N-2)/(N-1)] [S/(N-2)] [N/(MK)].
9. [(N-2)/(N-1)] [S/(N-2)] [N/(MK)]
   = [N/(N-1)] [S/N] [N/(MK)].
10. [N/(N-1)] [S/N] [N/(MK)]
    = [N/(N-1)] [N/(MK)] V(y0*).
11. [N/(N-1)] [N/(MK)] V(y0*)=CE.

All sums in these links run over I. This is a corrected imputed-moment
chain, not an assertion about the covariance of original y1,y0.

### SAP.P031.T9

For every finite I, every s, every Y, every admissibility proof and
then every proof N=2|s|, let N,M be real counts and S=sum e_i^2.
All of the following links hold together:

1. [(N-1)/(N-2)] CE=OLS.
2. OLS=[S/(2(M-1))] [2M/M^2].
3. [S/(2(M-1))] [2M/M^2]
   = [(sum over s of e_i^2)/(M-1)]/M
     + [(sum over I\s of e_i^2)/(M-1)]/M.
4. That last sum equals S_s^2(Y)/M+S_(I\s)^2(Y)/M.
5. S_s^2(Y)/M+S_(I\s)^2(Y)/M=Neyman.
6. Neyman=HC2.

### SAP.P031.T10

With no external hypotheses, Witness(1,1), Witness(2,4/7), and
Witness(1/2,52/25) all hold, and 4/7 != 52/25. In addition, for
every Population P, every real c, and then every real d, the following
are asserted together for Q=Shift(P,c,d):

* mean_I(Q.y0)=mean_I(P.y0)+c;
* tau_Q=tau_P+d;
* V_Q=V_P;
* for every subset s of {0,...,P.N-1}, if |s|=P.M,
  OLS(Q,s)=OLS(P,s).

All Witness clauses were expanded above. No finite N=8 enumeration,
finite-row OLS formula, explicit observed/residual shift identity, or CE
limit is part of this proposition.

### SAP.P031.T11

For every sequence P, if Growing(P), then for every ordered tuple of
reals p,v1,v0,c, if 0<p, p<1, M_n/N_n -> p, V(y1_n) -> v1,
V(y0_n) -> v0, and C(y1_n,y0_n) -> c, all of the following hold.
There are no first-moment limits assumed. Put

    A = v1/(1-p) + v0/p,
    D = (1-p)/p v1 + p/(1-p) v0 + 2c.

1. N_n V_(P_n) -> D.
2. N_n E_(M_n)(OLS(P_n,s)) -> A.
3. N_n [E_(M_n)(OLS(P_n,s))-V_(P_n)]
   -> (2p-1)(v1-v0)/(p(1-p)) + v1+v0-2c.
4. V(y1_n-y0_n) -> v1+v0-2c.
5. If UniformlyBounded(P), then ArmMoments(P).
6. If ArmMoments(P) OR UniformlyBounded(P), then N_n OLS(P_n,s)
   converges in probability to A, and, if in addition D>0,
   OLS(P_n,s)/V_(P_n) converges in probability to A/D.
7. For every real c', every real d, and every natural n, putting
   Q=Shift(P_n,c',d), mean(Q.y0)=mean(P_n.y0)+c',
   tau_Q=tau_(P_n)+d, V_Q=V_(P_n), and for every legal
   assignment s of P_n, OLS(Q,s)=OLS(P_n,s).

The positive-D assumption belongs only to the ratio clause. The
arm-moment/ boundedness assumption belongs only to the probability
clauses, except for the separate boundedness sufficiency assertion.

## Mathlib interpretation checks

The relevant implementations checked were `Finset.mem_compl` in
`Data/Finset/BooleanAlgebra.lean`, `Finset.powersetCard` and its
membership/cardinality lemmas in `Data/Finset/Powerset.lean`,
`Filter.Tendsto` in `Order/Filter/Defs.lean`, `Filter.atTop` in
`Order/Filter/AtTopBot/Defs.lean`, `nhds` in `Topology/Defs/Filter.lean`,
and `ProbabilityTheory.cdf`/`cdf_eq_real` and `gaussianReal` in
`Probability/CDF.lean` and `Probability/Distributions/Gaussian/Real.lean`.
`Real.sqrt_eq_zero_of_nonpos` is used in
`Analysis/SpecialFunctions/Sqrt.lean`. Finite sums require no
integrability assumptions; these statements contain neither an
unbounded limsup nor an empty probability index type under their
stated design conditions.
