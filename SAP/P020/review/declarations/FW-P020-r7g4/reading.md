# Blind statement reading

Written before opening `claims.json` or `record.json`. The Challenge docstrings,
all source declarations in both closure lists, and the generated auxiliary
declarations printed by `scratch/Inspect.lean` have been read. This file records
the statements, without using the canonical claims or architect's decisions.

## SAP.P020.T16

The theorem at `SAP/P020/Challenge/Part1.lean:99` asserts the proposition defined
at `SAP/P020/Defs/Part4.lean:204`. Its docstring calls the statistic a sharp-null
variance estimator and says it is conservative in expectation under constant
cluster-total effects or balanced cluster counts.

### Objects, definitions, quantifiers, and conclusion

A population P consists of natural numbers M,t with 0 < t < M, positive natural
numbers n_j for j in Fin M (the integers 0,...,M-1), and arbitrary real vectors
y0_j,y1_j indexed by Fin M. The structure includes proofs of both arm-count
inequalities and of every size's positivity. Thus M >= 2. Define

* N = sum_j n_j, a positive natural number;
* c = M-t, using natural subtraction (here equal to ordinary subtraction);
* A = {s subset of Fin M : card(s)=t}, a nonempty finite set;
* s^c = (Fin M) \ s and K = card(A) > 0.

The finite law is the record with support A and constant real weight 1/K. More
generally `FiniteLaw Ω` is a finite support together with real weights
nonnegative on that support and summing to 1. Its expectation of f:Ω→R is the
finite real sum sum_{ω in support} weight(ω) f(ω); its variance is the expectation
of (f-E f)^2. In this theorem write E f = K^(-1) sum_{s in A} f(s).

`armSum P true v s` is sum_{j in s} v_j; the false version sums over s^c.
The Horvitz--Thompson statistic is

    H(s) = [ (M/t) sum_{j in s} y1_j
             - (M/c) sum_{j in s^c} y0_j ] / N.

Observed cluster totals are u_s(j)=y1_j when j∈s and y0_j otherwise. For any
real vector v indexed by Fin M, its cluster mean is (sum_j v_j)/M, and its
cluster variance is (sum_j (v_j-(sum_i v_i)/M)^2)/M: the divisor is M, not M-1.
The sharp-null statistic in the conclusion is

    V(s) = M^4 [ (1/M) sum_j (u_s(j)-(1/M)sum_i u_s(i))^2 ]
           / [ N^2 (M-1) c t ].

All counts in these formulas are cast to real numbers. The subtraction M-1 in
this denominator takes place in R.

In order, the theorem universally quantifies P, then a proof of

    (there exists τ∈R such that for every j, y1_j-y0_j=τ) OR c=t.

It concludes

    (1/K) sum_{s in A} (H(s)-(1/K)sum_{a in A}H(a))^2
      <= (1/K) sum_{s in A} V(s).

The constant-effect condition concerns cluster totals, not per-person effects.
The sharp null y1=y0 is not imposed. There is no Des Raj clause, probability
tail bound, pointwise conservativeness, or consistency assertion in this
statement. There are no other hypotheses.

### Junk-value and boundary audit

Real division is total, with division by zero equal to zero, but every actual
denominator in this statement is nonzero: M>=2, t>0, c>0, N>0, and K>0. The
generic cluster mean and variance would be zero at M=0 by empty sums and 0/0;
that specialization is excluded here. Natural c=M-t cannot truncate because
t<M. The support is genuinely nonempty, as certified by
`assignments_nonempty`; `uniformLaw` cannot use an empty support. The generated
`uniformLaw._proof_1` and `_proof_2` prove weight nonnegativity and normalization
from this nonemptiness, respectively. None is an extra hypothesis.

No infinite sums, Bochner integrals, nonintegrable means, extended-real
`toReal`, logarithms, square roots, real powers, infima, suprema, liminf,
limsup, partial-function defaults, or integer casts occur. Powers are natural
powers of real numbers. All sums are finite and all real inputs are finite.

## SAP.P020.T17

The theorem at `SAP/P020/Challenge/Part1.lean:110` asserts `T17WholeStatement`
(`SAP/P020/Defs/WholeW1.lean:272`), which includes `T17Statement`
(`SAP/P020/Defs/Part4.lean:211`) as its first conjunct. Its docstring describes
independent exact copies, a common probability-space realization, strictly
growing total and arm sizes, and within-cluster replication preserving the
sampling distribution and a nonzero bias.

### Base population and all statistical definitions

Independently for this declaration, P has M,t∈N, 0<t<M, n_j∈N with n_j>0 for
each j∈Fin M, and arbitrary real potential cluster totals y0_j,y1_j. Put
N=sum_j n_j>0, c=M-t>0, nbar=N/M, and

    δ = [sum_j y1_j-sum_j y0_j]/N.

Let A be the finite nonempty set of t-element subsets of Fin M and K=card(A).
A supported assignment is a member s of A together with its membership proof;
the proof carries no additional condition. Set A_1(s)=s and A_0(s)=s^c. For
a∈{0,1}, define

    F_a(v,s) = sum_{j in A_a(s)} v_j,
    B_a(s) = sum_{j in A_a(s)} n_j,
    m_1=t, m_0=c, p_a=m_a/M,
    D(s) = F_1(y1,s)/B_1(s) - F_0(y0,s)/B_0(s),
    H(s) = [(M/t)F_1(y1,s)-(M/c)F_0(y0,s)]/N,
    R_k(s) = [(M/t)F_1(y1-k(n-nbar),s)
              -(M/c)F_0(y0-k(n-nbar),s)]/N.

Here n is viewed as a real vector, k∈R, and n-nbar is componentwise. These are
the unfolded difference in means, HT, differenced potential totals,
`rajPotential`, `rajTotal`, and fixed-coefficient Des Raj statistic. Both B_a(s)
are positive for every supported s. A single assignment is uniform on A.
For a finite law L with nonnegative normalized real weights, E_L T is its
weighted finite sum and bias_L(T,d)=E_L T-d. In particular put b=E D-δ under
uniform s∈A.

For any such law L, statistic T, target d and ε∈R,

    errorProbability(L,T,d,ε)
       = sum_{ω in support(L)} if ε<|T(ω)-d| then weight(ω) else 0.

For a sequence of possibly changing finite spaces and laws L_r, statistics
T_r, and real targets d_r, `DesignConsistent` means exactly

    for every real ε>0,
      lim_{r→∞} errorProbability(L_r,T_r,d_r,ε) = 0.

The limit is Mathlib `Filter.Tendsto` from the natural-number `atTop` filter to
the usual real neighborhood filter at zero. This generic definition itself
does not require increasing sizes; growth is asserted separately below.

### Copy and within-cluster constructions

For h∈N a finite copy assignment is s:Fin h→A. The finite law is uniform on
all such functions, with probability K^(-h); this is the product of h uniform
one-copy laws, so the copies are independent. Define

    C_a(v,h,s) = (sum_{r in Fin h} F_a(v,s_r))/h,
    Q(h,s) = (sum_r F_1(y1,s_r))/(sum_r B_1(s_r))
             -(sum_r F_0(y0,s_r))/(sum_r B_0(s_r)).

These unfold `copyAverage` and `copiedDifferenceInMeans`.

For h>0, the within-cluster replication P[h] keeps M,t and changes
n_j to h*n_j and ya_j to h*ya_j for a=0,1. Its positive-size certificate is
`Nat.mul_pos` applied to h>0 and the original n_j>0. No new random assignments
are part of this operation. `WithinReplicationConsistent P` means finite-law
convergence in probability of D for P[r+1] to its own ATE as r→∞.

The common copy path space is Ω=A^N, where N in this exponent denotes the
natural-number index set, not the population size. Each finite A has the
discrete measurable space (all subsets measurable), Ω has its product
measurable space, and

    μ = product_{r∈N} Uniform(A)

is Mathlib `Measure.infinitePi`. Its h-prefix is s_r=ω(r) for r∈Fin h. The
one-assignment law ν is Mathlib `uniformOn Set.univ` on the supported subtype
A. For a measure λ on a measurable space and real statistics X_r,
`W1InProbability λ X d` means the conjunction

    λ is a probability measure, and
    for every ε∈R with ε>0, lim_{r→∞} λ.real{ω:ε<|X_r(ω)-d|}=0.

Here `λ.real E` is the real conversion of the extended nonnegative measure
λ(E). Independence (`iIndepFun`) means mutual independence of all finite
families of the coordinate random variables in the usual measurable-set
sense. A measure map is pushforward.

On the product cluster label set Fin h × Fin M define

    Ncopy(h) = sum_{(r,j)} n_j,
    δcopy(h) = [sum_{(r,j)}y1_j-sum_{(r,j)}y0_j]/Ncopy(h),
    Acopy_a(h,s) = {(r,j):j∈A_a(s_r)}.

`W1CopiedEstimator` is the difference of the ya total divided by the size
total on Acopy_1 and Acopy_0, respectively.

### Entire assertion, including quantifier order

The top-level proposition is the conjunction of the following assertions;
every displayed universal quantifier is local to its own conjunct. There is
no additional premise assuming any convergence result.

1. For every P, under the h=r+1 finite independent-copy law, each of
   C_1(y1,h), C_0(y0,h), C_1(n,h), C_0(n,h), Q(h)
   converges in probability, respectively, to
   p_1 sum_j y1_j, p_0 sum_j y0_j, p_1 N, p_0 N, δ.
   Each convergence quantifies every real ε>0 after P.
2. For every P,
   [(sum y1)*p_1]/[N*p_1]-[(sum y0)*p_0]/[N*p_0]=δ.
3. For every P, then every h∈N and proof h>0, N(P[h])=h*N(P).
4. For every P, h>0, s a subset in A, and k∈R, jointly
   δ(P[h])=δ, D(P[h],s)=D(P,s), H(P[h],s)=H(P,s), and
   R_k(P[h],s)=R_k(P,s).
5. For every P and proof b≠0, every h>0 has the same D bias b, and the
   constant sequence consisting of the base law and base D is not
   `DesignConsistent` for the constant target δ.
6. For the specific population P* with M=3,t=1,n=(1,2,4),y0=(0,1,1),y1=(0,0,0),
   the constant sequence just described is not consistent; 7h→∞ as h→∞;
   for every h>0 its within-cluster replicated law equals the base law;
   its positive within-cluster replication sequence is not consistent;
   and for every h>0 its D bias is -1/315.
7. For every P, h∈N, then a proof h>0, and every s:Fin h→A, all of the
   following hold: card(Fin h × Fin M)=hM; card(Acopy_1)=ht;
   card(Acopy_0)=hc; Ncopy(h)=hN; δcopy(h)=δ; for every a∈{0,1}, the
   size total on Acopy_a is sum_r B_a(s_r)>0; and the product-cluster
   estimator equals Q(h,s).
8. For every P and h∈N, h*c=h*M-h*t (natural arithmetic).
9. For every P, μ is a probability measure, its coordinate maps are mutually
   independent, each coordinate pushforward is ν, and for every h∈N its
   h-prefix pushforward is uniform on Fin h→A. Further, for every h∈N,
   every T:(Fin h→A)→R, and all d,ε∈R, the μ probability of
   ε<|T(prefix_h(ω))-d| equals the finite error probability under `copyLaw`.
10. For every P, all four growth statements hold: r↦Ncopy(r+1) is strictly
    increasing; for every ω∈Ω and a∈{0,1},
    r↦sum_{i∈Fin(r+1)}B_a(ω(i)) is strictly increasing;
    r↦N(P[r+1]) is strictly increasing; and for every supported single
    assignment s and a, r↦B_a(P[r+1],s) is strictly increasing.
    `StrictMono f` means ∀r<r', f(r)<f(r').
11. For every P, the five convergence statements in item 1 also hold on
    the single path probability space (Ω,μ), evaluating all statistics on
    the prefixes of that path, with the same five limits. Each occurrence
    of `W1InProbability` also asserts that μ is a probability measure.
12. For every P, h∈N and proof h>0: for every a and every subset s of Fin M
    (even unsupported ones), B_a(P[h],s)=h*B_a(P,s); the finite laws of
    P[h] and P are equal; their D biases agree; and for every ε∈R the ν
    probability of |D(P[h],s)-δ|>ε equals the finite error probability for
    the replicated population and its ATE.
13. For every P, p_1 N>0 and p_0 N>0.
14. For every P and proof b≠0, its positive within-cluster sequence is not
    `WithinReplicationConsistent`, and its same-draw sequence
    r,s↦D(P[r+1],s) does not converge in probability to δ on (A,ν).
15. For every h∈N with h>0, P*[h] has size 7h, ATE -2/7, and D error
    probability 1 at ε=1/25.

For P* the three equally likely base assignments give D=-1/3,-1/5,-1/3.
Their respective absolute errors from -2/7 are 1/21,3/35,1/21, all >1/25;
their mean is -13/45 and their bias is -1/315. This is the concrete witness
encoded by the statement. It concerns repeated units inside fixed clusters,
not dependent copies in the independent-copy construction.

### Junk-value and boundary audit

* All base M,t,c,N, and K denominators are positive. The natural subtraction
  c=M-t and hM-ht is exact, since t<M and multiplication preserves the
  inequality for positive h (and both sides are zero for h=0).
* Generic `differenceInMeans` can divide by zero on an empty arm for an
  unsupported s. All statistical claims using it restrict to supported
  assignments. Item 12's unrestricted-s identity concerns only arm sizes
  and contains no division. No unsupported assignment supplies a witness.
* `copyAverage`, Q, and δcopy are totalized at h=0 by empty sums and real
  0/0=0; Ncopy(0)=0. Every population-ratio assertion uses h>0, and all
  limit sequences use h=r+1. Zero prefixes occur only in the valid uniform
  prefix law and general event-law identity on the one-element empty
  function space. No target equality or positive denominator is claimed
  for a zero-size copied population.
* For h>0 every copied arm size is a sum of h positive supported arm sizes.
  Within-cluster replication explicitly requires h>0. It preserves
  positivity and nonempty assignment support. All casts of natural counts
  into R are exact; no integer casts occur.
* `Measure.real` uses `ENNReal.toReal`, which would send infinity to zero.
  All measures used here are genuine probability measures: the finite
  supported uniform law and its countable product. Every event therefore
  has finite measure. Even for an arbitrary λ in the generic
  `W1InProbability` definition, the probability-measure condition is part
  of the proposition, so an infinite measure cannot satisfy it. All
  statistics/events actually used depend on finitely many discrete
  coordinates and are measurable; the single-assignment ones are on a
  finite discrete space. No nonmeasurable function is being used.
* Finite-law expectations are finite sums, not Bochner integrals. The
  discrete uniform laws are normalized by nonzero finite cardinalities;
  their countable product is Mathlib's product probability measure, not
  an unnormalized product. The path space is nonempty. The auxiliary
  `copyLaw._proof_1` chooses a genuine supported assignment to demonstrate
  nonempty function support, including h=0. `assignments_nonempty` also
  underlies the one-assignment nonempty instance.
* `efficiencyPopulation._proof_1`, `_proof_2`, `_proof_3` certify 0<1,
  1<3, and positivity of the entries (1,2,4). The generated
  `T17Statement._proof_1`, `T17WholeStatement._proof_1`, and
  `T3WholeStatement._proof_1`, `_proof_2` are numeral/`AtLeastTwo`
  certificates (for 315,25,2,7), not mathematical premises or hidden
  dependence on T3's claim.
* There are no logarithms, square roots, nonnatural real powers, infinite
  expectations, partial-function defaults, infima, suprema, liminf or
  limsup. The genuine filter limits are not totalized limit values.
