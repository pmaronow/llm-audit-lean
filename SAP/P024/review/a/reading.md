# Blind reading of the Lean statements

This file was written from `SAP/P024/Defs.lean`, all six Defs parts,
`SAP/P024/Challenge.lean`, and `Challenge/Part1.lean`, before opening either
`claims.json` or `record.json`. Names below are mathematical abbreviations for
the definitions, not additional assumptions. All conclusions in a numbered
list belonging to one theorem are conjoined.

## Common definitions, expanded

All outcomes, weights, expectations, and divisions take values in the real
numbers. A finite type is a type with a specified enumeration of all its
elements; `Fin K` is the set of integers from 0 through K-1. `Finset (Fin K)`
ranges over **all** subsets, including the empty and full subsets. Membership
indicators are ordinary 0/1 indicators (`Bool`, `decide`, and `if` introduce
no additional probabilistic assumptions).

A `Design` on a finite assignment space Ω is a function d:Ω→R such that
d(ω)≥0 for every ω and Σω d(ω)=1. Thus such a design cannot exist on an empty
assignment space. It need not give positive probability to every assignment.
For any real function X and predicate A,

- E_d X = Σω d(ω)X(ω);
- Pr_d(A) = Σω d(ω)1_A(ω);
- Var_d(X) = Σω d(ω)(X(ω)-E_d X)^2.

These are finite sums, not integrals or extended-real quantities. `uniformDesign`
requires a nonempty finite space and gives every assignment mass 1/|Ω|.

Given exposure z(ω,i)∈{false,true} and fixed potential outcomes y0(i), y1(i),
`observed` is y1(i) when z(ω,i) is true and y0(i) otherwise. There is no
dependence of these potential outcomes on any other unit's exposure or on
assignment history in this definition. Write π(i)=Σω d(ω)1_{z(ω,i)}.
The overlap set is E={i:0<π(i)<1}. For a finite set E,

- τ_E = (Σi∈E [y1(i)-y0(i)])/|E|;
- H_E(ω) = (Σi∈E [y1(i)/π(i) if z(ω,i), otherwise
  -y0(i)/(1-π(i))])/|E|.

The underlying functions are total even for zero denominators (real division
in Lean has 0 inverse equal to 0), but statements using H here explicitly
make E nonempty and use actual strict-overlap probabilities.

For any finite assignment space and D:Ω→R,
`randomizationP D ω` is p_D(ω)=|{υ∈Ω:D(υ)≥D(ω)}|/|Ω|. This is the inclusive
upper-tail rank fraction under the **uniform** law, with ties counted. It is
not the weighted tail under an arbitrary Design.

For a finite set J of clusters, positive sizes n(j), cluster potential means
a(j),b(j), and exposure z:J→Bool, write

    C(n,a,b,z) = Σ_{z(j)=true} n(j)b(j) / Σ_{z(j)=true} n(j)
                - Σ_{z(j)=false} n(j)a(j) / Σ_{z(j)=false} n(j),
    τ(n,a,b)   = Σj n(j)[b(j)-a(j)] / Σj n(j).

These are `clusterDIM` and `clusterEffect`. `treatedCount z` counts j with
z(j)=true. `fixedDIM m a b z` replaces the two denominators in C(1,a,b,z)
by the stipulated real numbers m and |J|-m, respectively. The subtraction
in that second denominator is real subtraction, not natural-number truncation.

A `ClusterPopulation K` has K clusters, positive natural sizes n(j), and
arbitrary fixed real outcomes y0(j,i),y1(j,i), where 0≤i<n(j). Its cluster
means are a(j)=Σi y0(j,i)/n(j) and b(j)=Σi y1(j,i)/n(j). Its total size is
N=Σj n(j), weight w(j)=n(j)/N, and `populationEffect` is τ(n,a,b).
For a subset S of treated clusters and an arbitrary real function e on
subsets, `populationEstimator P e S`, denoted X_e(S), equals e(S) when S is
empty or full and otherwise equals C(n,a,b,1_S). On a population with K=k+2
clusters, `maxClusterWeight` is max_j w(j).

For K clusters, the Bernoulli joint mass is

    b_p(S) = (∏j∈S p)(∏j∉S (1-p)) = p^|S|(1-p)^(K-|S|).

`independentClusterLaw d p` says d(S)=b_p(S) for **every** subset S.
`completeClusterLaw d m` says d(S)=1/binom(K,m) if |S|=m, and 0 otherwise.
`bernoulliDesign K p` constructs the former law for 0≤p≤1. Empty products
are 1, as usual. Each use below either has interior p or p=1/2; complete
assignment is used with 0<m<K.

For K=k+2, A_K is the set of proper nonempty subsets. `NonemptyAllocations k`
is exactly this subtype, with one element for each such subset and no extra
copies. `conditionalNonemptyDesign k` is uniform on A_K. Define

    Z_K(p) = ΣS∈A_K b_p(S),
    c_p(S) = b_p(S)/Z_K(p),
    E_cond,p X = ΣS∈A_K c_p(S)X(S).

These are `bernoulliNonemptyMass`, `bernoulliConditionalMass`, and
`bernoulliConditionalExpectation`. Their definitions alone do not assert
normalization or positivity; T7 supplies positivity and identifies the
denominator with an actual event probability.

For n≥0, `halfClusterDesign n` is uniform on the (n+1)-element subsets of
2n+2 clusters. Such subsets form a nonempty finite type.

Limits `Tendsto f atTop (nhds L)` below mean the ordinary limit f(k)→L as
the natural index k→∞. In epsilon form: for every δ>0, eventually
|f(k)-L|<δ. Negated Tendsto is failure of this ordinary limit.

Mathlib endpoints checked: `Finset.sup'` in
`Mathlib/Data/Finset/Lattice/Fold.lean` is the supremum of an explicitly
nonempty finite image, hence an attained real maximum here;
`Finset.powersetCard` and its membership lemma in
`Mathlib/Data/Finset/Powerset.lean` select exactly the subsets of a prescribed
cardinality; `Mathlib/Data/Fintype/Powerset.lean` enumerates all subsets and
identifies cardinalities with 2^K and binom(K,m); `Nat.choose` in
`Mathlib/Data/Nat/Choose/Basic.lean` is the usual binomial coefficient.
`Filter.Tendsto` in `Mathlib/Order/Filter/Defs.lean`, `atTop` in
`Mathlib/Order/Filter/AtTopBot/Defs.lean`, and `nhds` in
`Mathlib/Topology/Defs/Filter.lean` give the ordinary limits just described.
There is no limsup, infinite maximum, or integrability convention in a stub.

## SAP.P024.T1

There are no hypotheses or external parameters. The assignment is uniformly
distributed on s∈{0,1,2}, representing treatment onset s+2. The four date
indices t∈{0,1,2,3} represent dates t+1. Exposure is z(s,t)=1 exactly when
s+2≤t+1. Fixed untreated outcomes are a(t)=(t+1)^2 and treated outcomes
are b(t)=a(t)+2. The chosen effect/estimator set is E={1,2}, representing
dates 2 and 3. Let H(s)=H_E(s) with actual exposure probabilities. Let

    D(s) = Σ_{t:z(s,t)=1} a(t)/(3-s)
           - Σ_{t:z(s,t)=0} a(t)/(s+1).

This is a before-after contrast computed under the fixed path a, with the
correct strictly positive numbers of dates in each arm. The theorem states:

1. For every t, π(t) is the t-th entry of (0,1/3,2/3,1).
2. a(0)=1, a(1)=4, a(2)=9, a(3)=16; for every t, b(t) is the t-th
   entry of (3,6,11,18); and a(0)≠a(1).
3. H(0)=69/4, H(1)=21/4, H(2)=-33/2.
4. τ_E=2, E H=2, and Var(H)=1561/8.
5. D(0)=26/3, D(1)=10, D(2)=34/3.
6. p_D(0)=1, p_D(1)=2/3, p_D(2)=1/3.
7. For every r∈{0,1,2,3}, Pr(p_D(s)≤r/3)=r/3.
8. For every real α, if 0≤α and α≤1, then Pr(p_D(s)≤α)≤α.
9. E H=τ_E (also separately stated despite the preceding numerical equalities).

The sharp-null calculation uses path a in both arms; the effect calculation
uses paths a and b. The theorem does not identify these two outcome schedules.

## SAP.P024.T2

There are three groups of conjoined assertions, whose universal parameters
are independent of one another.

1. For every finite unit type I, every finite assignment type Ω, every
   Design d on Ω, every exposure function z:Ω→I→Bool, and every pair of
   fixed real potential-outcome functions y0,y1:I→R, **if** their actual
   overlap set E is nonempty, then E_d H_E=τ_E. Parameters are universal
   in precisely that order; nonempty overlap is the only hypothesis after
   those objects. The set E is determined by d and z, not chosen by the user.
2. For every finite **nonempty** Ω, every real function D on Ω, and every
   real α, if 0≤α and α≤1, then under the uniform Design on Ω,
   Pr(p_D(ω)≤α)≤α. No nonuniform law or outcome model appears in this clause.
3. For the fixed T1 calendar paths, E D=10 and E D≠0. If D_obs(s) is
   obtained by using observed outcomes b(t) on exposed dates and a(t) on
   unexposed dates in the same before-after means, then for every s,
   D_obs(s)=D(s)+2. Also E D_obs=12 and E D_obs≠2.

## SAP.P024.T4

There are no hypotheses. The theorem defines a deterministic sequence of
populations and asserts all the following facts. For every natural k, put
K=k+2. Cluster 0 has K^2 individuals, each with (y0,y1)=(1/2,3/4). Every
other cluster has one individual with (y0,y1)=(1/4,1/2). Write P_K for this
population, X_e for its estimator, and X_0 for extension 0.

For real K,m and a Boolean h define

    V(K,m,true)  = 1/4 + (1/4)K^2/(K^2+m-1),
    V(K,m,false) = 1/4 - (1/4)K^2/(K^2+K-m-1).

The theorem states:

1. For every k, total population size is K^2+K-1.
2. For every k, every cluster j, and every individual i in that cluster,
   both potential outcomes lie strictly between 0 and 1 and their
   difference is 1/4. For every k, the population effect is 1/4.
3. For every k and every subset S of its K clusters, if S is nonempty
   and proper, then

       X_0(S)=V(K,|S|,1_{0∈S}),
       (1/4)K^2/(K^2+K-2) ≤ |X_0(S)-1/4|,
       1/8 < (1/4)K^2/(K^2+K-2).

4. For every k, the uniform law on **all** subsets is the independent
   Bernoulli law with p=1/2. Under that law Pr(A_K)=1-2/2^K.
5. For **every** family of real functions e_k on all subsets, the following
   three statements hold together: for every k,

       1-2/2^K ≤ Pr(|X_{e_k}(S)-populationEffect(P_K)|>1/8);

   these error probabilities tend to 1 as k→∞; and they do not tend to 0.
   The family e_k is fixed before these conclusions and may depend
   arbitrarily on k and S, with no boundedness assumption.
6. For every k, under the uniform law on A_K, E X_0=1/4.
7. For every natural n, set K=2n+2, let S be uniform over |S|=n+1,
   and put R_n=K^2/(K^2+n). Under this law:

   - Pr(0∈S)=1/2;
   - for every such S, X_0(S)=1/4+(1/4)R_n when 0∈S and
     X_0(S)=1/4-(1/4)R_n otherwise;
   - E X_0=1/4 and Var(X_0)=R_n^2/16;
   - R_n>1/2 and Pr(|X_0-1/4|>1/8)=1.

8. R_n→1, and those half-allocation variances tend to 1/16.
9. For every k, max_j w(j)=K^2/(K^2+K-1), and this maximum tends to 1.
10. The real expressions V(6,3,true)=37/76 and V(6,3,false)=1/76.
    There are 20 three-element subsets of six clusters, exactly 10 of
    which contain cluster 0; there are 64 total subsets; and under the
    uniform law on all subsets Pr(A_6)=62/64.
11. For every j∈{0,...,5}, P_6 has size 36 when j=0 and size 1 otherwise.
    Its variance under uniform three-of-six assignment is 81/1444.
    For every proper nonempty subset S, |X_0(S)-1/4|≥9/40, and there
    exists such an S with equality.

## SAP.P024.T5

This is the conjunction of a consistency implication and a separate
equivalence. In the first clause the universal parameters, in order, are:

1. a sequence P_k of populations with K=k+2 positive-sized clusters;
2. a sequence d_k of Designs on **all** cluster subsets;
3. a real sequence p_k;
4. an arbitrary family e_k of empty/full-arm real extensions;
5. two real constants B and η.

The hypotheses, in order, are B≥0; η>0; for every k,j,i both
|y0(k,j,i)|≤B and |y1(k,j,i)|≤B; for every k either d_k has independent
Bernoulli joint masses at p_k, **or** there exists a natural m with
0<m<K, p_k=m/K, and d_k has the complete m-of-K joint masses; for every k,
η≤p_k≤1-η; and max_j w_k(j)→0. The disjunction is inside the universal
quantifier on k: the design branch may change with k.

The conclusion is: for every real ε>0,

    Pr_{d_k}(|X_{e_k}(S)-populationEffect(P_k)|>ε) → 0.

The target effect may change with k. No moment bound on e_k is required,
and no independence of potential outcomes or clusters' sizes is asserted.

The second clause states, independently: for every sequence P_k of
positive-sized populations with k+2 clusters, with **no** bounded-outcome,
design, or probability hypotheses,

    max_j w_k(j)→0  if and only if  Σj w_k(j)^2→0.

## SAP.P024.T6

For every finite unit type J and finite assignment type Ω, every Design d,
and every natural m, if 0<m and m<|J|, then for every exposure function
z:Ω→J→Bool and every two fixed real outcome functions y0,y1 on J, the
following two hypotheses imply the conclusion:

1. For **every** assignment ω (including any of d-mass zero), exactly m
   units are exposed.
2. For every unit j, its actual marginal Pr_d(z(ω,j)=true) equals m/|J|.

The conclusion is

    E_d[C(1,y0,y1,z(ω))] = Σj[y1(j)-y0(j)]/|J|.

Thus the statistic uses actual observed group means, which have nonzero
denominators m and |J|-m under the hypotheses. There is no further assumption
of uniform complete assignment or independence. The outcomes are universal
before the two hypotheses, and the right side averages over the whole pool.

## SAP.P024.T7

The first clause universally quantifies a natural k, a natural q, assumes
q>0, then universally quantifies a population P with K=k+2 clusters. After
assuming n(j)=q for every cluster, it universally quantifies real p with
0<p and p<1. Under precisely those hypotheses it states:

1. The explicitly constructed Bernoulli Design has independent joint
   masses b_p(S).
2. Pr(A_K)>0 under that Design.
3. For every proper nonempty subset S,

       c_p(S)=d(S)/Pr_d(A_K).

4. For **every** empty/full-arm extension e on subsets,

       E_cond,p X_e = populationEffect(P).

5. For every proper nonempty S, X_0(S) equals the fixed-divisor contrast
   `fixedDIM |S| a b 1_S`, using cluster means a,b and divisors |S| and
   K-|S|. Equal sizes make this the individual treatment mean minus the
   individual control mean.

The second clause is an unconditional separate example. There are two
clusters with real sizes n=(1,2), untreated means a=(0,0), and treated
means b=(0,1). The parent law is uniform on all four subsets. It states:

1. This parent law has independent joint masses with p=1/2.
2. Pr(A_2)=1/2.
3. For every S∈A_2, the uniform mass on A_2 equals its parent mass divided
   by the parent probability of A_2.
4. τ(n,a,b)=2/3; C(n,a,b,1_{\{0\}})=0;
   C(n,a,b,1_{\{1\}})=1.
5. For every real extension e, the expectation under the uniform law on
   A_2 of the statistic that is e on empty/full subsets and C otherwise
   equals 1/2.
6. Under that same conditional law, E C≠τ(n,a,b).

There is no general closed formula for Pr(A_K) asserted in this theorem.

## SAP.P024.T8

Universal parameters, in order: a finite **nonempty** block type B; a
finite assignment space Ω; a family of finite unit types I_b; a Design d
on Ω; and a natural count m_b for each block. Assume for every b, m_b>0,
then for every b, m_b<N_b=|I_b|. Next universally quantify all exposure
functions z(ω,b,i) and all fixed real outcome functions y0(b,i),y1(b,i).
Assume for every ω,b, exactly m_b units in block b are treated, and for
every b,i, the actual marginal exposure probability is m_b/N_b.

Let N=Σb N_b, which is positive under these hypotheses. Define

    H(ω) = (1/N) Σb Σi∈I_b
            [y1(b,i)/(m_b/N_b) if z(ω,b,i)=true,
             otherwise -y0(b,i)/(1-m_b/N_b)],
    W(ω) = Σb (N_b/N) C(1,y0(b,·),y1(b,·),z(ω,b,·)),
    τ = (1/N) Σb Σi∈I_b [y1(b,i)-y0(b,i)].

The three conjoined conclusions are: for every assignment ω, H(ω)=W(ω);
E_d H=τ; and E_d W=τ. Counts are required on all assignments, including
zero-mass ones. No independence across blocks or uniform distribution of
the m_b-element subsets is required. The separate helper `blockedEstimate`
is the same weighted sum with `fixedDIM m_b` in place of actual group
means, but the theorem itself concludes equality with actual `clusterDIM`.
