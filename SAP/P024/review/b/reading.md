# Blind mathematical reading

This file was written from `SAP/P024/Defs*.lean`, `SAP/P024/Defs/*.lean`, and
`SAP/P024/Challenge*.lean` only, before opening `claims.json` or `record.json`.
The statements below are readings of the propositions, independently of the
descriptive docstrings. There are seven theorem stubs: T1, T2, T4, T5, T6, T7,
and T8. There is no T3 stub.

## Shared objects and the underlying Mathlib meanings

All outcomes and numerical expectations take values in the ordinary real field.
A `Design Ω` on a finite type Ω is a function d(ω) ≥ 0 whose sum over every
element of Ω is 1. In particular, the existence of a Design rules out an empty
Ω, even where `[Nonempty Ω]` is not an explicit argument. Write

* E_d X = Σ_{ω∈Ω} d(ω)X(ω);
* Pr_d(A) = Σ_{ω∈Ω} d(ω)1_A(ω);
* Var_d(X) = E_d[(X − E_d X)²].

These are finite sums, not Mathlib integrals. `uniformDesign Ω` has mass
1/|Ω| and explicitly requires Ω nonempty. Fintype supplies an enumeration of
every element, and `Finset.univ`, its sums, filters, cardinality, complement,
products, and `powersetCard m` have their usual finite-set meanings.
`Fin n` is the set {0,…,n−1}; subtype conditions restrict the actual sample
space rather than adding elements of mass zero. `decide` and Bool tests are
ordinary characteristic functions. An empty finite sum is 0 and an empty
product is 1.

For an exposure array z(ω,i)∈{0,1} and fixed potential outcomes y_i(0),y_i(1),
`observed` returns y_i(z(ω,i)). No outcome depends on ω or on other units'
assignments apart from this exposure. Define π_i=E_d z_i and
E={i:0<π_i<1}. For a finite set A of units,

    τ_A = |A|⁻¹ Σ_{i∈A}(y_i(1)−y_i(0)),
    H_A(ω) = |A|⁻¹ Σ_{i∈A}
        [z_i(ω)y_i(1)/π_i − (1−z_i(ω))y_i(0)/(1−π_i)].

The definition uses an if-then-else selecting the treated or control term;
this formula is its equivalent numerical reading whenever the displayed
denominators are nonzero. T1 and T2 use nonempty sets with strict overlap.

For a finite, nonempty sample space and any fixed real function D, the
upper-tail value is

    r_D(ω) = |{υ∈Ω:D(υ)≥D(ω)}|/|Ω|.

Ties are counted, and rejection uses r_D≤α.

For cluster weights n_j and cluster potential means a_j,b_j, write

    DIM_n(z) = (Σ_{z_j=1}n_j b_j)/(Σ_{z_j=1}n_j)
               − (Σ_{z_j=0}n_j a_j)/(Σ_{z_j=0}n_j),
    τ_n = (Σ_j n_j(b_j−a_j))/(Σ_j n_j).

`treatedCount` counts treated clusters/units, without weighting by n_j.
`fixedDIM m` instead divides the treated sum of b_j by m and the control
sum of a_j by |J|−m. That subtraction is in ℝ, not truncated natural
subtraction. `clusterDIM (fun _ => 1)` is the ordinary observed difference
in group means if both groups are nonempty.

A `ClusterPopulation K` consists of K labelled clusters, positive integer
sizes n_j, and arbitrary fixed real individual outcomes y_{ji}(0),y_{ji}(1),
for i=0,…,n_j−1. Its means are a_j=Σ_i y_{ji}(0)/n_j and
b_j=Σ_i y_{ji}(1)/n_j. Its total size is N=Σ_j n_j, its shares are
w_j=n_j/N, and `populationEffect` is τ_n, equivalently the mean individual
effect. For K=k+2, N>0. `maxClusterWeight` is max_j w_j: `Finset.sup'`
requires a nonempty finite set and is the usual real maximum, with no
default or infinite-supremum convention.

An allocation s is a subset of the K clusters, with z_j=1 iff j∈s.
`populationEstimator P empty s` equals DIM_n(z) on ∅≠s≠all clusters,
and equals the explicitly supplied arbitrary real `empty s` on either
empty-arm allocation. Thus it never evaluates a zero group-size ratio as
an observed group mean. `NonemptyAllocations k` is exactly the proper
nonempty subsets of k+2 clusters.

`bernoulliMass p s` is the product of p for every j∈s and of 1−p for
every j∉s. `independentClusterLaw d p` requires equality of *every* joint
mass with that product. `bernoulliDesign K p` constructs this Design
when 0≤p≤1. `completeClusterLaw d m` requires mass 1/binomial(K,m)
on each m-element subset and 0 elsewhere. In T5, 0<m<K guarantees its
denominator is positive. `conditionalNonemptyDesign k` is uniform on
proper nonempty subsets (the fair independent law conditioned on both
arms being nonempty). `halfClusterDesign n` is uniform on the subsets
of size n+1 of 2n+2 clusters, a nonempty space.

`bernoulliNonemptyMass k p` is the sum of Bernoulli joint masses over
proper nonempty subsets. `bernoulliConditionalMass` divides the joint
mass by that sum, and `bernoulliConditionalExpectation` is the finite
weighted sum with these masses. T7 uses only K≥2 and 0<p<1, for which
the normalizing sum is positive.

For blocks b∈B with finite unit sets I_b, set N_b=|I_b| and N=Σ_b N_b.
`blockPopulation I` is N. `blockedHT` is the sum of the individual HT
terms, with stipulated π_b=m_b/N_b, divided by N. `blockedEstimate`
(not used in the theorem conclusions) is Σ_b(N_b/N) fixedDIM_{m_b}.

Real division in Mathlib is total (x/0=0), but the actual uses of means
and normalization above have positivity/nonemptiness hypotheses or an
explicit empty-arm extension. Expressions such as `(3-s.val : ℝ)` and
`(k+2 : ℝ)^2+(k+2)-2` have real subtraction. Natural-valued cluster sizes
are cast to ℝ before they enter numerical weights.

`Tendsto f atTop (nhds L)` for f:ℕ→ℝ means: for every δ>0 there is
k₀ such that |f(k)−L|<δ for every k≥k₀. Mathlib defines Tendsto by
mapping filters, atTop by eventual lower bounds, and nhds by the usual
real topology. In particular, the statements use ordinary real limits,
not extended-real limsup or convergence along an empty index set.

Source checks in Mathlib: `Data/Finset/Lattice/Fold.lean` (`sup'`),
`Data/Finset/Powerset.lean` (`powersetCard`),
`Algebra/BigOperators/Group/Finset/Defs.lean` (finite sum/product),
`Order/Filter/Defs.lean` (`Tendsto`),
`Order/Filter/AtTopBot/Defs.lean` (`atTop`), and
`Topology/MetricSpace/Pseudo/Defs.lean` (`Metric.tendsto_atTop`).

## SAP.P024.T1

This is a closed conjunction with no hypotheses. There are four dates
t=0,1,2,3 (calendar dates 1,2,3,4), and an onset s=0,1,2 is uniform
(onset dates 2,3,4). Exposure is z_s(t)=1 iff s+2≤t+1. Baseline
potential outcomes are y_t(0)=(t+1)², and treated potential outcomes
are y_t(1)=(t+1)²+2. Let A={1,2} (calendar dates 2,3), and let H be
the HT estimator above using the actual onset probabilities on A.
The theorem asserts all of the following:

1. For every t, π_t equals the corresponding entry of (0,1/3,2/3,1).
   The baselines at the four dates are 1,4,9,16; every treated outcome
   is the corresponding entry of (3,6,11,18); and the first two
   baselines are different.
2. H(0)=69/4, H(1)=21/4, H(2)=−33/2; τ_A=2; E H=2;
   Var H=1561/8; and separately E H=τ_A.
3. Define the baseline-only before-after statistic

       D(s) = [Σ_{t:z_s(t)=1}(t+1)²]/(3−s)
              − [Σ_{t:z_s(t)=0}(t+1)²]/(s+1).

   Then D(0)=26/3, D(1)=10, D(2)=34/3 and
   r_D(0)=1, r_D(1)=2/3, r_D(2)=1/3.
4. For every k∈{0,1,2,3}, Pr(r_D≤k/3)=k/3. For every real α,
   if 0≤α and α≤1, then Pr(r_D≤α)≤α.

The baseline-only statistic is a separate sharp-null calculation; it
does not assert that the treatment potential outcomes equal the
baselines in the effect-estimation calculation.

## SAP.P024.T2

This is a conjunction of two universal propositions and five concrete
before-after assertions, with no hypothesis linking its separate parts.

First, in order: for every pair of finite types I,Ω, every Design d on
Ω, every exposure array z:Ω×I→{0,1}, and every pair of fixed real
potential-outcome functions y(0),y(1) on I, if
E={i:0<Pr_d(z_i=1)<1} is nonempty, then E_d H_E=τ_E.
No independence, uniformity, monotone exposure, or fixed treated count
is assumed in this part.

Second, for every finite nonempty type Ω, every D:Ω→ℝ, and every
real α, if 0≤α≤1, then Pr_uniform(r_D≤α)≤α. The statistic is an
arbitrary fixed function of the assignment, with upper-tail ties counted.

Third, for exactly the four-date population and uniform three-onset
design of T1, E D=10≠0. For every onset s, let D_obs(s) be the actual
treated-period observed mean minus the actual control-period observed
mean, using the same positive counts 3−s and s+1. Then
D_obs(s)=D(s)+2 for every s, E D_obs=12, and E D_obs≠2.

## SAP.P024.T4

This is a closed conjunction about a particular sequence of populations
and designs. For each k∈ℕ set K=k+2. Cluster 0 has K² individuals;
the other K−1 clusters have one individual each. Individuals in cluster
0 have (y(0),y(1))=(1/2,3/4), and all other individuals have
(y(0),y(1))=(1/4,1/2). Write τ_K for its individual population effect,
X_K^e(s) for its estimator with empty-arm extension e, and define

    V(K,m,true)  = 1/4+(1/4)K²/(K²+m−1),
    V(K,m,false) = 1/4−(1/4)K²/(K²+K−m−1),
    L_K = (1/4)K²/(K²+K−2).

All of these assertions are included:

1. For every k, N=K²+K−1. For every k, cluster j, and individual i,
   both outcomes lie strictly between 0 and 1, and the effect is 1/4.
   For every k, τ_K=1/4.
2. For every k and every allocation s, if s is proper and nonempty,
   X_K^0(s)=V(K,|s|,1_{0∈s}), and
   L_K≤|X_K^0(s)−1/4| with L_K>1/8.
3. For every k, the uniform law on all 2^K subsets has the full joint
   independent law with p=1/2, and Pr(∅≠s≠all)=1−2/2^K.
4. For every family of real empty-arm extensions e_k (quantified
   before the following conjunction), for every k,

       Pr(|X_K^{e_k}−τ_K|>1/8) ≥ 1−2/2^K,

   these error probabilities tend to 1 as k→∞, and they do not tend
   to 0.
5. For every k, under the uniform law on proper nonempty subsets,
   E X_K^0=1/4.
6. For every n∈ℕ put K=2n+2 and
   R_n=K²/(K²+(n+1)−1). Under the uniform law on the allocations of
   exactly n+1 treated clusters: Pr(0∈s)=1/2; for every allocation s,
   X_K^0(s)=1/4+(1/4)R_n if 0∈s and 1/4−(1/4)R_n otherwise;
   E X_K^0=1/4; Var X_K^0=R_n²/16; R_n>1/2; and
   Pr(|X_K^0−1/4|>1/8)=1. Also R_n→1 and these variances tend to
   1/16 as n→∞.
7. For every k, max_j w_j=K²/(K²+K−1), and these maxima tend to 1.
8. V(6,3,true)=37/76 and V(6,3,false)=1/76. There are exactly 20
   three-subsets of six clusters and exactly 10 containing cluster 0.
   There are 64 subsets in all, and the proper-nonempty event has
   probability 62/64 under the uniform law on all subsets. For every
   j∈Fin 6 the cluster size in this population is 36 if j=0 and 1
   otherwise. The half-treated design variance is 81/1444. Every
   proper nonempty allocation has |X_6^0−1/4|≥9/40, and there
   exists a proper nonempty allocation attaining equality 9/40.

## SAP.P024.T5

The first part has these quantifiers and hypotheses, in this order:
for every population sequence P_k with K=k+2 positive-sized clusters,
every sequence of Designs d_k on *all* subsets of those clusters,
every real probability sequence p_k, every real empty-arm extension
family e_k, and every pair of reals B,η, assume

1. B≥0 and η>0;
2. for every k,j,i, |y_{kji}(0)|≤B and |y_{kji}(1)|≤B;
3. for every k, either d_k has the full independent common-p_k law,
   or there exists an integer m with 0<m<k+2, p_k=m/(k+2), and
   d_k the uniform complete law on m-subsets;
4. for every k, η≤p_k≤1−η;
5. max_j w_{kj}→0 as k→∞.

Then, for every real ε>0, Pr_{d_k}(|X_k^{e_k}−τ_k|>ε)→0.
The design branch may vary with k. Outcomes, sizes, p_k, effects,
and arbitrary empty-arm values may all vary with k. The population
effect need not itself converge. Independence is of cluster assignments,
not of individual outcomes.

The second part is independent of all the preceding hypotheses: for
every population sequence P_k with k+2 positive-sized clusters,

    max_j w_{kj}→0  iff  Σ_j w_{kj}²→0.

There is no theorem clause here about any particular finite-sample
bias, or any sequence failing consistency without the share condition.

## SAP.P024.T6

In order: for every finite unit type J and finite assignment type Ω,
every Design d on Ω, and every natural m, assume 0<m<|J|. Then for
every exposure array z and every pair of arbitrary fixed real potential
outcomes y(0),y(1) on J, assume

* for every ω∈Ω, exactly m units are treated;
* for every j∈J, its actual marginal treatment probability under d is
  m/|J|.

The conclusion is

    E_d[(Σ_{z_j=1}y_j(1))/m − (Σ_{z_j=0}y_j(0))/(|J|−m)]
      = (Σ_j(y_j(1)−y_j(0)))/|J|,

where the expression inside the expectation is defined as the actual
observed treatment mean minus actual observed control mean. The first
hypothesis is imposed on every ω, including zero-mass assignments;
the law need not be uniform or independent. Nothing is claimed for a
random treated count, even if marginal probabilities are equal.

## SAP.P024.T7

The first conjunct quantifies, in order: every k,q∈ℕ with q>0;
every population P of K=k+2 clusters whose sizes all equal q;
every real p and proofs 0<p and p<1. For the product Bernoulli
Design with this p, write A={∅≠s≠all}. It asserts

1. the Design has the full independentClusterLaw with parameter p;
2. Pr(A)>0;
3. for every proper nonempty s, its defined conditional mass is its
   parent joint mass divided by Pr(A);
4. for every real function e on all allocations, the conditional
   expectation of X_P^e given A equals the individual population
   effect τ_P;
5. for every proper nonempty s, X_P^0(s) equals the unweighted
   difference in cluster means with divisors |s| and K−|s|.

There is no asserted general closed formula for Pr(A).

The second conjunct is a closed two-cluster witness with weights
n=(1,2), cluster means a=(0,0), b=(0,1). The uniform parent law
on the four subsets is the independent p=1/2 law, Pr(A)=1/2,
and for every proper nonempty s the uniform conditional Design
mass equals the parent mass divided by Pr(A). Its population effect
is 2/3; DIM_n({0})=0 and DIM_n({1})=1. For every arbitrary real
empty-arm extension, the conditional observed-mean estimator has
expectation 1/2. Separately its conditional expectation without the
extension is asserted to differ from the population effect.

## SAP.P024.T8

In order: for every finite nonempty block type B, every finite
assignment type Ω, every family of finite within-block unit types
I_b, every Design d on Ω, and every function m:B→ℕ, assume
for every block 0<m_b<N_b. Then for every exposure array z and
every pair of arbitrary fixed individual potential-outcome functions,
assume

* for every ω and b, exactly m_b units are treated in block b;
* for every block b and unit i, its actual marginal probability is
  m_b/N_b.

With N=Σ_b N_b, π_b=m_b/N_b, and

    H(ω)=(1/N)Σ_bΣ_{i∈I_b}
       [z_{bi}(ω)y_{bi}(1)/π_b
          − (1−z_{bi}(ω))y_{bi}(0)/(1−π_b)],
    W(ω)=Σ_b (N_b/N)
       [(Σ_{i:z_{bi}=1}y_{bi}(1))/m_b
           − (Σ_{i:z_{bi}=0}y_{bi}(0))/(N_b−m_b)],
    τ=(1/N)Σ_bΣ_i(y_{bi}(1)−y_{bi}(0)),

the conclusion is the conjunction: H(ω)=W(ω) for *every* assignment
ω; E_d H=τ; and E_d W=τ. W is defined using actual observed group
means, with positive group sizes guaranteed by the fixed counts.
There is no within-block joint-uniformity or between-block independence
hypothesis. Nonempty B and N_b≥2 guarantee N>0.
