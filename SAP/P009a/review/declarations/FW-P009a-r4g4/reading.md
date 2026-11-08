# Blind statement reading

This file was written before opening `claims.json` or `record.json`. Sources are
`SAP/P009a/Challenge/Part2.lean:84–105` and every declaration listed in the two
closures in `closure.json`. The generated declarations with source line zero
were inspected by `#print` in `scratch/ClosureCheck.lean` (successful compilation).

## SAP.P009a.T16

### Objects, definitions, and quantifier order

The theorem is `T16WholeStatement` (`Defs/WholeW1.lean:21–43`). It universally
quantifies, in this order, over a natural number n, a proof n>0, an experiment E
on n units, an arm b in {false,true}, a real k, and a proof k>0.

Write I=Fin n and Ω=I→Bool, the full finite binary assignment cube. An experiment
consists of a mass function p:Ω→ℝ satisfying p(z)≥0 for every z and Σ_z p(z)=1,
and arbitrary real outcome functions y_i:Ω→ℝ. Its design/outcome projections and
constructors introduce no further conditions. For a real X on Ω and an event A,

* E_p X = Σ_z p(z)X(z);
* P_p(A) = Σ_z p(z)1_A(z);
* Cov_p(X,Y) = Σ_z p(z)(X(z)−E_p X)(Y(z)−E_p Y).

These are finite sums, not integrals on a hidden measure space. Put
π_i=P_p(z_i=b) and X_i(z)=1_{z_i=b}. Affects(ℓ,i) means either ℓ=i or there
exist z,z' agreeing at all coordinates other than ℓ with y_i(z)≠y_i(z'). This
existence is over the full cube, including zero-mass assignments. SharesCause(i,j)
means there exists ℓ with Affects(ℓ,i) and Affects(ℓ,j). Define

* d_ij=1 if SharesCause(i,j), and 0 otherwise;
* d_i=Σ_j d_ij and d_AVG=(Σ_i d_i)/(n:ℝ);
* Δ_ij=P_p(z_i=b,z_j=b)−π_iπ_j;
* α_ij=sSup { |P_p(z_i∈S,z_j∈T)−P_p(z_i∈S)P_p(z_j∈T)| :
  S,T arbitrary subsets of Bool };
* R_b=Σ_i Σ_j [0 if j=i, otherwise α_ij]+Σ_i π_i(1−π_i).

All division and subtraction in these expressions is over ℝ after the indicated
natural-number casts. There are no independence, arm-positivity, moment, or
regularity hypotheses on E. In particular, k need not bound an arm probability
or an outcome.

The conclusion is the conjunction of every item below:

1. For every ordered pair i,j, Cov_p(X_i,X_j)=Δ_ij,
   |Δ_ij|≤α_ij, 0≤α_ij≤1/4, and d_ij+(1−d_ij)=1.
2. For every i, d_ii=1, Δ_ii=π_i(1−π_i), and α_ii=π_i(1−π_i).
3. Σ_i Σ_j d_ij=(n:ℝ)d_AVG.
4. (k²/n²)Σ_i Σ_j Δ_ij ≤ (k²/n²)Σ_i Σ_j α_ij.
5. (k²/n²)Σ_i Σ_j α_ij ≤ k²d_AVG/n
   +(k²/n²)Σ_i Σ_j (1−d_ij)α_ij.
6. Σ_i Σ_j α_ij=R_b.
7. The inequalities in items 4 and 5 also hold with Σ_i Σ_j α_ij
   replaced by R_b.

The Challenge and definition docstrings describe the corrected full-pair mixing
bound, termwise domination including the diagonal, self-dependence, and the
equivalent off-diagonal sum with diagonal Bernoulli variances restored.

### Junk-value and boundary audit

* Real division by zero would return zero. All n and n² denominators are
  positive because n>0. Zero or unit arm probabilities are allowed and cause
  no undefined quantity: no reciprocal arm probabilities occur here.
* `mixingCoefficient` uses the real conditional supremum `sSup`. Its defining
  set is nonempty (empty S or T gives zero) and bounded: there are only finitely
  many possible subsets of Bool, and all terms are finite. Thus neither an
  empty-set nor an unbounded-set default determines this value. The asserted
  [0,1/4] bound has its usual probabilistic meaning.
* Fin n is nonempty under n>0, and Ω has 2^n points. More generally, the
  normalization in `FiniteDistribution` prevents a distribution on an empty
  type. Empty event sets still have their ordinary probability zero.
* All expectations and covariances are finite real sums on a finite cube;
  arbitrary real-valued outcomes are bounded on that cube. There is no
  nonintegrable-integral convention or `ENNReal.toReal`.
* Natural n casts injectively into ℝ. There is no natural-number subtraction,
  log, sqrt, real power, limsup/liminf, partial-function default, or other
  domain extension in this closure.
* `T16WholeStatement._proof_1` only proves that the numeral 4 is at least two
  for elaborating real powers. It adds no mathematical assumption.

## SAP.P009a.T17

### Objects, definitions, and quantifier order

The theorem is `T17WholeStatement` (`Defs/WholeW1.lean:257–277`). It is a
conjunction of a universal counting identity and an existence claim. Its
experiments, full assignment cube, probability, expectation, and Affects relation
are the finite objects explicitly defined above, with no implicit randomness in
the outcome functions. All unit indices below are Lean's zero-based indices.

For any experiment E and unit i, let

* C_i=|{j∈Fin n : Affects(j,i)}|, a natural number that includes i;
* T_i(z)=Σ_j [1 if j≠i and Affects(j,i) and z_j=true, else 0], a natural number;
* M_i(t)=Σ_z p(z)1_{T_i(z)=t};
* M_i^b(t)=[Σ_z p(z)1_{z_i=b}1_{T_i(z)=t}]/P_p(z_i=b).

`FixedSizeDesign E m` means 0<m<n and, for every z,
p(z)=1/(n.choose m:ℝ) if Σ_i 1_{z_i=true}=m, and p(z)=0 otherwise.
The `NoSpillovers` predicate means for all i,z,z', z_i=z'_i implies
y_i(z)=y_i(z'). The potential response y_i(b,z) is y_i evaluated at the
function obtained by replacing coordinate i of z by b.

`Regularity E k q s` is exactly the conjunction
k>0, q≥2, s≥1,
1/k≤P_p(z_i=true)≤1−1/k for every i,
Σ_z p(z)|y_i(z)|^q≤k^q for every i, and
Σ_z p(z)|y_i(b,z)|^s≤k^s for every i and b.
Here powers with real exponents are `Real.rpow`; all their bases are
nonnegative and k is positive.

Two auxiliary numeric formulas, with all arguments except p and b natural,
are

H(N,m,c,t) = (m.choose t:ℝ)((N−m).choose(c−t):ℝ)/(N.choose c:ℝ),

Q(N,c,p,b,t) = [c/(p(N−c))]
  [p−v(b)t/c−(1−v(b))(c−t)/c],

where v(true)=1 and v(false)=0. In H, both subtractions are truncated natural
subtraction. In Q, N,c,t are first cast to ℝ, and subtractions are real.

First, for every n, every E on n units and every i∈Fin n, the theorem asserts

|{j∈Fin n : j≠i and Affects(j,i)}|=C_i−1,

where the right side uses natural truncated subtraction. Next it asserts
there exist experiments E,F on four units with all the following clauses.

For E:

1. For every z, p_E(z)=1/6 if exactly two coordinates are true and 0 otherwise.
2. For every i,z, y_i(z)=v(z_i)+[v(z_1) if i=0, else 0].
3. FixedSizeDesign E 2 and Regularity E 2 4 1.
4. For every i,b, P_E(z_i=b)=1/2.
5. For every j, Affects_E(j,0) iff j=0 or j=1.
6. C_0=2 and C_0=min(2,4−2), with the latter arithmetic natural-valued.
7. For every z, T_0(z)=1 if z_1=true, and 0 otherwise.
8. For every t∈Fin 3 (only t=0,1,2), all six table entries below hold:

   | quantity | t=0 | t=1 | t=2 |
   | --- | --- | --- | --- |
   | M_0(t) | 1/2 | 1/2 | 0 |
   | H(4,2,2,t) | 1/6 | 2/3 | 1/6 |
   | M_0^true(t) | 2/3 | 1/3 | 0 |
   | H(3,1,2,t) | 1/3 | 2/3 | 0 |
   | M_0^false(t) | 1/3 | 2/3 | 0 |
   | H(3,2,2,t) | 0 | 2/3 | 1/3 |

9. M_0(0)>0, P_E(z_0=true)>0, and (4:ℝ)−(C_0:ℝ)>0.
10. M_0^true(0)/M_0(0)=4/3,
    H(3,1,2,0)/H(4,2,2,0)=2,
    M_0^true(0)/M_0(0)−1=1/3, Q(4,C_0,P_E(z_0=true),true,0)=1,
    and the last two quantities are unequal.

For F (`W1HypergeomSecond`):

1. For every z, p_F(z)=1/6 if exactly two coordinates are true and 0 otherwise.
2. For every i,z, y_i(z)=v(z_i).
3. FixedSizeDesign F 2, Regularity F 2 4 1, and NoSpillovers F.
4. For every i,b, P_F(z_i=b)=1/2.
5. For every i,j, Affects_F(j,i) iff j=i.
6. For every i, C_i=1, T_i(z)=0 for every z, and M_i(0)=1.
7. H(4,2,1,0)=1/2 and (1:ℝ)≠1/2.

The Challenge and definition docstrings say these examples disprove the two
printed hypergeometric laws and their printed ratio identity, because C_i
includes self whereas T_i excludes self. They explicitly exclude a refutation
of the inequality of Lemma A12.

### Printed reading and witness conditions, before comparison to the claim

The reading described by the docstring is: under complete randomization,
the count of treated *other* incoming interferers is claimed to have the
hypergeometric laws with draw count C_i including self, and the displayed
ratio-minus-one formula Q with that same C_i.

The visible setting requires a genuine probability design, 0<m<n, uniform
fixed-size assignment, the stated full-cube outcome schedule, self-including
incoming interference, self-excluding T_i, regularity, and meaningful
conditional probabilities and ratios. E and F use n=4,m=2 and the same uniform
six-point design, bounded full-cube outcomes, all marginals 1/2, and the asserted
regularity. E has C_0=2=min(m,n−m), so also satisfies that visible potential
support restriction. Its M_0(0)=1/2, arm probability 1/2, C_0=2, and n−C_0=2
are all positive. F has C_i=1 and T_i=0. Both are genuine candidates under this
reading; canonical conditions remain to be checked after saving this file.

### Junk-value and boundary audit

* `conditionalMean` uses real division and would return zero at a null event.
  Here both conditioning arms have probability 1/2. Thus each conditional mass
  is an ordinary conditional probability.
* The likelihood-ratio denominator M_0(0)=1/2 and the printed-ratio denominator
  H(4,2,2,0)=1/6 are positive. In Q the denominator c=2 and p(N−c)=1 are
  positive. No asserted discrepancy is produced by division by zero.
* For `FixedSizeDesign`, 0<m<n guarantees the binomial denominator is positive.
  All evaluated H denominators are 6, 3, or 4 and are positive.
* In general H is not a correctly extended mass function beyond t≤c:
  c−t truncates at zero and may make impossible counts have nonzero values.
  That convention cannot affect this statement's tables: every table has c=2
  and t∈{0,1,2}; the remaining evaluation has c=1,t=0. Also N≥m at every use,
  so N−m is the ordinary difference. This theorem does not quantify over the
  out-of-support values of H.
* C_i−1 is truncated natural subtraction, but Affects(i,i) always holds.
  Therefore any quantified i implies C_i≥1, and no truncation artifact affects
  the universal counting identity. For n=0 there is no i, so that subcase is
  harmless universal quantification over an empty type; the existential
  counterexamples both have four units.
* Fin-literal indices 0 and 1 have their ordinary values within Fin 4, as do
  0,1,2 within Fin 3. Vector notation is only evaluated on its finite domain.
  No modular numeral wraparound or partial array default occurs.
* At q=4 and s=1, `Real.rpow` is used on absolute values and on k=2; all
  bases and exponents are in their usual domains. Zero absolute outcomes are
  raised to positive powers and give zero. There is no negative-base or
  negative-exponent artifact.
* Function.update is total; it replaces the specified coordinate and gives no
  default behavior. All expectations are finite real sums and every quantity
  exists. No log, sqrt, sInf/sSup, limsup/liminf, or toReal is used here.
* The closure's generated `_proof_1`, `_proof_2`, `_proof_3` declarations
  merely certify numeric base sizes (2,3,4,6 at least two, and 4 nonzero).
  Their reuse from names such as `W1SparseErrors` and `wholeVarianceEstimate`
  does not import those named mathematical predicates or add assumptions.
