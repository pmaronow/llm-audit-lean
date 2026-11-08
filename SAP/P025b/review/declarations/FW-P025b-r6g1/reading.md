# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. This reads the current declarations and their dependencies,
without deciding whether their descriptions match the paper.

## Mathematical notation used below

All sums below are finite sums in the real numbers, unless a sum of natural
numbers is expressly indicated. `Fin n` means the integers from 0 through n−1.
Vector notation lists coordinates in that order. The following are mathematical
abbreviations, fully expanded here, rather than additional assumptions:

* For a finite index set I and real vectors y,a,w, put
  R(y,a,w) = (Σᵢ aᵢwᵢyᵢ)/(Σᵢ aᵢwᵢ).
* B(α,β) = {w : I → ℝ | ∀i, 1/β ≤ wᵢ ≤ 1/α}.
  A(y,a;α,β) = {R(y,a,w) | w ∈ B(α,β)}.
  E₋(y,a;α,β) = inf A(y,a;α,β) and
  E₊(y,a;α,β) = sup A(y,a;α,β), using the conditionally complete
  lattice operations on ℝ.
* For y,a indexed by `Fin n`, let uᵏᵢ = 1 if i<k and γ otherwise,
  and lᵏᵢ = γ if i<k and 1 otherwise. Write
  Uₖ(y,a,γ) = R(y,a,uᵏ), Lₖ(y,a,γ) = R(y,a,lᵏ).
  The upper cut k is the least element of
  {j ∈ Fin n | Uⱼ(y,a,γ) ≤ yⱼ}. Separation means
  ∀k ∈ Fin n, yₖ ≠ Uₖ(y,a,γ) and yₖ ≠ Lₖ(y,a,γ).
* A finite design d consists of a finite type K, a subset S(t) of a population
  I for each t∈K, and real p(t)≥0 with Σₜp(t)=1. Its expectation is the
  finite sum Σₜp(t)X(t); πᵢ = Σₜp(t)1{i∈S(t)} is its inclusion probability.
  Given c:I→Fin J, Mⱼ = Σ_{i:c(i)=j}πᵢ and
  Cⱼ(t) = Σᵢ1{c(i)=j and i∈S(t)}.
* For a measurable finite K, P is the countable product measure on K^ℕ
  of the probability measure whose atom t has mass `ENNReal.ofReal(p(t))`.
  Thus its coordinates are iid with that finite law when singletons are
  measurable. An explicit iid assertion below means `iIndepFun` of all
  coordinate projections together with equality of each marginal measure to
  that finite law. Independence means that finite intersections of inverse
  images of measurable sets have product probabilities.
* At replicate count h and path ω∈K^ℕ the pooled index set is Fin h × I,
  a_{r,i}=1{i∈S(ω(r))}, and y_{r,i}=y_{c(i)}. Pooled lower and upper
  endpoints are respectively E₋ and E₊ for those vectors. Pooled nonemptiness
  is ∃r<h, S(ω(r))≠∅. Occurrences of the same unit in different replicates
  are distinct indices and may receive separate weights.
* For J classes, m:Fin J→ℕ, and real y, the class population mean is
  H(y,m) = (Σⱼ mⱼyⱼ)/(Σⱼ mⱼ), with natural counts cast to ℝ.
  Absolute compatibility of a real mass vector b means
  ∀j, mⱼ>0 and αmⱼ≤bⱼ≤βmⱼ.
  Share compatibility for q means that there exists a real T>0 such that
  ∀j, mⱼ>0 and αmⱼ≤Tqⱼ≤βmⱼ.
  V(y,q;α,β) is the set of H(y,m) for share-compatible natural count
  vectors. Vabs(y,b;α,β) instead uses absolute compatibility.
  Vabs,N additionally requires the natural sum Σⱼmⱼ=N.
  Vshares,N uses share compatibility and that same size requirement.
* The proportion region Q(q,γ) consists of real r with all rⱼ≥0,
  Σⱼrⱼ=1, and ∀j,k, rⱼqₖ≤γrₖqⱼ.
  P(m)ⱼ=mⱼ/(Σₖmₖ); Pq(W)ⱼ=Wⱼqⱼ/(ΣₖWₖqₖ).
  A rational vector means ∀j, ∃x∈ℚ with its real cast equal to rⱼ.

These definitions cover all the non-proof declarations in the supplied closures.
The generated declarations were also read through `#print` in
`scratch/ClosurePrint.lean` (output `scratch/ClosurePrint.log`). They are numeric
index instances, finite-law normalization/nonnegativity proofs, the outer-measure
instance, and the enumeration/completeness proofs for the finite subtype of quota
draws. `FiniteDesign.mk` and its sample/probability projections are the constructor
and ordinary projections of the structure just described; they add no hidden
condition. The structure's nonnegativity and normalization fields have been
included above.

## SAP.P025b.T12

There are no external parameters or hypotheses. This is a conjunction about a
specified two-unit census: I=Fin 2, K=Fin 1, S(t)=I, p(t)=1, y=(0,1),
one class per unit (c=id), α=β=1, hence γ=1. The description says this
refutes printed boundary proof steps, two stopping rules, and two Supplement
equivalences, while preserving the optimizers and endpoints.

The complete conjunction is:

1. Each unit has πᵢ=1; y=(0,1) is nondecreasing; for every natural k,
   uᵏ is the constant vector 1. Also 1/1=1.
2. U₀=U₁=U₂=1/2 for a=(1,1), γ=1. The increment U₁−U₀≤0,
   but U₀≤y₀ is false. The least k∈Fin 2 for which Uₖ≥Uₖ₊₁
   is 0, whereas the upper cut (least k with Uₖ≤yₖ) is 1.
3. The literal expressions 0·0−0+1·1·(0−1) and
   0−0·1+1·1·(0−1) both equal −1.
   The ratio R((0,1),(1,1),(1,1)) is not strictly greater than itself.
4. For every real w:Fin 2→ℝ, w∈B(1,1) iff w=(1,1).
   A((0,1),(1,1);1,1)={1/2}.
5. The ordinary population mean (0+1)/2 and H((0,1),(1,1)) both
   equal 1/2. For every class j, Mⱼ=1; for every class j and census
   outcome t, Cⱼ(t)=1; and 1/Mⱼ=1.
6. Both E₋ and E₊ are 1/2, both for a=(1,1) and for a=M.
   The physical vector (1/1)u¹=(1,1), and (0+1·1)/(1+1)=1/2.
7. Define F(c₁,c₂,p,q,u,v,x,z) =
   (c₁+xpu+zqv)/(c₂+xp+zq). Then F(0,0,1,1,0,1,1,1)=1/2.
   Each of the following biconditionals is false:
   F(0,0,1,1,0,1,1/1,1/1)>F(0,0,1,1,0,1,1/1,1/1)
   iff 0·0−0+1·1·(0−1)<0;
   and that same strict comparison iff 0−0·1+1·1·(0−1)<0.

Junk conventions: real division is total with x/0=0, and real infimum/supremum
are total even for empty or unbounded sets. Here every displayed denominator is
1 or 2; Mⱼ=1; B is a singleton and its image is a bounded nonempty singleton.
Thus neither convention supplies a substantive assertion. The k=2 weight vector
has all indices in its prefix, and is defined by an ordinary comparison; no
out-of-range vector evaluation occurs in U₂. Cuts quantify only over Fin 2.
All vectors use inhabited finite types and legitimate numeral indices. There is
no natural subtraction, logarithm, square root, real power, integral, `toReal`,
limsup/liminf, or choice/default value of a partial function.

## SAP.P025b.T13

The quantifier order and hypotheses are: for all naturals N,J with N>0,J>0;
for every finite measurable type K with measurable singletons; for every finite
design d on Fin N with outcome type K; for every c:Fin N→Fin J that is
surjective; for every strictly increasing real y:Fin J→ℝ; and for every
real α,β satisfying 0<α≤β≤1 and
∀i, α≤πᵢ≤β, the following two conclusions hold.

The first conclusion holds P-almost surely, with all three parts holding on the
same full-measure set of paths ω:

* For all sufficiently large natural h, ∃r<h with S(ω(r)) nonempty.
* As h→∞, the pooled lower endpoint tends to E₋(y,M;α,β).
* As h→∞, the pooled upper endpoint tends to E₊(y,M;α,β).

The second conclusion is an implication: if
∀k∈Fin J, yₖ≠Uₖ(y,M,β/α) and yₖ≠Lₖ(y,M,β/α), then that
same almost-sure three-part conclusion holds. It is conjoined with the first
unconditional conclusion, not an additional hypothesis on it. Convergence means
Mathlib `Tendsto` from the natural atTop filter to the usual real neighborhood
filter; eventually means that some natural threshold works for every larger h.
The description calls this independent Brewer replication and emphasizes that
separation is unnecessary.

Junk conventions: R and the endpoints are total for h=0 or an empty pooled
sample. In that case all coefficients are zero and A={0}, so the endpoints
are 0. Almost-sure eventual nonemptiness explicitly removes this finite-prefix
issue from convergence. On a nonempty pooled sample the denominator is positive
for every w∈B. Surjectivity, positive α, and the unit inclusion bounds imply
every Mⱼ>0, so the limiting ratios also have positive denominators and bounded
nonempty attainable sets. β/α and the reciprocal bounds have positive
denominators. Finite sums over an empty outcome type cannot satisfy Σp=1;
thus the design itself excludes that case. N,J are expressly positive. The
finite probabilities are nonnegative, so `ENNReal.ofReal` does not truncate
negative masses, and their sum is 1. The infinite product is an actual probability
measure, not a zero-measure device. No Bochner integrals, infinite real sums,
`toReal`, `limsup`/`liminf`, logarithms/powers, truncated subtraction, or partial
function defaults appear in this closure.

## SAP.P025b.T14

There are no external parameters or hypotheses. The fixed population is
Fin 3 × Fin 2, two units in each class j. The class value vector is
y=(0,2,3), and c(j,b)=j. The outcome type is Fin 2 × Fin 2 × Fin 2;
an outcome t=(b₀,b₁,b₂) selects exactly {(0,b₀),(1,b₁),(2,b₂)}
and has probability 1/8. Here α=1/4, β=1/2, γ=2. The description
calls this an independent-replication counterexample to necessity of separation.

The complete conjunction states:

1. Every πᵢ=1/2. Every Mⱼ=1. For every outcome t and class j,
   Cⱼ(t)=1. U₁(y,(1,1,1),2)=U₂(y,(1,1,1),2)=2.
2. A(y,(1,1,1);1/4,1/2) has least element 5/4 and greatest
   element 2. For every path ω and every natural h>0, the pooled
   sample is nonempty. The unit inclusion bounds [1/4,1/2] hold.
3. Separation at (y,M,2) fails. E₋(y,M;1/4,1/2)=5/4 and
   E₊(y,M;1/4,1/2)=2. For every path and every h>0 the
   corresponding pooled endpoints are exactly 5/4 and 2. For every path
   both endpoint sequences converge to those numbers.
4. Under the countable product law of this design, all coordinate draws are
   independent and each has the finite 1/8 law.
5. For every W:Fin 3→ℝ with 2≤Wⱼ≤4, put
   D=W₀+W₁+W₂ and A=2W₁+3W₂. Then D>0,
   4A−5D=3(W₁−2)+7(W₂−2)+5(4−W₀)≥0,
   2D−A=2(W₀−2)+(4−W₂)≥0, and 5/4≤A/D≤2.
   R(y,(1,1,1),(4,2,2))=5/4;
   R(y,(1,1,1),(2,4,4))=R(y,(1,1,1),(2,2,4))=2.
6. Every class contains exactly two units. For every natural h>0 and every
   path ω, Σ_{r<h}Cⱼ(ω(r))=h for every j.
7. In that order of quantifiers, for every real weight vector w on
   Fin h × (Fin 3 × Fin 2) in [2,4], define
   Aⱼ=Σ_{r<h}w(r,(j,bⱼ(ω(r)))). Then 2h≤Aⱼ≤4h for every j,
   A₀+A₁+A₂>0, and the pooled ratio equals
   (2A₁+3A₂)/(A₀+A₁+A₂)=R(y,(1,1,1),(Aⱼ/h)ⱼ).
   Moreover every Aⱼ/h lies in [2,4].
8. For every W∈[2,4]^3 there exists w∈[2,4] on that pooled
   index type such that Aⱼ/h=Wⱼ for every j, with A computed from
   that w and the already quantified h,ω.

Junk conventions: h=0 endpoints have the total value 0 but all exact pooled
formula and normalization statements require h>0. All displayed class and
sample denominators are strictly positive; even the unnormalized D≥6.
The attainable sets are compact nonempty images of positive-weight boxes,
so their real infima/suprema are ordinary extrema. Probability conversion
preserves 1/8, and the iid law has total mass 1. No empty index, bad numeral
cast, natural subtraction, nonintegrable integral, extended-real conversion,
logarithm/power, limsup/liminf, or partial function default contributes.

## SAP.P025b.T15

This theorem conjoins five blocks. The description calls it shares-only
sharpness with unrestricted finite population size, plus rational attainment,
compatibility, design realization, positive scaling, integer calibration, and
failure of sharpness when richer information is retained.

The main block has quantifiers, in order: all natural J>0; all real vectors
y,q on Fin J with y strictly increasing, qⱼ>0 for every j, and Σq=1;
all reals 0<α≤β≤1; and the hypothesis that at least one natural vector
m is share-compatible (there is T>0 with mⱼ>0 and
αmⱼ≤Tqⱼ≤βmⱼ). The conclusions, jointly, are:

1. For every natural vector m and real vector b, if bⱼ>0 for every j
   and m is absolutely compatible with b, then
   (mⱼ/bⱼ)ⱼ∈B(α,β) and
   R(y,b,(mⱼ/bⱼ)ⱼ)=H(y,m).
2. For every share-compatible m,
   E₋(y,q;α,β)≤H(y,m)≤E₊(y,q;α,β).
   These endpoints are respectively a greatest lower bound and a least upper
   bound of V(y,q;α,β); these predicates specify genuine bounds and their
   universal optimality, not just equalities to totalized infimum operations.
3. {Pq(W):W∈B(α,β)}=Q(q,β/α).
   The set {Σrⱼyⱼ:r∈Q(q,β/α)} has least and greatest elements
   E₋ and E₊ respectively.
4. For every real vector r, there exists a share-compatible natural vector
   m with P(m)=r iff r∈Q(q,β/α) and r is rational in every
   coordinate. Each endpoint belongs to V iff there is such a rational
   feasible r with Σrⱼyⱼ equal to that endpoint.
5. For all real b and natural m, absolute compatibility is equivalent to
   ∀j, mⱼ>0 and bⱼ/β≤mⱼ≤bⱼ/α.
6. For all positive real mass vectors b and all absolutely compatible m,
   E₋(y,b;α,β)≤H(y,m)≤E₊(y,b;α,β).
7. For all real b, natural N, and real v, v∈Vabs,N iff there
   exists a natural vector m with all mⱼ>0,
   bⱼ/β≤mⱼ≤bⱼ/α, natural sum Σm=N, and H(y,m)=v.
8. For all real b and natural m, absolute compatibility iff all mⱼ>0
   and, for each j, there exists a vector π:Fin(mⱼ)→ℝ with
   α≤πᵢ≤β and Σπᵢ=bⱼ.

The second block independently quantifies over J>0, qⱼ>0, Σq=1,
and 0<α≤β≤1. If β/α>1, a share-compatible m exists.
If β/α=1, existence of such m is equivalent to rationality of every
coordinate of q. This block has no prior compatibility-existence premise.

The third block independently quantifies over every natural J (including zero),
all 0<α≤β≤1, real b and natural m. Absolute compatibility iff
all mⱼ>0 and there exists a finite design with population
I={(j,i):j∈Fin J, i∈Fin(mⱼ)}, outcome type I→Bool,
all unit inclusion probabilities in [α,β], and Σ_{i in class j}πᵢ=bⱼ
for every j. Sample size is not fixed by this definition. The design includes
nonnegative probabilities summing to 1.

The fourth block independently quantifies over J>0, arbitrary real y,
positive q (without requiring Σq=1 or sorted y), all reals α,β,T
with 0<α≤β≤1 and T>0. For every W∈B(α,β),
R(y,Tq,W)=R(y,q,W); the two attainable sets are equal; and their
lower and upper endpoints are equal respectively.

The fifth block is concrete and has no hypotheses:
Vabs((0,1),(2/3,4/3);1/2,3/4)={2/3}, its continuous
endpoints are 4/7 and 3/4;
Vshares,3((0,1),(1/3,2/3);1/2,3/4)={2/3}, its
continuous endpoints are again 4/7 and 3/4; and 4/7<2/3<3/4.

Junk conventions: total real division and real infimum/supremum are the only
potentially relevant general defaults. In the main block J>0, positive q,
positive class counts, and positive weight bounds make every objective and
normalization denominator positive. The compatibility premise makes V nonempty;
it is an actual hypothesis, with independent existence criteria in the second
block. V is bounded by the smallest/largest outcome. No sharpness is asserted
for an empty V. Positive masses and counts protect each mⱼ/bⱼ.
The scaling block also has positive denominators. Known-size characterizations
allow an empty compatible set, including impossible N, but assert only set
membership equivalences then, not an artificial endpoint. In the design block
J=0 means an empty population and a singleton Boolean-function outcome type;
an empty sample with probability 1 is possible, and no mean is taken there.
All natural casts preserve positive counts and sums. The concrete sets in the
last block are nonempty singletons. No truncated subtraction, `Real.log`,
`sqrt`, `rpow`, Bochner integral, `toReal`, limsup/liminf, or partial default
is present.

## SAP.P025b.T16

There are no external parameters or hypotheses. The description explicitly
limits its refutation to a reading that retains absolute totals (and also size
in the second example); it says the outer bounds and shares-only sharpness
remain valid. Its complete conjunction comprises:

1. In the three-unit design, K=Fin 3, S(t)=Fin 3 minus {t}, and
   p(t)=1/3. Outcomes are (0,1,1), with class labels (0,1,1).
   Each unit has inclusion probability 2/3, class totals are (2/3,4/3),
   and the population mean is 2/3.
2. For every natural m:Fin 2→ℕ, absolute compatibility with
   b=(2/3,4/3), α=1/2,β=3/4 holds iff m=(1,2).
   H((0,1),(1,2))=2/3;
   L₁((0,1),b,3/2)=4/7 and U₁((0,1),b,3/2)=3/4.
   The gaps are 2/3−4/7=2/21 and 3/4−2/3=1/12;
   4/7<2/3<3/4; and separation holds on Fin 2.
3. Vabs for these data is {2/3}; 4/7 is not its greatest lower bound
   and 3/4 is not its least upper bound.
4. For every natural m, absolute compatibility with b=(50,100),
   α=1/10,β=1/5 together with m₀+m₁=1000 iff
   m₀+m₁=1000 and 500≤m₁≤750.
   For every natural k with 500≤k≤750, (1000−k,k) is
   absolutely compatible. H((0,1),(250,750))=3/4.
   L₁((0,1),b,2)=1/2 and U₁((0,1),b,2)=4/5;
   4/5−3/4=1/20 and 3/4<4/5.
5. The known-size compatible mean set is exactly
   {k/1000:k∈ℕ,500≤k≤750}. Its least element is 1/2
   and greatest element is 3/4. E₊((0,1),b;1/10,1/5)−3/4=1/20.
6. The continuous attainable sets for the first and second examples have
   least/greatest elements (4/7,3/4) and (1/2,4/5) respectively.
7. The omit-one design's coordinate draws under its infinite product law
   are independent and each has the uniform finite law.
8. The physical ratios at b=(2/3,4/3), w=(4/3,2) and
   w=(2,4/3) are 3/4 and 4/7 respectively. At b=(50,100),
   w=(5,10) and w=(10,5) they are 4/5 and 1/2.
   U₀((0,1),(2/3,4/3),3/2)=
   L₀((0,1),(2/3,4/3),3/2)=2/3.
9. For every natural vector m, first-example absolute compatibility iff
   all mⱼ>0 and 8/9≤m₀≤4/3 and 16/9≤m₁≤8/3.
   Second-example absolute compatibility iff all mⱼ>0 and
   250≤m₀≤500 and 500≤m₁≤1000.
10. For every natural k with 500≤k≤750 there exists a finite design
    on the disjoint union Fin(1000−k) ⊕ Fin k. Its outcome type is
    the product of the set of 50-element subsets of Fin(1000−k)
    and the set of 100-element subsets of Fin k, each with its finite
    enumeration and full discrete measurable structure. For every outcome
    (s,t) the sample is their disjoint union; its probability is
    [1/(number of 50-subsets)]·[1/(number of 100-subsets)].
    Every left unit has probability 50/(1000−k), every right unit has
    probability 100/k; all these probabilities lie in [1/10,1/5].
    Class totals (left=0,right=1) are exactly (50,100). Every sample
    has size 150. The countably replicated draws are independent with
    this finite law. The existential design follows k and its two inequalities.
11. H((0,1),(500,500))=1/2.
12. For all absolutely compatible m, first-example means lie in
    [4/7,3/4], and second-example means lie in [1/2,4/5].
    For shares q=(1/3,2/3) without a fixed size, V has greatest
    lower/least upper bounds (4/7,3/4) at α=1/2,β=3/4,
    and (1/2,4/5) at α=1/10,β=1/5.

Junk conventions: real division and total infimum/supremum are harmless here:
all masses, counts, optimizer denominators, and feasible-set bounds are
positive. The quota-draw definition is total even if the quota exceeds N,
when its finite subtype is empty and its reciprocal cardinal is 1/0=0.
The theorem invokes its existence assertion only when 500≤k≤750;
then 250≤1000−k≤500 and 500≤k≤750, so both quota types
are nonempty and all reciprocal cardinals are positive and finite.
`1000−k` is truncated natural subtraction, but k≤750 prevents truncation.
The fixed-size set is nonempty (k=500 and k=750 are admissible) and bounded;
the singleton example is nonempty. All Fin 2/Fin 3 literals are valid indices;
casts to real numbers are exact. All design probabilities normalize to 1,
and iid is under a probability measure. There are no integrals, `toReal`,
logarithms/square roots/real powers, limsup/liminf, or partial-function defaults.
