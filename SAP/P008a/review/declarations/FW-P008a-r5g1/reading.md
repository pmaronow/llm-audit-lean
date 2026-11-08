# Blind reading

This file was written before opening `claims.json` or `record.json`. I read all five Challenge statements and docstrings, all source declarations listed in their closures, and all 47 distinct generated auxiliary declarations in the closures. The latter were printed in `scratch/BlindClosure.lean` (output in `scratch/BlindClosure.out`): they prove numeral typeclass facts, nonemptiness, finite-index bounds, the probability-law structure obligations, or membership of the four specified nodes in the rectangle. They add no assumptions to the statements.

## SAP.P008a.T1

This is an unconditional conjunction about fixed finite objects; there are no supplied hypotheses.

Let U be the set of all 60-element subsets of {0,...,120}. Let B be the set of unions a ∪ b, where a is a 5-element subset of {0,...,9} and b is a 55-element subset of {10,...,120}. These are Mathlib finsets of finsets of natural numbers. Let o = {0,...,4} ∪ {10,...,64}, and let o' = (o \ {10}) ∪ {5}. For any finite support C of finite subsets, define q_C(z) = 1/|C| if z ∈ C, and zero otherwise, with values in the reals.

The first two groups of conclusions say:

- |U| = choose(121,60), |B| = choose(10,5) choose(111,55), and B is a strict subset of U.
- o belongs to both supports, o' belongs to U and not B; q_U(o), q_B(o), and q_U(o') are positive; q_B(o') = 0.
- The sums of q_U and q_B over their respective supports are each one, and q_U and q_B are different functions on all finite subsets of the naturals.

For the remaining conclusions an assignment is a function {0,1,2,3} → Bool. Its treated count is the natural-number sum of the indicators of `true`. The six enumerated assignments, in index order k = 0,...,5, are 1100, 1010, 1001, 0110, 0101, 0011. The four blocked assignments, in index order l = 0,...,3, are assignments 1,2,3,4 from this list. Both enumerations are injective. For every Boolean assignment z, its treated count is two iff it occurs in the six-element enumeration, and it occurs in the four-element enumeration iff z(0) ≠ z(1) and z(2) ≠ z(3). Assignment 1 is explicitly 1010.

Write b(true)=1 and b(false)=0, as real numbers. For any four-vector y and assignment z the defined contrast is

    C_y(z) = (Σ_i b(z_i)y_i)/2 - (Σ_i (1-b(z_i))y_i)/2.

For every k in the six-element enumeration, the contrasts for y=(0,1,0,1) are (0,-1,0,0,1,0), and those for y=(0,1/3,2/3,1) are (-2/3,-1/3,0,0,1/3,2/3).

A finite law is a real-valued nonnegative mass function with sum one. Its event probability is the finite sum of its masses on the event. The uniform law on a nonempty finite type of size n has mass 1/n at each point. The tail at z for a real statistic T is the inclusive, two-sided event probability Σ_{w: |T(z)| ≤ |T(w)|} q(w). For the common observation 1010 (index 1 under the six-element law, index 0 under the four-element law), the two respective tails are 1/3 and 1/2 for the first y, and 2/3 and 1/2 for the second y. The statement also asserts 1/3 < 1/2 < 2/3.

The docstring describes this as a restricted, fixed-observation demonstration of nonidentification of a reference law; it expressly omits quantification over all original 60-treated observations and a relabelling result.

Junk-value audit: real inverse at zero would make q_C identically zero for an empty C, but the particular supports are nonempty and the statement explicitly proves positive masses and normalization. Uniform laws require nonempty types (here sizes six and four). Every denominator in a contrast is the nonzero real number two. Natural-number finset erasure and intervals have their usual exact set meanings; no truncated numerical subtraction is used. All rational constants are real-valued divisions. Indices are bounded `Fin` indices, so there is no partial lookup or default element. No integrals, logarithms, square roots, extended-real conversions, infima, suprema, or sequence limits occur.

## SAP.P008a.T2

The statement is a conjunction of five independently quantified parts. Finite laws, assignment bits, contrasts, and inclusive absolute-value tails have exactly the finite-sum meanings unfolded above.

1. For every finite type Ω, every normalized nonnegative real mass function Q on Ω, every T:Ω→ℝ, and every δ∈ℝ with 0≤δ≤1, the Q-probability that the Q-inclusive tail of T is at most δ is at most δ. The quantifier order is Ω, its finite-type instance, Q, T, δ, and the two inequalities.
2. For every such Ω and Q, every event A:Ω→Prop with Q(A)>0, every T and every δ∈[0,1], the same conclusion holds under the conditional mass function Q_A(z)=Q(z)/Q(A) on A and zero elsewhere. The order is Ω,Q,A,positivity,T,δ,level bounds.
3. For every natural N, law Q on the Boolean functions on `Fin N`, p∈ℝ with 0<p<1, and hypothesis that Q(z)=Π_i (p if z_i=true else 1-p) for every assignment, and then for every natural M≤N, the probability of treated count M is positive. For every assignment z of count M, Q(z)/Q(count=M)=1/choose(N,M).
4. For every natural N and spatial model P, law Q on assignments, event A of positive Q-probability, finite set D of real radii, and the hypotheses below, followed by any δ∈[0,1], the cumulative statistic has a calibrated conditional inclusive tail and is imputable on the positive conditional support.

A spatial model consists of a subset F of the Euclidean plane `EuclideanSpace ℝ (Fin 2)`, a node s_i∈F for each i∈`Fin N`, a measure ζ on the plane, and Y:Plane→(Fin N→Bool)→ℝ. For i,d define C_i(d)={x∈F:dist(s_i,x)=d}; ν_i,d is ζ restricted to this set; m_i,d is `(ν_i,d(univ)).toReal`; and

    M_i(d,z) = (m_i,d)^(-1) ∫ Y(x,z) dν_i,d(x).

The fourth part assumes: F is measurable; Y(x,z)=Y(x,all-false) for all x∈F and every assignment z; N>0; every circle for i and d∈D has positive real mass and finite extended-real mass; every Y(·,z) is Bochner integrable on every such circle for every assignment z; and every z with A(z) and Q(z)>0 has nonzero treated and control counts. The treated count n_1(z)=Σ_i b(z_i) is real-valued; the control count is the real subtraction N-n_1(z). For an array H_i(z),

    HJ_H(z) = [Σ_i b(z_i)H_i(z)]/n_1(z)
               - [Σ_i (1-b(z_i))H_i(z)]/[N-n_1(z)].

Let S(z)=Σ_{d∈D} HJ_{M(d,·)}(z). The two conclusions are Q_A{z:tail_{Q_A,S}(z)≤δ}≤δ and, for every z with A(z) and Q(z)>0,

    S(z) = Σ_{d∈D} HJ_{i,w ↦ M_i(d,all-false)}(z).

5. The four fixed tail identities and strict inequalities from T1 are repeated: for observation 1010, unrestricted and blocked tails are (1/3,1/2) for (0,1,0,1) and (2/3,1/2) for (0,1/3,2/3,1).

The docstring discloses confinement to finite laws and Euclidean circle averages, positive finite masses, integrability for all assignments, and nonempty conditional arms; it describes imputability of the cumulative statistic on that support and omits documentary/application conclusions.

Junk-value audit: Q(A)>0 excludes division by zero in conditioning. The Bernoulli count event is asserted positive, and choose(N,M)>0 when M≤N. N=0 is allowed in the Bernoulli clause, with its unique empty assignment and count zero; its empty product is one and no invalid quotient arises. An empty Ω cannot carry a finite law because normalization would require 0=1. In the spatial clause, `ENNReal.toReal ∞=0`, zero-mass normalization, and the default zero Bochner integral for a nonintegrable function are all potential hazards of the bare definitions, but the positive/finite-mass and integrability hypotheses exclude them on every evaluated circle. Measurability of F and continuity of distance make those circles measurable. Division by an empty arm is excluded on positive conditional support; possible values off that support carry zero probability. The control subtraction is in ℝ, not truncated natural subtraction. D may be empty, in which case S=0 and the result is the legitimate constant-statistic special case. Negative radii are impossible in a nonempty evaluated D under positive circle mass. No logarithm, square root, real power, extremum, or asymptotic limit occurs.

## SAP.P008a.T3

This is a conjunction about fixed data and a final general conditional-law implication; it has no premise supplying the counterexample. The six-assignment enumeration is the two-of-four enumeration in T1, and its injectivity, exhaustiveness, and index-1 observation 1010 are repeated.

Embed a rational x as the Euclidean point (x,0). The four nodes are s_i=(10i,0), i=0,...,3. The spatial field is the closed rectangle [-1,31]×[-1,1]. For every point x and assignment z the outcome is

    Y(x,z) = Σ_{i=0}^3 [i if dist(x,s_i)≤1 else 0],

so it does not depend on z. The measure is the sum of 24 unit Dirac measures at (10i+k/10,0), i=0,...,3 and k=0,...,5. The five radii are r_j=(j+1)/10, j=0,...,4. Circle restrictions, real circle masses, normalized Bochner averages M_i(r_j,z), real treated/control counts, and the Hajek difference of means have the exact meanings given for T2.

The statement asserts that each closed unit ball around a node is contained in the rectangle; any two such balls for unequal nodes are disjoint; and every one of the 20 node/radius circles has positive finite mass and integrable outcomes for every assignment. It explicitly asserts the sharp null Y(x,z)=Y(x,all-false) for all plane points and all assignments. For every i,j,z the actual circle average is M_i(r_j,z)=i. For every j,k, the Hajek statistic T_j(k) under the kth two-treated assignment equals the kth entry of (-2,-1,0,0,1,2).

For a real array s indexed by `Fin(n+1)`, the percentile definition is the arithmetic formula: h=nq, j=min(toNat(floor(h)),n), g=h-j, and Q7(s,q)=(1-g)s_j+g s_min(j+1,n). It does not sort its input. Here the asserted statistic arrays are already in increasing order, so this is the interpolated type-7 percentile. Being outside (l,u) means the strict event t<l or u<t.

For each j, Q7(T_j,1/40)=-15/8 and Q7(T_j,39/40)=15/8, and the probability under the uniform six-element law of being strictly outside these endpoints is 1/3. For the five-radius sum Σ_j T_j the corresponding percentiles are -75/8 and 75/8, and the rejection probability is also 1/3, greater than the nominal 1/20.

For every finite law Q on all four-node Boolean assignments, if Q(z)=Π_i(1/2) for every assignment (independent fair bits), then Q(count=2)>0 and Q(z)/Q(count=2)=1/6 for every count-two assignment. Finally, for every j and k, single-radius rejection occurs iff k=0 or k=5; the five-radius cumulative statistic is the kth entry of (-10,-5,0,0,5,10); and cumulative rejection occurs iff k=0 or k=5.

The docstring calls this a counterexample to a specified interpolated-percentile level reading, at nominal level 1/20, using a true sharp null and full enumeration.

Junk-value audit: every evaluated circle actually contains one measure atom, so its mass is one; the stated positive/finite-mass and integrability conclusions also expressly exclude `toReal ∞`, zero-circle normalization, and nonintegrable-integral defaults. The spatial model uses a measurable rectangle, finite atomic measure, and bounded Borel indicators of closed balls. All assignments used for the statistic have two treated and two control nodes, so neither Hajek denominator vanishes. Uniform sampling is on a nonempty six-element type. The conditional count event is explicitly positive. The percentile input type always has n+1≥1 entries. `Int.toNat` would clip negative floors to zero, and `min` clips upper indices; for the two probabilities here, h is respectively 1/8 and 39/8, with valid j=0 and j=4 and interpolation fractions in [0,1]. No out-of-range extrapolation or unsorted input is used. The cumulative array is likewise sorted. Rational-to-real casts and index-to-natural/real casts are exact; there is no truncated subtraction, partial function, or undefined geometric operation.

## SAP.P008a.T4

This is a conjunction of six parts. Assignment, bit, real arm counts, contrast, finite law, and inclusive tail are unfolded in T1–T2. The six assignments have order 1100,1010,1001,0110,0101,0011. Complementation of their indices is the permutation k↦5-k, given explicitly by the vector (5,4,3,2,1,0).

1. For every real four-vector y and every k in `Fin 6`, the complement index differs from k, its assignment is the pointwise Boolean complement, both arm counts are two, and the Hajek statistic for the assignment-independent outcomes y equals the half-treated-sum minus half-control-sum contrast.
2. For every natural J, every a:`Fin J`→ℝ and m:`Fin J`→(`Fin 4`→ℝ), define S(k)=Σ_j a_j C_{m_j}(z_k). For every k, S(complement(k))=-S(k), the uniform-six inclusive absolute tail is at least 1/3, and this tail is not ≤1/20. The order is J,a,m, then the pointwise k quantifiers in the two conclusions.
3. For every nonempty finite subset R of `Fin 6`, its uniform-six probability is |R|/6, at least 1/6 and strictly greater than 1/20. This concerns deterministic rejection sets.
4. For every finite Ω, law Q on Ω, statistic T:Ω→ℝ, and δ∈[0,1], Q{z:tail_{Q,T}(z)≤δ}≤δ.
5. For every finite Ω, law Q, natural B, and law R on arrays z:`Fin(B+1)`→Ω, assume, for every entire array z, R(z)=Π_{k=0}^B Q(z_k). Then for every S:Ω→ℝ and δ∈[0,1],

       R{z: [1 + #{b∈Fin B : |S(z_0)|≤|S(z_(b+1))|}]/(B+1) ≤ δ} ≤ δ.

   Thus the observed coordinate and all B reference coordinates are independent draws from Q. Equality is counted in the tail and the observed coordinate contributes the added one. The law R and its product-mass hypothesis occur before S and δ.
6. The real arithmetic identity 1491/1000+1550/1000+1550/1000+1691/1000+1714/1000=1999/250 (7.996).

The docstring describes the complementation/tail and rejection-set obstructions, exact and IID calibration, and displayed-estimate sum. It discloses omission of an actual unrounded observed statistic, the particular reconstructed six cumulative values and their observed tail, and a repetition of T3's percentile example.

Junk-value audit: the defined contrast denominator is two, and Hajek denominators on all six assignments are proved to be two. B+1 is always a positive natural number and is cast to ℝ before division. The b.succ index lies in `Fin(B+1)`. B=0 is allowed, giving a tail estimate identically one, a legitimate no-reference-draw special case. J=0 gives S=0 and tail one; other J are unrestricted and nonzero contrasts are available. Empty R is excluded from the rejection-set assertion. An empty Ω cannot satisfy finite-law normalization. All numerical sums use real division, not natural division. There are no integrals, extended-real conversions, percentiles, unbounded extrema, or limit operations in this statement.

## SAP.P008a.T5

The first conclusions concern fixed two-node data. Four assignments enumerate (00,01,10,11) bijectively as functions `Fin 2`→Bool. Their index carries the uniform law with mass 1/4. The field is the rational finset F={-1,0,1,2,3}, the nodes are s_0=0,s_1=2, and

    Y(x,z) = 1_{|x|≤1} b(z_0) + 1_{|x-2|≤1} b(z_1).

For a rational field, node, index i, and rational radius d, the defined line circle is the field filtered by |x-s_i|=d, and its mean is the real sum of Y on this finite circle divided by its cardinality. At radius one the circles are {-1,1} and {1,3}; thus M_0(z)=b(z_0)+b(z_1)/2 and M_1(z)=b(z_1)+b(z_0)/2. Both nodes belong to F.

Expectation under a finite law is Σ_z q(z)f(z); covariance is Σ_z q(z)(f(z)-Ef)(g(z)-Eg); variance is covariance with itself. `Function.update z i b` overwrites the ith treatment by b. For both nodes the expectations of M_i with its own treatment overwritten to true and false are 5/4 and 1/4, respectively.

For any array of circle outcomes M and real centering constants m_1,m_0, the defined linearization contribution is

    φ_i(z)=2 b(z_i)(M_i(z)-m_1) - 2(1-b(z_i))(M_i(z)-m_0).

Using m_1=5/4,m_0=1/4, for every i and every one of the four assignments this equals (1/2)(2b(z_0)-1)(2b(z_1)-1). Each contribution has mean zero and variance 1/4; the covariance of contributions 0 and 1 is 1/4. The variance of (φ_0+φ_1)/2 is 1/4. The diagonal-only value (1/4+1/4)/4 is 1/8<1/4. Embedding rational nodes as (s_i,0) in the Euclidean plane, the explicit covariance sum

    (1/2)^2 Σ_i Σ_j 1_{dist(s_i,s_j)≤1} Cov(φ_i,φ_j)

is 1/8, whereas Var((1/2)Σ_i φ_i)=1/4. The mean of the two own-treatment override differences is one.

For replication, let M be a natural number and index nodes by I_M=`Fin M`×`Fin 2`. Node (g,c) is s_(g,c)=6g+2c, a rational. The field F_M is the image of `(g,k)∈Fin M×Fin 5` under 6g+k-1. Assignments are Boolean functions on I_M, and the law is uniform on the entire function type, hence all 2M bits are independent and fair. Define

    Y_M(x,z)=Σ_{i∈I_M} 1_{|x-s_i|≤1} b(z_i),
    C_i={x∈F_M: |x-s_i|=1},
    M_i(z)=Σ_{x∈C_i}Y_M(x,z)/|C_i|,
    φ_i(z)=2b(z_i)(M_i(z)-5/4)-2(1-b(z_i))(M_i(z)-1/4),
    ψ_(g,c)(z)=(1/2)(2b(z_(g,0))-1)(2b(z_(g,1))-1).

The statement's remaining independent universal clauses, in source order, are:

- For every M>0: all nodes lie in F_M; for every x∈F_M and assignment z, 0≤Y_M(x,z)≤2; every C_i={s_i-1,s_i+1}; and for every g,z the two circle means are b(z_(g,0))+b(z_(g,1))/2 and b(z_(g,1))+b(z_(g,0))/2. For every i,z, φ_i(z)=ψ_i(z). Under the uniform assignment law, Var((2M)^(-1)Σ_i φ_i)=1/[2(2M)], whereas (2M)^(-2)Σ_i Var(φ_i)=1/[4(2M)].
- For every M>0, then every i and b∈Bool, E[M_i(update(z,i,b))]=b(b)+1/4 (where the first b in b(b) denotes the real bit indicator).
- For every natural M, index i∈I_M, and rational x, x∈C_i iff x∈F_M and dist((s_i,0),(x,0))=1.
- For every natural M and distinct i,j∈I_M, their planar distance is at least two.
- For every M>0, index i, and two assignments z,z', if both bits at (i.first,0) and (i.first,1) agree, then M_i(z)=M_i(z').
- For every M>0, (2M)^(-2)Σ_iΣ_j 1_{dist(s_i,s_j)≤1} Cov(φ_i,φ_j)=1/[4(2M)].

The docstring describes a counterexample to sufficiency of a cutoff equal to the outcome-effect range, distinguishes that reading from an instruction to cover contribution dependence, disclaims coverage conclusions for specific printed intervals, and says that an optional asymptotic consequence is not asserted.

Junk-value audit: the bare counting mean returns zero for an empty circle through real division by zero. The fixed circles are explicitly two-element sets. In the replicated construction with M>0 every circle is explicitly the two distinct endpoints; statements without M>0 quantify over an index in `Fin M` and thus are vacuous only for the ordinary empty-node case M=0. Every variance/cutoff normalization uses M>0, so 2M is nonzero as a real number. Uniform laws are on nonempty four-element or Boolean-function types; the latter remains nonempty even for zero indices. The subtraction 6g+k-1 takes place in ℚ, not ℕ; there is no natural truncation at the leftmost field point -1. All other count and index casts are exact. The finite rational field, real outcomes, and finite assignment law make all means and moments finite. Euclidean distances are ordinary total metric distances. No `toReal`, Bochner integral, logarithm, square root, real power outside its domain, extremum, or limit is used by this declaration.
