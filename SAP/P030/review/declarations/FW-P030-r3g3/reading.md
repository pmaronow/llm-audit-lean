# Blind reading

This file was written before opening `claims.json` or `record.json`. The source statements, their docstrings, and every entry in `closure.json` were inspected. Source line references below use the original files. The 39 structure/projection/constructor and generated helper declarations needing elaborated inspection were printed in `scratch/BlindClosure.lean`; its successful output is in `scratch/BlindClosure.log`. In particular, the helpers attached to unrelated-looking names such as `fiveX`, `printedReject`, `TableRankDetails`, and `T5WholeStatement` are only numeral nonzeroness/`AtLeastTwo` instances. Other helper types establish the index bound for `tableTreatment`, that each `tenFixed` index has fixed indicator true, or normalization/nonnegativity of a uniform finite law. They add no substantive assumptions.

## SAP.P030.T11

Sources: `Challenge/Part1.lean:50–52`, `Defs/Part6.lean:10–26`. The theorem asserts the conjunction of three propositions, without global hypotheses.

1. For every type A with decidable equality, and every four finite subsets U, F, C, T of A, if U = (F ∪ C) ∪ T and F, C, T are pairwise disjoint, then both |U| = |F| + |C| + |T| and it is not the case that the four cardinalities are simultaneously (344056, 114629, 191228, 38198). The equality of sets and three disjointness assumptions precede both conclusions. There is no probabilistic or empirical assumption connecting these arbitrary sets to a particular dataset.
2. In the natural numbers, 114629 + 191228 + 38198 = 344055, 344055 ≠ 344056, and 344056 − 191228 − 38198 = 114630.
3. For every N, F, C, T in the natural numbers, the following are equivalent: (a) N = F + C + T and exactly one entry of (N, F, C, T) differs from the printed quadruple (344056, 114629, 191228, 38198); (b) the quadruple is exactly one of (344055,114629,191228,38198), (344056,114630,191228,38198), (344056,114629,191229,38198), (344056,114629,191228,38199). “Exactly one” is expanded in the source as four disjuncts, each changing one entry and fixing the other three.

No other SAP definition occurs after unfolding `T11Statement`.

Junk-value/domain audit: the subtraction in item 2 is truncated natural subtraction, associated to the left. Here 344056 ≥ 191228 and 344056 − 191228 ≥ 38198, so no truncation occurs. Cardinalities and sums are exact natural numbers with no machine overflow. Empty sets and even an empty ambient type are permitted and make the cardinality identity meaningful; the set hypotheses have many nonempty models. There is no division, root, logarithm, power with nonintegral exponent, integral, extended-real conversion, infimum, limit, or partial function.

## SAP.P030.T12

Sources: `Challenge/Part1.lean:54–58`, `Defs/Part6.lean:28–42`, and the listed definitions in `Defs/Part1.lean`.

Quantification, in order: for every natural N, finite set Ω of functions z : {0,…,N−1} → {false,true}, fixed-indicator function S on the same unit type, assignment a, proof that

K = {z ∈ Ω : for every i with S(i)=true, z(i)=a(i)}

is nonempty, real potential-outcome function Y(i,z), and real statistic function g(y,z), where y is a function from {i : S(i)=true} to R, assume the following disjunction:

- for every unit i and z,z′ ∈ Ω, z(i)=z′(i) implies Y(i,z)=Y(i,z′); or
- for every fixed unit i and z,z′ ∈ K, Y(i,z)=Y(i,z′).

Define t(z)=g((Y(i,z)) over fixed i,z), and r(z,w)=g((Y(i,z)) over fixed i,w). Let μ be the finite uniform law on K: its explicit support is K and each assignment in K has mass 1/|K|. A finite law in this unit is a finite support together with a real-valued mass function, nonnegative on that support, whose sum on that support is one. Its event probability is the sum of these masses over the support satisfying the event; masses outside the explicit support are ignored. Define

L(x) = |{w ∈ K : t(w) ≤ x}| / |K|, and p(z)=L(t(z)).

The conclusion is the conjunction of:

1. For all z ∈ K and w ∈ K, r(z,w)=t(w). This states that the observed fixed outcomes can be used for every reference assignment.
2. For every z ∈ K, the sum defining the μ-probability of t(w) ≤ t(z) equals its assignment-count ratio |{w ∈ K : t(w)≤t(z)}|/|K|.
3. For every real u with 0≤u≤1, |{z ∈ K : p(z)≤u}|/|K| ≤ u.
4. For every z ∈ K, |{w ∈ K : p(w)≤p(z)}|/|K| = p(z).
5. For every real u (without a [0,1] restriction), q=|{z ∈ K : p(z)≤u}|/|K| is a greatest element of the real set {0} ∪ {p : there is z ∈ K with p=p(z) and p≤u}. `IsGreatest` means q belongs to this set and every member is ≤q. Thus the explicit sentinel 0 is included even when u<0, when the conclusion says q=0. For u≥1, it says q=1.

All probabilities and tails above are inclusive (≤); assignments, rather than distinct statistic values, carry equal mass. The statement does not require a∈Ω, only that its fixed-treatment event has a nonempty intersection with Ω. It makes no independence assumption. The docstring describes uniform conditional p-values, observed-data imputation, a counting formula, super-uniformity, exactness at attainable levels, and the greatest-attainable-level formula.

Junk-value/domain audit: cardinality casts from natural numbers to R are exact. Uniform probability is defined as a real quotient and would give 0 on an empty support because real division by zero is totalized to zero; the explicit nonemptiness proof excludes that case here and is also required by the uniform-law constructor. The mass outside K is also defined as 1/|K|, but event probabilities sum only on K, so it contributes nothing. A `FiniteLaw` cannot have empty support since the empty sum is zero and its total is one. Finite sums of real-valued functions are always finite. N=0 and an empty fixed-unit subtype are allowed; assignments and input vectors then have their usual unique empty-function values, and g still has a well-defined real output. This is a meaningful singleton experiment, not an undefined expectation. The maximum set in item 5 is nonempty because 0 is expressly adjoined, and bounded because all p-values lie in [0,1]; it uses `IsGreatest`, not a default-valued `sSup`. No Bochner integral, measurability completion, infinity conversion, logarithm, root, limit, or partial lookup occurs.

## SAP.P030.T13

Sources: `Challenge/Part1.lean:60–63`, `Defs/Part6.lean:44–61`, `Defs/Part3.lean:20–26`, and `Defs/Part1.lean:11,16`.

For every natural N followed by every natural M, assume N≥2 and M≤N. Then, for every i in {0,…,N−1} and every finite neighbor set B in that unit type, assume i∉B. Let

- K be all Boolean assignments with exactly M true coordinates;
- K1={z ∈ K : z(i)=true} and K0={z ∈ K : z(i)=false};
- X_B(z)=sum over j∈B of the real number 1 if z(j)=true and 0 otherwise;
- E=(sum over z∈K of X_B(z))/|K|, and E1,E0 the corresponding sum/cardinality expressions on K1,K0.

The conjunction concluded is:

1. K is nonempty; if 1≤M then K1 is nonempty; if M≤N−1 then K0 is nonempty.
2. E=|B|M/N.
3. If 1≤M then E1=|B|(M−1)/(N−1).
4. If M≤N−1 then E0=|B|M/(N−1).
5. For every unit j and neighbor set B′ with j∉B′, if 1≤M and |B|<|B′| then E < (sum over z∈K of X_B′(z))/|K|. The second unit need not differ from i; only each unit's exclusion from its own neighbor set is required.
6. If 1≤M≤N−1 and |B|≥1, then E1<E<E0.
7. If 1≤M≤N−1, then (M/N)E1+((N−M)/N)E0=E.

Every multiplication and division in formulas 2–7 is in R after the relevant natural cardinalities/counts are cast. In particular the M−1 and N−1 denominators in the mean formulas are real subtraction, whereas the hypotheses M≤N−1 use natural subtraction. No assumption is made that neighborhoods cover the population or arise from a particular geometry. The defined exposure is an unnormalized number of treated neighbors. The statement proves strict comparisons only under the displayed positive-count/nonempty-neighborhood assumptions.

Junk-value/domain audit: `uniformMean` is an explicit finite real sum divided by the support cardinality, so on an empty set its totalized value is 0. K is proved nonempty. E1 may syntactically denote this empty-set value at M=0, and E0 may denote it at M=N, but every assertion using either as a conditional mean is guarded by its nonempty-support conditions. Consequently no conclusion relies on either empty mean. N≥2 makes both real denominators N and N−1 positive. It also ensures natural N−1 is ordinary subtraction. In real coefficients N−M is nonnegative by M≤N. Finite sums and exact natural casts introduce no integrability or overflow issue. Empty neighbor sets give actual zero exposure and are allowed; strict own-treatment comparisons explicitly exclude them. The full design has finitely many assignments; no integral, infinity, `sInf`/`sSup`, limit, logarithm, root, or partial function is used.

## SAP.P030.T14

Sources: `Challenge/Part1.lean:65–66`, `Defs/WholeW1.lean:150–176`, `Defs/Part6.lean:63–75`, `Defs/Part4.lean:10–36`, and the specified definitions and generated helpers in Parts 1 and 2. The actual Challenge theorem has type `T14WholeStatement`, not merely `T14Statement`. There are no hypotheses or outer data parameters; this is a conjunction about fully specified finite data.

For readability this section uses physical labels 1,…,10. They correspond to Lean indices 0,…,9. An assignment is a Boolean vector on these ten units. Write e_j for the vector treating only physical unit j. Locations are x_j=j. The fixed set is F={1,8,9,10}; all other units are variant units. The original design K={e_1,…,e_10} is a finite set. The observed assignment is a=e_7. The conditional set H={e_2,e_3,e_4,e_5,e_6,e_7} is the set of assignments in K agreeing with a on every fixed unit.

The actual outcome model is defined by

ψ_i=|{j : |x_i−x_j|=1}|,
θ_i(z)=|{j : z(j)=true and |x_i−x_j|=1}|,
Y_i(z)=ψ_i+θ_i(z).

These are real casts of finite neighbor counts, so there is no direct own-treatment term. For an arbitrary assignment z, d_i(z) is the minimum of |x_i−x_j| over variant units j with z(j)=true when there is at least one such unit; otherwise the definition returns 0. Fixed units are read in the order 1,8,9,10.

For any real vector v of length n, define its midrank at k as

R_v(k)=|{l : v(l)<v(k)}|+(|{l : v(l)=v(k)}|+1)/2.

Define c_v(k)=R_v(k)−(n+1)/2, A(v)=sum over k of c_v(k)^2, B(v,w)=sum over k of c_v(k)c_w(k), and ρ(v,w)=B(v,w)/sqrt(A(v)A(w)). These definitions use all coordinate indices, preserving multiplicities of ties. The statistic g(y,z) is ρ((d_i(z)) over the four fixed units,(y_i) over those fixed units). The actual statistic is g((Y_i(z)) over F,z); the reference statistic with observation a and reference z is g((Y_i(a)) over F,z). Thus the reference calculation keeps observed outcomes fixed even though the model itself has interference.

A separate, constant potential-outcome schedule Ynull_i(z)=(1,2,2,2,2,3,2,3,2,1)_i is used solely to define the table's common fixed vector y=(1,3,2,1). It is not an assumption that the actual Y equals this schedule for every assignment. The theorem explicitly relates every reference statistic for the actual model at a to the table correlations, and identifies the actual observed fixed vector with y.

The theorem asserts all of the following.

- ψ=(1,2,2,2,2,2,2,2,2,1); θ(a)=(0,0,0,0,0,1,0,1,0,0); Y(a)=(1,2,2,2,2,3,2,3,2,1); and (Y_i(a)) over F=(1,3,2,1).
- |K|=10, |H|=6, and the fixed-treatment filter of K at a is exactly H. Under uniform K, the probability of this conditioning event is 3/5. Every e_j treats exactly one unit, and every e_j has unconditional mass 1/10. Each of the six assignments in H has uniform conditional mass 1/6, which is also its unconditional mass divided by the conditioning-event probability.
- The six fixed-unit distance vectors, ordered by treated unit 2,3,4,5,6,7, are respectively (1,6,7,8), (2,5,6,7), (3,4,5,6), (4,3,4,5), (5,2,3,4), (6,1,2,3). The last is also asserted separately as the observed vector.
- For each row the treated variant set is nonempty, A(distance)>0, and A(y)=9/2. The six table correlations equal (−1/sqrt(90),−1/sqrt(90),−1/sqrt(90),−5/6,−3/sqrt(10),−3/sqrt(10)). Their three distinct values obey −3/sqrt(10)<−5/6<−1/sqrt(90)<0, and every row is negative.
- The absolute errors in displaying −1/sqrt(90), −5/6, −3/sqrt(10) as −0.105, −0.833, −0.949 are each less than 0.0005.
- For every row z∈H, the actual model's reference statistic with observation a equals that row's table correlation. The actual statistic at a equals −3/sqrt(10).
- The number of row indices with correlation at most the observed row is 2. The actual subset of H passing the reference-statistic comparison is exactly {e_6,e_7}; this also identifies the assignments rather than only their number.
- The actual observed-data probability |{w∈H : reference(a,w)≤actual(a)}|/|H| is 1/3, and |1/3−0.333|<0.0005.
- The midranks of the actual observed fixed vector are (3/2,4,3,3/2).
- For every one of the six rows, A(distance)>0 and A(actual observed fixed vector)>0; the row's reference value times sqrt(A(distance)A(actual observed fixed vector)) equals B(distance,actual observed fixed vector); and there exists exactly one real number ρ satisfying this multiplication equation. Thus these are defined correlations with a nonzero normalizing factor, rather than just values assigned by totalized division.

Junk-value/domain audit: `spearman` would return 0 when its real denominator is zero. Here the positive rank-square assertions, y=(1,3,2,1), and positivity of 90 and 10 exclude this. A(v) is a sum of squares for every vector, so its product with A(w) is never negative; `Real.sqrt`'s value 0 on negative inputs is never needed. `nearestDistance` expressly returns 0 when its treated-variant set is empty, but each relevant row has a treated variant and the theorem asserts that nonemptiness. Its nonempty `Finset.inf'` is an attained minimum of finitely many actual distances, without any unbounded- or empty-infimum convention. All uniform support cardinalities are proved to be 10 or 6; the conditional-probability divisor is 3/5. Midrank division is only by 2, and all displayed square-root and rational divisions have nonzero denominators. Decimal literals denote exact rationals, so the rounding clauses are strict rational-error bounds rather than floating-point computations. `Fin` numerals in Lean are reduced modulo their type's size in general; all used indices are in range, including the map r↦r+1 from Fin 6 into Fin 10, whose bound is proved. Every finite index type in this instance is nonempty. All casts are exact. No logarithm, nonintegral real power, integral, infinity conversion, unrestricted extremum, limit, or undefined partial function appears. The theorem claims no no-interference null for the actual adjacency model.

## SAP.P030.T15

Sources: `Challenge/Part1.lean:68–71`, `Defs/Part6.lean:77–84`, `Defs/Part3.lean:27`, and numeral helper instances in the closure.

The theorem asserts a conjunction.

1. For every real C and then every real f, f(C−f)=C²/4−(f−C/2)². This identity is not restricted to positive values or integral inputs.
2. For every integer C and then integer M, assume C≥1 and M≥1. Define the integer objective O(f)=f(C−f)M. The conclusion has two parts:
   - For every integer k, if C=2k, then for every integer f with 0≤f≤C, the condition “for every integer g with 0≤g≤C, O(g)≤O(f)” is equivalent to f=k.
   - For every integer k, if C=2k+1, then for every integer f with 0≤f≤C, the same maximality condition is equivalent to f=k or f=k+1.

The even and odd branches characterize every feasible maximizer, rather than merely exhibit one. M is a positive multiplicative treatment count. C is a positive control count; f and C−f split it, and the optimization domain includes its endpoints. There is no additional probabilistic condition or finite-population object in this statement. Integer parity representations cover every C, and the positivity assumptions make their nearest-half candidates feasible.

Junk-value/domain audit: all objective subtractions and products use the integers, so there is no truncated subtraction or overflow. The completion-of-square identity uses real division only by the fixed nonzero constants 2 and 4. The integer characterization avoids integer division and has no rounding or negative-division convention. C,M≥1 excludes the degenerate M=0 objective in which every split would maximize. C=1 is allowed and both f=0 and f=1 are correctly characterized; an even positive C is at least 2. The candidate set {f∈Z : 0≤f≤C} is finite and nonempty, and maximality is expressed by a universal comparison, not by an `sSup` or an implicit maximizer/default choice. No logarithm, root, nonintegral power, integral, infinity, empty index type, or partial function occurs.
