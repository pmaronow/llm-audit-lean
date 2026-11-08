# Blind statement reading

Written before opening `claims.json` or `record.json`. The Challenge docstrings, the five theorem statements, every named declaration in `closure.json`, and the bodies/types of all its generated auxiliary declarations have been read. The auxiliary declarations were inspected by compiling `scratch/BlindPrint.lean` against `SAP.P001b.Challenge`.

Conventions below: all probabilities are literally `(μ A).toReal`, converting Mathlib's extended nonnegative real measure of a set to a real number. A finite probability written as `P_w(A)` means the finite real sum `∑ i : Fin n, if A i then w i else 0`; there is no measure or normalization built into that definition. A real countable sum is Mathlib's `tsum`, whose value defaults to zero if the family is not summable. All powers here have natural exponents. All displayed real or integer subtraction is ordinary subtraction, not truncated natural subtraction.

## SAP.P001b.T25

The theorem has no hypotheses or free parameters. Its proposition `T25Statement` is the conjunction of the following three assertions. On the one-element set `Fin 1`, give the unique element real weight 1 (`zeroMass`), and let the random quantity be constantly zero:

1. `∑ i : Fin 1, if (0 : ℝ) < 4 then 1 else 0 = 1`.
2. `∑ k ∈ {1,2,3} ⊂ ℤ, ∑ i : Fin 1, if (0 : ℤ) = k then 1 else 0 = 0`.
3. Those same two finite sums are unequal.

Thus it specifies a constant-zero integer-valued law, probability one of being below four, zero total probability at one, two, three, and the inequality between those quantities. It does not assert the normalization or nonnegativity of the weights separately, but the unfolded weights satisfy both. It contains no Bernoulli example. The docstring calls this a refutation of a printed claim and explicitly says it retains only the constant-zero example.

Full SAP closure: `T25Statement` (Defs/Part3.lean:93–97), `finiteProbability` (Defs/Part1.lean:30–32), `zeroMass` (Defs/Part1.lean:68), and `T21Statement._proof_8`. The last declaration is only a proof of `(3+1).AtLeastTwo`, implemented by `Nat.instAtLeastTwoHAddOfNat 3`; it supplies the numeral 4 and imports no substantive hypothesis from T21.

Junk-value audit: only finite sums over `Fin 1` and the nonempty integer interval `[1,3]` occur. There is no division, infinite measure conversion, integral, infinite sum, partial function, or empty index. Integer/real zeros and integer bounds are exact casts/numerals. No junk value influences the example.

## SAP.P001b.T26

`T26WholeStatement` is a conjunction of a general assertion and a fixed fair-die calculation.

The general assertion quantifies, in this order, over an arbitrary type Ω, a sigma-algebra on Ω, a measure μ, a proof that μ is a probability measure, and a function `X : Ω → ℝ`. It then assumes (a) X is measurable, (b) its actual range is countable, and (c) for every real x that is not the cast of any integer, `(μ {ω | X ω = x}).toReal = 0`. In the conclusion define, for every integer k, `q(k) = (μ {ω | X ω = (k : ℝ)}).toReal`. It asserts jointly:

* The real family q on ℤ is summable and `∑' k : ℤ, q(k) = 1`.
* `(μ {ω | X ω < 4}).toReal = ∑' k : ℤ, if (k : ℝ) ≤ 3 then q(k) else 0`.
* `(μ {ω | X ω < 4}).toReal - ∑ k ∈ Finset.Icc (1 : ℤ) 3, q(k) = (μ {ω | X ω ≤ 0}).toReal`.
* The equality of the below-four probability with that finite sum is equivalent to `(μ {ω | X ω ≤ 0}).toReal = 0`.

Countable range plus hypothesis (c) allows noninteger values at null sample points but forces integer values almost surely. It is a condition on atom masses, not literal pointwise integer-valuedness.

The fixed assertion uses `Fin 6`, weights `w(i)=1/6` and values `Y(i)=(i.val : ℝ)+1`. It says: every weight is nonnegative; the weights sum to 1; for every real x, `∑ i : Fin 6, if Y(i)=x then 1/6 else 0` equals `1/6` when x belongs to the real set `{1,2,3,4,5,6}` and equals zero otherwise; `P_w(Y<4)` equals the sum of `P_w(Y=k)` over integer k from 1 to 3; `P_w(Y<4)=3/6`; and `3/6=1/2`.

Full SAP closure: `T26WholeStatement` (Defs/WholeW1.lean:205–230), `probability` (Defs/Part1.lean:12–14), `integerCDF` (70–71), `finiteProbability` (30–32), `dieMass` (73), and `dieValue` (74). The generated auxiliaries `T22WholeStatement._proof_1`, `T26WholeStatement._proof_1`, `T26WholeStatement._proof_2`, `W1Fair._proof_2`, `W1OverlapT._proof_1`, and `dieMass._proof_1` prove respectively `(3+1).AtLeastTwo`, `(4+1).AtLeastTwo`, `(5+1).AtLeastTwo`, `(1+1).AtLeastTwo`, `(2+1).AtLeastTwo`, and `(5+1).AtLeastTwo`, using the corresponding standard natural-number instance. Their suggestive parent names add no model assumptions.

Junk-value audit: `ENNReal.toReal ∞ = 0` is irrelevant because μ is a probability measure, so every set has finite measure. q and its nonnegative subfamilies are summable, so `integerCDF`'s default nonsummable `tsum` value cannot be used. Real division occurs only by 6 or 2, both nonzero. The integer interval includes exactly 1,2,3, and `Fin 6` is nonempty. The cast from ℤ to ℝ is injective, and `dieValue` casts a natural value in 0,…,5 without truncation. There are no integrals, logarithms, square roots, real powers, extrema of sets, limit superior/inferior, or partial functions.

## SAP.P001b.T27

This theorem has no external hypotheses or universally chosen laws: it states properties of a fixed construction. The sample space is `I = Σ m : ℕ, Fin (2^m)`, with the full sigma-algebra (every subset measurable). A point `(m,k)` has value `L(m,k)=(2(k.val : ℝ)+1)/(2 : ℝ)^(m+1)` and weight `w(m,k)=(1/2 : ℝ)^(2*m+1)`. Define the measure `μ = Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac i)`, and define `D(x)=∑' i : I, if L(i)≤x then w(i) else 0`. The SAP-defined set of dyadic rationals is precisely `{x : ℝ | 0<x ∧ x<1 ∧ ∃ a n : ℕ, x=(a:ℝ)/(2:ℝ)^n}`.

Its conclusion is the conjunction, in order, of:

1. For every natural m, `∑ k : Fin (2^m), w(m,k)=(1/2)^(m+1)`.
2. The iterated sum of those level sums equals `∑' m : ℕ, (1/2)^(m+1)`.
3. That geometric series equals 1.
4. w is summable as a real family on I and its sum is 1.
5. For every i, `0<w(i)`.
6. Every subset of I is measurable, and μ is a probability measure.
7. L is measurable and injective, its range equals the dyadic set just defined, and its range is countable.
8. For every i, `μ {i} = ENNReal.ofReal (w i)`, `(μ {j | L(j)=L(i)}).toReal=w(i)`, and that real event probability is positive.
9. For every real x, `(μ {i | L(i)≤x}).toReal=D(x)`.
10. For every pair of reals a,b, `0<a → a<b → b<1 → D(a)<D(b)`.
11. For every pair of reals a,b, `0≤a → a<b → b≤1 → ¬∃ c : ℝ, ∀ x∈Set.Ioo a b, D(x)=c`.
12. `μ {i | L(i)=1/3}=0` (an equality of extended nonnegative real numbers).
13. D is continuous at 1/3 in the ordinary real topology.
14. There is no real ε>0 such that for every real x with `|x-1/3|<ε`, `D(x)=D(1/3)`.

The formulas for atoms and weights are genuine formulas, with odd numerators choosing unique reduced dyadic locations. They do not incorporate continuity or monotonicity into their definitions. The docstring describes this law as a counterexample to local flatness at every non-jump point.

Full SAP closure: `DyadicIndex`, `dyadicLocation`, `dyadicWeight`, `dyadicDistributionFunction` (Defs/Part2.lean:13–18); `probability`, `distributionFunction` (Defs/Part1.lean:12–14,26–28); `instMeasurableSpaceDyadicIndex`, `W1DyadicLaw`, `W1DyadicRationals`, `T27WholeStatement` (Defs/WholeW1.lean:232–272). The local measurable-space instance is literally `⊤`. The generated auxiliaries `W1Fair._proof_1`, `W1Fair._proof_2`, `W1OverlapT._proof_1`, `dyadicLocation._proof_1` are respectively the standard scalar-tower proof for ENNReal acting on itself and standard proofs of `(1+1).AtLeastTwo`, `(2+1).AtLeastTwo`, `(1+1).AtLeastTwo`. They add no probabilistic premise.

Junk-value audit: `(2:ℝ)^n>0` for every natural n, so no dyadic denominator is zero, even at n=0. Divisors 2 and 3 in weights and thresholds are nonzero. `2^m` is a positive natural, so every level is nonempty and I is nonempty; finite-index casts are ordinary natural-to-real casts. `ENNReal.ofReal` would truncate negative weights to zero, but all actual weights are positive. The extended sum defining μ exists without a default-zero convention and the theorem asserts it is a probability measure; hence all applications of `toReal` are finite. Real `tsum` defaults are ruled out by the summability and geometric series facts and the domination `0≤if L(i)≤x then w(i) else 0≤w(i)`. No integral, real exponent, logarithm, square root, set extremum, limsup/liminf, or partial-function default occurs.

## SAP.P001b.T28

`T28Statement` is a conjunction of four assertions.

First, universally quantify over a type Ω, a sigma-algebra, a measure μ, a proof that μ is a probability measure, and `X : Ω → ℝ`; assume X measurable; then quantify over a proof that its range is countable and over every real x. The conclusion is

`(μ {ω | X ω ≤ x}).toReal = ∑' t : Set.range X, if t.val ≤ x then (μ {ω | X ω = t.val}).toReal else 0`.

The range subtype indexes each distinct actual value once, including any null values. It is not a sum over sample points with multiplicity.

Second, for every natural m and function `w : Fin (m+1) → ℝ`, assume every weight nonnegative and `∑ i,w(i)=1`; for every `X : Fin (m+1) → ℝ`, assume X is strictly increasing (i<j implies X(i)<X(j)); for every real x conclude jointly:

* If x<X(0), `∑ i, if X(i)≤x then w(i) else 0=0`.
* For every `l : Fin m`, if `X(l.castSucc)≤x` and `x<X(l.succ)`, that event sum equals `∑ i : Fin (m+1), if i≤l.castSucc then w(i) else 0`. Here `castSucc` retains l's natural value, and `succ` adds one.
* If `X(Fin.last m)≤x`, that event sum is 1, with `Fin.last m` the element of natural value m.

Third, for every natural n and `w : Fin n → ℝ`, assume nonnegative weights summing to 1; for every `X : Fin n → ℝ` and every real a,b, assume a≤b and no i has `a<X(i) ∧ X(i)≤b`. Then `∑ i, if X(i)≤a then w(i) else 0 = ∑ i, if X(i)≤b then w(i) else 0`.

Fourth, for the fixed weights `w(i)=1/6` and values `Y(i)=(i.val:ℝ)+1` on `Fin 6`, the same finite event sum `P_w(Y≤x)` has values: 0 at x=−1; 1/6 at 1; 1/6 at 3/2; 1/3 at 2; 1 at 6; 1 at 7.

The docstring claims point-mass sums for countable discrete laws, interval formulas for finite ordered laws, and these six die calculations. There is no assertion that every countably supported CDF is locally flat off its atoms.

Full SAP closure: `T28Statement` (Defs/Part3.lean:114–135); `finiteProbability`, `probability`, `distributionFunction`, `dieMass`, `dieValue` (Defs/Part1.lean:30–32,12–14,26–28,73–74). Generated auxiliaries `T21Statement._proof_3`, `T21Statement._proof_6`, `T28Statement._proof_2`, `T28Statement._proof_3`, `dieMass._proof_1` prove respectively `(1+1).AtLeastTwo`, `(2+1).AtLeastTwo`, `(5+1).AtLeastTwo`, `(6+1).AtLeastTwo`, `(5+1).AtLeastTwo` using standard instances; `T28Statement._proof_1` proves `∀ {m:ℕ}, NeZero (m+1)` via the standard successor nonzero instance. There are no extra hypotheses from their parent declaration names.

Junk-value audit: probability measures exclude infinite measures in every `toReal`. Countable disjoint measurable fibers imply that the real atom sums and their threshold subseries are summable, so the `tsum` default cannot establish the first clause spuriously. A probability measure on an empty Ω cannot exist. In the second clause `Fin (m+1)` is always nonempty; for m=0 the middle list of intervals indexed by `Fin 0` is empty, and the below/above formulas correctly describe a one-point law. In the third clause n=0 is a formally allowed index but normalization would say 0=1, so that specialization has no hypotheses-satisfying instance; n=1 and larger do. The theorem as a whole is not vacuous. Divisions are only fixed nonzero denominators 6,2,3. All casts preserve finite-index values; no truncated subtraction or partial lookup is used. There are no integrals, logarithms, roots, real powers, set extrema, or limsup/liminf.

## SAP.P001b.T29

There are no external hypotheses or arbitrary density choices. Define four fixed real functions:

* `F(x)=max 0 (min 1 x)`.
* `f_c(x)=if x∈Set.Icc (0:ℝ) 1 then 1 else 0`.
* `f_o(x)=if x∈Set.Ioo (0:ℝ) 1 then 1 else 0`.
* `f_m(x)=if x=1/3 then 3/2 else f_c(x)`.

`T29Statement` asserts the conjunction:

1. For every real x, all three f values are nonnegative.
2. For every real x, the three Bochner integrals against Lebesgue measure restricted to `Set.Iic x` satisfy `∫ u≤x, f_c(u) = F(x)`, `∫ u≤x, f_o(u) = F(x)`, and `∫ u≤x, f_m(u) = F(x)`.
3. The three functions are pairwise unequal as functions (not as equivalence classes modulo null sets).
4. F is not differentiable over ℝ at 0 and is not differentiable over ℝ at 1.
5. For every real h, if 0<h and h≤1 then all four equalities hold: `(F(−h)−F(0))/(−h)=0`; `(F(h)−F(0))/h=1`; `(F(1−h)−F(1))/(−h)=1`; `(F(1+h)−F(1))/h=0`.
6. `f_c(0)=1` and `f_c(1)=1`.

Thus these are distinct nonnegative pointwise functions yielding the same integrated distribution function, which has incompatible left/right slopes at both endpoints. There is no explicit assertion `Integrable f volume` or a named probability measure in the theorem, but all three definitions are bounded Borel functions supported on [0,1], and their integrals over the full line are one. The example consequently uses genuine probability densities. The docstring calls a printed claim false; the mathematical statement itself mentions no arbitrary claim or uniqueness proposition.

Full SAP closure: `T29Statement` (Defs/Part3.lean:137–152); `uniformDistributionFunction`, `closedUniformDensity`, `openUniformDensity`, `modifiedUniformDensity` (Defs/Part2.lean:20–24); and `dyadicLocation._proof_1`, `modifiedUniformDensity._proof_1`, which are the standard proofs of `(1+1).AtLeastTwo` and `(2+1).AtLeastTwo`. The auxiliary names do not introduce dyadic data into the statement.

Junk-value audit: Bochner integrals totalize to zero for nonintegrable functions, but each explicit function is Borel, bounded by 3/2 and compactly supported, hence Lebesgue integrable and integrable on every restricted half-line. Thus the equalities use genuine integrals. All displayed difference quotients are under 0<h, so neither h nor −h is zero. The density definitions divide only by 2 or 3. max and min are binary lattice operations on ℝ, not extrema of possibly empty or unbounded sets. Endpoint differences of densities are intentional changes on Lebesgue-null sets; none invokes an arbitrary partial-function value. No extended-real conversion, infinite sum, logarithm, root, real exponent, empty index, truncated subtraction, limsup/liminf, or partial-function default occurs.
