# Blind reading

This file was written and saved before opening `claims.json` or `record.json`.
Sources read: `closure.json`, the five target docstrings in
`SAP/P007/Challenge/Part1.lean`, and every declaration listed in their closures.
The source definitions are in `Defs/Part1.lean`, `Defs/Part2.lean`,
`Defs/Part3.lean`, and `Defs/WholeW2.lean`. `scratch/Closure.lean` was compiled to
read all 22 generated, line-zero declarations as well as the finite-law
constructor/projection and relevant Mathlib definitions. The generated
declarations are ordinary `Nat.AtLeastTwo` proofs for numerals, not additional
statistical assumptions.

## Common fully expanded notation

The following abbreviations are mathematical notation for the expansions below;
they do not leave any SAP statistical notion uninterpreted.

* `Row h` is the finite function type `Fin h → Bool` and `Array n h` is
  `Fin n → Fin h → Bool`. `true` means missing; `false` means observed. These
  are missingness indicators, not the numerical values in the data set.
* A `Law A` consists of a real function `w : A → ℝ` on a finite type, proofs
  `∀ a, 0 ≤ w a`, and `∑ a, w a = 1`. `Law.mk` is precisely this constructor;
  `Law.weight` projects `w`. Write
  `P_w(E) = ∑ x, if E(x) then w(x) else 0` and
  `E_w(f) = ∑ x, w(x) f(x)`. These are `probability` and `expectation`.
* Write `O_i(j,x)` for `∀ t : Fin h, t.val < j → x i t = false`.
  This is `prefixObserved (x i) j`. Write
  `s_i(j) = P_w(O_i(j,·))`, which is `survival L i j`.
  `O_i(0,x)` is true. For `j ≥ h`, it says the whole row is observed.
* `allDeleted L`, denoted `p_w`, is
  `P_w(∀ i : Fin n, ¬ O_i(h,·))`: every row has at least one missing cell.
* `rowIndependent L` means that for every family of predicates
  `E_i : (Fin h → Bool) → Prop`,
  `P_w(∀ i, E_i(x i)) = ∏ i : Fin n, P_w(E_i(x i))`.
  Predicates can be the sure event, so this tests full mutual independence of
  arbitrary subfamilies, not just pairwise independence. No identical-row-law
  condition is included.
* `observationBound L q` is exactly
  `0 ≤ q ∧ q < 1 ∧ ∀ i : Fin n,
    ((0 < h → s_i(1) ≤ q) ∧
     ∀ j : ℕ, 1 ≤ j → j < h → 0 < s_i(j) → s_i(j+1)/s_i(j) ≤ q)`.
  The positive-prefix antecedent matters: no conditional ratio is imposed
  at a zero-probability prefix.
* `deletedIndicator x i`, denoted `D_i(x)`, is the real number zero if
  `O_i(h,x)` and one otherwise. `deletedFraction x`, denoted `F_n(x)`, is
  `(∑ i : Fin n, D_i(x))/↑n`.
* `lowerBound n q h`, denoted `B(n,q,h)`, is `(1-q^h)^n`, with both
  exponents natural. `fractionBound q h`, denoted `b(q,h)`, is `1-q^h`.
* `realThreshold n q a`, denoted `K(n,q,a)`, is
  `Real.log (1 - Real.rpow a (↑n)⁻¹) / Real.log q`.
  `realLowerBound n q x`, denoted `R(n,q,x)`, is
  `(1 - Real.rpow q x)^n`; the inner exponent is real, the outer exponent
  natural. Natural floor and ceiling are Mathlib's `Nat.floor` and `Nat.ceil`.
* Given real observation probabilities `a_ij`, `cellWeights a x` is
  `∏ i : Fin n, ∏ j : Fin h, (if x i j then 1-a_ij else a_ij)`.
  `equalWeights n h q` uses `a_ij=q`.
  `unequalWeights n h` uses `a_i0=3/4` and `a_ij=1/4` for `j.val ≠ 0`.
  `figure5Weights` has `n=h=2` and `a_i0=3/4`, `a_i1=1/2`.
  These are explicit point masses on the entire finite array space.
* `equalModel n h q P` means there exists a normalized nonnegative finite
  law `w` equal to `equalWeights n h q`, with the full row independence and
  observation-bound conditions just expanded, and satisfying `P(w)`.
  `unequalModel n h P` means the same with `unequalWeights` and bound `q=3/4`.
  Their normalization and hypotheses are existential conclusions, not
  unproved conditions imposed on a nominal weight function.

## SAP.P007.T6

Location: `Challenge/Part1.lean:37–40`; statement: `Defs/Part2.lean:110–122`.
The docstring calls this the corrected finite Bernoulli sandwich, its zero
endpoint, a positive-domain exponential identity, and two-variable group
counts. It states a conjunction of three independent universally quantified
claims, not an asymptotic limit theorem.

1. For all natural `n,h`, assuming `n>0` and `h>0`, and then for all real
   `q` with `0≤q<1`,
   `-1 < -q^h`, `1-q^h ≤ 1`,
   `1+↑n*(-q^h)=1-↑n*q^h`, and
   `1-↑n*q^h ≤ (1-q^h)^n ≤ 1`.
2. For all natural `n,h`, assuming `n>0,h>0`, then for every normalized
   finite law `w` on `Fin n → Fin h → Bool` and real `q`, assuming full
   mutual independence of row vectors and the expanded observation bound,
   the conjunction is
   `1-↑n*q^h ≤ (1-q^h)^n ≤ P_w(∀ i, ¬O_i(h,·)) ≤ 1`,
   `0 ≤ 1-p_w ≤ ↑n*q^h`,
   `q=0 → p_w=1`, and
   `q>0 → ↑n*q^h = exp(log ↑n + ↑h*log q)`.
   There is no identical-distribution assumption and no cell independence
   assumption. The assumptions `0≤q<1` are inside `observationBound`.
3. For every natural `n>0`, `n ≤ 2*n`, `2*n ≠ n`, and the finite cardinality
   of `Fin n × Fin 2` is `2*n`. This is a cardinality statement; it does not
   by itself define a missingness process on groups or a limiting regime.

Closure read: `Array`, `Row`, `Law`, `Law.mk`, `Law.weight`, `T6Statement`,
`probability`, `prefixObserved`, `survival`, `rowIndependent`,
`observationBound`, `allDeleted`. All are expanded above.

Junk values: ratios are tested only with strictly positive denominators;
`q=0` is allowed, but `h>0` gives the ordinary value `q^h=0`. Neither a
`0^0` endpoint nor empty row/column index type occurs. The logarithm identity
requires both `n>0` and `q>0`, so it uses the ordinary logarithm. There are no
integrals, inverse natural casts, truncated subtractions, `sqrt`, real
powers, infima/suprema, limits, or partial functions in this statement. All
subtractions displayed are real subtractions. Natural casts are exact.

## SAP.P007.T7

Location: `Challenge/Part1.lean:42–45`; statement: `Defs/Part3.lean:28–61`.
The docstring describes equality, rounding, worked-value, and probability
upper-guarantee counterexamples. There are no outer hypotheses; the statement
is a conjunction of six existential-law packages and a numerical package.
Every law package includes normalization, nonnegativity, full row
independence, and the observation bound from the common expansion.

1. An equal-weight law for `(n,h,q)=(1,2,3/4)` exists such that
   `B(1,3/4,2)=7/16 < 1/2 < 37/64=B(1,3/4,3)`,
   `2<K(1,3/4,1/2)<3`, its natural floor is two and its ceiling is three,
   `∀ k : ℕ, B(1,3/4,k)≠1/2`, and its actual all-deletion probability is
   `7/16`. For every natural `k`,
   `B(1,3/4,k)≤1/2 ↔ k≤2` and
   `1/2≤B(1,3/4,k) ↔ 3≤k`.
   The real-exponent expression at the real inverse equals `1/2`:
   `R(1,3/4,K(1,3/4,1/2))=1/2`.
   The formulas at `k=3` and at arbitrary `k` are scalar formulas; this
   particular existential law still has exactly two columns.
2. An equal-weight law for `(10000,33,3/4)` exists with
   `p_w=B(10000,3/4,33)<1/2<B(10000,3/4,34)`.
3. An equal-weight law for `(10000,952,99/100)` exists with
   `p_w=B(10000,99/100,952)<1/2<B(10000,99/100,953)`.
4. An unequal-weight law for `(1,2)` exists with observation chances
   `3/4,1/4`, and `B(1,3/4,2)=7/16≤1/2`, but `p_w=13/16>1/2`.
5. An unequal-weight law for `(1,16)` exists with
   `B(1,3/4,16)=4251920575/4294967296 < 99/100 < B(1,3/4,17)`,
   `p_w=4294967293/4294967296 > 99/100`, and floor/ceiling of
   `K(1,3/4,99/100)` equal to 16/17.
6. An unequal-weight law for `(10000,33)` exists with
   `p_w=(1-3/4^33)^10000`,
   `1-30000/4^33 ≤ p_w`, `99/100 < 1-30000/4^33`,
   `99/100 < p_w`, and `B(10000,3/4,33)<1/2`.
7. Independently of those witnesses, the natural floor/ceiling of
   `K(10000,3/4,1/2)` are 33/34 and those of
   `K(10000,99/100,1/2)` are 952/953.

(The source has six existential-law conjuncts; the final seventh package is
the floor/ceiling arithmetic package.)

Closure read: `Array`, `Row`, `Law`, constructor/projection,
`T7Statement`, `allDeleted`, `cellWeights`, `equalModel`, `equalWeights`,
`unequalModel`, `unequalWeights`, `lowerBound`, `observationBound`,
`prefixObserved`, `probability`, `realLowerBound`, `realThreshold`,
`rowIndependent`, `survival`, and every listed generated proof of
`T7Statement`, `unequalModel`, `unequalWeights`, and `workedValues`.
These generated proofs merely supply numeral `AtLeastTwo` instances.

Junk values: all distribution spaces are nonempty finite function types with
positive row/column counts. Observation chances and conditional denominators
are positive in these particular product laws. All inverse-threshold uses
have `n>0`, `0<q<1`, `0<a<1`; thus `1-a^(1/n)` is positive, `log q` is
negative and nonzero, and `K>0`. Mathlib defines `log 0=0` and extends log to
negative inputs via absolute value, but neither extension is used here.
Real powers have positive bases here. Natural floor/ceiling truncate at zero
outside their usual nonnegative domain, but these inputs are positive.
Universal `k=0` uses `q^0=1`, so `B(...,0)=0` with positive outer exponent;
this is an ordinary meaningful zero-variable scalar expression. All fixed
rational denominators and powers of four are positive. No division-by-zero,
integral, infinite value conversion, `sqrt`, infimum/supremum, limit, natural
subtraction, or partial function affects the statement. `j.val=0` in the
unequal model selects the first column; it is not a default array index.

## SAP.P007.T8

Location: `Challenge/Part1.lean:47–50`; statement: `Defs/Part3.lean:63–92`.
The docstring describes the corrected inverse and integer threshold for the
lower bound, sharp probability guarantees, worked values, and explicit laws.
The statement is a conjunction of a general theorem and three fixed packages.

The general theorem quantifies `n : ℕ`, assumes `n>0`, then quantifies real
`q,a`, assuming, in order, `q>0`, `q<1`, `a>0`, `a<1`. Under these hypotheses:

1. `B(n,q,0)=0`, every natural `k` has `0≤B(n,q,k)<1`, and the sequence
   `k ↦ B(n,q,k)` is strictly increasing (Mathlib `StrictMono`: all `k<l`
   have a strict inequality).
2. `K=K(n,q,a)>0`, `R(n,q,K)=a`, and for every real `x≥0`,
   `R(n,q,x)=a → x=K`. Uniqueness is asserted on nonnegative real `x`.
3. For every natural `k`,
   `B(n,q,k)≤a ↔ ↑k≤K`, `a≤B(n,q,k) ↔ K≤↑k`, and
   `B(n,q,k)=a ↔ ↑k=K`.
4. For every natural `k`, `B(n,q,k)≤a ↔ k≤⌊K⌋₊` and
   `a≤B(n,q,k) ↔ ⌈K⌉₊≤k`. Also `B(n,q,⌊K⌋₊)≤a` and
   `a≤B(n,q,⌈K⌉₊)`.
5. `⌈K⌉₊=⌊K⌋₊ ↔ ∃ m : ℕ, ↑m=K`. If there is no such natural `m`,
   then `⌈K⌉₊=⌊K⌋₊+1` and
   `B(n,q,⌊K⌋₊)<a<B(n,q,⌈K⌉₊)`.
6. For every natural `k>0`, and then every normalized finite law on
   `Fin n → Fin k → Bool`, full row independence and the expanded
   observation bound imply `B(n,q,k)≤p_w`; if `⌈K⌉₊≤k`, both the lower
   bound and `p_w` are at least `a`.
7. For every natural `k>0` with `↑k<K`, an equal-weight normalized law exists
   with full row independence and the observation bound and
   `p_w=B(n,q,k)<a`.
8. For every natural `k>0`, an equal-weight normalized law exists with those
   same conditions and `p_w=B(n,q,k)`.

The three further packages do not depend on the preceding variables:

* `workedValues`: floor/ceiling of `K(10000,3/4,1/2)` are 33/34;
  floor/ceiling of `K(10000,99/100,1/2)` are 952/953;
  `0.47075≤B(10000,3/4,33)<0.47085` and
  `0.49685≤B(10000,99/100,952)<0.49695`.
* The crossings are strict:
  `B(10000,3/4,33)<1/2<B(10000,3/4,34)` and
  `B(10000,99/100,952)<1/2<B(10000,99/100,953)`.
* An unequal-weight `(1,2)` normalized law exists with row independence,
  bound `q=3/4`, `B(1,3/4,2)≤1/2`, but `p_w>1/2`.

Closure read: `Array`, `Row`, `Law`, constructor/projection, `T8Statement`,
`allDeleted`, `cellWeights`, `equalModel`, `equalWeights`, `unequalModel`,
`unequalWeights`, `lowerBound`, `observationBound`, `prefixObserved`,
`probability`, `realLowerBound`, `realThreshold`, `rowIndependent`,
`survival`, `workedValues`, and all the listed generated proofs of
`unequalModel`, `unequalWeights`, and `workedValues`.

Junk values: all threshold hypotheses give positive real-power bases, positive
log numerator argument, nonzero negative log denominator, positive `n`, and
positive `K`, so log, inverse, real power, floor, and ceiling have their
ordinary meanings. `x=0` is meaningful (`q^0=1`). `k=0` is intentionally
allowed for the scalar bound, but the probability-law clauses require `k>0`.
Observation ratios have positive-prefix guards. All law/statistic spaces are
finite; no undefined expectation, `toReal ∞`, empty extremum, limit, `sqrt`,
natural truncated subtraction, or partial-function default is involved.
Real subtraction `1-q^x` is nonnegative at the specified `x≥0`.

## SAP.P007.T9

Location: `Challenge/Part1.lean:52–55`; statement: `Defs/Part3.lean:94–104`.
The docstring describes a two-row counterexample involving the expected
fraction and the two all-deletion probability expressions. There are no outer
hypotheses. There exists a normalized nonnegative law on
`Fin 2 → Fin 2 → Bool` with point masses
`∏ i : Fin 2, (if x i 0 then 1/4 else 3/4) *
               (if x i 1 then 1/2 else 1/2)`.
It has full row independence, satisfies the expanded observation bound at
`q=3/4`, and additionally has the following properties:

* For every real `q`, if it satisfies that observation bound, then `3/4≤q`.
* For every row `i`, `s_i(1)=3/4`, `s_i(2)=3/8`, `s_i(1)>0`, and
  `s_i(2)/s_i(1)=1/2`.
* For every row `i`, the finite expectation of its 0/1 deletion indicator is
  `5/8`.
* The finite expectation of `F_2(x)=(D_0(x)+D_1(x))/2` is `5/8`, whereas
  `b(3/4,2)=1-(3/4)^2=7/16 < E_w(F_2)`.
* `B(2,3/4,2)=(1-(3/4)^2)^2=49/256`, and this scalar value differs from
  `b(3/4,2)`.
* Its actual all-deletion probability is `25/64`.

Closure read: `Array`, `Row`, `Law`, constructor/projection, `T9Statement`,
`allDeleted`, `cellWeights`, `figure5Weights`, `deletedFraction`,
`deletedIndicator`, `expectation`, `fractionBound`, `lowerBound`,
`observationBound`, `prefixObserved`, `probability`, `rowIndependent`,
`survival`, and every listed generated proof (including reused numeral
proofs with names from `T7Statement`, `laterNullWeights`, `unequalModel`,
`unequalWeights`, and `workedValues`). Reusing these proof names does not
import the other statements or their statistical content.

Junk values: the law is explicitly normalized/nonnegative, all sums are
finite, and `F_2` divides by the positive real number two. Its conditioning
probability is explicitly `3/4>0`. The universal observation-bound clause
continues to guard later ratios. Finite expectations always exist; no
Bochner defaults are used. There are no empty index types, exceptional logs,
real powers, `sqrt`, natural subtractions, infinite value conversions,
extrema, limits, or partial functions.

## SAP.P007.T10

Location: `Challenge/Part1.lean:57–68`; statement:
`Defs/WholeW2.lean:83–113`. The docstrings at both locations say that usual
measure-theoretic conditions are assumed and describe a corrected expected
deletion fraction, independence-free inequalities, independent-cell equality
cases, and comparison with the all-deletion lower-bound formula.

Additional SAP definitions, fully expanded: for a measurable space `Ω`,
measure `μ`, array function `M : Ω → Fin n → Fin k → Bool`, and predicate
`E` on arrays, write
`P_{μ,M}(E) = (μ {ω | E(M ω)}).toReal`, exactly `eventOnW2 μ M E`.
`survivalOnW2 μ M i j` is `P_{μ,M}(O_i(j,·))`.
`observationBoundOnW2` is the common observation-bound formula with this
probability replacing the finite sum.
`rowsIndependentOnW2` is the common full row-event product formula with
this probability. `cellsIndependentOnW2` says, for every family
`E_ij : Bool → Prop`,
`P_{μ,M}(∀ i j, E_ij(x i j)) = ∏ i, ∏ j, P_{μ,M}(E_ij(x i j))`.
`cellsIndependentW2` is precisely that cell formula for a finite law's sum
probabilities. All subfamilies are included by allowing the sure predicate
at other coordinates. There is no additional SAP definition in the
statement: `lawRealizesW2`, though nearby, is not used.

The statement is a conjunction of four packages. Its universe parameter
allows an arbitrary underlying type at that universe; it is not fixed to a
finite sample space.

1. For every type `Ω` with measurable-space structure, every measure `μ`
   with `IsProbabilityMeasure μ`, then natural `n,k` with `n>0,k>0`, every
   function `M : Ω → Array n k` with `Measurable M`, and every real `q`
   satisfying `observationBoundOnW2 μ M q`:
   for each `i : Fin n`, `D_i∘M` is Bochner integrable,
   `∫ D_i(M ω) dμ = 1-P_{μ,M}(O_i(k,·))`, and
   `1-q^k ≤ ∫ D_i(M ω) dμ`.
   Also `F_n∘M` is integrable,
   `∫ F_n(M ω) dμ = (∑ i, (1-P_{μ,M}(O_i(k,·))))/↑n`, and
   `1-q^k ≤ ∫ F_n(M ω) dμ`.
   There is no row independence hypothesis in this package.
2. Independently, for every `Ω`, measurable-space structure, probability
   measure `μ`, positive `n,k`, measurable `M`, and real `q` with
   `0≤q<1`, if all cells have the full event-product independence property
   and `∀ i j, P_{μ,M}(x i j=false)=q`, then full row independence and
   the observation bound hold, and `∫ F_n(M ω) dμ=1-q^k`.
3. For every positive natural `n,k`, and every real `0≤q<1`, there exists
   a normalized nonnegative finite law on arrays with the equal-weight point
   masses expanded above, full cell independence, full row independence,
   the observation bound, observation probability exactly `q` at every cell,
   and finite expectation `E_w(F_n)=1-q^k`.
4. For every positive natural `n,k` and every real `0≤q<1`,
   `B(n,q,k)=b(q,k)^n` and `B(1,q,k)=b(q,k)`;
   if `q>0` and `n≥2`, then `0<b(q,k)<1` and `B(n,q,k)<b(q,k)`;
   `B(n,q,k)=b(q,k) ↔ (n=1 ∨ q=0)`;
   and if `q=0`, both scalar bounds equal one.

This last package compares explicit scalar expressions. It does not assert an
all-deletion probability inequality on the arbitrary underlying space.
The right side `1-q^k` has no `n` argument, which realizes the stated
independence of this lower bound from row count.

Closure read: `Array`, `Row`, `Law`, constructor/projection,
`T10WholeStatement_W2`, `cellWeights`, `equalWeights`,
`cellsIndependentOnW2`, `cellsIndependentW2`, `eventOnW2`,
`survivalOnW2`, `observationBoundOnW2`, `rowsIndependentOnW2`,
`rowIndependent`, `observationBound`, `probability`, `prefixObserved`,
`survival`, `deletedFraction`, `deletedIndicator`, `expectation`,
`lowerBound`, `fractionBound`.

Junk values: `Measure.real` is `ENNReal.toReal`, which would send infinity
to zero, but a probability measure gives finite measure to every set here.
Bool, finite indices and their function spaces carry the usual discrete
measurable structures; `Measurable M` makes every tested finite-array event
measurable. The Bochner integral would default to zero for a nonintegrable
function; here all used statistics are measurable with finite range on a
probability space, hence integrable. Package 1 explicitly concludes
integrability as well. Division in `F_n` and the mean identity has positive
denominator `↑n`. Ratios have positive-prefix guards; this includes the
ordinary `q=0` endpoint without dividing by a null probability. `k>0`
excludes `0^0` in that endpoint. No empty row or column type occurs. There
are no logs, real powers, square roots, infinite extrema, limsup/liminf,
natural subtractions, or partial-function defaults. All natural-to-real
casts are exact.
