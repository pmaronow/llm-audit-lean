# Blind reading of T6–T10

This file was saved before opening either `claims.json` or `record.json`.
The sources inspected were the five docstrings and statements in
`SAP/P037a/Challenge/Part1.lean`, every entry in their `closure.json`
closures, and the relevant definition sources. `scratch/BlindClosure.lean`
successfully prints all 95 distinct closure declarations; its output is
saved in `scratch/BlindClosure.out`. The compact declaration inventory is
`scratch/BlindClosure-declarations.txt`.

Generated constructor/projection declarations have the ordinary structure
meanings described below. The five exposure constructors are distinct nullary
constructors; their recursor, `casesOn`, and `printedCase.match_1` perform
exhaustive five-way case distinction. The generated `_proof_*` entries in
Part6, `FrequencyFacts`, `frequencyExample`, `T10Statement`, and
`withinBlockDependence` certify that particular numeral denominators are at
least two. They do not supply statistical assumptions or assert the audited
conclusions. `treatmentPair._proof_1` certifies `NeZero 4` for finite numerals.
The generated proofs for the finite designs establish nonnegative weights
and total mass one, using ordinary finite-sum/product identities. All these
entries were inspected, including auxiliary entries whose names originate
in a different definition from the one currently using the numeral.

## SAP.P037a.T6

Source: Challenge/Part1.lean:70–72; Defs/Part6.lean:88–111;
Defs/Part1.lean:102–103.

There are no outer parameters or hypotheses. The statement is a conjunction
of the following fixed arithmetic facts and two universally quantified
conditional assertions. All fractions below are real fractions except the
two expressly identified natural-number calculations. The abbreviation
“reduction of c to t” means exactly the real number `(c-t)/c`.

The fixed assertions are:

1. In the natural numbers, `2695 - 2012 = 683`.
2. `(2695-2012)/2695 = 683/2695` in the reals.
3. `49/200 < 683/2695 < 51/200`.
4. `683/2695 < 59/200`, and `683/2695 ≠ 3/10`.
5. In the natural numbers, `6830 ≠ 8085`.
6. `11/200 ≤ 683/11938 < 13/200`.
7. `9/40 < 2695/11938 < 23/100`.
8. `3/10 - 1/4 = 1/20` and `(1/20)/(3/10) = 1/6`.

For every pair of real numbers A and B, first assuming
`5389/2 ≤ A ≤ 5391/2`, and then assuming
`4023/2 ≤ B ≤ 4025/2`, the theorem says

`1364/5389 ≤ 1-B/A ≤ 1368/5391`,

and also `49/200 < 1364/5389` and `1368/5391 < 51/200`.
The intervals include both endpoints. They are supersets of any particular
tie-breaking convention for rounding to an integer.

For every pair of real numbers e and m, first assuming
`11/200 ≤ e ≤ 13/200`, and then assuming
`39/200 ≤ m ≤ 41/200`, the theorem says

`(3/50)/(1/5) = 3/10`, `11/41 ≤ e/m`, and `51/200 < e/m`.

Thus the fixed reduction is about 25.34%; the rounded-total version lies
strictly within the 24.5%–25.5% bin. Ratios of numbers in the latter
mixed-basis intervals lie above that bin. The statement does not quantify
over empirical data sets or identify a stochastic estimator.

Junk conventions: natural subtraction is truncated at zero, but 2695 exceeds
2012, so the subtraction is the ordinary positive difference. Real division
uses inverse zero equal to zero, but every constant denominator is positive;
A is at least 2694.5 and m at least 0.195. Consequently no division-by-zero
value participates in an asserted instance. The displayed natural numerals
used in real arithmetic have the usual exact casts; no integer rounding or
natural division is used in those fractions. There are no integrals,
infinite extended-real values, logs, roots, real powers, extrema, limits,
partial functions, or index types in this closure affecting the assertion.

The docstring describes exact arithmetic for printed totals and rounding
bins and an exclusion of 25% from the two mixed-basis numbers. This is an
arithmetic assertion, not a theorem that the printed totals are the correct
empirical totals.

## SAP.P037a.T7

Source: Challenge/Part1.lean:74–76; Defs/Part7.lean:12–31,37;
Defs/Part1.lean:44–61.

An exposure datum is a quadruple `(s,z,p,r)` of natural numbers, in that
order: school indicator, seed indicator, peer count, referent-peer count.
“Feasible” means precisely

`s ≤ 1`, `z ≤ s`, and `r ≤ p`.

In particular s and z are binary and a seed must be in a treated school.
There is no additional graph, population-size, or design-support condition
in this definition. The five labels C, S, N, R, D are distinct constructors
of a five-element type. The printed predicates on these labels are exactly:

| Label | Predicate |
| --- | --- |
| C | `s = 0` |
| S | `s = 1 ∧ z = 0 ∧ p = 0` |
| N | `s = 1 ∧ r = 0` |
| R | `s = 1 ∧ z = 0 ∧ 0 < r` |
| D | `z = 1` |

There are no outer parameters or premises. The first conjunct explicitly
asserts that `(1,0,0,0)` is feasible and satisfies both S and N, and that
S and N are unequal. It also asserts that `(1,1,0,0)` is feasible and
satisfies both N and D, and that N and D are unequal.

The second conjunct says that there does not exist a function f from all
natural-number quadruples to the five-label type such that, for every
quadruple x, if x is feasible, then for every label e, satisfaction of the
printed predicate for e implies `f(x) = e`. Quantifier order is
`¬∃ f, ∀ x, feasible(x) → ∀ e, printed(x,e) → f(x)=e`.
This prohibits simultaneous satisfaction of all printed implications. It
does not prohibit selecting one label after imposing a priority convention.

The third conjunct says: for every quadruple x, assuming feasibility,
(i) its S predicate implies its N predicate, and
(ii) `s=1`, then `z=1`, then `r=0` imply both N and D.

Junk conventions: all coordinates are natural numbers and inequalities
are natural-number inequalities. There is no subtraction, division,
coercion, probability, integral, logarithm, root, power, extremum, or limit.
All predicates are total; the generated match is exhaustive and supplies
no default value. The quantified type of labels is inhabited and has five
distinct elements. Feasible quadruples are inhabited by both displayed
witnesses. No overlap is obtained by using malformed negative counts.

The docstring describes the two feasible overlaps and the absence of a
single-valued function satisfying all rules; this is the precise form of
the negative function assertion.

## SAP.P037a.T8

Source: Challenge/Part1.lean:78–80; Defs/Part7.lean:33–40;
Defs/Part1.lean:44–54,63–68.

An exposure datum is again an arbitrary quadruple `(s,z,p,r) ∈ ℕ⁴`.
Feasibility is exactly `s ≤ 1 ∧ z ≤ s ∧ r ≤ p`. The five labels are
distinct nullary constructors C, S, N, R, D. Here their predicates are:

| Label | Corrected predicate |
| --- | --- |
| C | `s = 0` |
| S | `s = 1 ∧ z = 0 ∧ p = 0` |
| N | `s = 1 ∧ z = 0 ∧ 0 < p ∧ r = 0` |
| R | `s = 1 ∧ z = 0 ∧ 0 < r` |
| D | `z = 1` |

There are no outer parameters or premises. The main assertion is: for every
quadruple x, after assuming feasibility, there exists exactly one label e
whose corrected predicate holds at x. In expanded quantifiers, this is
`∀ x, feasible(x) → ∃ e, corrected(x,e) ∧
∀ e', corrected(x,e') → e'=e`.
It asserts both coverage and uniqueness, not merely pairwise disjointness.
The two additional conjuncts say `(1,0,0,0)` satisfies S and `(1,1,0,0)`
satisfies D. These particular conjuncts do not separately state feasibility,
but both quadruples satisfy all three feasibility inequalities directly.

The corrected N predicate adds absence of direct treatment and the presence
of at least one treated peer. R need not expressly require p positive,
because feasibility and r positive imply p positive. D need not expressly
require s one, because feasibility and z one imply s one.

Junk conventions: only natural-number fields, ordinary comparisons, finite
constructor case distinctions, and existence/uniqueness are used. There is
no arithmetic operation with an exceptional domain, no mean or integral,
and no partial/default-valued function. Feasibility is nonempty; the label
type is nonempty. No implication here can rely on an empty domain.

The docstring's partition and two classifications agree with this literal
reading; no comparison with an external definition has yet been made.

## SAP.P037a.T9

Source: Challenge/Part1.lean:82–84; Defs/Part7.lean:42–68;
Defs/Part1.lean:12–22,70–72,77–94.

For a finite type Ω, a design is a real weight function q on Ω satisfying
`q(w) ≥ 0` for every w and the Mathlib finite sum `Σ_w q(w) = 1`.
For any real function Y on Ω, the definitions mean exactly

`E_q Y = Σ_w q(w)Y(w)`,

`V_q Y = Σ_w q(w)Y(w)² - (Σ_w q(w)Y(w))²`,

and for an event F, `P_q(F) = Σ_w q(w) 1_F(w)`.
These are finite real sums. No Bochner integration is used.

For J draws, the sample space is the finite function type `Fin J → Ω`.
The specified weight of a sample vector w is `Q_J(w)=Π_{j∈Fin J}q(w(j))`.
This is an actual product law, not an assumption of equal marginal laws
without independence. The more general product constructor allows distinct
finite spaces and designs at each finite index; its positivity and total
mass are proved using finite products and sums.

There are no outer parameters or premises. The first major conjunct has
the following universal quantifier order: for every finite type Ω in
`Type`, every design q on it, every event `E : Ω → Prop`, and every
decision procedure for E, define `X(w)=1` when E(w) and zero otherwise,
and `π=Σ_w q(w)X(w)`. Then:

1. `V_q X = π(1-π)`.
2. For every natural J, assuming `0<J`, define
   `H_J(w)=(Σ_j X(w(j)))/(J:ℝ)` on the product sample space. Then
   `E_{Q_J}H_J=π`, `V_{Q_J}H_J=π(1-π)/J`, and
   `V_{Q_J}H_J ≤ 1/(4J)`. Further, for every real ε, assuming `0<ε`,
   `P_{Q_J}(ε < |H_J-π|) ≤ 1/(4Jε²)`.
3. For every real ε, assuming `0<ε`, as natural J tends to infinity,
   `P_{Q_{J+1}}(ε < |H_{J+1}-π|)` tends to the real number zero.
   This is Mathlib `Filter.Tendsto` from `atTop` on naturals to `nhds 0`
   on reals. It allows the probability space to vary with sample size and
   gives the usual probability-of-error form of consistency.

The second major conjunct quantifies first over natural J, assumes J
positive, then quantifies over real v and target a. It says

`1_{((Σ_{j∈Fin J} v)/J)=a} = 1_{v=a}`.

The summand is the same real v for every index. This assertion itself has
no array of exposure values or an index selecting a last draw. It supplies
the algebraic simplification of a repeated scalar.

The third conjunct contains three fixed calculations. For any type A with
decidable equality the frequency helper is
`frequency(J,z,a)=(Σ_{j∈Fin J} 1_{z(j)=a})/(J:ℝ)`.
The calculations are `frequency(2,[0,1],1)=1/2` for a natural-valued
array; `1_{(1+1)/2=1}=1`; and `1_{(0+1)/2=1}=0`, with the latter
two equalities interpreted in the reals. They distinguish an empirical
frequency from both zero and one but do not define a printed-formula
function of a full array.

Junk conventions: the general frequency helper gives zero at J=0 because
the sum is empty and real division by zero gives zero. All universal
statistical and repeated-scalar conclusions exclude J=0 by hypothesis;
the limit uses J+1. Positive ε excludes the other potentially zero
denominator. Natural casts to real are exact and nonzero at positive J.
If a product has zero indices it is one and the empty function space has
one element; those conventions give a legitimate empty product law, but
that case is not used to prove the positive-sample conclusions. A finite
empty Ω cannot admit a design, since its total mass would be zero rather
than one; many nonempty designs exist. Zero-weight outcomes and events of
probability zero or one are explicitly permitted and cause no undefined
quantity. The event-decidability premise is classical logic, not an
assumption about independence or a rate. There are no logs, square roots,
real powers, extended-real conversions, infima/suprema, limsup/liminf, or
partial functions. The limit is an actual convergence assertion, not a
totalized extremum of an unbounded sequence.

The docstring describes unbiasedness, variance, Chebyshev and consistency
for independent finite-design draws. Its phrase about the printed formula
using the last draw is represented only by the repeated-scalar identity
and fixed calculations, rather than a function of the array.

## SAP.P037a.T10

Source: Challenge/Part1.lean:86–88; Defs/Part7.lean:70–106;
Defs/Part1.lean:12–42.

The first sample space is `Fin 6`, with weights `q(w)=1/6`. Its six
states enumerate the pairs of treated schools from four school indices
`Fin 4` in this order:

`(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)`.

Define `T_i(w)` to be the real indicator that school i belongs to the pair
at w. This unfolds the finite vector lookup and treatment predicate in
full. Define `E_q Y=Σ_w q(w)Y(w)`,
`V_q Y=Σ_w q(w)Y(w)²-(Σ_w q(w)Y(w))²`, and
`C_q(Y,Z)=Σ_w q(w)Y(w)Z(w)-(Σ_w q(w)Y(w))(Σ_w q(w)Z(w))`.

The second sample space is `Fin 6 × Fin 6`, with constant weight
`q₂(u,v)=1/36`. The treatment functions in its first and second block are
`T_i(u)` and `T_j(v)` respectively.

There are no outer parameters or premises. The conjunction asserts:

1. For every w and school i, `T_i(w)=0 ∨ T_i(w)=1`, and for every w,
   `Σ_i T_i(w)=2`.
2. For every school i, `E_q T_i=1/2`. For every ordered pair i,j,
   assuming `i≠j`,
   `E_q(T_iT_j)=1/6`, `C_q(T_i,T_j)=-1/12`,
   `C_q(1-T_i,1-T_j)=-1/12`, and
   `E_q(T_iT_j) ≠ (E_qT_i)(E_qT_j)`.
   Thus the displayed control-exposure functions are specifically the
   complements of school assignment indicators.
3. For every finite type Ω in `Type`, every nonnegative unit-sum real
   weight function q on Ω, and every family `T : Fin 4 → Ω → ℝ`,
   first assume all T_i(w) are zero or one, then assume
   `Σ_i T_i(w)=2` for every w, then assume `E_q T_i=1/2` for every i.
   The conclusions are
   `V_q(Σ_i T_i)=0`, `Σ_i V_q(T_i)=1`,
   `Σ_i Σ_j [if i=j then 0 else C_q(T_i,T_j)]=-1`, and
   `∃ i,j, i≠j ∧ C_q(T_i,T_j)<0`.
   The covariance sum counts ordered off-diagonal pairs. This general
   assertion concludes a negative pair exists, rather than claiming that
   all pairs have the same covariance for every balanced fixed-count law.
4. For every u,v, `q₂(u,v)=q(u)q(v)`; for every i,j the covariance under
   q₂ of `T_i(u)` and `T_j(v)` is zero.
5. The Cartesian-product state space has cardinality 36, and each of its
   states (universally quantified u,v) has weight `1/36`.

The general assertion has nontrivial hypotheses, but the six-state uniform
law and its explicit treatment functions are a direct candidate satisfying
all of them. Product factorization is asserted for complete block states,
which is stronger than the displayed treatment zero covariances alone.
There is no general model of student networks in this closure.

Junk conventions: all sums are over finite types and all random variables
are finite real-valued functions, so no nonintegrable mean is involved.
The only divisions have positive constant denominators. Real subtractions
such as `1-T_i` are not truncated. `Fin 4` and `Fin 6` are nonempty;
their numeral indices lie in range (Lean's modular finite numeral
convention therefore changes none of them). The finite vector lookup is
total and has no out-of-range default. The generalized Ω cannot be empty
if a design exists, by its mass-one requirement. No log, root, rpow,
extended-real conversion, extremum, limit, or partial-function default
appears in the statement closure.

The docstring describes within-block negative dependence and a product
law for independently randomized blocks. Literally, the product-law part
here treats two independent copies of the explicit six-state law.
