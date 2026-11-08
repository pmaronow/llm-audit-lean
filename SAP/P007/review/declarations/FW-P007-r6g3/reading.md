# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: the five
Challenge docstrings/statements, all source declarations named by `closure.json`,
and all its generated auxiliary declarations (printed by the successful
`scratch/ClosureCheck.lean` compilation). No claim/record information is used here.

## SAP.P007.T11

Source: `SAP/P007/Challenge/Part1.lean:70-73` and
`SAP/P007/Defs/Part3.lean:124-131`.

The statement is a conjunction of a universal identity and an existential example.
In all the following formulas a Boolean `true` means missing and `false` observed.
`Row k` is the function type `Fin k → Bool`; `Array n k` is
`Fin n → Fin k → Bool`. A `Law` on this finite type consists of real weights
`w(x) ≥ 0` for every array, with `Σ_x w(x) = 1`. `Law.mk` constructs exactly
these data and `Law.weight` projects `w`. Thus there is an ordinary probability
distribution on every Boolean array, and no assumption about the underlying
values of the observations. `probability L P` is exactly
`Σ_x (if P(x) then w(x) else 0)`.

First, for every natural `n,k`, in that order, if `n>0` and `k>0`, then for every
such normalized law L, if for **every** family of row events
`E_i : (Fin k → Bool) → Prop` one has

`Σ_x 1_{∀i E_i(x_i)} w(x) = Π_i Σ_x 1_{E_i(x_i)} w(x)`,

then

`Σ_x 1_{∀i ¬(∀t : Fin k, t.val<k → x_i(t)=false)} w(x)
 = Π_i (1 - Σ_x 1_{∀t : Fin k, t.val<k → x_i(t)=false} w(x))`.

In ordinary notation, writing `s_i(j)=P(∀t<min(j,k), X_it is observed)`,
this is `P(every row has a missing entry) = Π_i(1-s_i(k))`.
The independence hypothesis is mutual independence of the entire row vectors,
not merely pairwise independence or independence of individual cells.
There is no observation-bound hypothesis in this first conjunct.

Second, there exists a normalized law on `Fin 2 → Fin 1 → Bool` whose weight at
an array x is

`Π_(i : Fin 2) Π_(j : Fin 1)
  (if x_i(j)=true then 1-a_i else a_i)`,

where `a_0=1/4` and `a_1=1/2` (the finite vector literal has precisely those
two entries). This law must simultaneously satisfy:

* the mutual-independence identity above;
* the bound `observationBound L (1/2)`, meaning `0≤1/2<1`,
  `s_i(1)≤1/2` for each row (the dimension is positive), and
  `s_i(j+1)/s_i(j)≤1/2` for every natural j with
  `1≤j<1` and `s_i(j)>0` (there are no such j);
* the negation of `∀i,j,E, P(E(X_i))=P(E(X_j))`, so the row-vector
  distributions are not all equal;
* `s_0(1)=1/4`, `s_1(1)=1/2`,
  `P(every row has a missing entry)=3/8`,
  `(1-(1/2)^1)^2=1/4`, and
  `(1-(1/2)^1)^2≤P(every row has a missing entry)`.

These unfold `cellWeights`, `nonidenticalWeights`, `sameRowLaw`, `lowerBound`,
`prefixObserved`, `survival`, `allDeleted`, and `observationBound` completely.
The docstring describes the failure of identical distribution to follow from
independence, illustrated by this witness and product identity.

Junk/edge conventions: sums and products are finite, so no integrability or
measurability issue is concealed. The ratio in `observationBound` is guarded by
a strictly positive denominator; in the one-column witness it is never used.
All displayed rational denominators are nonzero. Natural exponents are ordinary
integer powers, with Mathlib's `a^0=1` convention; both dimensions are positive
where used. Empty `Fin` types would make empty conjunctions/products true/one,
but the quantified dimensions exclude them, and the witness uses 2 and 1.
The space of arrays itself is inhabited even at zero dimensions. No truncated
subtraction, real logarithm/power/square-root, supremum/infimum, partial function,
extended-real conversion, or integral occurs. The generated closure declarations
are numeral infrastructure: `T11Statement._proof_1` proves `NeZero 2`;
`T9Statement._proof_1` proves `8.AtLeastTwo`;
`laterNullWeights._proof_1` and `workedValues._proof_1` prove `2.AtLeastTwo`;
`unequalModel._proof_1` proves `3.AtLeastTwo`; and
`unequalModel._proof_2` and `unequalWeights._proof_2` prove `4.AtLeastTwo`.
Their names do not import the semantic statements of those other definitions.

## SAP.P007.T12

Source: `SAP/P007/Challenge/Part1.lean:75-79` and
`SAP/P007/Defs/Part4.lean:10-35`.

There are three universally quantified conjuncts. For any finite column type J,
`missingCount m` is the natural number `Σ_(j:J) Σ_(i:Fin n) 1_{m_ij=true}`.
`missingAverage m` is the real number
`[Σ_(j:J) (Σ_(i:Fin n) 1_{m_ij=true})/n]/|J|`.
It averages each column's missing fraction, giving all columns equal weight.
All indicators in this average are real numbers; all indicators in the count
are natural numbers.

First, for every natural n,K,d, in that order, if n>0 and K>0, for every Boolean
matrix `m : Fin n → (Fin K ⊕ Fin d) → Bool`, if
`m(i,inr j)=true` for every i,j, put A=`missingCount m` and
`m'(i,j)=m(i,inl j)`. Thus the last d columns are wholly missing, and the first
K columns are retained. There is no hypothesis that each retained column has an
observed entry. The conclusion is all five identities:

1. `A = missingCount m' + n*d` (natural arithmetic).
2. `missingAverage m = A/[n(K+d)]` (real arithmetic).
3. `missingAverage m' = (A-n*d)/(n*K)` (real subtraction after casting A).
4. `(K+d)*missingAverage m = d + K*missingAverage m'`.
5. `missingAverage m' = [(K+d)*missingAverage m - d]/K`.

Second, for every `m : Fin 8580 → (Fin 1205 ⊕ Fin 19) → Bool`, if all the
19 right-hand columns are missing, and
`0.6675≤missingAverage m<0.6685`, then all three inequalities hold:

`missingAverage m' < 199811/301250`,
`199811/301250 < 0.6675`, and `missingAverage m' < 0.6675`.

Third, for every matrix of those same dimensions, if all 19 right-hand columns
are missing and `missingCount m=7019387`, then all these conclusions hold:

* `missingAverage m = 7019387/10501920`;
* `missingAverage m' = 6856367/10338900`;
* `0.6625≤missingAverage m'<0.6635`;
* `missingAverage m-missingAverage m'=66168127/12654813600`;
* `100*(missingAverage m-missingAverage m')=66168127/126548136`.

The docstring describes removal of wholly missing columns, incompatibility of
the printed retained average with the original rounded average, and a corrected
retained average and overstatement under the specified exact missing-cell count.

Junk/edge conventions: the definitions would assign zero to division by zero
over the reals when n=0 or J is empty. Here n,K>0, so both J=`Fin K ⊕ Fin d`
and `Fin K` are nonempty and every average denominator is positive. d may be
zero: the removal condition is then vacuous and the identities express no change.
The hypotheses force A≥n*d; moreover the subtraction in the conclusion is in
the reals, not truncated natural subtraction. Casts are exact embeddings of
finite natural counts and dimensions. There is no overflow, partial array
lookup, unbounded sum, integral, `toReal`, log, square-root, real power,
supremum/infimum, limsup/liminf, or default value. The auxiliary declarations
`T12Statement._proof_1` through `_proof_10` prove, respectively,
`AtLeastTwo` for 199811, 301250, 7019387, 10501920, 6856367, 10338900,
66168127, 12654813600, 100, and 126548136. These are numeral elaboration
proofs and add no assumptions or mathematical clauses.

## SAP.P007.T14

Source: `SAP/P007/Challenge/Part1.lean:81-84` and
`SAP/P007/Defs/Part4.lean:37-39`.

Quantifiers/hypotheses, in order: for every n,k in the naturals, if n>0 and k>0,
for every normalized distribution L on the finite type
`Fin n → Fin k → Bool`, and then every real q, assume mutual independence of
row vectors and the observation bound below. A law is a real weight function
`w(x)≥0`, `Σ_x w(x)=1`; its probability of event P is
`Σ_x (if P(x) then w(x) else 0)`. Missing means true.

Mutual independence says for every family `E_i : (Fin k → Bool) → Prop`,
`P(∀i E_i(X_i))=Π_i P(E_i(X_i))`. Define, merely as notation,
`s_i(j)=Σ_x 1_{∀t:Fin k, t.val<j → x_i(t)=false} w(x)`.
The observation-bound hypothesis is exactly the conjunction:

* `0≤q`;
* `q<1`;
* for each i, `(0<k → s_i(1)≤q)`;
* for each i and each natural j, if `1≤j`, `j<k`, and `s_i(j)>0`, then
  `s_i(j+1)/s_i(j)≤q`.

The conclusion is
`(1-q^k)^n ≤ Σ_x 1_{∀i ¬(∀t:Fin k, t.val<k → x_i(t)=false)} w(x)`:
the probability that **every** row has at least one missing entry is at least
`(1-q^k)^n`. This completely unfolds `Row`, `Array`, `Law`, `probability`,
`prefixObserved`, `survival`, `rowIndependent`, `observationBound`, and
`allDeleted`. No identical-distribution or within-row independence hypothesis
is present. The docstring calls this the printed conditional observation bound.

Junk/edge conventions: natural powers, not `Real.rpow`, occur; q=0 is allowed
but k>0 prevents `0^0` in the bound. Every conditional denominator is positive
where division is asserted, so real division at zero cannot strengthen the
hypothesis. A null observed prefix imposes no conditional ratio constraint.
The zero prefix is a true empty conjunction of probability one. For j≥k the
prefix predicate saturates at the entire row, but the theorem only tests the
listed ranges. Positive n,k rule out empty row or column indices in the bound.
All sums/products are finite over a nonempty array state space, and all weights
are normalized; there are no integrability, real-domain, truncated-subtraction,
extended-real, extremum, limsup/liminf, or partial-function conventions.

## SAP.P007.T15

Source: `SAP/P007/Challenge/Part1.lean:86-89` and
`SAP/P007/Defs/Part4.lean:41-43`.

For every natural n,g in that order, if n>0 and g>0, for every L and then every
real q, where L has weights `w(x)≥0`, `Σ_x w(x)=1` on
`x : Fin n → Fin g → Bool`, assume:

1. For every family of group-indicator row events
   `E_i : (Fin g → Bool) → Prop`,
   `Σ_x 1_{∀i E_i(x_i)} w(x) = Π_i Σ_x 1_{E_i(x_i)} w(x)`.
2. `0≤q<1`, and for every row i,
   `P(∀t<1, x_i(t)=false)≤q` (g>0); furthermore, for every natural j,
   `1≤j<g` and `P(∀t<j, x_i(t)=false)>0` imply
   `P(∀t<j+1, x_i(t)=false)/P(∀t<j, x_i(t)=false)≤q`.
   Here each t ranges over `Fin g`, and each P is the finite sum with weight w.

Then `(1-q^g)^n ≤ Σ_x 1_{∀i ¬(∀t:Fin g, x_i(t)=false)} w(x)`.
Thus every row has some missing group with at least the stated probability.
The mathematical statement is T14 with g in place of k. Its coordinates can
represent groups sharing a missingness pattern. There is no explicit partition
of original variables, original variable count, group size, or map from variables
to groups in the statement. There is also no condition on within-row dependence
or identical row distributions. These formulas unfold every SAP definition in
the closure. The docstring interprets the coordinates as groups and calls the
assumption the printed group observation bound.

Junk/edge conventions: q=0 is allowed, g>0 excludes `0^0` in the bound, and the
real ratio is used only for a positive conditioning probability. Zero-probability
prefixes impose no ratio inequality. The all-observed predicate and probability
are finite predicates/sums, and independence is a finite product identity.
The positive n,g hypotheses exclude empty row/group indices; the array state
space is always inhabited. There are no integrals, undefined expectations,
`toReal`, real powers/logarithms/square-roots, truncated subtraction,
suprema/infima, limsup/liminf, or defaults of partial functions.

## SAP.P007.T16

Source: `SAP/P007/Challenge/Part1.lean:91-95`,
`SAP/P007/Defs/Part4.lean:45-52`, and `SAP/P007/Defs/Part1.lean:61-62`.

For every function `k : ℕ → ℕ`, then every dependent family L with
`L_n : Law (Fin n → Fin (k n) → Bool)`, assume
`∀n, 0<n → 0<k(n)`. Then for every single real q, assume in order:

* `0≤q`;
* `q<1`;
* `∀n>0`, the entire row vectors under L_n are mutually independent;
* `∀n>0`, L_n satisfies the conditional observation bound with that same q;
* `k(n)/log(n) → +∞` as n tends to infinity through the naturals.

The conclusion is
`P_(L_n)(∀i:Fin n, ∃t:Fin (k n), X_it=true) → 1`.
Equivalently, the all-row deletion probability converges to one.

More explicitly, each L_n consists only of weights `w_n(x)≥0` with
`Σ_x w_n(x)=1`. Every probability in the assumptions and conclusion is
`Σ_x (if the stated predicate on x then w_n(x) else 0)`.
For each n>0 mutual independence is the equality of the probability of
`∀i E_i(X_i)` to the product of `P(E_i(X_i))` for **every** family
`E_i : (Fin (k n) → Bool) → Prop`. Put
`s_(n,i)(j)=Σ_x 1_{∀t:Fin (k n), t.val<j → x_i(t)=false} w_n(x)`.
The observation assumption says `0≤q<1` and for every i,
`(0<k(n) → s_(n,i)(1)≤q)` and
`∀j, 1≤j → j<k(n) → s_(n,i)(j)>0 →
 s_(n,i)(j+1)/s_(n,i)(j)≤q`.
The conclusion's probability is
`Σ_x 1_{∀i ¬(∀t:Fin (k n), t.val<k(n) → x_i(t)=false)} w_n(x)`.
Thus all SAP notions have been reduced to finite sums, products, function
types, real inequalities/division, and Mathlib filters/topology/logarithm.

The growth hypothesis is `Tendsto (fun n => (k n : ℝ)/Real.log (n : ℝ))
atTop atTop`: for every real threshold M, eventually all n have this ratio
at least M. The conclusion is Mathlib `Tendsto` at `𝓝 1`, equivalently for
every ε>0 there is N such that all n≥N have deletion probability within ε of 1.
No coupling, consistency of marginal distributions, or independence between
different n is required. L_0 exists but has no independence/observation/positive
dimension requirement. The docstrings explicitly permit changing laws, include
q=0, and explain that n=0 extends the sequence solely for the natural filter.

Junk/edge conventions: `Real.log 0=0`, `Real.log 1=0`, and real division by zero
is zero, so the growth-ratio sequence has value zero at n=0 and n=1 regardless
of k. These two terms do not affect either `atTop` limit. For n≥2 the logarithm
is positive, so the eventual growth condition is ordinary superlogarithmic
growth. At n=0 the row index type is empty, the all-deletion event is true,
and its probability is one for every normalized L_0. This initial value cannot
affect convergence. All conditioning ratios are guarded by positivity; n>0
also forces k(n)>0. All counts/casts are exact. No real powers, square-roots,
extended-real conversions, Bochner integrals, truncated subtraction,
suprema/infima, limsup/liminf, or partial-function defaults occur.
