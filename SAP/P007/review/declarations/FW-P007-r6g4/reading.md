# Blind reading

This file was written before opening `claims.json` or `record.json`.

## SAP.P007.T17

### Sources and complete unit closure

The declaration and its docstring are at `SAP/P007/Challenge/Part1.lean:97–101`.
The elaborated statement is `SAP.P007.T17Statement`, defined at
`SAP/P007/Defs/Part4.lean:54–59`. Every unit declaration listed in `closure.json`
has been read: `Array`, `Law`, `Law.mk`, `Law.weight`, `Row`, `T17Statement`,
`allDeleted`, `observationBound`, `prefixObserved`, `probability`,
`rowIndependent`, `superlog`, and `survival`. `Law.mk` and `Law.weight` are the
constructor and projection of the structure at `Defs/Part1.lean:18–21`, whose
nonnegativity and normalization fields are also accounted for below.

### Objects and unfolded definitions

For a natural number h, a row is a function from the finite set
{0,...,h−1} to the Booleans. A true entry denotes missingness, and a false
entry denotes observation. An n-by-h array is a function from
{0,...,n−1} to those rows. The row docstring permits a coordinate to represent
a variable or a nonempty group of variables with a shared missingness pattern.

A `Law` on a finite type A consists of a real weight w(a) for every a in A,
proofs w(a) >= 0 for every a, and the normalization sum over A of w(a) = 1.
There is no implicit uniformity or independence in a Law. Its probability of
an event P is the finite real sum of w(a) over all a satisfying P (formally,
the sum of `if P a then w(a) else 0`). These are actual probabilities on a
finite discrete space.

For a row r of length h, `prefixObserved r j` means that for every coordinate
t in {0,...,h−1} with t < j, r(t) is false. For 0 <= j <= h it says the first
j coordinates are observed. For j = 0 the event is universal; for j >= h it
says the entire row is observed. For a law L on n-by-h arrays,
`survival L i j` is the finite probability of that prefix event in row i.

`allDeleted L` is the finite probability that every row fails the
all-observed event: for each i there is a coordinate t < h with x(i,t) true.
Thus every row has at least one missing coordinate. It is the probability
that complete-case deletion deletes all rows, not an expected deleted
fraction and not a separate event about each column.

`rowIndependent L` means that for every family of row events E_i, the
probability of the intersection of all events E_i(x_i) equals the product
of their marginal probabilities. Events are arbitrary predicates on the
finite Boolean row space. This is full mutual independence of the row
vectors, with no requirement of identical row distributions and no
independence requirement between coordinates of a row.

`observationBound L q` means all of the following:

1. q is real, 0 <= q, and q < 1.
2. For every row i, if h > 0 then P(x(i,0) is observed) <= q.
3. For every row i and every natural j with 1 <= j < h, if the probability
   s(i,j) of observing the first j coordinates is positive, then
   s(i,j+1) / s(i,j) <= q.

The ratio in (3) is the usual conditional probability that coordinate j is
observed given observation of its predecessors. There is deliberately no
condition at a prefix of probability zero. The explicit first-coordinate
bound supplies the j = 0 case without division.

`superlog g` means that the real sequence g(n) / log(n) tends to positive
infinity as the natural number n tends to infinity. In elementary terms,
for every real M there is N such that g(n) / log(n) >= M for all n >= N.
The natural values n and g(n) are cast exactly to real numbers.

### Statement and quantifier order

For every function g : N -> N, and for every family L which assigns to each
natural n a finite probability law on n-by-g(n) Boolean arrays, assume:

1. For every n > 0, g(n) > 0.
2. Fix a single real q with 0 <= q < 1.
3. For every n > 0, the row vectors of L(n) are mutually independent in
   the event-factorization sense above.
4. For every n > 0, all the first-coordinate and positive-prefix conditional
   observation probabilities of L(n) satisfy the same fixed bound q.
5. g(n) / log(n) tends to positive infinity.

Then P under L(n) that every one of its n rows has at least one missing
coordinate tends to 1. Formally this is convergence of a real sequence to
1 in the real topology, along the natural-number `atTop` filter; equivalently,
for every real epsilon > 0 there is N such that for all n >= N the absolute
difference between that probability and 1 is less than epsilon.

The precise binder order is g, L, positivity of g at every positive n, q,
nonnegativity of q, q < 1, independence at every positive n, observation
bounds at every positive n, superlogarithmic growth, conclusion. In
particular, q is independent of n. No common sample space, coupling between
different n, identical row laws, or independence within rows is required.

The docstring describes this as the group-indicator version of an
all-deletion asymptotic result, with independent rows, one fixed bound and
superlogarithmic group count, explicitly allowing q = 0.

### Totalization, boundary values, and junk-value audit

- The one potentially partial arithmetic operation in the conditional bound
  is real division. Real division by zero is defined as zero in Lean.
  However, the ratio is required only under the strict hypothesis
  s(i,j) > 0. Thus division by zero cannot help satisfy a relevant bound.
  For a null prefix the extension is also null, since the prefix events are
  nested; no arbitrary conditional probability is asserted there.
- `superlog` divides by `Real.log (n : R)`. In Mathlib log(0) = log(1) = 0,
  so the ratio is zero at n = 0 and n = 1, regardless of g there. These
  finitely many terms have no effect on `atTop` convergence. For n >= 2
  log(n) is the ordinary strictly positive logarithm. Negative arguments
  never arise because n is natural (Mathlib's extension of log to negative
  reals is consequently irrelevant).
- The arrays and their laws are defined at n = 0. The row index is empty,
  the universal all-deleted event is true, and its probability is 1.
  Independence and observation assumptions are not required there. This
  initial value has no effect on the limit.
- A zero column/group count produces an empty coordinate type and a
  universally observed row. For positive n, its all-deleted probability
  would be 0. The theorem excludes this case by g(n) > 0 for every n > 0;
  g(0) is unconstrained and harmless.
- Finite empty sums and products have their usual values 0 and 1. The
  array state space itself is never empty: a Boolean function exists for
  every choice of dimensions, including zero. There is no fabricated law
  on an empty state space.
- Prefix indices j outside the coordinate range are meaningful through the
  test t < j and simply saturate at the full row; only 1 <= j < h enters
  the conditional ratio. The successor j+1 is natural addition, with no
  truncated subtraction.
- All natural-to-real casts are exact. There are no integer casts, square
  roots, real powers, extended-real conversions, infima/suprema, liminf/
  limsup, partial functions with defaults, integrals, or means in the
  target's closure. Finite summation defines probabilities without any
  measurability or integrability issue. Classical predicate decisions in
  the event sums do not change the probabilities.

No conclusion about the canonical claim or architect's decision is made
at this blind stage.
