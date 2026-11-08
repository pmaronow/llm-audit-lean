# Blind reading

This file was written before opening `claims.json` or `record.json`. The source
docstring was read as part of the target, without treating its interpretation as
evidence that its statement matches any external claim.

## SAP.P045a.T16

Location: `SAP/P045a/Challenge/Part1.lean:174` (docstring), line 183 (theorem).
Statement definition: `SAP/P045a/Defs/Part6.lean:60`.
Fingerprint: `30f5375cb477f17f0f09f456a679fa8b5bc9cd2bb1f2cc0860a79838df2b21e4`.

### Objects and definitions, completely unfolded

All vertices belong to `Fin 10`, the natural numbers 0 through 9. An
`Assignment 10` is a function from these vertices to `Bool`; `true` means treated.
`Exposure` is a four-element inductive type with constructors `d11`, `d10`,
`d01`, and `d00`. The first digit is the vertex's treatment indicator; the second
is 1 exactly when at least one adjacent vertex is treated. More explicitly, for
a Boolean matrix A and assignment z, the exposure at i is d11 if z(i) is true
and there exists j with A(i,j) = true and z(j) = true; d10 if z(i) is true and
no such j exists; d01 if z(i) is false and such j exists; and d00 otherwise.
There is no outcome or statistical assumption hidden in this type.

`printedAdj` is the fixed Boolean matrix with the following neighbor sets:

| Vertex i | Neighbors | Degree g(i) |
| --- | --- | --- |
| 0 | 1, 2, 4 | 3 |
| 1 | 0, 2, 3, 9 | 4 |
| 2 | 0, 1, 3, 4, 5, 8 | 6 |
| 3 | 1, 2, 4, 5, 6 | 5 |
| 4 | 0, 2, 3, 5, 7 | 5 |
| 5 | 2, 3, 4 | 3 |
| 6 | 3, 7, 8 | 3 |
| 7 | 4, 6, 8, 9 | 4 |
| 8 | 2, 6, 7, 9 | 4 |
| 9 | 1, 7, 8 | 3 |

This is a symmetric, loopless graph; its degree sum is 40.

Let P = {(u,v) : u,v in Fin 10 and u < v}. This is precisely the finite set
`treatmentPairs`, represented by a filter of the finite Cartesian product.
It contains 45 elements. `pairAssignment (u,v)` assigns true to exactly u and v
(to a single vertex if u = v, but only distinct pairs are used in this theorem).
For d in Exposure, define the following ordinary finite expressions:

- C_d(e) = {i in Fin 10 : exposure(printedAdj, pairAssignment(e), i) = d}.
  `pairCellNonempty d e` means that this set contains a vertex, i.e. there exists
  i of that exposure.
- For any finite set S, `average S f` is `(sum over e in S of f(e)) / |S|`,
  with the natural cardinality cast to the reals.
- p_i(d) = `(sum over e in P of 1{ i in C_d(e) }) / |P|`.
  This is exactly `pairExposureProb printedAdj i d`: the exposure probability
  under the uniform distribution on all distinct unordered treatment pairs.
- `dilated b d` is 2b at d11, (3/2)b at d10, (5/4)b at d01, and b at d00.
  The theorem uses only b = 1 at every vertex. Thus its outcome table y_i(d)
  is constantly 2, 3/2, 5/4, 1 over vertices, for the four respective exposures.
- H_d(e) = `sum over all i in Fin 10 of
  (if i in C_d(e) then y_i(d) / p_i(d) else 0)`.
  This is `pairHT printedAdj (fun _ => dilated 1) d e`, an HT population total,
  not an HT population mean.
- T(e) = `(H_d11(e) - H_d00(e)) / 10`, exactly `printedContrast e`.

The definitions of `pairHT` and `pairExposureProb` accept arbitrary Boolean
matrices, and the former also accepts arbitrary real outcome tables. Here they
are applied only to the fixed matrix and outcome table just given; no universal
assertion about all matrices or outcome tables is made.

### Quantifiers, hypotheses, and conclusions

The theorem has no parameters and no hypotheses. It asserts the conjunction
below. All displayed numbers in divisions are real numbers after elaboration;
the subtraction `9-g` inside a natural expression is explicitly identified below.
The quantifier over i in item 1 scopes only that item's four equalities and
positivity assertion. The quantifier over i in item 3 scopes only its equivalence.
All subsequent assertions are closed numerical equalities or cardinalities.

1. For every i in Fin 10, let the natural number g be its degree, that is the
   cardinality of the neighbor set above. Then
   p_i(d11) = g/45,
   p_i(d10) = (9-g)/45,
   p_i(d00) = choose(9-g,2)/45,
   p_i(d01) = (36-choose(9-g,2))/45,
   and for every d in Exposure, p_i(d) > 0.
   In both occurrences under `choose` and in the d10 numerator, 9-g is natural
   subtraction before casting; the subtraction from 36 is real subtraction.
2. C_d11((5,8)) is empty, expressed as the negation of an existential vertex.
3. For every i in Fin 10, i belongs to C_d00((5,8)) if and only if i = 0 or i = 1.
4. H_d11((5,8)) = 0.
5. H_d00((5,8)) = 15/2.
6. T((5,8)) = -3/4.
7. Let P11 = {e in P : C_d11(e) is nonempty}. Then |P11| = 20.
8. Let P11,00 = {e in P : C_d11(e) and C_d00(e) are both nonempty}.
   Then |P11,00| = 19.
9. `(sum over e in P of H_d11(e)) / |P|` = 20.
10. `(sum over e in P11 of H_d11(e)) / |P11|` = 45.
11. `(sum over e in P of T(e)) / |P|` = 1.
12. `(sum over e in P11 of T(e)) / |P11|` = 651/200.
13. `(sum over e in P11,00 of T(e)) / |P11,00|` = 1227/380.

In items 10, 12, and 13, conditioning is performed by restricting the uniform
support and averaging the original estimator. The inclusion probabilities in
H_d remain those of P, not probabilities recomputed after restriction.

The docstring describes these as retained calculations about an empty exposure
cell and changed expectations under support restrictions. It expressly omits
separate population totals 20 and 10 and true effect 1, a general equivalence
between adjacency of the treated pair and a nonempty d11 cell, and identifying
the exceptional adjacent pair called {3,9} there. It says the unconditional
contrast mean is still explicitly 1. At this blind stage no claim is made about
whether those omissions or the vertex labeling match an external statement.

### Closure inspection

Every entry in `closure.json` was read. The ordinary definitions read directly
were `Assignment`, `Exposure` and all four constructors, `average`, `exposure`,
`printedAdj`, `treatmentPairs`, `pairAssignment`, `pairExposureProb`, `dilated`,
`pairHT`, `printedContrast`, `pairCellNonempty`, and `T16Statement`.

The generated declarations were also inspected using `#print` in
`scratch/BlindPrint.lean` (output in `scratch/blind-print.txt`):

- `Exposure.casesOn`, `Exposure.rec`, and `Exposure.ctorIdx` perform ordinary
  four-way case analysis, with constructor indices 0, 1, 2, 3 respectively.
- `instDecidableEqExposure` and its `_proof_1` and `_proof_2` decide equality
  by equality of constructor indices. Their proof terms express injectivity of
  the index and preservation of indices under equality; they add no hypotheses.
- `cancellingOut2.match_1` is the shared, exhaustive four-constructor match used
  to implement the exposure case split. It has one branch per constructor and
  no default or partial branch.
- `T15Statement._proof_2`, `_proof_5`, `_proof_7` certify `AtLeastTwo` for
  4, 2, 3 respectively. `T16Statement._proof_1`, `_proof_2`, `_proof_4`,
  `_proof_5`, `_proof_6`, `_proof_7`, `_proof_8`, `_proof_9` do the same
  for 45, 36, 15, 20, 651, 200, 1227, 380. Its `_proof_3` certifies
  `NeZero 10`.
- `printedContrast._proof_1` certifies `AtLeastTwo 10`;
  `cancellingOut2._proof_2` certifies `AtLeastTwo 2`;
  `tractOutcome._proof_2`, `_proof_3`, `_proof_6` certify `AtLeastTwo`
  for 4, 3, 5. These are generated numeral elaboration facts, even where the
  auxiliary declaration happens to be named after another theorem or definition.

These auxiliaries introduce neither statistical assumptions nor extra content.

### Junk-value and boundary conventions

- Real division by zero is defined in Lean, with x/0 = 0. The generic `average`
  gives 0 on an empty finite set. The actual averaging supports have sizes 45,
  20, and 19, so none of the asserted averages uses that value. Every denominator
  in the four probability formulas and the contrast is the positive number 45
  or 10; the outcome factors use positive 2 and 4.
- `pairHT` would silently use y/0 if an included unit had zero exposure
  probability. Here all 40 probabilities p_i(d) are asserted strictly positive;
  direct inspection of the degrees 3 through 6 also verifies this. No term in
  this theorem rests on zero-probability division. A realized empty cell instead
  makes every indicator summand zero. This is the usual empty HT sum, not a
  mean divided by a realized cell count.
- Natural subtraction is truncated at 0. Here g ranges from 3 to 6, so `9-g`
  equals ordinary subtraction and lies from 3 to 6. `Nat.choose` returns 0 when
  too many elements are chosen, but here its top argument is at least 3 and its
  bottom argument is 2. Casting these finite natural values to the reals is
  exact. The remaining subtractions occur in the reals and are not truncated.
- Numerals of type `Fin 10` use the standard residue convention modulo 10.
  Every vertex numeral actually used is in range, so it denotes its displayed
  vertex without wraparound. Matrix vectors have exactly ten entries in each
  row and ten rows, and all their indices are in Fin 10.
- The index types Fin 10 and Exposure are nonempty. The universal product used
  for treatment pairs is finite and nonempty, and filtering leaves the positive
  support sizes already given. Existential failure in the d11 cell for (5,8)
  represents the asserted empty cell and does not vacuously discharge an
  implication: there are no hypotheses in this theorem.
- There are no logarithms, square roots, real powers, integrals, infinite sums,
  extended-real `toReal`, infima/suprema, limits, partial-function defaults,
  or unbounded index sets in the statement after unfolding its SAP definitions.
  Finite means require no integrability or measurability assumptions. Finite
  discrete spaces also admit the usual measurable structure without difficulty.

### Blind checks

`scratch/BlindChecks.lean` checks the 45-element design, membership of (5,8),
symmetry and absence of loops, the degree bounds, the realized exposure cells,
and both restricted-support sizes directly from definitions. These checks do
not import or use the Challenge theorem. The theorem has no assumptions needing
a separate satisfiability witness; the finite design itself supplies concrete
data and the support cardinalities show that its averages have nonempty domains.
