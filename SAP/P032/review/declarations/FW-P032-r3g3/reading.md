# Blind reading

This file was written before opening `claims.json` or `record.json`. Sources read:
`closure.json`, the Challenge declarations and docstrings, and the source of every
dependency in the two closures. `scratch/ClosureCheck.lean` also prints all 78
distinct closure declarations, including generated proof declarations; its output
is saved in `scratch/ClosureCheck.log`. These are readings of the statements, not
yet judgments against the canonical claims or the architect's decisions.

## SAP.P032.T8

Location: `SAP/P032/Challenge/Part1.lean:47` (theorem at line 52).
Fingerprint: `0b108c791f84b2bc9e4ea53ae152e1589ea202c3e6bb72adfef6478bcd630753`.

### Objects, definitions, hypotheses and quantifiers

There are no external parameters or hypotheses. This is an unconditional conjunction
about fixed finite data and real numbers. `Fin n` means the natural numbers strictly
less than n, with the standard finite enumeration. All the sums below are ordinary
finite sums over their indicated complete index sets. All arithmetic in the variance,
pooling and fit formulas is real arithmetic, including subtraction.

There are four members i in {0,1,2,3}, six dyads e in {0,...,5}, and 24 records
r=(e,j), j in {0,1,2,3}. A `DyadData M` is a finite subset of M together with a proof
that its cardinality is two; `members` projects the subset, and `mk` constructs this
structure from such a set and proof. The six member sets, in order, are

    D = ({0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}).

Each record (e,j) has member set D[e]. `sixDyadData` constructs precisely these sets.

There are two completed-data types indexed by the two-element type `Bool`:

    s_false = (4,2,2,2,2,0),  s_true = (4,3,3,3,3,2).
    y_B(e,j) = 1 if j < s_B(e), and 0 otherwise.
    p_B = (1/24) sum_r y_B(r).
    b_B = log(p_B/(1-p_B)).
    I_B = 24 p_B (1-p_B).
    z_B(r) = y_B(r)-p_B.

Here log is Mathlib's `Real.log`, equal to the ordinary real logarithm for positive
inputs. These formulas unfold `imputationSuccesses`, `imputationOutcome`,
`imputationProbability`, `imputationEstimate`, `imputationInformation`, and
`imputationScore`. The statement names an estimate using this formula; it does not
separately quantify over regression coefficients or assert an optimization theorem.

The three scalar covariance helpers are the following explicit sums. Their names
do not insert centering, division, expectation, or a small-sample correction:

    recordScalarCovariance(z) = sum_r z(r)^2.
    clusterScalarCovariance(g,z) = sum_k (sum_{r:g(r)=k} z(r))^2.
    memberScalarCovariance(d,i,z) = (sum_{r:i in d(r)} z(r))^2
                                   + sum_{r:i not in d(r)} z(r)^2.

In the generic cluster definition both record and cluster types have finite
enumerations, and cluster equality is decidable. In the generic member definition
the record type has a finite enumeration and member equality is decidable. In this
theorem they are instantiated with the finite sets above, g(e,j)=e and d(e,j)=D[e].
Define, purely as shorthand for the fully explicit expressions,

    V_E(B) = I_B^(-2) sum_r z_B(r)^2,
    V_D(B) = I_B^(-2) sum_e (sum_j z_B(e,j))^2,
    V_i(B) = I_B^(-2) [(sum_{r:i in D[r.e]} z_B(r))^2
                         + sum_{r:i not in D[r.e]} z_B(r)^2].

These are respectively `imputationRecordCovariance`, `imputationDyadCovariance`,
and `imputationMemberCovariance`. The exponent -2 is an integer power, not a
natural exponent or real power. The common scaling is the inverse square of I_B.

The five scalar estimates, viewed as functions on the singleton coefficient set
`Fin 1`, are b=(0,0,0,log 3,log 3). More generally, for m estimates b_t(i),

    estimateAverage(b)(i) = (1/m) sum_t b_t(i),
    betweenCovariance(b)(i,j) = (1/(m-1))
        sum_t (b_t(i)-estimateAverage(b)(i))
              (b_t(j)-estimateAverage(b)(j)),
    rubinContribution(b)(i,j) = (1+1/m) betweenCovariance(b)(i,j).

The matrices here are functions from two coefficient indices to real numbers, and
scalar multiplication is pointwise. In T8, m=5, i=j=0. Write Q for this last scalar.
For each component X in {i,D,E}, define its five-imputation average by

    bar V_X = (3 V_X(false)+2 V_X(true))/5.

These unfold the three `average*Covariance` definitions. Finally, set

    W = sum_{i=0}^3 bar V_i - bar V_D - 2 bar V_E,
    V_correct = W+Q,
    V_code = sum_{i=0}^3 (12/13)(bar V_i/(12/13)+Q)
             - (5/6)(bar V_D/(5/6)+Q)
             - 2(23/24)(bar V_E/(23/24)+Q),
    v_B = sum_i V_i(B)-V_D(B)-2 V_E(B).

These are the complete meanings of `correctPooledVariance`, `codePooledVariance`,
and `imputationDCR`. In particular, neither pooled variance is defined by its
claimed final logarithmic numerical value.

### Entire conclusion

The conjunction asserts all of the following; the displayed finite universal
quantifiers are conclusions, not premises:

1. p_false=1/2, p_true=3/4; b_false=0, b_true=log 3;
   I_false=6, I_true=9/2.
2. V_D(false)=2/9, V_D(true)=8/81; V_E(false)=1/6,
   V_E(true)=2/9; for every i in `Fin 4`, V_i(false)=7/36; and
   the function i -> V_i(true) equals (5/27,5/27,11/81,11/81).
3. v_false=2/9 and v_true=8/81.
4. The average estimate at coefficient 0 is (2/5)log 3; its sample
   between-imputation covariance is (3/10)(log 3)^2; and Q=(9/25)(log 3)^2.
5. V_correct=14/81+(9/25)(log 3)^2;
   V_code=14/81+(441/1300)(log 3)^2;
   V_code-V_correct=-(27/1300)(log 3)^2;
   V_code<V_correct; 0<V_code; 0<V_correct; and
   4(12/13)-5/6-2(23/24)=49/52.
6. The record type has cardinality 24; for every member i in `Fin 4`, the finite
   set of records containing i has cardinality 12.
7. (3(2/9)+2(8/81))/5=14/81;
   V_code=14/81+(49/52)Q;
   V_code-V_correct=(49/52-1)Q.
8. For every B in `Bool`, 0<v_B and max(v_B,0)=v_B.
   Also max(V_code,0)=V_code and max(V_correct,0)=V_correct.

Quantifier order is exactly the conjunction of these closed propositions, with
the universal quantifiers local to the clauses indicated. There is no arbitrary
imputation count, model, score vector, outcome, or covariance matrix being
universally quantified. The docstring explicitly excludes separate equalities
between the completed-data decomposition values v_B and direct ordered-pair sums.
No such direct sum occurs in the statement's dependency closure.

### Junk values and domain checks

- Real and rational division are total, with inverse of zero and division by
  zero equal to zero. In the generic averaging definitions m=0 would give zero
  from an empty sum; in the generic sample covariance m=1 would use inverse zero.
  T8 uses m=5, so m and m-1 are 5 and 4. All explicit constant denominators
  (including 5,6,9,13,24,25,27,36,52,81,1300) are nonzero.
- An integer exponent -2 uses a total inverse; if I_B=0 its inverse square would
  be zero. Both actual informations are positive (6 and 9/2). The outcomes give
  p_B=1/2 or 3/4, so 1-p_B is positive, and the log arguments are 1 and 3.
- `Real.log 0=0`, and at negative arguments `Real.log x=log |x|`. Neither
  extension is used here; log 1=0 is the legitimate logarithm of 1.
- m is cast to the reals before m-1 is formed; it is not truncated natural
  subtraction. Likewise y_B-p_B and all variance differences are real
  subtractions. The comparison of j with s_B(e) is a natural comparison, and
  success counts stay in [0,4]. All natural casts are exact.
- Each array is a total function on a matching `Fin` type. Numerals used as
  actual indices are in range; there is no wrapped out-of-range `Fin` numeral,
  unchecked array lookup, or partial-function default involved. `Fin 1` really
  has one element. None of the instantiated summation types is empty.
- Squaring and max are ordinary total real operations. There is no square root,
  real `rpow`, measure, expectation, Bochner integral, `ENNReal.toReal`, infimum,
  supremum, limsup, liminf, conditional law, or limiting operation in this closure.
  Thus none of their possible junk values can affect T8.

### Generated declarations in the closure

All are proof-only; none supplies a mathematical hypothesis or data value.
`sixDyadData._proof_1` is the six-case decidable proof that each listed set has
two members. `pairDyads._proof_1`, `correctPooledVariance._proof_1` and
`imputationBetweenStatement._proof_1` prove respectively `NeZero 4`, `NeZero 1`,
and `NeZero 1` for literal indices. The remaining generated proofs certify
`Nat.AtLeastTwo` for positive literal numerals used in the arithmetic:

| Declaration suffix after SAP.P032 | Certified numeral |
| --- | --- |
| averageMemberCovariance._proof_1 | 5 |
| codePooledVariance._proof_1, _proof_2, _proof_3, _proof_4 | 12, 13, 6, 23 |
| decompositionWeight._proof_2 | 2 |
| fiveEstimates._proof_1 | 3 |
| imputationFitsStatement._proof_1, _proof_2, _proof_3, _proof_4 | 9, 81, 36, 11 |
| imputationGapStatement._proof_1, _proof_2, _proof_3, _proof_4, _proof_5, _proof_6 | 14, 441, 1300, 23, 49, 52 |
| imputationProbability._proof_1 | 24 |
| survivalComponentsStatement._proof_4 | 25 |
| survivalDiscrepancyStatement._proof_1, _proof_2, _proof_3, _proof_4 | 23, 8, 10, 27 |
| survivalScoresStatement._proof_1, _proof_2, _proof_3, _proof_4 | 6, 4, 2, 12 |
| survivalSubjectTotalsStatement._proof_1, _proof_2, _proof_3 | 3, 7, 5 |
| tenFitStatement._proof_2 | 13 |

The names reused from other statements do not import those other statements'
mathematical assumptions or definitions into T8.

## SAP.P032.T10

Location: `SAP/P032/Challenge/Part1.lean:68` (theorem at line 71).
Fingerprint: `c2c9f697030c6ba5eb60d261ff2e3d30239917e1443b8f3348de41ed6e082cd4`.

### Objects, definitions, hypotheses and quantifiers

There are no external parameters or hypotheses. `StudyEntry` is a structure
with four unrestricted natural-number fields `(n,loss,lossMilli,serMilli)`.
Its four projections return those fields, and its constructor takes those four
natural numbers. It has no field asserting any numerical relationship.

`studyData` is the following fixed function from `Fin 22` to that structure,
with zero-based indices; this is its whole definition:

| i | n | loss | lossMilli | serMilli |
| --- | --- | --- | --- | --- |
| 0 | 6 | 1 | 167 | 2739 |
| 1 | 173 | 43 | 249 | 2187 |
| 2 | 29 | 6 | 207 | 2200 |
| 3 | 8 | 3 | 375 | 1099 |
| 4 | 9 | 8 | 889 | 3269 |
| 5 | 24 | 0 | 0 | 1526 |
| 6 | 45 | 5 | 111 | 898 |
| 7 | 36 | 5 | 139 | 1511 |
| 8 | 4 | 2 | 500 | 4158 |
| 9 | 1 | 1 | 1000 | 1691 |
| 10 | 170 | 7 | 41 | 955 |
| 11 | 3 | 0 | 0 | 1895 |
| 12 | 6 | 0 | 0 | 1301 |
| 13 | 41 | 8 | 195 | 1432 |
| 14 | 16 | 0 | 0 | 908 |
| 15 | 18 | 4 | 222 | 1426 |
| 16 | 20 | 1 | 50 | 1291 |
| 17 | 18 | 0 | 0 | 999 |
| 18 | 9 | 0 | 0 | 1071 |
| 19 | 15 | 0 | 0 | 1212 |
| 20 | 28 | 17 | 607 | 3268 |
| 21 | 12 | 2 | 167 | 1311 |

### Entire conclusion

Writing `(n_i,l_i,a_i,s_i)` for each row, `T10Statement` asserts:

1. For every i in `Fin 22`, 0<n_i.
2. For every i in `Fin 22`, then for every natural number k,

       [k <= n_i and |k/n_i - a_i/1000| <= 1/2000] iff k=l_i.

   All arithmetic inside the absolute value is rational arithmetic, with each
   natural cast to the rationals before division. The absolute value is the
   ordinary ordered-field absolute value. This is both existence and uniqueness
   of a bounded integer loss count compatible with the displayed proportion up
   to half of a unit in the third decimal place, including endpoints.
3. The subset of row indices with n_i<=2l_i is exactly {4,8,9,20}; the subset
   with n_i<2l_i is exactly {4,9,20}; their cardinalities are respectively 4 and 3.
   The subset with 500<=a_i is exactly {4,8,9,20}. Row 8 has n_8=4, l_8=2.
4. The cardinality of the row index type is 22; sum_i n_i=691; exactly seven
   rows have l_i=0; exactly eighteen rows have 1000<s_i; for every i,
   898<=s_i<=4158; and s_6=898, s_8=4158.

All subsets here are finite sets obtained by filtering the full index set, and
all cardinalities, n_i, l_i, a_i and s_i comparisons are natural-number
comparisons. The last two endpoint equalities and the universal bounds jointly
assert that the finite minimum and maximum SER entries are 898 and 4158.
The mathematical scale suggested by the field names and docstrings is a_i/1000
for the printed loss proportion and s_i/1000 for the printed SER. The arithmetic
does not define a function computing an SER from regression output. The data
docstring associates rows 4,8,9,20 with Colgan (2014), Efrat and Newman (2016),
Fang, Johnson and Leeds (2014), and Weisiger (2016), respectively. The theorem's
docstring calls this exact recovery from printed proportions with corrected
weak and strict half-loss counts and neighboring counts.

### Junk values and domain checks

- Rational division is total, so k/n_i would be zero when n_i=0. Every actual
  n_i is positive, explicitly asserted by the first conjunct; 1000 and 2000 are
  nonzero. Thus no division-by-zero convention is used by the recovery result.
- Natural-to-rational casts are injective exact casts. The difference inside
  absolute value is rational subtraction, not truncated natural subtraction.
  Thresholds use multiplication and comparison of naturals, with no overflow.
- `Fin 22` is inhabited, its 22 entries are all present, and literal row indices
  4,8,9,20 and 6 are in range. No default lookup or wrapped numeral is used.
- The tolerance is closed at both ends. It intentionally describes compatibility
  with rounding rather than an explicitly defined tie-breaking rounding rule;
  this is a potential interpretation point for later comparison.
- `StudyEntry` allows inconsistent rows in general, but T10 refers only to this
  fixed table and proves its recovery property. It has no premise about arbitrary
  rows that could be inconsistent or conceal the desired conclusion.
- No square roots, logs, negative powers, real `rpow`, integrals, expectations,
  `toReal`, infima, suprema, or sequence limits occur. Every set cardinality and
  sum is finite. Empty-set extrema and unbounded-limit conventions do not arise.
- The sole generated proof in this closure, `studyThresholdStatement._proof_1`,
  proves `NeZero 22` for the finite index type and contributes no substantive
  assumption. All other closure members are the structure, constructor,
  projections and the five explicit proposition/data definitions unfolded above.
