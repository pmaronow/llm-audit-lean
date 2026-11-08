# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: the complete
`closure.json`, both Defs and Challenge entry modules, and both Part1 modules.
`scratch/ClosureCheck.lean` was compiled to print the target and every declaration
in its closure, including all generated proof declarations.

## SAP.P038.T1

Location: `SAP/P038/Challenge/Part1.lean:6` (the theorem command is line 13).
Fingerprint: `e43d99880bf645c9e15d73ef5e2264c7def9244f9c0b70d068360fc23e8e8102`.

### Objects and definitions, unfolded

All ratios and divisions below are in the real numbers. Window sizes are natural
numbers; week labels and the separate count variable k are integers.

* `referenceWeeks(m)` is the finite set of integers w satisfying
  `-(m : Z) <= w <= (m : Z)` and `w != 0`. It is Mathlib's integer closed finite
  interval with zero erased. It has 2m elements, including no election-day label.
* `moreExtreme(R,x)` is the proposition
  `x < min(R,1/R) OR max(R,1/R) < x`. Both comparisons are strict.
* `tailWeeks(R,r,m)` is that finite interval, excluding zero, filtered by the
  preceding proposition applied to the real-valued function `r : Z -> R`.
* `tailCount(R,r,m)` is the natural-number cardinality of that filtered finite
  set. To abbreviate the fully unfolded expression, write
  `C_m = #{w in Z : -m <= w <= m, w != 0,
  r(w) < min(R,1/R) OR max(R,1/R) < r(w)}`.
* `empiricalP(R,r,m)` is `P_m = (C_m : R)/(2*(m : R))`.
* `roundsTo(x,v)` means `v-1/200 <= x AND x < v+1/200`. It is a predicate
  for a specified half-open bin, not an invocation of a rounding function.
* `electionDayAdjustedP(R,r,m)` is
  `A_m = ((C_m+1 : N) : R)/(2*(m : R)+1)`.

These definitions use actual finite intervals, filtering, and cardinality. They
do not refer to a probability measure or to measured crash data. The function r
is arbitrary supplied data, and the election ratio R is a separate real number;
there is no equation `r(0)=R`, and r(0) is never inspected.

### Statement and quantifiers

`T1` asserts `T1Statement`, the conjunction of the following three independently
quantified blocks. The third block includes the nested-window and specified-tail
conclusions. There are no additional parameters or typeclass hypotheses on T1.

1. For every real R and every function `r : Z -> R`, if `0 < R`, every
   `r(w)` with `-25 <= w <= 25` and `w != 0` is positive, and `C_25=2`, then
   all four of these real equalities hold:
   `P_25=2/50`, `P_25=1/25`, `P_25=4/100`, and
   `6/100-P_25=1/50`.
2. For every integer k, if `0 <= k <= 50`, then all four equivalences hold:
   * `(k : R)/50 = 6/100` iff `k=3`;
   * `6/100-1/200 <= (k : R)/50 < 6/100+1/200` iff `k=3`;
   * `4/100-1/200 <= (k : R)/50 < 4/100+1/200` iff `k=2`;
   * `(k : R)/50 = 4/100` iff `k=2`.
   Each chained inequality here stands for the conjunction of its two comparisons.
3. For every real R and every function `r : Z -> R`, if `0 < R` and every
   `r(w)` with `-100 <= w <= 100` and `w != 0` is positive, then:
   * `P_25=6/100` iff `C_25=3`;
   * `6/100-1/200 <= P_25 < 6/100+1/200` iff `C_25=3`;
   * `4/100-1/200 <= P_25 < 4/100+1/200` iff `C_25=2`;
   * `P_25=4/100` iff `C_25=2`;
   * for every pair of natural numbers m,n, if `1 <= m`, `m <= n`, and
     `n <= 100`, then `C_m <= C_n`;
   * if the filtered set of extreme weeks in `[-25,25]` excluding zero is
     exactly the two-element set `{-14,7}`, then **all** of the following hold:
     1. `C_12=1` and `C_25=2`;
     2. `P_12=1/24`, `35/1000 <= P_12`, and `P_12 < 45/1000`;
     3. `4/100-1/200 <= P_12 < 4/100+1/200`;
     4. `P_25=4/100` and it is false that
        `6/100-1/200 <= P_25 < 6/100+1/200`;
     5. `A_25=3/51` and `A_25=1/17`;
     6. `55/1000 <= A_25`, `A_25 < 65/1000`, and
        `6/100-1/200 <= A_25 < 6/100+1/200`;
     7. `A_12=2/25`, `A_12=8/100`, and it is false that
        `4/100-1/200 <= A_12 < 4/100+1/200`;
     8. it is false that both P_12 is in the 0.04 bin and P_25 is in the
        0.06 bin;
     9. it is false that both A_12 is in the 0.04 bin and A_25 is in the
        0.06 bin.

In block 3, the particular two-week set is an antecedent only of the final
sub-block; the preceding four equivalences and monotonicity require no such
antecedent. The positivity assumptions on the entire 100-week window precede all
of block 3. Block 2 has no R or r and no empirical-data premise. The separate
universal quantifiers in blocks 1 and 3 do not couple their inputs.

### Docstrings as read blindly

The target docstring identifies a footnote value, the figure's election-hours
panel and caption, and Methods. It describes the result as conditional on the
figure's two outside points, gives the 25-week value 0.04, and says the exact
counts, rounding, nested windows and 12-week value show that neither of two
counting conventions reconciles both displayed numbers. It claims to retain all
four clauses of a corrected claim, while leaving the figure reading and which
published output used final data conditional. No content of that corrected claim
has been consulted at this stage. The statement itself asserts no historical
fact about which published data or computation was final.

### Complete closure, including generated declarations

The mathematical definitions above and `T1Statement` account for every named
definition in the closure. Lean's additional declarations were individually
printed. They are closed proofs of `Nat.AtLeastTwo` used in the elaboration of
numeric constants:

| Declaration | Printed proposition |
| --- | --- |
| `T1Statement._proof_1` | `(49+1).AtLeastTwo` |
| `T1Statement._proof_2` | `(24+1).AtLeastTwo` |
| `T1Statement._proof_3` | `(3+1).AtLeastTwo` |
| `T1Statement._proof_4` | `(99+1).AtLeastTwo` |
| `T1Statement._proof_5` | `(5+1).AtLeastTwo` |
| `T1Statement._proof_6` | `(23+1).AtLeastTwo` |
| `T1Statement._proof_7` | `(34+1).AtLeastTwo` |
| `T1Statement._proof_8` | `(999+1).AtLeastTwo` |
| `T1Statement._proof_9` | `(44+1).AtLeastTwo` |
| `T1Statement._proof_10` | `(2+1).AtLeastTwo` |
| `T1Statement._proof_11` | `(50+1).AtLeastTwo` |
| `T1Statement._proof_12` | `(16+1).AtLeastTwo` |
| `T1Statement._proof_13` | `(54+1).AtLeastTwo` |
| `T1Statement._proof_14` | `(64+1).AtLeastTwo` |
| `T1Statement._proof_15` | `(7+1).AtLeastTwo` |
| `empiricalP._proof_1` | `(1+1).AtLeastTwo` |
| `roundsTo._proof_1` | `(199+1).AtLeastTwo` |

Every printed proof is `Nat.instAtLeastTwoHAddOfNat` applied to the displayed
predecessor. These are numeric elaboration certificates, with no empirical or
mathematical assumption smuggled into the statement.

### Totalization and junk-value audit

* Real division is total: `1/0=0`. `moreExtreme(0,x)` consequently means
  `x<0 OR 0<x`. The definition permits that input, but both quantified data
  blocks require `R>0`, excluding it everywhere the predicate is used in T1.
* `P_0` is zero because its denominator is zero (also the reference set and its
  tail count are empty). The theorem evaluates P only at 12 and 25, so this
  convention cannot affect the assertion. Its monotonicity subclaim concerns C,
  not P, and explicitly has `1 <= m <= n <= 100`.
* `A_m` has denominator `2m+1`, strictly positive for every natural m. Its
  numerator uses natural addition, then casts to R. There is no truncated
  subtraction or overflow. At m=0 it is 1, deliberately counting the single
  added election-day point; the theorem uses only positive windows.
* The `-m` endpoint is negation after casting the natural number to Z, not
  natural subtraction. Finite intervals and erased/filtered sets have their
  usual empty-set meanings. The index type Z is not empty. The only zero-window
  set is empty by its actual membership condition, not by a default element.
* Natural/integer casts to R are exact. Counts are genuine nonnegative finite
  cardinalities bounded by 2m. k is an integer in [0,50]. All rational constants
  and all constant denominators in the theorem are nonzero and interpreted in R;
  no integer-division truncation occurs.
* R=1 is allowed and makes both thresholds 1; strict equality to a threshold
  does not count. Both R below 1 and above 1 are handled by min/max. Positivity of
  reference ratios holds only in the stated windows; other r values are
  irrelevant to the assertion. Classical decidability of real comparisons
  supports finite filtering and supplies no default data values.
* `roundsTo` explicitly includes the lower endpoint and excludes the upper.
  This fixes a tie convention. For the actual count grids here (multiples of
  1/50 and the displayed 1/24, 3/51 and 2/25), none of the relevant values is a
  bin boundary, so ties cannot change these conclusions. The predicate is not
  asserted to be a general rounding operation for arbitrary targets.
* There is no logarithm, square root, real power, integral, mean, `toReal`,
  infimum, supremum, limit superior/inferior, partial-function fallback, or
  default value from an empty type anywhere in the closure.

The source is a Challenge stub with `sorry`; as instructed, the certified
Solution is taken as given. This review concerns its statement and definitions.
