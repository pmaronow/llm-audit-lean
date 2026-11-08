# Blind reading of SAP.P038.T1

This reading was saved before opening `claims.json` or `record.json`. It uses only the four supplied Defs/Challenge files and the relevant Mathlib sources. There is one theorem stub, `SAP.P038.T1`, in `SAP/P038/Challenge/Part1.lean:13`. Its proposition is the definition `SAP.P038.T1Statement` in `SAP/P038/Defs/Part1.lean:40`. The aggregate files only import their respective `Part1` files and set elaboration options.

## Objects and definitions, expanded

All real arithmetic below is ordinary arithmetic in Mathlib's ordered field of real numbers. In particular, the displayed fractions in the statement are real fractions, not integer or natural-number division. Natural-number and integer casts into the reals have their ordinary exact meanings.

For a natural number m, define

    W_m = {w in Z : -m <= w <= m and w != 0}.

This is `referenceWeeks m`, a finite set of integers, containing exactly the 2m nonzero integers from -m to m. It is not a multiset and contains no repetitions. Mathlib's `Finset.Icc` is the closed ordered interval (`Order/Interval/Finset/Defs.lean:280,301`); its integer implementation is in `Data/Int/Interval.lean:30`. `Finset.erase 0` deletes the integer zero, with membership characterized by inequality to zero and membership in the original set (`Data/Finset/Erase.lean:49,57`). The casts of m into the integers are exact, and unary negation is integer negation.

For real numbers R and x, `moreExtreme R x` means

    x < min(R, 1/R) or max(R, 1/R) < x.

The min and max are the ordinary real minimum and maximum. Both inequalities are strict: points exactly at either threshold are excluded. R is assumed positive wherever this predicate is used in the theorem, so its reciprocal is the ordinary nonzero reciprocal.

For R real, a function r : Z -> R, and m natural, put

    S_m(R,r) = {w in W_m : r(w) < min(R,1/R)
                             or max(R,1/R) < r(w)},
    C_m(R,r) = |S_m(R,r)|,
    P_m(R,r) = C_m(R,r)/(2m),
    A_m(R,r) = (C_m(R,r)+1)/(2m+1).

These are, respectively, `tailWeeks`, `tailCount`, `empiricalP`, and `electionDayAdjustedP`. `Finset.filter` retains precisely those elements satisfying its predicate (`Data/Finset/Filter.lean:52,127`), and `Finset.card` counts the elements of its repetition-free underlying multiset (`Data/Finset/Card.lean:47`). C_m is a natural number. In A_m the addition C_m+1 takes place in the natural numbers before the exact cast to the reals; all denominator arithmetic takes place in the reals. No subtraction of natural numbers occurs in these definitions.

For arbitrary real x and v, `roundsTo x v` means exactly

    v - 1/200 <= x < v + 1/200.

Write B(x,v) for this predicate below. It is a half-open interval of radius 0.005 around v, with the lower endpoint included and the upper endpoint excluded. In particular, B(x,0.04) is 0.035 <= x < 0.045, and B(x,0.06) is 0.055 <= x < 0.065. It is a defined interval predicate, not an invocation of a general rounding operation.

The definitions are total even when m=0 or R=0 (Mathlib real division is total, with inverse zero equal to zero). Those values do not cause denominator anomalies in this theorem: all uses of P_m or A_m have m=12 or m=25, and every quantified R is restricted by R>0. The monotonicity clause uses counts only.

## Exact assertion and quantifier scope

`SAP.P038.T1` has no external parameters or hypotheses. It asserts the conjunction of the following three universally quantified blocks. The variables R and r in the third block are fresh and independent of those in the first block.

1. For every real R, then every function r : Z -> R, if R>0, if for every integer w in W_25 one has r(w)>0, and if C_25(R,r)=2, then all four equalities hold:

       P_25(R,r) = 2/50,
       P_25(R,r) = 1/25,
       P_25(R,r) = 4/100,
       6/100 - P_25(R,r) = 1/50.

   The subtraction in the last equality is real subtraction. The hypotheses are in the order R>0, positivity on W_25, then the count equality.

2. For every integer k, if 0<=k and then k<=50, all four equivalences hold:

       ((k cast to R)/50 = 6/100) iff k=3,
       B((k cast to R)/50, 6/100) iff k=3,
       B((k cast to R)/50, 4/100) iff k=2,
       ((k cast to R)/50 = 4/100) iff k=2.

   The k in these equivalences is an integer, not an arbitrary real, and the equalities k=2 and k=3 are integer equalities.

3. For every real R, then every function r : Z -> R, if R>0 and then if for every integer w in W_100 one has r(w)>0, all the following conclusions hold together:

       (P_25(R,r) = 6/100) iff C_25(R,r)=3;
       B(P_25(R,r), 6/100) iff C_25(R,r)=3;
       B(P_25(R,r), 4/100) iff C_25(R,r)=2;
       (P_25(R,r) = 4/100) iff C_25(R,r)=2.

   In addition, for every natural m, then every natural n, if 1<=m, then m<=n, then n<=100, one has

       C_m(R,r) <= C_n(R,r).

   This compares counts, not proportions. There is no assertion that P_m is monotone. The same R and the same r are used at every window size.

   Finally, under the additional hypothesis

       S_25(R,r) = {-14, 7},

   all eighteen of the following conclusions hold together, in the order printed in the definition:

       C_12(R,r) = 1;
       C_25(R,r) = 2;
       P_12(R,r) = 1/24;
       35/1000 <= P_12(R,r);
       P_12(R,r) < 45/1000;
       B(P_12(R,r), 4/100);
       P_25(R,r) = 4/100;
       not B(P_25(R,r), 6/100);
       A_25(R,r) = 3/51;
       A_25(R,r) = 1/17;
       55/1000 <= A_25(R,r);
       A_25(R,r) < 65/1000;
       B(A_25(R,r), 6/100);
       A_12(R,r) = 2/25;
       A_12(R,r) = 8/100;
       not B(A_12(R,r), 4/100);
       not (B(P_12(R,r), 4/100) and B(P_25(R,r), 6/100));
       not (B(A_12(R,r), 4/100) and B(A_25(R,r), 6/100)).

The equality S_25={-14,7} is an equality of finite sets of integers: it specifies both membership of those two distinct integers and absence of every other outside point in W_25. Its implication is only one conjunct of the third block; the four count/value equivalences and the monotonicity conclusion do not depend on that extra hypothesis.

## What the statement does not supply

R and r are arbitrary real objects with the stated positivity assumptions. The formal statement does not define a risk ratio from observations, identify r(0) with R, identify a particular dataset or figure with R and r, or assert that an observed tail count is two or that an observed tail set is {-14,7}. The first block assumes its count; the final implication assumes its exact tail set. The function r is defined on all integers, but positivity outside W_25 in the first block, and outside W_100 in the third block, is not assumed. r(0) is unconstrained and never used. There are no other SAP definitions, ambient assumptions, hidden typeclass parameters, integrals, limits, or infinite cardinalities in the proposition.
