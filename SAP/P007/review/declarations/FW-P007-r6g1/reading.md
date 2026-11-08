# Blind reading

This file was written before opening `claims.json` or `record.json`. It describes the elaborated statements without deciding whether they match an external claim. Sources read: `closure.json`, all of `Defs/Part1.lean` and `Defs/Part2.lean`, the target docstrings and declarations in `Challenge/Part1.lean`, and the import aggregators. Every closure entry was read. All generated `_proof_` entries were also printed with Lean in `scratch/Blind.lean`: they are only `Nat.AtLeastTwo` numeral witnesses or `NeZero` witnesses for positive finite index sizes. They introduce no assumptions or mathematical clauses.

All source paths below are relative to `SAP/P007/`.

## SAP.P007.T1

The docstring describes an exact certificate that the expected four-column deletion fraction is below 99% for every fixed 8580-row, 1205-column array with a specified observed-cell total.

Unfolded objects: an `ObservedArray n K` is a function from `Fin n` to finite subsets of `Fin K`. Thus a row `m(i)` is its observed-column set. `sampleSets K k` is the set of all k-element subsets of the K-element universe. For a chosen subset S, `retainedShare m S` is `(sum over i in Fin n of 1 if S is a subset of m(i), otherwise 0)/n`. `meanRetained m k` is the sum of these shares over all k-element S, divided by the number of those S. `meanLoss` is one minus this mean. These are finite uniform arithmetic means, with no distributional assumptions on the fixed array.

Write R(m) for that uniform four-column mean, D(m)=1-R(m), and c_i=|m(i)|. The theorem is the conjunction of all the following clauses; variables in different clauses are separately quantified.

1. For **every** m : Fin 8580 -> finite subsets of Fin 1205, first `R(m) = (sum_i choose(c_i,4))/(8580*choose(1205,4))`, with numerator and denominator interpreted in the reals. Furthermore, **if** the integer sum of the c_i is 3482533, then all five conclusions hold: integer `sum_i choose(c_i,4) >= 9560288484630`; `R(m) >= 24513560217/1923069889510`; `R(m)>1/100`; `D(m)<=1898556329293/1923069889510`; and `D(m)<99/100`. The counting identity has no observed-total hypothesis.
2. For every r : Fin 1206 (so its natural value runs from 0 to 1205), the integer inequality `1104475905 + (r-405)*10989810 <= choose(r,4)` holds. The subtraction here is in the integers, not truncated natural subtraction.
3. The integer equalities `choose(405,4)=1104475905`, `choose(405,3)=10989810`, and `choose(406,4)=1115465715`.
4. Integer `8580*choose(1205,4)=749997256908900`.
5. Integer `947*choose(405,4)+7633*choose(406,4)=9560288484630`.
6. Integer `3482533=8580*405+7633`.
7. Real `9560288484630/749997256908900=24513560217/1923069889510`.
8. Real `1/100<24513560217/1923069889510`.
9. Real `1898556329293/1923069889510<99/100`.
10. Integer `choose(405,4)=1104475905+(405-405)*10989810`.
11. Integer `choose(406,4)=1104475905+(406-405)*10989810`.
12. Real `1-24513560217/1923069889510=1898556329293/1923069889510`.

Here `choose` is Mathlib's natural binomial coefficient, subsequently cast to the displayed number system; the casts preserve exact natural values. The statement does not assert that a particular observed-total array exists or that equality in the lower bound is attained.

Junk conventions: real division is total and `x/0=0`; generally the share would therefore be 0 for n=0, and the mean would be 0 for an empty family of k-subsets (k>K), making `meanLoss=1`. Here n=8580>0 and k=4<=1205; the family has positive cardinality, so neither convention is used. All fixed rational denominators are positive. `Nat.choose c 4=0` when c<4 is the correct combinatorial count, not a spurious value. Empty individual observed sets are allowed and correctly retain no row at k=4. There is no integration, extended-real conversion, log, root, real power, supremum, limit or partial-function default.

## SAP.P007.T2

The docstring says that the logged average implies corrected counts and 66.3% missingness, a four-variable population bound, and the ordering of three displayed simulation estimates. It explicitly drops an assertion about every variable count above six.

All sample-set means and observed-set objects are exactly the finite notions unfolded for T1. Independently, a Boolean mask m : Fin n -> J -> Bool uses `true` for missing. For finite J, `missingCount m` is the natural sum of all cell indicators `1 if missing, else 0`. `missingAverage m` is `(sum over columns j of ((sum over rows i of that same indicator)/n))/card(J)`, in the reals. `observedColumns m i` is the finite set of column indices j with m(i,j)=false.

The theorem is a conjunction of five parts:

1. For every natural A, if `abs(A/10501920 - 0.668390827582004)<=0.000000001`, with A cast to the reals, then A=7019387. Decimal constants are exact real rationals.
2. `averageArithmetic` asserts the natural equalities `8580*1224=10501920`, `8580*19=163020`, `7019387-8580*19=6856367`, `8580*1205=10338900`, `10338900-6856367=3482533`, and the real inequalities `0.6625<=6856367/10338900<0.6635`, `6856367/10338900<0.6675`, and `0.6675<=7019387/10501920<0.6685`.
3. For every Boolean m on 8580 rows and the disjoint union of 1205 retained and 19 removed columns, **if** every entry in each of the 19 removed columns is true **and if** `abs(missingAverage m-0.668390827582004)<=0.000000001`, then the following conjunction `correctedMask m` holds. Let after(i,j)=m(i,inl(j)). The original missing count is 7019387; after's missing count is 6856367; the sum of after's observed-row-set cardinalities is 3482533; the two missing averages are exactly 7019387/10501920 and 6856367/10338900; the latter is at least .6625, below .6635 and below .6675; and the four-column mean loss on after is at most 1898556329293/1923069889510 and strictly below .99. There is no assumption or assertion that each retained column has an observed cell.
4. Independently, for every observed-set array m with dimensions 8580 by 1205, **if** its integer observed-total sum is 3482533, then its four-column mean loss satisfies those same two bounds.
5. `simulationComparisons` asserts only the exact real arithmetic `1-.02820753=.97179247`, `1-.01365003=.98634997`, `1-.006640252=.993359748`, and `.97179247<.98634997<.99<.993359748`. It provides no stochastic experiment, replicate data, sample estimator or accuracy bound for those displayed numbers.

Junk conventions: division by a zero row/column count or an empty subset family is possible in the generic definitions, but the instantiated row count, both column counts, and four-subset family here are all positive. Natural subtraction in `averageArithmetic` is truncated; the subtrahends are smaller and the stated arithmetic is ordinary subtraction. Integer/real casts are exact; finite index types are nonempty; no coercion from infinity or undefined analytic quantity occurs. Every decimal is a rational, not a floating-point approximation. The theorem is conditional on the stated tolerance and does not itself assert an eligible input mask exists.

## SAP.P007.T3

The docstring describes two laws as refuting both directions of an asserted equivalence between zero observation bound and full missingness; it says the same examples apply to two singleton groups.

Full probability definitions: `Row h` is the function type Fin h -> Bool, true meaning missing. `Array n h` is Fin n -> (Fin h -> Bool). A `Law` on a finite type is a real weight on each point, with every weight nonnegative and the sum over the complete finite type equal to one. The constructor `Law.mk` takes precisely those data/proofs, and `Law.weight` is their projection. `probability L P` is the finite sum over all arrays of their weight when P holds and zero otherwise. No independence is built into a Law.

`rowIndependent L` means: for **every** family of arbitrary row predicates E_i, the probability of `for every i, E_i(row_i)` equals the product over i of the individual probabilities. Thus it is mutual independence of whole row vectors, not independence of columns.

For a natural j, `prefixObserved r j` means that every column t : Fin h with t.val<j is false. Write s_i(j) for the probability of this event in row i (`survival`). The j=0 event is the whole space; j>=h checks all columns. `allDeleted` is the probability that **every** row fails the h-column prefix event, that is, every row has at least one missing entry.

`observationBound L q` is exactly `0<=q<1`, together with, for every row i: if h>0, s_i(1)<=q; and for every natural j with 1<=j<h and s_i(j)>0, `s_i(j+1)/s_i(j)<=q`. No conditional coefficient is constrained at a zero-probability prefix. q is an arbitrary upper bound, not required to be smallest or attained.

The theorem asserts two independently existential laws (not one law satisfying both descriptions):

1. There exists a Law on one row and two columns whose weight is `nullFirstWeights`: weight one on the single array with row (true,false), weight zero otherwise. (The source writes a product over a singleton row index.) This law is row independent and has observationBound 0; s_0(1)=s_0(2)=0; column 1 (zero-based, the second column) is observed with probability one and missing with probability zero; allDeleted=1; and `(1-0^2)^1=1`.
2. There exists a Law on one row and two columns whose weight is `fullyMissingWeights`: mass one on (true,true), zero otherwise. **For every real q**, **if** 0<=q and q<1, then it is row independent, has observationBound q, and, for every j : Fin 2, column j is missing with probability one. The quantifier for q is inside the existential law: the same law works for all such q.

The first example has a wholly missing first column and wholly observed second column; it does not have all entries missing. The second has every entry missing and accepts positive q as well as zero q.

Junk conventions: the conditional-ratio denominator is strictly positive whenever its inequality is required, so real division by zero is never used as conditional probability. The zero prefix in the first witness merely disables the guarded later hypothesis. The explicit finite weights must still satisfy Law.nonneg and Law.total; neither existential can use arbitrary unnormalized weights. A one-row independence condition is automatic but is mathematically the correct independence condition at n=1. Both finite coordinate types are nonempty; Fin numeral witnesses printed in the closure certify valid indices. No natural subtraction, analytic partial domain, integral, infinite extremum, or extended-real operation occurs; all powers are natural powers with positive exponent here.

## SAP.P007.T4

The docstring describes two normalized laws satisfying the assumptions, with a null conditioning prefix and a valid deletion bound, also usable as singleton-group examples.

`Array`, `Law` (including its constructor, weight projection and normalization requirements), probability, mutual row independence, prefix observations, s_i(j), allDeleted and observationBound have exactly the finite definitions unfolded in T3. In particular, conditionals are constrained only for strictly positive conditioning probability.

The theorem is a conjunction of two existential statements:

1. There exists a one-row, two-column law with weights `nullFirstWeights`, hence mass one on (true,false), which is row independent, has observationBound 1/2, has s_0(1)=s_0(2)=0, and satisfies **for every real v**, **if** 0<=v and v<=1, then `s_0(2)=v*s_0(1)`. It also asserts `1/2<1`, `s_0(2)<=(1/2)^2`, allDeleted=1 and `3/4<=allDeleted`. The v equality is not a definition of a unique conditional probability: every coefficient in [0,1] gives the same zero product.
2. There exists a two-row, three-column law with weights `laterNullWeights`. For each row, the weight factor is `1/2` on pattern (true,false,false), `1/2` on pattern (false,true,false), and zero on every other pattern; the array weight is the product of the two row factors. This is a normalized product distribution on four arrays, each of weight 1/4. The law is row independent and has observationBound 1/2. **For every row i**, s_i(1)=1/2, s_i(2)=0, s_i(3)=0, 0<s_i(1), `s_i(2)/s_i(1)=0`, and `s_i(3)<=1/8`. Finally allDeleted=1 and `49/64<=allDeleted`.

Junk conventions: the one explicit ratio in the conclusion has denominator 1/2; ratios required by observationBound have positive denominators. Null-prefix statements do not divide by zero. The statement illustrates the freedom of coefficients on a null event rather than assigning a conditional probability to such an event. Products of actual probability masses have no default value; both Laws must prove normalization. No index type is empty. The `decide` functions used in the point patterns are exact decidable tests of coordinate equality, not partial choices. All rational denominators are positive; no other analytic junk values occur.

## SAP.P007.T5

The docstring describes a repaired prefix-recursion proof, with an explicit coefficient convention at zero prefixes, a product identity, the zero endpoint, and a finite bound usable for variables or groups.

`Array`, `Law`, probability, prefix events, s_i(j), allDeleted, observationBound and rowIndependent are precisely the finite notions unfolded in T3. The one additional definition is `conditionalObserved L i j`, denoted c_i(j): it equals `s_i(j+1)/s_i(j)` if s_i(j)>0, and equals **zero by definition** otherwise. The source explicitly distinguishes the latter from a conditional probability given a null event.

Quantifiers and hypotheses in order: for every natural n and h, **if** n>0, then for every proof hh that h>0, for every joint Law L on n-by-h Boolean arrays, and for every real q, **if** observationBound L q, then the following whole conjunction holds. There is no row independence hypothesis until the final implication and no column independence hypothesis at all.

1. **If q=0**, then for every row i its first coordinate (Fin h element with value zero, justified by hh) is missing with probability one; allDeleted=1; and `(1-q^h)^n=1`. This does not assert that every later coordinate is missing.
2. For every row i, s_i(0)=1.
3. For every row i and every natural j<h, `s_i(j+1)<=s_i(j)*q`.
4. For every row i and every natural j<h, if s_i(j)=0, then s_i(j+1)=0.
5. For every row i, c_i(0)=s_i(1), `s_i(h)=product over t in {0,...,h-1} of c_i(t)`, for every natural j<h `0<=c_i(j)<=q`, `s_i(h)<=q^h`, and `1-q^h<=1-s_i(h)`.
6. **If rowIndependent L**, then `allDeleted=product over i in Fin n of (1-s_i(h))` and `(1-q^h)^n<=allDeleted`.

Junk conventions: c_i(j)=0 at a null prefix is an intentional extension, disclosed in both the definition and docstring. The quotient branch is evaluated only for a positive denominator as a mathematical piecewise definition, so the product formula has no dependence on an accidental division-by-zero value. The observationBound ratios are similarly guarded. n,h are strictly positive; neither the row product nor the column product is an empty product, and no 0^0 endpoint is used. Generic prefixes at j>=h simply mean all columns, but the theorem's recursion/coefficient bounds use j<h. Every finite probability is normalized, and no integral/existence convention or analytic out-of-domain operation occurs. All casts/numerals serve valid finite indices or natural powers.
