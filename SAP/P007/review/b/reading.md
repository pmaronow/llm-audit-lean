# Blind statement reading

This file was written and saved after reading only the Defs and Challenge files and relevant Mathlib definitions. Neither `claims.json` nor `record.json` had been opened. There are 16 Challenge theorems: T1–T12 and T14–T17. The readings below concern their propositions, independently of the docstrings' descriptions of the source.

## Common objects and complete definition expansion

All dimensions are natural numbers, including zero unless an individual theorem excludes it. `Fin h` is the set of integers 0 through h−1. A row is an h-tuple of Booleans; true means missing and false means observed. An n-by-h array x is a function from `Fin n` to rows. A `Law` on a finite type assigns every state a nonnegative real weight, with the sum over **all** states equal to one. There are no further conditions on the law. For any event E, P(E) is the finite sum of the weights of its states. For any real-valued f, E[f] is the finite sum of weight times f; this is an ordinary finite expectation, with no integrability assumption or convention needed.

For a law on n-by-h arrays, write S_i(j) for `survival L i j`: the probability that all columns t<h with t<j of row i are observed. Thus S_i(0)=1; for j≥h the event is that the whole row is observed. Write D for `allDeleted L`: P(every row has at least one missing column). A missingness indicator I_i is 0 when the entire row is observed and 1 otherwise. `deletedFraction` is (sum_i I_i)/n in the real numbers. Every Challenge use of this fraction has n>0.

`rowIndependent L` means: for **every family of row events** E_i (arbitrary predicates on whole Boolean rows), P(for every i, E_i(x_i)) = product_i P(E_i(x_i)). This is full mutual independence of row vectors. It places no independence restriction on the coordinates within a row, and no equality-of-distribution restriction across rows. `sameRowLaw L` means: for every pair of row indices i,j and every row event E, P(E(x_i))=P(E(x_j)).

Write B(L,q) for `observationBound L q`. Its exact requirements are 0≤q<1, and for every row i:

* if h>0, S_i(1)≤q;
* for every natural j with 1≤j<h **and S_i(j)>0**, S_i(j+1)/S_i(j)≤q.

There is no ratio condition on a null prefix. Write c_i(j) for `conditionalObserved L i j`: it is S_i(j+1)/S_i(j) if S_i(j)>0, and is explicitly **zero** otherwise. It is a total, defined coefficient; on null prefixes it does not purport to be a uniquely determined conditional probability.

Put b(n,q,h)=(1−q^h)^n (`lowerBound`) and f(q,h)=1−q^h (`fractionBound`), using ordinary natural integer powers. Put t(n,q,a)=log(1−a^(1/n))/log(q) (`realThreshold`) and R(n,q,x)=(1−q^x)^n (`realLowerBound`). Here 1/n is real reciprocal and the powers with real exponents use Mathlib's `Real.rpow`. On positive bases these are exp(exponent·log(base)). All threshold uses in these theorems have n>0 and 0<q,a<1, so both logarithm arguments are positive and log(q) is nonzero. Natural floor and ceiling are used, denoted floor_+(t), ceil_+(t). Natural floor truncates a negative real to zero; these threshold uses have t>0. `StrictMono` means that a<b implies the corresponding function values satisfy a strict inequality.

`superlog h` is lim_{n→∞} h(n)/log(n)=+∞, where n ranges over all natural numbers. Mathlib defines log(0)=0, log on negatives by log of the absolute value, and real division by zero to be zero. Those extensions affect only n=0,1 in this ratio and have no effect on its limit. `Tendsto ... atTop (nhds 1)` means the usual limit to one as n→∞; `atTop atTop` for a real sequence means eventual exceedance of every real bound. No limsup or integral is used.

`cellWeights a` assigns to x the product over rows i and columns j of (1−a_ij) if x_ij is missing, and a_ij if it is observed. `equalWeights n h q` has a_ij=q. `unequalWeights n h` has a_i0=3/4 and a_ij=1/4 for j>0. `equalModel n h q P` **asserts existence** of an actual normalized law L with equalWeights as its weight function, row independence, B(L,q), and P(L). `unequalModel n h P` asserts the same with unequalWeights and B(L,3/4). These are existential conclusions, not hypotheses assuming P(L).

The other named weights expand as follows. `nullFirstWeights` is the point mass, for one row and two columns, at the row (missing,observed). `fullyMissingWeights` is the point mass at (missing,missing). `laterNullWeights` for two rows and three columns is the product of two row distributions, each giving weight 1/2 to (missing,observed,observed) and weight 1/2 to (observed,missing,observed). `figure5Weights` for two-by-two arrays is the independent-cell law with observation chances (3/4,1/2) in each row. `nonidenticalWeights` for two-by-one arrays has independent observation chances 1/4 for row 0 and 1/2 for row 1. These descriptions specify the weights; the relevant statements additionally assert normalized Laws realizing them.

For a fixed observed array m, each row m_i is a subset of K columns. `sampleSets K k` is the finite set of **all k-element subsets** of those K columns, by Mathlib `Finset.powersetCard`. `retainedShare m S` is the number of rows i with S⊆m_i divided by n. `meanRetained m k`, denoted M_k(m), averages this share uniformly over all k-element column sets; `meanLoss`, denoted H_k(m), is 1−M_k(m). In all Challenge uses n>0 and k≤K, so both denominators are positive. If r_i=|m_i|, the counting identity is M_k(m)=sum_i choose(r_i,k)/(n·choose(K,k)). `Nat.choose r k` is zero when k>r.

For a Boolean matrix m with row count n and arbitrary finite column type J, `missingCount m`, denoted A(m), is the natural number of true cells. `missingAverage m`, denoted p(m), is (sum over columns of the fraction of true cells in that column)/|J|. All its Challenge uses have n>0 and |J|>0, so this is exactly A(m)/(n|J|). `observedColumns m` returns, row by row, the set of false cells. Columns `Fin K ⊕ Fin d` distinguish retained K columns from d removed columns; the retained submatrix is m'(i,j)=m(i,inl j). All finite sums/products use the whole specified finite index set unless a range is written. Empty sums/products have their usual values 0/1. Decimal literals are exact rational reals, not floating-point numbers. Subtractions in real/integer formulas are ordinary subtraction. The two subtractions explicitly typed natural in `averageArithmetic` are truncated natural subtraction of the displayed fixed numbers; both minuends exceed their subtrahends.

Mathlib definitions consulted: `Analysis/SpecialFunctions/Log/Basic.lean` (`Real.log`); `Analysis/SpecialFunctions/Pow/Real.lean` (`Real.rpow`); `Algebra/Order/Floor/Defs.lean` (`Nat.floor`, `Nat.ceil`); `Data/Finset/Powerset.lean` (`powersetCard`); `Order/Monotone/Defs.lean` (`StrictMono`); `Order/Filter/Defs.lean` (`Tendsto`); `Order/Filter/AtTopBot/Defs.lean` (`atTop`). All SAP definitions used by the theorem types are expanded above or below.

## SAP.P007.T1

This is a conjunction, without outer hypotheses, of the following assertions:

1. For **every fixed observed array m with 8580 rows and 1205 columns**, M_4(m)=sum_i choose(r_i,4)/(8580·choose(1205,4)). Furthermore, **if** the integer sum_i r_i=3482533, then all five conclusions hold: sum_i choose(r_i,4)≥9560288484630; M_4(m)≥24513560217/1923069889510; M_4(m)>1/100; H_4(m)≤1898556329293/1923069889510; H_4(m)<99/100.
2. For every integer r=0,...,1205, choose(r,4)≥1104475905+(r−405)·10989810. This subtraction and the entire inequality are in integers.
3. choose(405,4)=1104475905, choose(405,3)=10989810, and choose(406,4)=1115465715.
4. 8580·choose(1205,4)=749997256908900.
5. 947·choose(405,4)+7633·choose(406,4)=9560288484630.
6. 3482533=8580·405+7633.
7. 9560288484630/749997256908900=24513560217/1923069889510.
8. 1/100<24513560217/1923069889510 and 1898556329293/1923069889510<99/100.
9. The affine inequality of item 2 is an equality at r=405 and r=406: choose(405,4)=1104475905+(405−405)·10989810 and choose(406,4)=1104475905+(406−405)·10989810.
10. 1−24513560217/1923069889510=1898556329293/1923069889510.

No independence or random-data law is assumed. Only column selection is averaged uniformly, conditional on the fixed array.

## SAP.P007.T2

This is a conjunction of five components:

1. For every natural A, if |A/10501920−0.668390827582004|≤0.000000001, then A=7019387.
2. The complete `averageArithmetic` conjunction: 8580·1224=10501920; 8580·19=163020; 7019387−8580·19=6856367; 8580·1205=10338900; 10338900−6856367=3482533; 0.6625≤6856367/10338900<0.6635; 6856367/10338900<0.6675; and 0.6675≤7019387/10501920<0.6685. Products/subtractions of the first five identities are natural arithmetic; fractions and decimal comparisons are real arithmetic.
3. For **every** Boolean matrix m with 8580 rows and columns `Fin 1205 ⊕ Fin 19`, if every cell of its last 19 columns is missing and |p(m)−0.668390827582004|≤0.000000001, then `correctedMask m` holds. Expanded, this conclusion says A(m)=7019387, A(m')=6856367, sum_i |observedColumns(m')_i|=3482533, p(m)=7019387/10501920, p(m')=6856367/10338900, 0.6625≤p(m')<0.6635, p(m')<0.6675, H_4(observedColumns(m'))≤1898556329293/1923069889510, and H_4(observedColumns(m'))<99/100.
4. For every observed array m with 8580 rows and 1205 columns whose integer observed total is 3482533, H_4(m)≤1898556329293/1923069889510 and H_4(m)<99/100.
5. The exact `simulationComparisons` conjunction: 1−0.02820753=0.97179247; 1−0.01365003=0.98634997; 1−0.006640252=0.993359748; 0.97179247<0.98634997; 0.98634997<0.99; 0.99<0.993359748.

The last component compares supplied numbers; it makes no assertion that a simulation was run or that its estimates equal a population mean. There is no statement for every variable count above six.

## SAP.P007.T3

Two existential assertions are conjoined:

1. There exists a Law L on one-by-two arrays with **exactly nullFirstWeights**, row independence and B(L,0), such that S_0(1)=S_0(2)=0, P(second cell observed)=1, P(second cell missing)=0, D=1, and (1−0^2)^1=1.
2. There exists a Law L on one-by-two arrays with **exactly fullyMissingWeights**, such that **for every real q**, if 0≤q<1, then L has row independence and B(L,q), and for **every** of the two column indices j, P(cell (0,j) missing)=1.

The second existential law is selected before q and works for all admissible q simultaneously. Row independence for a single row is a genuine but automatic one-event identity.

## SAP.P007.T4

Two existential assertions are conjoined:

1. There exists a Law L on one-by-two arrays with exactly nullFirstWeights, row independence and B(L,1/2), with S_0(1)=S_0(2)=0; for **every real v** with 0≤v≤1, S_0(2)=v·S_0(1); 1/2<1; S_0(2)≤(1/2)^2; D=1; and 3/4≤D.
2. There exists a Law L on two-by-three arrays with exactly laterNullWeights, row independence and B(L,1/2), such that for **each row i**, S_i(1)=1/2, S_i(2)=S_i(3)=0, S_i(1)>0, S_i(2)/S_i(1)=0, and S_i(3)≤1/8; moreover D=1 and 49/64≤D.

In the first model a first-prefix event is null; in the second model it is positive but a later prefix is null. The statement asserts the valid recursion against every v in the first model; it does not assert an undefined conditional probability has a particular value.

## SAP.P007.T5

Quantifier order: for every natural n,h, if n>0, then for every proof hh that h>0, every Law L on n-by-h arrays, and every real q, **if B(L,q)**, all the following hold:

1. If q=0, then for every row i the first cell (index 0, available because hh) is missing with probability one, D=1, and (1−q^h)^n=1.
2. For every row i, S_i(0)=1.
3. For every row i and natural j<h, S_i(j+1)≤S_i(j)·q.
4. For every row i and natural j<h, if S_i(j)=0, then S_i(j+1)=0.
5. For every row i: c_i(0)=S_i(1); S_i(h)=product_{t=0}^{h−1} c_i(t); for every natural j<h, 0≤c_i(j)≤q; S_i(h)≤q^h; and 1−q^h≤1−S_i(h).
6. **If row independence additionally holds**, then D=product_i(1−S_i(h)) and (1−q^h)^n≤D.

Independence is required only for item 6, not for the prefix conclusions or the zero endpoint.

## SAP.P007.T6

There are three universally quantified components:

1. For every natural n,h with n>0,h>0 and every real q with 0≤q<1: −1<−q^h; 1−q^h≤1; 1+n(−q^h)=1−nq^h; 1−nq^h≤(1−q^h)^n≤1.
2. For every natural n,h with n>0,h>0, every Law L on n-by-h arrays, and every real q, if row independence and B(L,q) hold, then 1−nq^h≤(1−q^h)^n≤D≤1 and 0≤1−D≤nq^h; if q=0 then D=1; and if q>0 then nq^h=exp(log(n)+h log(q)). The n and h in the latter real formulas are cast to reals.
3. For every natural n>0: n≤2n, 2n≠n, and the cardinality of `Fin n × Fin 2` is 2n.

The last component is a cardinality/arithmetic fact about n pairs, without any separate random variable or grouping map.

## SAP.P007.T7

This is a conjunction of six model-existence components and four threshold-rounding identities:

1. An equal model n=1,h=2,q=3/4 exists with: b(1,3/4,2)=7/16, b(1,3/4,3)=37/64; the first is <1/2 and the second >1/2; 2<t(1,3/4,1/2)<3; floor_+(t)=2 and ceil_+(t)=3; for **every natural k**, b(1,3/4,k)≠1/2; D=7/16; for every natural k, b(1,3/4,k)≤1/2 iff k≤2; for every natural k, 1/2≤b(1,3/4,k) iff 3≤k; and R(1,3/4,t)=1/2.
2. An equal model n=10000,h=33,q=3/4 exists with D=b(10000,3/4,33)<1/2 and 1/2<b(10000,3/4,34).
3. An equal model n=10000,h=952,q=99/100 exists with D=b(10000,99/100,952)<1/2 and 1/2<b(10000,99/100,953).
4. An unequal model n=1,h=2 exists with b(1,3/4,2)=7/16≤1/2 and D=13/16>1/2.
5. An unequal model n=1,h=16 exists with b(1,3/4,16)=4251920575/4294967296<99/100<b(1,3/4,17), D=4294967293/4294967296>99/100, and floor_+(t(1,3/4,99/100))=16, ceil_+(t)=17.
6. An unequal model n=10000,h=33 exists with D=(1−3/4^33)^10000, 1−30000/4^33≤D, D>99/100, and b(10000,3/4,33)<1/2.
7. floor_+(t(10000,3/4,1/2))=33, ceil_+(t)=34, floor_+(t(10000,99/100,1/2))=952, and ceil_+(t)=953.

Each model component includes exact weights, normalized law existence, mutual row independence and the specified B(L,q), by the definitions above. Each existential has its own Law; the various dimensions need not share a sample space or coupling.

## SAP.P007.T8

The main universal component quantifies, **in this order**, over a natural n>0 and reals q,a with 0<q<1 and 0<a<1. For each such triple, put t=t(n,q,a). The conjunction asserts:

1. b(n,q,0)=0; for every natural k, 0≤b(n,q,k)<1; and k↦b(n,q,k) is strictly increasing on all naturals.
2. t>0, R(n,q,t)=a, and for every real x≥0, if R(n,q,x)=a then x=t.
3. For every natural k: b(n,q,k)≤a iff k≤t (casting k to real); a≤b(n,q,k) iff t≤k; b(n,q,k)=a iff k=t.
4. For every natural k: b(n,q,k)≤a iff k≤floor_+(t); a≤b(n,q,k) iff ceil_+(t)≤k. In addition b(n,q,floor_+(t))≤a≤b(n,q,ceil_+(t)).
5. ceil_+(t)=floor_+(t) iff there exists a natural m with m=t. If no such natural m exists, ceil_+(t)=floor_+(t)+1 and b(n,q,floor_+(t))<a<b(n,q,ceil_+(t)).
6. For every natural k>0 and every Law L on n-by-k arrays, if L has row independence and B(L,q), then b(n,q,k)≤D; furthermore, if ceil_+(t)≤k then a≤b(n,q,k) and a≤D.
7. For every natural k>0 with k<t, an equal model n,k,q exists with D=b(n,q,k)<a.
8. For every natural k>0, an equal model n,k,q exists with D=b(n,q,k), with no condition on k versus t.

Three more components follow the universal component:

9. `workedValues`: floor_+(t(10000,3/4,1/2))=33, ceil_+(t)=34; floor_+(t(10000,99/100,1/2))=952, ceil_+(t)=953; 0.47075≤b(10000,3/4,33)<0.47085; 0.49685≤b(10000,99/100,952)<0.49695.
10. b(10000,3/4,33)<1/2<b(10000,3/4,34) and b(10000,99/100,952)<1/2<b(10000,99/100,953).
11. An unequal model n=1,h=2 exists with b(1,3/4,2)≤1/2<D.

## SAP.P007.T9

There exists a Law L on two-by-two arrays with exactly figure5Weights, row independence and B(L,3/4), satisfying **all** these clauses:

* For every real q, B(L,q) implies 3/4≤q.
* For each row i, S_i(1)=3/4, S_i(2)=3/8, S_i(1)>0, and S_i(2)/S_i(1)=1/2.
* For each row i, E[I_i]=5/8.
* E[deletedFraction]=5/8; f(3/4,2)=7/16; and f(3/4,2)<E[deletedFraction].
* b(2,3/4,2)=49/256 and b(2,3/4,2)≠f(3/4,2).
* D=25/64.

The universal q lower bound is a conclusion about this specific law, not an extra hypothesis on the existential witness.

## SAP.P007.T10

Six universally quantified components are conjoined:

1. For every natural n,k with n>0,k>0, every Law L on n-by-k arrays and real q, if B(L,q), then for each row i, E[I_i]=1−S_i(k) and f(q,k)≤E[I_i]; also E[deletedFraction]=sum_i(1−S_i(k))/n and f(q,k)≤E[deletedFraction]. **No row independence** is assumed in this component.
2. For every natural n,k with n>0,k>0 and real q with 0≤q<1, an equal model n,k,q exists satisfying E[deletedFraction]=f(q,k).
3. For every natural n,k with n>0,k>0 and real q with 0≤q<1, b(n,q,k)=f(q,k)^n and b(1,q,k)=f(q,k).
4. For every natural n,k with n≥2,k>0 and real q with 0<q<1, 0<f(q,k)<1 and b(n,q,k)<f(q,k).
5. For every natural n,k with n>0,k>0 and real q with 0<q<1, b(n,q,k)=f(q,k) iff n=1.
6. For every natural n,k with n>0,k>0, f(0,k)=1 and b(n,0,k)=1.

The n=1 equivalence explicitly excludes q=0; the expectation bound and attainment permit q=0.

## SAP.P007.T11

Two assertions are conjoined:

1. For every natural n,k with n>0,k>0 and every Law L on n-by-k arrays, if row independence holds, D=product_i(1−S_i(k)). There is **no** observation-bound or identical-law hypothesis here.
2. There exists a Law L on two-by-one arrays with exactly nonidenticalWeights, row independence, B(L,1/2), and **failure** of sameRowLaw, with S_0(1)=1/4, S_1(1)=1/2, D=3/8, b(2,1/2,1)=1/4, and b(2,1/2,1)≤D.

## SAP.P007.T12

Three components are conjoined:

1. For every natural n,K,d with n>0,K>0, every Boolean matrix m with columns `Fin K ⊕ Fin d`, if every cell in the d right-hand columns is missing, then, writing A=A(m) and m' for the retained matrix, A=A(m')+nd; p(m)=A/[n(K+d)]; p(m')=(A−nd)/(nK) (real subtraction); (K+d)p(m)=d+Kp(m'); and p(m')=((K+d)p(m)−d)/K. The removed count d may be zero.
2. For every Boolean matrix m with 8580 rows and columns `Fin 1205 ⊕ Fin 19`, if all right-hand-column cells are missing and 0.6675≤p(m)<0.6685, then p(m')<199811/301250, 199811/301250<0.6675, and p(m')<0.6675.
3. For every such m, if all right-hand-column cells are missing and A(m)=7019387, then p(m)=7019387/10501920; p(m')=6856367/10338900; 0.6625≤p(m')<0.6635; p(m)−p(m')=66168127/12654813600; and 100(p(m)−p(m'))=66168127/126548136.

## SAP.P007.T14

For every natural n,k with n>0,k>0, every Law L on n-by-k Boolean missingness arrays and every real q, if row independence and B(L,q) hold, then (1−q^k)^n≤P(every row contains at least one missing entry). This includes q=0 because B supplies 0≤q<1. There is no equality-of-row-laws or within-row independence assumption.

## SAP.P007.T15

For every natural n,g with n>0,g>0, every Law L on n-by-g Boolean missingness arrays and every real q, if row independence and B(L,q) hold, then (1−q^g)^n≤P(every row contains at least one true group indicator). This is exactly the same mathematical statement as T14 with g in place of k. A coordinate can represent a nonempty group sharing a missingness pattern, but the theorem does not itself introduce group member types, their sizes, or an underlying variable-to-group map.

## SAP.P007.T16

Quantifier order: for every function k:N→N, and **every family of Laws L_n on n-by-k(n) arrays (for all natural n, including zero)**, if k(n)>0 for every n>0, then for every **single real constant q** with 0≤q<1, if L_n has row independence for every n>0 and satisfies B(L_n,q) for every n>0, and if k(n)/log(n)→+∞, then P_{L_n}(every row is deleted)→1 as n→∞.

The laws need not be related across n, and there is no coupling, identical-law hypothesis, or constant coordinate dimension. The same q bounds all positive n. There is no probability assumption at n=0; its Law is still part of the family. The limit ignores any finite initial segment.

## SAP.P007.T17

Quantifier order: for every function g:N→N, and every family of Laws L_n on n-by-g(n) group-indicator arrays for all natural n including zero, if g(n)>0 for every n>0, then for every single real q with 0≤q<1, if row independence and B(L_n,q) hold for each positive n and g(n)/log(n)→+∞, then P_{L_n}(every row has at least one missing group)→1.

As in T15, the formal object is a Boolean group-indicator array without an additional grouping map. The laws can change arbitrarily with n, subject to the stated bounds and independence. All restrictions and quantifier order match T16 with g replacing k.
