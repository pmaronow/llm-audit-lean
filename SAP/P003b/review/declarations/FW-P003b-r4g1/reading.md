# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: the five
Challenge docstrings and statements, every source declaration in their closures,
and `#print` output for all 99 distinct closure entries, including generated
constructors, recursors, equality tests, auxiliary proofs and match functions.
The elaborated output is in `scratch/closure-print.txt`. This document describes
the statements as written; it does not infer the canonical claims.

## Common expanded notation

The following is mathematical shorthand for fully expanded finite constructions,
not an additional assumption. A count vector is a tuple
`v=(a,b,c,d)` of **natural numbers**, ordered 11,10,01,00. Write
`N(v)=a+b+c+d`, `e(v)=(b:integer)-(c:integer)`, and
`tau(v)=(b-c)/N(v)`, with division in the rationals and then inclusion into the
reals when required. For an observed vector `o=(A,B,C,D)`, write
`m=A+B`, `n=A+B+C+D`, and `T(o)=A/(A+B)-C/(C+D)` (rational division, then real
inclusion).

For `v` and a natural `m`, the allocation list `R(v,m)` is formed by looping over

* `qa=0,...,min(a,m)`;
* `qb=0,...,min(b,m-qa)`;
* `qc=0,...,min(c,m-qa-qb)`;
* `qd=m-qa-qb-qc`, keeping the tuple only if `qd<=d`.

These are nested natural-number operations. Thus it lists once each tuple
`q` with `0<=q_i<=v_i` and sum `m`. Its integer weight is
`W(v,q)=choose(a,qa) choose(b,qb) choose(c,qc) choose(d,qd)`.
Here `choose` is Mathlib's natural binomial coefficient; the executable
`Nat.fast_choose` is the same coefficient. The observed vector from this tuple is

`O(v,q)=(qa+qb, qc+qd, a-qa+c-qc, b-qb+d-qd)`.

Subtraction in this expression is natural subtraction, left associated. On the
listed allocations it equals the ordinary nonnegative count. For a predicate
`E` on allocations and a real function `f`, the probability and mean used below
are respectively

`sum_{q in R(v,m)} W(v,q) 1_E(q) / choose(N(v),m)` and
`sum_{q in R(v,m)} W(v,q) f(q) / choose(N(v),m)`.

They are finite sums with the indicated real division, not unspecified measures.

The possible-vector list `P(o)` loops independently over
`0<=i<=A, 0<=j<=B, 0<=k<=C, 0<=l<=D` and returns

`(i+k, A-i+l, C-k+j, B+D-j-l)`.

Its membership predicate is the definition of possibility. Duplicates in the
list do not change membership or the eventual finite sets. Each such vector has
total `n`. Define the integer

`H(v,o,m)=N(v)((N(v)-m) A-m C)-m(N(v)-m)e(v)`.

All arithmetic in `H` is signed integer arithmetic, including the occurrences of
`N(v)-m`. The exact p-value is the rational number

`p(v,o) = sum_{q in R(v,A+B), |H(v,O(v,q),A+B)| >= |H(v,o,A+B)|} W(v,q)
            / choose(N(v),A+B)`.

Integer absolute values here are implemented by `Int.natAbs`. When the two arms
are positive and the totals agree, this is the usual inclusive two-sided tail
comparison of `|T-tau|`, multiplied by a common positive denominator.

For real `alpha`, let `K(alpha,o)` be the finite set of the real numbers
`tau(v)` for `v` in `P(o)` with `alpha<=p(v,o)`. Let

`I(alpha,o)={t:real | exists l,u in K(alpha,o), l<=t<=u}`,
`L(alpha,o)=sInf K(alpha,o)`, and `U(alpha,o)=sSup K(alpha,o)`.

The candidate numerator list is every integer
`A-C-(A+B)+r`, for `r=0,...,n`. The candidate set is
`C(o)={d/n : d in that list}`, with real division. Its largest listed value,
when `n>0`, is `cPlus(o)=(A-C-(A+B)+n)/n`.

A labeled binary potential-outcome table on `n` labels is a function
`w:{0,...,n-1}->Bool x Bool`. Its four counts count labels of each Boolean pair.
Writing Boolean values as the real numbers 0 and 1, put

`tau_w=(sum_i (w_i1-w_i0))/n`,
`T_w(z)=(sum_{i in z} w_i1)/|z|-(sum_{i notin z} w_i0)/(n-|z|)`.

The elaboration confirms that `n-|z|` in this last denominator is **real**
subtraction after casts. A fixed-size assignment is a finite subset `z` of the
`n` labels with cardinality `m`. Uniform probability on any finite type is the
real ratio `number of elements satisfying E / cardinality of the type`.

The generated count constructors/projections/recursors have their ordinary
four-natural-coordinate meanings. The derived equality test compares the four
coordinates. Its helper proofs just establish reflexivity or constructor
injectivity. The various generated `_proof_*` for numeric literals establish
nonzero/at-least-two facts used in rational literals or finite-index notation;
they add no hypotheses to any theorem.

## SAP.P003b.T24

Source: `SAP/P003b/Challenge/Part1.lean:8`, statement in
`SAP/P003b/Defs/Part4.lean:17`.

Quantifiers, in order: for every natural `n` (implicit), every binary table `w`
on `n` labels, and every natural `m`, assume `m>0` and `n=2m`. Then all of the
following hold:

1. For every finite subset `z` of the labels, if `|z|=m`, its complement has
   cardinality `m`, and
   `T_w(z)+T_w(z complement)=sum_i(w_i1-w_i0)/m=2 tau_w`.
2. With `v` the actual four counts of `w`, the finite mean
   `sum_{q in R(v,m)} W(v,q) T(O(v,q))/choose(N(v),m)` equals `tau_w`.
3. For every real `t`, the finite weighted mass of allocations with
   `T(O(v,q))=tau_w-t` equals that with `T(O(v,q))=tau_w+t`.

The statement asserts symmetry of all point masses, not merely symmetry of a
selected tail or an unweighted distribution of count tuples. It includes the
correct factor 2 in the complementary-estimate sum. It does not quantify over
nonbinary outcomes or unbalanced designs.

Junk/boundary audit: `n=2m>0`, both assignment arms have size `m>0`, and actual
table counts sum to `n`, so every mean, estimate and probability denominator is
positive. The bounds in `R` prevent all its natural subtractions from truncating;
`q<=v` prevents truncation in `O`. Empty allocation lists cannot occur here.
The underlying definitions would return zero on division by zero if called
outside their intended ranges, and `tableTau` would be zero at `n=0`, but the
theorem excludes those cases. There are no logs, roots, rpow, integrals, extended
reals, extrema, limits, or partial-list operations in this closure. Casts of
natural counts and signed effects preserve their intended meanings.

## SAP.P003b.T25

Source: `SAP/P003b/Challenge/Part1.lean:13`, statement in
`SAP/P003b/Defs/WholeW2.lean:114`.

In addition to the common finite constructions, define

`J(alpha,o)={t in C(o) | exists v in P(o), tau(v)=t and alpha<=p(v,o)}`,

and

`Jprinted(alpha,o)={t in C(o) | exists natural count vector v,
   N(v)=n and tau(v)=t and alpha<=p(v,o)}`.

The second set omits possibility but keeps the population total. These are the
exact definitions, including the candidate-set clause in both. The theorem is a
conjunction with these independently quantified parts:

1. For every observed natural vector `o`, then every real `alpha`, if `A+B>0`,
   `C+D>0`, and `0<alpha<1`, then `J(alpha,o)=K(alpha,o)` and
   `J(alpha,o) subset I(alpha,o) intersect C(o)`.
2. For every `o`, then every real `alpha`, if `A+B>0`, `A+B=C+D`, and
   `0<alpha<1`, then
   * `J=I intersect C(o)`;
   * `[T(o),cPlus(o)] intersect J=[T(o),U] intersect C(o)`;
   * `K` is nonempty, `L<=T(o)<=U<=cPlus(o)`;
   * `cPlus(o)` belongs to `C(o)` and every member of `C(o)` is at most it.
3. For the fixed vector `o*=(0,2,0,2)` the candidate set is exactly
   `{-1/2,-1/4,0,1/4,1/2}`.
4. The vectors `(1,0,2,1)` and `(1,2,0,1)` respectively have effects `-1/2`
   and `1/2`, both have p-value `2/3`, and neither is in `P(o*)`.
5. Every possible vector with effect `-1/2` is `(0,0,2,2)`. That vector really
   is possible, has effect `-1/2`, and has p-value `1/3`.
6. For every integer `e` in `[-2,-1,0,1,2]`, let `p_e=1/3` at `e=-2,2`
   and `p_e=1` otherwise. Every possible `v` with integer effect `e` has
   `p(v,o*)<=p_e`, and there exists a possible vector of that effect attaining
   `p_e`.
7. At `alpha=1/2`, `J={-1/4,0,1/4}`, `I=[-1/4,1/4]`,
   `L=-1/4`, `U=1/4`, and `Jprinted=C(o*)`.
8. Both `-1/2` and `1/2` are outside `I(1/2,o*)`, while `1/8` is inside it
   and outside `C(o*)`.

Junk/boundary audit: all general clauses require positive arms and hence `n>0`.
The explicit examples have `n=4,m=2`. In the p-values of possible vectors the
total is `n`; the two impossible example vectors and all witnesses permitted by
`Jprinted` also have total `n`. Thus the binomial denominator is positive in
every relevant p-value, even the impossible ones. `P` only subtracts within its
loop bounds; `R` and `O` are safe as described above. The numerator-list formula
uses signed subtraction, so negative candidate effects are retained. `I` is
empty if `K` is empty, by its existential definition. For arbitrary arguments
`L` and `U` use the conditionally complete real order's default values (in
particular zero for an empty finite set); here their uses are in the balanced
clause, which also asserts nonemptiness, or in the explicit nonempty example.
Every such finite set is bounded. Consequently no endpoint conclusion depends
on empty-set or unbounded-set defaults. There are no logs, roots, rpow,
integrals, extended-real conversions, limits or list-index defaults in this
closure. Rational-to-real casts are exact.

## SAP.P003b.T8

Source: `SAP/P003b/Challenge/Part1.lean:25`, statement in
`SAP/P003b/Defs/Part4.lean:45`.

Expanded definitions: for naturals `m,k`, define the rational numbers

`V_m(k)=(2m/(2m-2)) (2k(m-k)/m^3)`, `t_m(k)=(2k-m)/m`.

The subtractions `2m-2`, `m-k`, and `2k-m` in these formulas occur in the
**rationals**, as confirmed by the elaboration. Set
`W_m(k)=2z sqrt(V_m(k))` and
`A_m(k)=[t_m(k)-z sqrt(V_m(k)), t_m(k)+z sqrt(V_m(k))]`, in the real
numbers. The coverage function is
`sum_{k=0}^m choose(m,k)^2 1_{lo<=k<=hi}/choose(2m,m)`, computed in the
rationals. A number `d` is a design median of real values `Q(k)` if both

`sum_{0<=k<=m, Q(k)<=d} choose(m,k)^2/choose(2m,m)>=1/2` and
`sum_{0<=k<=m, d<=Q(k)} choose(m,k)^2/choose(2m,m)>=1/2`.

The finite-list median sorts the real list in increasing order; it is zero for
the empty list and otherwise averages entries with zero-based indices
`floor((length-1)/2)` and `floor(length/2)`.

Quantifiers: for every real `z`, assume the strict rational enclosure
`1.95996398454005<z<1.95996398454006`. The conclusion is the conjunction of:

1. For every natural `k<=25`, `0 in A_25(k)` iff `10<=k<=15`.
2. For every natural `k<=25` whose interval contains zero, `W_25(k)>0.55`.
3. For every list `runs` of elements of `Fin 26`, if it is nonempty and at
   least the fraction `0.925` of its entries have `0 in A_25(k)`, the finite
   list median of its widths is strictly greater than `0.55`.
4. The coverage sum over `10,...,15` at `m=25` is exactly
   `14399081696900/15801325804719`.
5. `W_25(11)=2z sqrt(77/3750)`. The weight on `k=12,13` is strictly less
   than `1/2`, and the weight on `k=11,...,14` is strictly greater than `1/2`.
6. The coverage sum over `21,...,29` at `m=50` is exactly
   `3816125510529753382833452/4109292299835622081085553`, and
   `W_50(23)=2z sqrt(621/61250)`.
7. For every nonempty list `runs` in `Fin 26`, if more than half its entries
   have intervals containing zero, its median width is at least
   `2z sqrt(1/50)`.
8. For every natural `k<=25`, put `V0(k)=2k(25-k)/15625` and use center
   `t_25(k)`. The interval with this variance contains zero iff `10<=k<=15`,
   and every such covering width `2z sqrt(V0(k))` is greater than `0.54`.
9. `2z sqrt(77/3750)` is a design median of `W_25`; for every natural
   `k<=50`, `0 in A_50(k)` iff `21<=k<=29`; and
   `2z sqrt(621/61250)` is a design median of `W_50`.
10. The two displayed design medians respectively lie strictly between
    `0.56170,0.56171` and between `0.39470,0.39471`.

The list quantifiers impose no randomness or independence: they are deterministic
implications for every run list. The conclusion does not separately assert
uniqueness of either design median, identify a normal quantile, connect the
formulas to a regression on labeled assignments, or give the wider critical-value
ranges mentioned as omissions in the docstring.

Junk/boundary audit: every use has `m=25` or `50`, so all rational variance and
estimate denominators are nonzero. Every relevant `k` is in `[0,m]`, making
the variance nonnegative; `sqrt(0)=0` at endpoint samples is the correct
degenerate variance. Outside that range `Real.sqrt` would be zero on negative
arguments, and at `m=0` or `1` rational division would totalize otherwise
undefined formulas, but no assertion here uses those arguments. The coverage
and median-weight denominator `choose(2m,m)` is positive. All list-average
implications exclude empty lists. Sorting preserves length, and both selected
indices are valid for any positive length; the `getElem!` default zero is
unreachable. Natural subtraction in `length-1` is safe. The fractions use exact
rationals/reals, including the decimal endpoints, rather than floating point.
The closure has no logs, rpow, Bochner integrals, extended reals, extrema or
limits.

## SAP.P003b.T19

Source: `SAP/P003b/Challenge/Part1.lean:40`, statement in
`SAP/P003b/Defs/WholeW2.lean:47`.

Expanded constructions: the set `A(n)` is the finite set from `R((n,n,n,n),n)`;
equivalently it contains all nonnegative four-tuples of sum `n`.
`S(N0,N1)=A(N0) x A(N1)`. For `X:Fin n->Bool`, let
`Ns=number of labels i with X(i)=s`. The eight counts of `w` are its four
Boolean-pair counts on each of the two sets `X=false` and `X=true`.
`Image(X)` is the finite image of **all** functions `w:Fin n->Bool x Bool`
under that count map. The total-only set is
`E(n)=union_{r=0}^n (A(r) x A(n-r))`.
The two real row vectors `r_s` in real eight-coordinate space, whose coordinates
are `((b1,b0),s')`, have value `1` if `s'=s` and `0` otherwise.

The theorem is the conjunction of:

1. The pair of rows indexed by `Bool` is linearly independent over the reals
   (every finite real linear combination equal to zero has zero coefficients),
   and `r_false(cell)+r_true(cell)=1` for every coordinate.
2. For every natural `n`, then every fixed function `X:Fin n->Bool`:
   * `Nfalse+Ntrue=n`;
   * for every table `w`, the two count totals are the two `Ns`, and their
     sum is `n`;
   * `Image(X)=S(Nfalse,Ntrue)`;
   * `|Image(X)|=choose(Nfalse+3,3) choose(Ntrue+3,3)`;
   * `|Image(X)|<=((n:real)+3)^6/36`;
   * the image of all tables under their unstratified four-count map is
     `A(n)`, `|A(n)|=choose(n+3,3)`, and there are `4^n` labeled tables.
3. For every natural `n`, and then every pair of natural four-count vectors
   `(v0,v1)`, membership in `E(n)` iff `N(v0)+N(v1)=n`;
   `|E(n)|=choose(n+7,7)`, which also equals
   `sum_{r=0}^n choose(r+3,3) choose(n-r+3,3)`.
4. For every two sequences `N0,N1:natural->natural`, if
   `N0(n)+N1(n)=n` for every `n`, the real cardinality sequence
   `|S(N0(n),N1(n))|` is both `O(n^6)` and `O(n^7)` at natural infinity.
   Each Big-O statement means that there exists a real constant bounding the
   absolute value by that constant times the absolute value of the indicated
   power for all sufficiently large natural `n`. The earlier explicit bound
   does not depend on the split.
5. The real cardinality sequences `|E(n)|` and `|A(n)|` are respectively
   `O(n^7)` and `O(n^3)` in the same sense.
6. For every `X:Fin 4->Bool` with both stratum sizes 2, there are 256 labeled
   tables, `|Image(X)|=100`, `|E(4)|=330`, and the pair
   `((3,0,0,0),(1,0,0,0))` belongs to `E(4)` but is not the eight-count
   image of any table for that fixed `X`.

Junk/boundary audit: empty strata and even `n=0` are included deliberately.
There is one table on no labels and one all-zero composition of zero, so those
are genuine finite counting cases. `R((n,n,n,n),n)` respects every subtraction
bound. `n-r` in the union and convolution does not truncate because `r<=n`.
There is no `sInf`, `sSup`, inverse, square root, logarithm, integral, toReal,
limit supremum, or partial lookup here. The division by 36 is a real constant
division. Big-O ignores finitely many small indices, with the quantifiers just
stated; it is not a convention for an unbounded sequence's extremum. Casts of
cardinalities are injective natural-to-real casts, with no machine overflow.

## SAP.P003b.T20

Source: `SAP/P003b/Challenge/Part1.lean:50`, statements in
`SAP/P003b/Defs/WholeW2.lean:172` and `SAP/P003b/Defs/Part4.lean:90`.

Further expanded definitions: for natural count vector `v` and natural `r`, the
reuse vector is `(a-r,b+r,c+r,d-r)`, with natural subtraction. For `o`, integer
effect numerator `x`, and natural `j`, form the sublist of `P(o)` satisfying
`b-c=x` (in the integers) and `a+b=j`. Select its member with least `b` by
recursive comparison; return `none` for an empty list. Ties select the earlier
member. This option is what `firstOnLine` denotes. The signed line, for arbitrary
integers `n,j,b,x`, is `(j-b,b,b-x,n-j-b+x)` with all four coordinates integer.

The binary-assignment type consists of Boolean functions on `Fin n` having
exactly `m` true entries, measured by the natural sum of their 0/1 values.
The binary coordinates of a treated set are its membership indicators.
The theorem is a conjunction, with quantifier order as follows:

1. For every natural `n,m` with `0<m<n`, there exists a bijection from the
   `m`-element subsets of the labels to the binary-assignment type. On every
   subset its value is exactly the membership-indicator function. For every
   predicate `E` on binary assignments, the fraction of subsets whose image
   satisfies `E` equals the fraction of binary assignments satisfying `E`.
2. The following three clauses are imported as a conjunction, rather than
   assumed as hypotheses:
   * For every implicit `n`, every natural `m` with `0<m<n`, and every pair
     of binary tables `w,w'` with equal four-count vectors, for every real
     `t` the uniform fractions of assignments with `T_w(z)=t` and
     `T_w'(z)=t` are equal.
   * For every natural count vector `v` with `a>=1,d>=1`, casting each
     coordinate of its one-step reuse vector into the integers gives exactly
     `(a-1,b+1,c+1,d-1)` in signed arithmetic.
   * For every tuple of integers `n,n11,n10,n01,j,b,x,u11,u10,u01,u00`
     satisfying `u11+u10+u01+u00=n` and `u10-u01=x`, the four equivalences
     below hold; so does
     `(u11+u10-b,b,b-x,n-(u11+u10)-b+x)`
     `=(u11+(u10-b),u10-(u10-b),u01-(u10-b),u00+(u10-b))`;
     and for every integer `a,d`, evenness of `a+2+d` implies
     `d mod 2=a mod 2`.
3. For all integers `n,n11,n10,n01,j,b,x`, with no hypotheses, the four
   equivalences are also asserted separately:
   * `j-b-n01<=j-b` iff `0<=n01`;
   * `j-b-n01<=n11` iff `j-n11-n01<=b`;
   * `j-b-n01<=j-x-n01` iff `x<=b`;
   * `j-b-n01<=n-b-n10-n01` iff `j+n10<=n`.
4. For every natural vectors `o,u,v`, if `u` is in `P(o)` and the selector
   on effect `u.b-u.c` and index `u.a+u.b` returns `some v`, let the integer
   `k=u.b-v.b`. Then `k>=0`, if `u!=v` then `k>0`, and the signed line at
   `(n=N(o),j=u.a+u.b,b=v.b,x=u.b-u.c)` is
   `(u.a+k,u.b-k,u.c-k,u.d+k)`.
5. For every `o,u,v`, then every real `alpha`, if `A+B>0`, `A+B=C+D`,
   `u` is possible, that same selector returns `v`, and `v.b+v.c>=1`,
   then `p(u,o)<=p(v,o)` and `p(v,o)<alpha` implies `p(u,o)<alpha`.
   There is no restriction on `alpha` in this implication.
6. For every integer `b,k`, the signed line `(4,0,b,2)` is unequal to
   `(k,2-k,-k,2+k)`.
7. The two tables on labels 0,1 are respectively `((1,1),(0,0))` and
   `((0,0),(1,1))`. Their four-count vectors both equal `(1,0,0,1)`, the
   fixed treated subset `{0}` has cardinality 1, and their estimates at
   that same subset are respectively `1` and `-1`.

The last signed-line assertion is a universal algebraic inequality, not a
formalized search transcript. The last two-table assertion distinguishes
equality of distributions from equality at an identical fixed assignment.

Junk/boundary audit: the uniform-law and equal-distribution clauses require
`0<m<n`; their assignment types are nonempty and their real cardinality
denominators are positive. Tables and subsets there have positive arms.
`reuseVector v 1` only occurs under `a,d>=1`, preventing truncation. Selector
claims require a returned `some v`, so no arbitrary value is substituted for
an empty line. Because a possible `u` is on the specified line, the line really
is nonempty. Possibility gives a common population total; the balanced p-value
clause therefore also has positive binomial denominators. Natural subtractions
inside the finite enumerations are bounded as in the common definitions.
The line itself uses signed integers, without `Int.toNat` or natural truncation.
All remainders are modulo the nonzero integer 2 and implement evenness correctly
for negative integers as well. The two-table example has both arms of size 1.
There are no logs, roots, rpow, integrals, extended-real conversions, extrema,
limits or out-of-range list lookups in this closure.
