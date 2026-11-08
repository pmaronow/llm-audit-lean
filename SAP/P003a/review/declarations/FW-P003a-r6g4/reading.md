# Blind reading

Written after reading `closure.json`, the three Challenge declarations and all
source declarations in their closures, and before opening `claims.json` or
`record.json`. Compiler-generated projections, recursors, pattern matchers,
default values and auxiliary proofs were also inspected with Lean in
`scratch/Closure.lean` (output: `scratch/closure-print.txt`). They implement the
displayed structures, finite-number bounds and recursive definitions; they add
no mathematical hypotheses. No paper or external source has been consulted.

## Common expanded vocabulary

The notation below is only an abbreviation for the following explicit finite
constructions, not an additional assumption.

* A `Counts` object is an arbitrary quadruple `(a,b,c,d)` of natural numbers.
  Its size is `N(v)=a+b+c+d` and its effect numerator is the integer
  `e(v)=int(b)-int(c)`. For potential outcomes the cell order is
  `(11,10,01,00)`; for observations it is `(treated success, treated failure,
  control success, control failure)`.
* For observation `o=(A,B,C,D)`, its possible population list `P(o)` is the
  nested finite enumeration, in increasing `i,j,k,l`, of
  `(i+k, A-i+l, C-k+j, B+D-j-l)`, where
  `0<=i<=A`, `0<=j<=B`, `0<=k<=C`, `0<=l<=D` are natural numbers.
  `Possible o v` means membership in this list. Repeated entries in a list
  are retained unless a conversion to a finite set or `dedup` is specified.
* The effect list `E(o)` has `N(o)+1` integer entries
  `A-C-(A+B)+h`, for `h=0,...,N(o)`; equivalently it runs from `-B-C`
  through `A+D`. A line `G(o,x,j)` is `P(o)` filtered by
  `e(v)=x` and `v.a+v.b=j`. Its base `F(o,x,j)` is absent if the line is
  empty, and otherwise is the first member with minimum `b` (the recursive
  minimum keeps the earlier member on a tie).
* `U(v,k)=(v.a-k,v.b+k,v.c+k,v.d-k)` uses natural subtraction in the
  first and last positions. This is the reuse transformation.
* For a population `v` and treated size `m`, `Q(v,m)` enumerates natural
  `(a,b,c,d)` with `a<=min(v.a,m)`, `b<=min(v.b,m-a)`,
  `c<=min(v.c,m-a-b)`, `d=m-a-b-c<=v.d`. Its assignment weight is
  `W(v,q)=choose(v.a,q.a)*choose(v.b,q.b)*choose(v.c,q.c)*choose(v.d,q.d)`.
  `binomial` is Mathlib `Nat.fast_choose`.
* The observation induced by treated type counts `q` is
  `O(v,q)=(q.a+q.b,q.c+q.d,v.a-q.a+v.c-q.c,v.b-q.b+v.d-q.d)`.
  The last two entries use left-associated natural subtraction/addition as
  written. On admissible treated counts they are the untreated totals.
* With `m=o.a+o.b`, define the integer
  `Delta(v,o,m)=N(v)*((N(v)-m)*o.a-m*o.c)-m*(N(v)-m)*e(v)`;
  every operation in this formula, including subtraction, is in the integers.
  Let `H(v,o)` be the sum of `W(v,q)` over `q` in `Q(v,m)` for which
  `abs(Delta(v,O(v,q),m))>=abs(Delta(v,o,m))`.
  Then `p(v,o)=rational(H(v,o))/choose(N(v),m)`. Ties are included.
* The rational population effect is `t(v)=e(v)/N(v)` and its real version is
  the rational-to-real cast. The rational observation estimate is
  `d(o)=o.a/(o.a+o.b)-o.c/(o.c+o.d)`, again cast to reals when needed.
* The real accepted-effect finite set `Acc(alpha,o)` is the image under
  real `t` of all entries `v` of `P(o)` with `alpha<=real(p(v,o))`.
  Its interval is `{z : real | exists l,u in Acc(alpha,o), l<=z<=u}`.
  Its real upper endpoint is the real `sSup` of that finite set.
* For rational `alpha`, the Boolean acceptance test uses denominator
  `D0=choose(N(v),o.a+o.b)`. If `D0=0`, it tests `alpha<=0`;
  otherwise it tests `alpha.num*D0<=H(v,o)*alpha.den` in the integers.
  `acceptedEffectsQ` deduplicates `P(o)`, filters by this Boolean and maps
  to `e(v)`. `intervalQ` is `none` for an empty resulting list, and otherwise
  `some(min effect/N(o),max effect/N(o))` using finite list folds.
* An `Assignment n m` is a finite subset of `Fin n` with cardinality `m`.
  There is no probability law in this type. The canonical labeled population
  for `v` assigns `(true,true)` to indices `<v.a`, `(true,false)` to the next
  `v.b`, `(false,true)` to the next `v.c`, and `(false,false)` thereafter.
  `treatedCounts(v,z)` counts these four types within the finite subset `z`.
  `canonicalObserved(v,z)` instead counts treated/control observed successes
  and failures over all indices in `Fin n`.
* A potential table is a function `Fin n -> Bool x Bool`.
  `tableCounts` counts its four types. `unitOutcomes(w,z)` chooses the first
  Boolean on `z` and the second outside `z`. `unitObserved(y,z)` counts the
  four assignment/outcome cells of the resulting Boolean function `y`.
* For any real statistic `R : Counts -> Counts -> real`, fixed observation
  `o`, population `v`, and sample counts `s : Fin K -> Counts`, the plus-one
  rank is
  `(1 + sum_{i<K} 1[abs(R(O(v,s(i)),v))>=abs(R(o,v))])/(K+1)`.
  Both statistic comparisons use the same `R` and population `v`.

## SAP.P003a.T21

Location: `SAP/P003a/Challenge/Part2.lean:72-77`. There are no hypotheses and
no free parameters: this is a conjunction of closed computations. Its docstring
describes a corrected nine-unit example, its attained maximum p-values,
accepted interval, negative fiber and two p-value-one witnesses.

The statement asserts all of the following, using exactly the finite
constructions above:

1. For `o=(1,6,0,2)` and rational `alpha=17/18`, the set of accepted integer
   effect numerators is `{0,1}`; the rational interval is `some(0,1/9)`;
   `d(o)=1/7`; `not(0<=1/7 and 1/7<=1/9)`;
   `p((1,0,1,7),o)=29/36<17/18`.
2. The same `o` has size 9, treated size 7 and two positive arms; the number
   of seven-element subsets of `Fin 9` is 36. Its integer candidate list is
   `[-6,-5,-4,-3,-2,-1,0,1,2,3]`.
3. `P(o)` equals the explicit nested list of `(i,1-i+l,j,8-j-l)` for
   `i=0,1`, `j=0,...,6`, `l=0,1,2`; its associated finite set has 42 members.
4. For each pair `(x,p0)` in
   `[(-6,1/36),(-5,1/12),(-4,1/6),(-3,4/9),(-2,1/2),
     (-1,29/36),(0,1),(1,1),(2,2/3),(3,1/12)]`, both
   `(forall v, v in P(o) -> e(v)=x -> p(v,o)<=p0)` and
   `(exists v, v in P(o) and e(v)=x and p(v,o)=p0)` hold.
   The maximum is attained, not an empty-fiber convention.
5. The finite set of all members of `P(o)` with `e(v)=-1` is exactly the set
   of entries in the ordered list
   `[(1,0,1,7),(0,1,2,6),(0,2,3,4),(0,3,4,2),(1,1,2,5),(1,2,3,3)]`.
   Mapping `p(v,o)` over this list gives, in that order,
   `[29/36,18/36,17/36,16/36,19/36,16/36]`.
6. With `alpha` cast to reals, `Acc(alpha,o)={0,1/9}`, its interval equals
   the real closed interval `[0,1/9]`, and the real `d(o)` is outside it.
7. Each of `(0,1,0,8)` and `(1,0,0,8)` belongs to `P(o)` and has p-value 1;
   their rational effects are respectively `1/9` and 0.

Junk-value audit: rational and real division by zero is defined to be zero in
Lean, and the Boolean p-value comparison has a special zero-denominator branch.
Here all populations being tested have size 9, each randomization denominator
is `choose(9,7)=36`, both observation arms are positive, and every effect and
interval division has positive denominator 9. The finite enumeration bounds
ensure that all natural subtractions in `P(o)`, `Q(v,m)` and observations of
admissible states represent ordinary nonnegative differences. Integer effect
subtraction remains signed. Empty lists return `none` for rational intervals;
the displayed accepted set is explicitly nonempty. The real interval uses
existential endpoints, so it gives the empty set on an empty input rather than
a spurious zero endpoint. There is no `sSup`, measure, integral, infinite
sum, log, root, real power or partial function in this target's closure.
Empty assignment spaces are excluded by this concrete `9,7` choice.

## SAP.P003a.T22

Location: `SAP/P003a/Challenge/Part2.lean:79-86`. The docstring describes a
corrected traversal of every feasible population, an output using actual ranks
and correlated count updates, and a first-line-only interpretation that misses
one value in a two-unit example. It does not call the printed assertion false.

Additional expanded finite constructions:

* A visit has a slot `(i,j)` in `Fin(N(o)+1)^2`, a base quadruple `v`, and a
  natural reuse index `k`. For a base `v`, `L(o,v)` lists positive integers
  `1<=k<=N(o)` satisfying `k<=v.a`, `k<=v.d`, and `U(v,k) in P(o)`.
* At a slot `(i,j)`, select `x=reverse(E(o))[i]`. If `F(o,x,j)` is absent,
  the visit list is empty. Otherwise it is the base visit `(slot,v,0)`
  followed by `(slot,v,k)` for `k` in `L(o,v)`.
* The corrected traversal concatenates these visit lists for all `i`, then
  all `j`, in ascending finite-index order. The first-line traversal instead
  takes only the first nonempty `j` visit list for each `i`.
* Given `v,q` and natural seeds `s0,s1`, put
  `c0 := s0 mod v.d < v.d-q.d` and
  `c1 := s1 mod v.a < v.a-q.a`. The next treated count is
  `(if c1 then q.a else q.a-1,
    if c1 then q.b else q.b+1,
    if c0 then q.c else q.c+1,
    if c0 then q.d else q.d-1)`.
* For each slot, initial samples are arbitrary functions
  `Fin K -> {z subset Fin N(o) : card(z)=m}`. Seeds are functions
  `Fin N(o) -> Fin K -> Fin(N(o)!) x Fin(N(o)!)`.
  At reuse index zero, sample counts are `treatedCounts(v,initial(i))`.
  At `t+1`, apply the preceding update to population `U(v,t)` and the
  sample at `t`, using seeds at time `t`. If `t>=N(o)`, the total definition
  substitutes the zero seed pair.
* `Output(corrected,alpha,theta,R,o,initial,seeds)` consists of real `t`
  for which some visit `s` in the chosen traversal satisfies
  `t=theta(U(s.base,s.k))` and `alpha<rank(R,o,U(s.base,s.k),samples_at_s.k)`.
  `Formula` is the set given by explicitly existentially quantifying a slot,
  a base with `F(o,reverse(E(o))[i],j)=some v`, and then a natural
  `k<=N(o),v.a,v.d` with `U(v,k) in P(o)`, and imposing the same value and
  strict rank comparison with the same slot's draws and seeds.

The theorem is the conjunction of these quantified and concrete statements:

1. For every pair of quadruples `o,u`, under the sole hypothesis `u in P(o)`,
   `e(u) in E(o)`, `u.a+u.b<=N(o)`, and there exists a quadruple `v` such
   that `F(o,e(u),u.a+u.b)=some v` and there exists a natural
   `k<=N(o),v.a,v.d` such that `u=U(v,k)`.
2. `P((0,1,0,1))` as a finite set is exactly
   `{(0,0,0,2),(0,0,1,1),(0,1,0,1),(0,1,1,0)}`; its effect-zero bases at
   `j=0,1` are `(0,0,0,2)` and `(0,1,1,0)`.
3. For every `o,u`, `(exists corrected visit s, U(s.base,s.k)=u)` if and
   only if `u in P(o)`. No arm-size, positivity or probabilistic hypothesis.
4. For every natural `m,K`, real `alpha`, real-valued functions `theta` of
   populations and `R` of observation/population pairs, observation `o`, then
   every well-typed initial-sample and seed array, corrected `Output=Formula`.
   There are no distribution, independence or accuracy hypotheses. This is
   an identity for each fixed input array, not a probability assertion.
5. For `o=(0,1,0,1)`, the effect-minus-one base at `j=0` is `(0,0,1,1)`;
   the effect-one line at `j=0` is empty and at `j=1` has base `(0,1,0,1)`.
   The reuse-index lists for `(0,0,1,1)`, `(0,0,0,2)` and `(0,1,0,1)` are
   all empty.
6. For every natural `K`, real `alpha`, hypotheses `K>0` and
   `0<alpha<1`, and then every initial array of size-one assignments on
   two labels and every corresponding seed array, set
   `theta(v)=real(v.b+v.c)` and `R(o,v)=0`. The first-line output is
   `{0,1}` and the corrected output is `{0,1,2}`.
7. For every natural `K`, quadruples `o,v`, and samples `Fin K -> Counts`,
   the rank of the zero statistic is exactly 1, including `K=0`.
8. Let the two-subject potential table give index 0 `(false,true)` and index
   1 `(true,false)`, and take the treated subset `{0}`. That subset has size
   one, the population counts are `(0,1,1,0)`, all observed outcomes are
   false, the observation is `(0,1,0,1)`, and `v.b+v.c=2`.

Junk-value audit: natural subtraction occurs in the reuse vector, admissible
state counts and the update. Actual visits require `k<=base.a,base.d`, so the
population subtractions on those visits do not truncate. On legal nonempty
updates, each pre-update population has positive `a,d`, and the sample cannot
lose a treated unit of an empty group. Nevertheless the definitions are total
on arbitrary invalid counts; subtraction then truncates. The general output
identity permits arbitrary `m` (and even an empty population), and asserts an
enumeration identity there without asserting a sampling interpretation.
`s mod 0=s` in Lean; the formula could use that convention on arbitrary inputs,
but positive reuse bounds exclude zero divisors during actual positive-index
visits. The plus-one rank denominator is always `K+1>0`. For `K=0` its
finite sum is empty and rank is 1; the nontrivial omitted-value demonstration
additionally requires `K>0`. If `m>N(o)`, assignments do not exist; initial
arrays then do not exist when `K>0`, but this does not vacate the separate
all-population coverage statement or the concrete legal example. There is no
division by arm sizes in this theorem's own use of ranks.

The reversed effect list has exactly `N(o)+1` entries, so its finite-index
`getElem!` is always in range; otherwise the integer default would be zero.
The zero fallback seed at `t>=N(o)` is never used to produce any visited
sample, since visited `k<=N(o)` requires only times `t<k`. Even for size
zero, `0!=1`, so every finite seed residue type has an element. Empty line
lists and the absent base are deliberately represented by `[]` and `none`.
No real extrema, integrals, infinite sums, logs, roots or powers occur.

## SAP.P003a.T23

Location: `SAP/P003a/Challenge/Part2.lean:88-95`. The docstring describes a
necessary pathwise condition on returning an upper endpoint, first for arbitrary
decisions and then for a chronological Monte Carlo implementation. It does not
claim Monte Carlo decision monotonicity or sufficient endpoint correctness.

Additional expanded constructions:

* The sentinel integer search with fuel `F`, decision `f : integer -> Bool`
  (`true` means reject), bracket `(a,b)`, returns `(a,[])` if `F=0` or
  `b<=a+1`. Otherwise it queries `c=floor((a+b)/2)`, recursively replaces
  `(a,b)` by `(a,c)` on rejection or `(c,b)` on acceptance with fuel `F-1`,
  and prepends `c` to the returned query list.
* The table-test list `C(o,x)` concatenates over `j=0,...,N(o)` the base
  `F(o,x,j)` when it exists. If that base has `b=c=0`, `a,d>=1`, and
  `(a-1,1,1,d-1) in P(o)`, that second vector is appended after the base.
* `Tests(reject,idx,vs)` scans that list, where
  `reject : Counts -> natural -> Bool`. A rejection records `(v,true)`,
  increments the index and continues; an acceptance records `(v,false)`,
  increments the index and immediately returns compatible. The empty list
  returns incompatible with no index increment. It records final index and
  chronological trace in addition to the compatibility Boolean.
* An effect search has an optional integer result, a list of query records
  `(x,start,rejected)`, and the complete table-test trace. At an adjacent
  bracket it returns `some a`. At zero fuel with a wider bracket it returns
  `none`. Otherwise it queries `c=floor((a+b)/2)` by running the whole
  compatibility scan on `C(o,c)`, records the original table-test index and
  negated compatibility, updates the bracket as in sentinel search, and
  continues with the final table-test index. Thus table tests stop at the
  first acceptance within each compatibility block, not at every vector.
* The upper run starts with index zero, fuel `N(o)+3`, and bracket
  `(2*(o.a-o.c)-1, o.a-o.c+(o.a+o.b)+1)` in the integers.
  The separately defined `upperRun true` executes the same corrected search
  without outer query records. (`adaptiveSearch false` instead has the
  additional printed boundary branches; these are not selected here.)
* `B(n)=(n+1)*(Nat.log2(n+1)+3)` and `L(n)=2*B(n)+1`. A pool has type
  `Fin L(n) -> Fin K -> Assignment n m`. The batch at natural index `idx`
  is the pool slot `idx mod L(n)`; it yields `K` treated subsets.
* The rational Monte Carlo mean for population `v`, observation `o`, and
  those treated subsets is
  `K^{-1} * sum_{i<K} 1[abs(Delta(v,canonicalObserved(v,draw_i),m))
                           >=abs(Delta(v,o,m))]`, with `m=o.a+o.b`.
  Approximate rejection is the Boolean test `real(mean)+epsilon<alpha`.

The theorem conjoins:

1. For every integers `k1,k2,u`, every Boolean-valued integer function `f`,
   then the hypothesis `k1<=k2`, run sentinel search with fuel
   `toNat(k2-k1+1)+1` from `(k1-1,k2+1)`, obtaining `(A,qs)`.
   Every queried `c` with `f(c)=true` satisfies `A<c`.
   If `u<=A`, every queried `c<=u` satisfies `f(c)=false`.
   For every natural `i,j`, if `i<j<length(qs)` and the decision at `qs[i]`
   rejects, then `qs[j]<qs[i]`. No condition at all on decision accuracy,
   monotonicity, randomness or independence is present.
2. For every observation `o`, natural `K`, real `alpha,epsilon`, under the
   hypotheses `0<o.a+o.b=o.c+o.d`, `K>0`, `0<alpha<1`,
   `0<=epsilon<alpha`, and for every pool of the type just defined with
   `n=N(o)` and `m=o.a+o.b`, let `reject` be its approximate-rejection
   function and `s` its instrumented upper run. There exist integers `A,r`,
   chosen after all those inputs, satisfying all of:
   * `s.value=some A`, and `upperRun true` returns `some A` with exactly
     the same complete table-test trace;
   * `Acc(alpha,o)` is nonempty and its real supremum equals `r/N(o)`;
   * for each query record `q`, its rejection Boolean equals negated
     compatibility of the entire scan starting at its recorded index;
   * for every natural `i<length(s.tests)`, `i<L(N(o))` and the recorded
     Boolean equals `reject(recorded_vector,i)`;
   * every rejected outer query `q` satisfies `A/N(o)<q.x/N(o)`;
   * for every natural `i<j<length(s.queries)`, if query `i` rejected,
     query `j` has a strictly smaller integer numerator;
   * if `r/N(o)<=A/N(o)`, every queried effect `q.x/N(o)` at or below
     the exact supremum has rejection Boolean false.

The final implication is necessary, not sufficient. There is no conclusion
that the returned endpoint reaches the exact endpoint, no probability bound,
and no independence hypothesis on the supplied pool. The assertion applies
to every realized pool, so it is meaningful without assigning any pool law.

Junk-value audit: `k2-k1+1` uses integer arithmetic and is positive under
`k1<=k2`, so `Int.toNat` does not truncate. Midpoint division is integer
Euclidean division by positive 2, including negative numerators; there is no
division by zero. The effect search explicitly distinguishes fuel exhaustion
(`none`) from an endpoint (`some A`); the quantified conclusion ensures
termination for its chosen fuel. The simpler sentinel search returns its lower
bound even on exhaustion, but no claim silently treats that case as a proven
compatible endpoint. Natural `log2` is total and here receives `n+1>=1`;
it is not `Real.log`. The pool divisor `L(n)` is positive, and the explicit
index bound in the conclusion ensures no actual table test wraps or repeats
a slot because of the modulo definition.

The mean would be zero at `K=0` by rational division-by-zero conventions,
but the Monte Carlo clause requires `K>0`. Balanced positive arms give
`N(o)>0`, so all effect divisions and exact p-value denominators are positive.
The supremum is of a finite set, hence bounded, and its nonemptiness is an
explicit conclusion; the real empty-set/unbounded `sSup` default (zero) is
not used to manufacture the endpoint. Out-of-range query-list access defaults
to integer zero or record `(0,0,false)`, and table-trace access defaults to
`((0,0,0,0),false)`; every such access in the theorem is guarded by an
in-range bound. Base/reuse subtractions in the special candidate are guarded
by `a,d>=1`. There are no integrals, infinite sums, `toReal` of infinity,
real logs/roots/powers, or unguarded partial functions in this closure.
