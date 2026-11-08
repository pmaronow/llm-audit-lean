# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. The sources and every entry of `closure.json` were read.
The 46 generated recursors, matchers, and auxiliary proofs were also printed and
read in `scratch/ClosurePrint.log`. They implement structure/list/option/natural
number elimination, decidable equality, and concrete numeral/cardinality facts;
they add no mathematical hypotheses. This reading uses mathematical abbreviations
defined below, not unexplained SAP notions.

## Common unfolded finite mathematics

A count vector is an arbitrary quadruple (v=(a,b,c,d)\in\mathbb N^4).
Write (n(v)=a+b+c+d), (e(v)=(b:\mathbb Z)-c),

\[
 t(v)=e(v)/n(v),\qquad h(o)=o_a/(o_a+o_b)-o_c/(o_c+o_d).
\]

These quotients are initially rational; the real versions are exact embeddings
into the reals. A potential table interprets the four cells as (11,10,01,00),
with treatment outcome first. An observed table interprets them as
(treated success, treated failure, control success, control failure).

For (m\in\mathbb N), (S(v,m)) is the list obtained by taking

* (q_a=0,\ldots,\min(a,m));
* (q_b=0,\ldots,\min(b,m-q_a));
* (q_c=0,\ldots,\min(c,m-q_a-q_b));
* (q_d=m-q_a-q_b-q_c), retaining the result when (q_d\le d).

All subtractions in this enumeration are natural-number truncated subtraction.
The nested bounds make them ordinary subtraction on retained states. Each state
occurs once, is componentwise at most (v), and sums to (m). Define

\[
 W_v(q)=\binom a{q_a}\binom b{q_b}\binom c{q_c}\binom d{q_d},\quad
 O_v(q)=(q_a+q_b,q_c+q_d,a-q_a+c-q_c,b-q_b+d-q_d).
\]

The latter subtractions are evaluated left to right in the naturals. On these
states there is no truncation loss. The computational binomial is
`Nat.fast_choose`. Probability of a predicate (E) on count states is

\[
 P_{v,m}(E)=\frac{\sum_{q\in S(v,m)}1_{E(q)}W_v(q)}{\binom{n(v)}m}.
\]

For any (v,o), put (m=o_a+o_b) and define the integer

\[
 B(v,o,m)=n(v)((n(v)-m)o_a-mo_c)-m(n(v)-m)e(v).
\]

Here all subtraction is in the integers. Let (H(v,o)) be the sum of (W_v(q))
over (q\in S(v,m)) with

\[
 |B(v,O_v(q),m)|\ge |B(v,o,m)|.
\]

Absolute value in the source is integer `natAbs`. The rational p-value is

\[
 p(v,o)=H(v,o)/\binom{n(v)}m.
\]

For valid experiments this is the two-sided randomization tail for

\[
 |h(O_v(q))-t(v)|\ge |h(o)-t(v)|
\]

because the cleared denominator (n(v)m(n(v)-m)) is positive.

The list (V(o)) enumerates, for (0\le i\le o_a,
0\le j\le o_b,0\le k\le o_c,0\le l\le o_d),

\[
 (i+k,\ o_a-i+l,\ o_c-k+j,\ o_b+o_d-j-l).
\]

Membership is the definition of a possible potential-outcome count vector.
Every such vector has size (n(o)). For real (\alpha), define the finite set

\[
 A_\alpha(o)=\{t(v):v\in V(o),\ \alpha\le p(v,o)\}.
\]

The real exact interval is the set

\[
 I_\alpha(o)=\{x:\exists l,u\in A_\alpha(o),\ l\le x\le u\}.
\]

Its endpoint functions are (L_\alpha(o)=\inf A_\alpha(o)) and

\(U_\alpha(o)=\sup A_\alpha(o)\), using real `sInf` and `sSup`.
For rational levels, the Boolean acceptance test cross-multiplies the normalized
rational numerator and positive denominator of (\alpha) against (H(v,o))
and the binomial denominator. If that binomial is zero it returns
`decide (α ≤ 0)`. The rational interval algorithm deduplicates (V(o)), keeps
accepted vectors, and takes the minimum and maximum integer effect divided by

\(n(o)\). It returns `none` for an empty accepted list, and `some (l,u)` otherwise.

A missing mask is (r\in\mathbb N^4) with each (r_i\le o_i); all such masks
are enumerated once. The favorable and unfavorable completed observed tables are

\[
 o^+=(o_a+r_b,o_b-r_b,o_c-r_c,o_d+r_c),\quad
 o^-=(o_a-r_a,o_b+r_a,o_c+r_d,o_d-r_d).
\]

All these subtractions are natural. Let (C(o,r)) enumerate, for

\(0\le s\le r_a+r_b\), (0\le u\le r_c+r_d\), the count vectors

\[
 (o_a-r_a+s,\ o_b-r_b+(r_a+r_b-s),
   o_c-r_c+u,\ o_d-r_d+(r_c+r_d-u)).
\]

Define the imputation interval (J_\alpha(o,r)=[\ell,u]) by

\[
 \ell=\begin{cases}\min(L_\alpha(o^-),h(o^-))&A_\alpha(o^-)\ne\varnothing\\
 h(o^-)&\text{otherwise},\end{cases}\quad
 u=\begin{cases}\max(U_\alpha(o^+),h(o^+))&A_\alpha(o^+)\ne\varnothing\\
 h(o^+)&\text{otherwise}.\end{cases}
\]

Its rational version makes the identical choice by matching the optional
rational intervals. Define the completion union and its closed hull by

\[
 C_\alpha(o,r)=\bigcup_{c\in C(o,r)} I_\alpha(c),\quad
 K_\alpha(o,r)=\{x:\exists l,u\in C_\alpha(o,r),\ l\le x\le u\}.
\]

The rational hull algorithm discards `none` intervals, returns `none` if no
interval remains, and otherwise folds minima of lower and maxima of upper
endpoints.

A missingness law is an arbitrary function

\(\mu:\mathbb N^4\to\mathbb N^4\to\mathbb R\) satisfying, for every

\(q\in S(v,m)\), nonnegativity on every admissible mask and

\[
 \sum_{r\le O_v(q)}\mu(q,r)=W_v(q)/\binom{n(v)}m.
\]

Its event probability is the finite double sum

\(\sum_{q\in S(v,m)}\sum_{r\le O_v(q)}1_{E(q,r)}\mu(q,r)\).
Values of (\mu) outside these finite supports are unused, even if negative.

For labeled data, a table on (n) units is a function

\(w:\{0,\ldots,n-1\}\to\{0,1\}^2\). Its count vector counts the four
ordered pairs. Its effect is (n^{-1}\sum_i(w_i(1)-w_i(0))\).
A treatment assignment is a finite subset (z\subseteq\{0,\ldots,n-1\})
with cardinality (m). Uniform event probability on a finite type is
the cardinality of the event divided by the cardinality of the type. The
canonical table assigns the first (a) units (1,1), next (b) (1,0), next

\(c\) (0,1), and all remaining units (0,0).
The canonical observed vector counts its observed bits according to membership
in (z). Treated type counts count the four types within (z).

The observed outcome function is (y_i=w_i(1)) on (z) and (w_i(0))
outside (z). A labeled table is possible for ((y,z)) exactly when this
function equals (y). Write

\[
 h_z(y)=\frac{\sum_{i\in z}y_i}{|z|}-\frac{\sum_{i\notin z}y_i}{n-|z|},\quad
 T_w(z)=\frac{\sum_{i\in z}w_i(1)}{|z|}-\frac{\sum_{i\notin z}w_i(0)}{n-|z|}.
\]

The labeled p-value (p_z(w,y)) is uniform probability over assignments (q)
of size (|z|) of (|T_w(q)-t(w)|\ge|h_z(y)-t(w)|).
The labeled observed count vector counts success/failure inside/outside (z).
For a missing set (r), (y^+_i=1_{i\in z}) on (r), and (y^+_i=y_i)
off (r). The coupled table replaces only each unit's outcome observed under

\(z\) by (y^+_i), preserving its unobserved potential outcome.

Common conventions: division in the rationals/reals is total, with division by
zero equal to zero. `Nat` subtraction truncates at zero; integer subtraction does
not. Finite lists retain multiplicities unless explicitly deduplicated; image
sets do not. Natural and integer casts are their exact embeddings; the effect
difference is cast to integers before subtraction. An existential hull is empty
when the underlying set is empty. Real `sInf ∅` and `sSup ∅` are zero, and these
endpoint functions are used under nonemptiness guards or established acceptance.
All sets of effects here are finite, hence bounded. There are no Bochner
integrals, infinite sums, extended-real conversions, square roots, real powers,
limsup/liminf, or default extraction of options in these five closures.

## SAP.P003a.T29

For every count vector (v\in\mathbb N^4), then every (m\in\mathbb N),
then every (\alpha\in\mathbb R), if (0<m<n(v)) and

\(0<\alpha<1\),

\[
 \frac{\sum_{q\in S(v,m)}W_v(q)1_{\{t(v)\in I_\alpha(O_v(q))\}}}
 {\binom{n(v)}m}\ \ge\ 1-\alpha.
\]

All symbols are unfolded in the common mathematics above. The conclusion is
coverage of the closed hull of accepted possible effects, rather than an
assertion that the accepted effect set has no gaps. Its docstring says exact
finite randomization inversion covers at least (1-\alpha).

The positive-arm hypothesis ensures positive population, treatment and control
denominators, and a positive assignment-space cardinality. Every observed table
and possible table used has that size and those arm sizes. Neither division by
zero nor invalid-state truncation affects the statement. Empty accepted sets
mean an empty interval on that observation, which is counted as noncoverage;
they do not turn into an artificial interval at zero. There is no use of an
unguarded endpoint in this closure.

## SAP.P003a.T1

This is a closed conjunction of concrete equalities, inequalities, finite
universal assertions, and embedded existence statements. It has no outer
hypotheses. Its docstring calls it a refutation of the printed missing-data
claim. Set (v=(11,0,3,6)), (m=3), (\alpha=109/500), (t=-3/20),
and define (r(q)=(0,0,1,0)) exactly at (q=(0,0,3,0)), zero otherwise.
It asserts:

* (n(v)=20), (\binom{20}3=1140), (0<3<20), (0<\alpha<1),
  and (t(v)=-3/20).
* The rational intervals of ((0,3,11,6)) and ((0,3,10,7)) are respectively
  ([-7/10,-3/20]) and ([-13/20,-1/5]); their missing-data interval for
  mask ((0,0,1,0)) is ([-7/10,-1/5]).
* The weighted rational coverage
  (\sum_{q\in S(v,3)}W_v(q)1_{\{t(v)\in J_\alpha(O_v(q),r(q))\}}/1140)
  is (297/380<1-\alpha); the state weights sum to 1140. For every count
  vector (q), even outside the randomization support, the chosen mask is
  admissible for (O_v(q)).
* Both (p(v,(0,3,11,6))) and (p(v,(0,3,10,7))) equal
  (83/380>\alpha). The true population is possible for the former observation
  and impossible for the latter. Their observed estimates are (-11/17) and
  (-10/17).

The labeled realization is fixed: units 0 through 10 have pair (1,1), 11 through
13 have pair (0,1), and 14 through 19 have pair (0,0). The distinguished
assignment is (z_*={11,12,13}). The missing set is ({0}) on this assignment
and empty on every other assignment. (M_i=-1) on the missing set, otherwise it
equals the observed bit. A binary completion of (M) is any Boolean function
agreeing with every non-(-1) entry. Its completion union is the union of

\(I_\alpha\) of the observed count tables of all these functions.
The unfavorable labeled completion sets a missing treated outcome to zero and
a missing control outcome to one. The favorable completion does the reverse.

Further conjuncts assert:

* This table has count vector (v), effect (-3/20), and 1140 assignments.
  For every size-three assignment, its outcomes have the canonical observed
  counts, the potential pairs equal the canonical pairs at every unit, its
  missing set is ({0}) iff the assignment is (z_*) and empty iff it is not,
  and its true outcomes complete (M).
* At (z_*), unit 0 is a control success with (M_0=-1), the observation is
  ((0,3,11,6)), unfavorable imputation changes no outcomes, and favorable
  imputation has counts ((0,3,10,7)).
* For every predicate (E) on count vectors, uniform labeled probability of
  (E) on the canonical observed vector equals (P_{v,3}(E\circ O_v)).
  For every size-three assignment, each of the four missing-cell counts equals
  the corresponding component of (r(q)), where (q) is its treated type
  count vector.
* The real exact intervals, their nonemptiness, and the real imputation interval
  equal the rational intervals above. The true effect lies in the complete
  interval and the labeled completion union at (z_*), but outside the
  imputation interval. The complete interval is contained in that union.
  The larger of the favorable endpoint and favorable estimate is below the true
  effect. The two uniform labeled tails using the true population and the
  original or favorable observed estimate both equal (83/380).
* For every (u\in V((0,3,10,7))) with (t(u)\ge-3/20),
  (p(u,(0,3,10,7))\le248/1140), with equality exactly for
  ((8,0,3,9)) or ((9,0,3,8)). Both vectors are possible, have effect
  (-3/20), attain the bound, and (248/1140<109/500).

The ten distinct complete-data rows, with (multiplicity, lower endpoint, upper
endpoint, true-effect coverage bit), are:

| Observation | Weight | Lower | Upper | Covers |
|---|---:|---:|---:|---|
| (0,3,11,6) | 1 | -7/10 | -3/20 | true |
| (0,3,12,5) | 18 | -3/4 | -3/10 | false |
| (0,3,13,4) | 45 | -4/5 | -7/20 | false |
| (0,3,14,3) | 20 | -17/20 | -2/5 | false |
| (1,2,11,6) | 33 | -11/20 | 1/20 | true |
| (1,2,12,5) | 198 | -3/5 | 0 | true |
| (1,2,13,4) | 165 | -13/20 | -1/20 | true |
| (2,1,11,6) | 165 | -7/20 | 1/4 | true |
| (2,1,12,5) | 330 | -2/5 | 1/5 | true |
| (3,0,11,6) | 165 | -1/10 | 2/5 | false |

For every assignment there exists a row with its observed vector. For every row
the labeled cardinality equals the weight, the rational and real intervals
equal its endpoints, the observed estimate belongs to the interval, and true
effect membership is equivalent to its bit. Exactly 1139 assignments have no
missing values. On every assignment other than (z_*), the zero-mask imputation
interval equals the complete interval. The uniform complete coverage is

\(892/1140\), the imputation coverage is (297/380=891/1140\), the five
remaining covering weights sum to 891, (249/1140=83/380\), and

\((1-109/500)-297/380=1/2375\).

Junk conventions: every numeric denominator is positive, the assignment spaces
are inhabited, and both critical accepted sets are expressly nonempty. The
diagnostic rows supply real intervals, avoiding any reliance on optional endpoint
defaults. Every mask used in coverage is valid, so completion subtraction is
ordinary. The canonical pair's final (0,0) branch is intentional and within a
20-unit table of size 20. The sentinel (-1) is an explicit missing-value code,
not an implicit default. Quantification over predicates is on a finite type and
has no measurability issue. No actual restriction on missingness independence is
present in the theorem.

## SAP.P003a.T2

This conjunction has three independently quantified clauses:

1. For every (v\in\mathbb N^4), (m\in\mathbb N), real
   (\alpha\), with (m>0), (n(v)=2m), (0<\alpha<1), and every
   function (\mu) satisfying the finite missingness-law conditions above,
   the double-sum probability of (t(v)\in J_\alpha(O_v(q),r)) is at least
   (1-\alpha).
2. For every observed vector (o), mask (r), and real (\alpha), with
   (0<\alpha<1), (0<o_a+o_b=o_c+o_d), and (r\le o),
   (C_\alpha(o,r)\subseteq J_\alpha(o,r)).
3. For each natural (n), then (m>0) with (n=2m), Boolean outcome
   functions (y,y'), finite subsets (z,r\subseteq\{0,\ldots,n-1\})
   with (|z|=m), agreement (y'_i=y_i) off (r), any labeled table
   (w) possible for ((y',z)), real (0<\alpha<1), acceptance
   (\alpha\le p_z(w,y')), and strict inequality (h_z(y^+)<t(w)), set
   (D=\{i:y'_i\ne y^+_i\}), (d=|D|), and form the coupled table
   (w^+). Then:
   * (w^+) is possible for ((y^+,z));
   * (t(w^+)=t(w)+d/n) and (h_z(y^+)=h_z(y')+2d/n);
   * for every size-(m) assignment (q), with
     (N=|\{i\in D:(i\in q\leftrightarrow i\in z)\}|), (N\le d),
     (T_{w^+}(q)=T_w(q)+2N/n), and the change in centered estimator has
     absolute value at most (d/n);
   * (|h_z(y^+)-t(w^+)|=|h_z(y')-t(w)|-d/n);
   * (p_z(w,y')\le p_z(w^+,y^+)\), so the new p-value is at least
     (\alpha); and (U_\alpha(o(y^+,z))\ge t(w^+)\ge t(w)).

The docstring describes balanced designs, arbitrary dependent missingness,
completion inclusion and coverage, and the possibility-preserving plus coupling.
These are universal statements, not assumptions that the conclusions hold.

Junk conventions: positive balanced arms force (n>0), (m>0), (n-m>0),
positive binomial denominators and inhabited assignment spaces. All count masks
are valid. The upper endpoint in clause 3 is unguarded syntactically but the
accepted, possible coupled table ensures its accepted set is nonempty. The
endpoint guards in (J) handle empty sets without using `sInf ∅` or `sSup ∅`.
The difference of absolute deviations in clause 3 is a real difference, not
truncated subtraction; its nonnegativity follows from the strict estimate
hypothesis. There is no requirement that the missing set be independent of the
assignment, or that (d>0); nonempty-change instances must be checked separately.

## SAP.P003a.T3

The conjunction consists of the following separately quantified assertions:

1. For every (v,m,\alpha), with (0<m<n(v)), (0<\alpha<1), and
   every finite joint law (\mu) as above, both the probability that
   (t(v)\in C_\alpha(O_v(q),r)) and the probability that
   (t(v)\in K_\alpha(O_v(q),r)) are at least (1-\alpha).
2. For every real (\alpha), observed table (o) with both arms positive,
   and valid mask (r\le o), (I_\alpha(o)\subseteq C_\alpha(o,r)).
   This clause places no bounds on (\alpha).
3. With the same separately quantified conditions,
   (C_\alpha(o,r)\subseteq K_\alpha(o,r)).
4. For every (o,r) with (r\le o), including tables with empty arms,
   (o\in C(o,r)), the list (C(o,r)) has no duplicates, and its length is
   ((r_a+r_b+1)(r_c+r_d+1)).
5. For every (v,m,\alpha) with positive arms and interior level, the
   complete-data coverage inequality of T29 holds.
6. For the fixed twenty-unit example and level above, the rational completion
   hull at the critical observation is ([-7/10,-3/20]), its rational
   weighted coverage is (892/1140), and it is at least (391/500).

The completion enumeration is over distinct observed count tables. The theorem
does not assert that this count is the number of labeled Boolean completions.
The docstring describes arbitrary allocation, both joint-law coverages, the
finite completion count, and the numerical repair.

Junk conventions: valid masks prevent truncation in all completion formulas.
The probability clauses exclude zero arms; clause 4 uses only finite
combinatorics and needs no denominators. Clauses 2 and 3 allow empty accepted
sets, with empty existential hulls, so extreme levels cause no artificial
coverage. Optional rational hulls explicitly represent emptiness. There are no
empty or unbounded infima/suprema in this closure.

## SAP.P003a.T4

This is another closed counterexample conjunction, not a universal correctness
statement. Its docstring calls the literal search false and gives both abstract
threshold and balanced-experiment witnesses.

Unfolding the search: a Boolean predicate (f:\mathbb Z\to\{\mathrm{false},
\mathrm{true}\}) means rejection when true. Given integer bounds (a,b),
query (c=(a+b)/2) using integer Euclidean division (floor division for the
positive divisor 2); change the bracket to ((a,c)) on rejection or ((c,b))
on acceptance. Only after this update, if (b=a+1), return: (a) if

\(a>k_1\) and (b<k_2\); otherwise if (a=k_1), query (k_1) and return

\(k_1-1\) on rejection, (k_1\) on acceptance; otherwise if (b=k_2), query

\(k_2) and return (k_2-1\) on rejection, (k_2\) on acceptance. The
lower-bound branch has priority if both equalities hold. Otherwise recurse.
Fuel zero returns `none`; a positive fuel permits one update and its boundary
query. The instrumented version also returns the chronological integer query
list and final bracket, and at zero fuel returns the current bracket with an
empty query list.

The ordered compatibility test at effect numerator (x) is defined explicitly:
for each (j=0,\ldots,n(o)), retain possible tables with integer effect (x)
and (v_a+v_b=j), take one with minimal (v_b) (earlier table on a tie), and
skip empty groups. Append that table; if its (v_b=v_c=0), (v_a,v_d\ge1)
and ((v_a-1,1,1,v_d-1)) is possible, append that second table too.
Scan the resulting list from chronological index `idx`, querying the Boolean
table-rejection function. Stop on the first nonrejection and return compatible;
an exhausted list is incompatible. Return the incremented index and full tested
table/Boolean trace.

The table-level upper search replaces (f(x)) by incompatibility of this scan,
using chronological indices. Its upper domain is

\[
 k_1=2(o_a-o_c),\quad k_2=o_a-o_c+(o_a+o_b).
\]

Its uncorrected run uses initial bracket ((k_1,k_2)), fuel (n(o)+3),
and the boundary rule above. The corrected branch uses sentinel bounds

\((k_1-1,k_2+1)\) and returns (a) immediately when (b\le a+1\), but
the statement here evaluates the uncorrected branch. Exact table rejection is
the negation of the rational acceptance test, ignoring the chronological index.

The asserted facts are:

* (0<1<2). On integer (1\le x\le2), the constantly accepting predicate
  accepts exactly (x\le2); the constantly rejecting predicate accepts exactly
  (x\le0). The accepting search with one fuel returns 1, not 2. One rejecting
  step sends ((1,2)) to ((1,1)). For every natural fuel, the rejecting
  search starting from ((1,1)) or ((1,2)) returns `none`.
* The instrumented accepting run with one fuel returns
  `(some 1, [1,1], (1,2))`. For every natural fuel (F), the rejecting run
  with (F+1) fuel returns `none`, a list of (F+1) copies of query 1, and
  final bracket ((1,1)). With
  (log_2 x=\mathrm{Real.log}(x)/\mathrm{Real.log}(2)),
  (lfloor\log_2 2+2\rfloor=3).
* For (o=(7,1,0,8)), its size is 16, both arms are 8,
  (h(o)=7/8), the full possible effect-numerator lattice is
  ([-1,0,1,\ldots,15]), and its upper search bounds are ((14,15))
  with (0<14<15). There are 144 distinct possible vectors and 12870
  size-eight labeled assignments. Both ((0,14,0,2)) and ((0,15,0,1))
  are possible, have p-value 1, and effects (14/16,15/16). The first
  nonempty line groups are respectively (j=14,15), selecting these vectors;
  all groups at smaller natural (j) are empty. They are the heads of the
  respective compatibility lists, and both compatibility scans accept.
* At level (1/20), both rational and real exact intervals of this observation
  are ([1/2,15/16]), with upper endpoint (15/16). The uncorrected upper
  run returns numerator 14. The one-step instrumented integer version using
  the exact compatibility predicate returns
  `(some 14, [14,14], (14,15))`; (14/16\ne15/16).
* The canonical labeled sixteen-unit table for ((0,15,0,1)) has that count
  vector and effect (15/16). Every size-eight assignment has estimator
  (7/8) or 1, each at exactly 6435 assignments. Both centered absolute
  deviations and the observed deviation are (1/16).
* For every member of the fixed three-element list
  (((0,8,1,7),(-2,7)), ((0,8,0,8),(0,8)),
  ((8,0,0,8),(16,16))), the observation has size 16 and balanced arms,
  its upper bounds equal the supplied pair, and that pair does not satisfy
  (0<k_1<k_2).

Junk conventions: the recursion uses an explicit fuel exhaustion value `none`;
the universally quantified failure at every fuel is stronger than failure at
one arbitrary fuel. No `get!` or default list index is used. Integer division
is by the nonzero number 2. All logarithm inputs actually evaluated in this
statement are 2, so Mathlib's total logarithm convention at zero/negative
arguments cannot affect it; the base logarithm is nonzero. The floor is real
floor to an integer. Candidate population, arm and probability denominators are
positive; all concrete accepted intervals are nonempty. The extra candidate's
natural subtractions are guarded by positivity. Canonical pairs are evaluated
only inside the sixteen-unit table with size 16. The low or singleton domains
in the last clause are asserted as domain failures, not fed into a theorem
whose hypotheses require (0<k_1<k_2).
