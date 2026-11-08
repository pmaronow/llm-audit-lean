# Blind reading

This file was saved before opening either `claims.json` or `record.json`. I read
the five Challenge statements and docstrings, the source of every definition in
their closures, and Lean's `#print` of all 79 distinct closure declarations in
`scratch/Closure.lean` (successful compilation). The generated `_proof_*`
declarations are proofs that displayed numeral types have at least two elements,
or that displayed successor naturals are nonzero. They introduce no mathematical
assumptions. In particular the unusually named T14/T15 auxiliaries in T17's
closure only justify numerals; they do not import those theorems as assumptions.

All coordinates below are indexed from zero. A vector of size n means a function
`Fin n → ℝ`; an assignment means a function `Fin n → Bool`. Write z_i=1 for
`z i = true`, z_i=0 for false; the real-valued indicator is exactly 1 or 0.
Every sum and product below is a Mathlib finite sum or product over the indicated
finite type. The convention for real division is the field convention 1/0=0.

## SAP.P016b.T17

Source: `Challenge/Part1.lean:56–59`, `Defs/Part4.lean:64–72`, with the
Part1 definitions in its closure.

For each Boolean group g, N_g(z)=Σ_i 1{z_i=g},
S_g(v,z)=Σ_i 1{z_i=g}v_i, and M_g(v,z)=S_g(v,z)/N_g(z), where the
natural count is cast to a real number. D(v,z)=M_1(v,z)−M_0(v,z).
Additive adjustment is u_i=Y_i−z_i t.

The first conjunct quantifies, in order, over every natural n, every real
vector Y of size n, and every assignment z. Assuming N_0(z)>0 and N_1(z)>0,
it then quantifies over every real t and sets u_i=Y_i−z_i t. It concludes
all three of the following:

1. For every coordinate i, z_i=1 implies u_i+t=Y_i.
2. M_1((u_i+t)_i,z)−M_0(u,z)=D(u,z)+t.
3. The same left-hand side equals D(Y,z).

These are followed by two unconditional numerical conjuncts. Let
v=(0,1,2,3) and z=(false,false,true,true). Then D(v,z)=2, whereas
M_1((v_i+10)_i,z)−M_0(v,z)=12. The helper `complete4` is the explicit
six-element array of assignments with treated sets {0,1}, {0,2}, {0,3},
{1,2}, {1,3}, {2,3}, in that order; only its last entry is used here.
The numerical vector `u4` is exactly v, with no statistical assumptions.

The docstring describes the comparison of two adjusted group means as the
corrected reading, and the imputed treated comparison as a conditional reading
giving the raw contrast. The formal assertions above are identities and a
specific distinguishing example; they do not quantify over all possible
statistics or define a general imputation model.

Junk-value check: M_g is defined as zero on an empty group because the sum and
denominator are both zero. Both groups are explicitly nonempty in the universal
clause, and have size two in the example, so this convention has no effect.
The n=0 domain is excluded by these hypotheses. The casts of counts are exact.
`Fin` vector indexing is total and bounded, including the index 5 of `Fin 6`.
There are no integrals, extrema, logs, roots, real powers, limiting operations,
or partial functions here.

## SAP.P016b.T18

Source: `Challenge/Part1.lean:61–65`, `Defs/Part5.lean:10–33`, and Part1.

The assignment has controls at coordinates 0 through 127 and treated units at
128 through 255. The real outcome vector y is

- 9 at 0–63; 11 at 64–127;
- 8 at 128; 9 at 129–191; 11 at 192–254; 12 at 255.

Set t=34/99, a=413/396. Additive generation is A_i=y_i+z_i t;
multiplicative generation is G_i=y_i(1+z_i(a−1)). Their discrepancy is
d_i=|G_i−A_i|, with ordinary real absolute value. Additive adjustment is
y_i−z_i t; multiplicative adjustment is y_i/(1+z_i(a−1)), so it divides
treated values by a and leaves controls unchanged.

For a vector of length 2m, `evenMedian` takes the list of its coordinates,
sorts it in nondecreasing real order with `mergeSort`, and averages the entries
at zero-based positions m−1 and m. These entries use `List.getD` with default
zero. Here m=128. Let M_g be the finite group mean described in T17, and let
bar(y)=(Σ_i y_i)/256. The total sum of squares is
TSS(y)=Σ_i(y_i−bar(y))².

`CalibrationWitness` is a conjunction of assertions, not a hypothesis placed
on an arbitrary witness. It asserts exactly:

1. Both group sizes are 128 and both group means are 10.
2. TSS(y)/256=131/128 and a=1+t/8.
3. For every coordinate i, d_i is 0 if i<129, t/8 if 129≤i<192,
   3t/8 if 192≤i<255, and t/2 otherwise.
4. Exactly 127 treated coordinates have nonzero discrepancy.
5. The average of the two central sorted discrepancies is zero.
6. M_1(G,z)−10=85/198; M_1(A,z)−10=t; and 85/198=(5/4)t.
7. 10−M_1((y_i/(1+z_i(a−1)))_i,z)=170/413;
   10−M_1((y_i−z_i t)_i,z)=t;
   (170/413)/t=495/413, and 1<495/413.

T18 asserts this entire conjunction and then, universally for every real a',
that the median of the discrepancies for this same y,z,t and a' is nonnegative.
Consequently the displayed a attains the global minimum zero of that objective.
There are no input hypotheses and no existentially unspecified data.

Junk-value check: both means divide by 128; the pooled mean divides by 256;
the inverse treated adjustment divides by the nonzero rational 413/396;
the displayed ratio divides by t=34/99≠0. All other numerical denominators
are positive. The sorted list has length 256, so positions 127 and 128 exist:
neither the `getD` default nor natural subtraction truncation is used. The
universal a' may be zero, but it occurs only in generation and discrepancy,
which contain no division by a'. The sample is nonempty. No other junk-value
operations occur.

## SAP.P016b.T19

Source: `Challenge/Part1.lean:67–80`, `Defs/Part5.lean:35–66`, and the
Part1/Part2 definitions in its closure.

Use the genuine finite vectors, group counts/means, pooled mean, additive and
multiplicative generators/adjusters, and sorted even median defined explicitly
above. For general n, bar(y)=Σ_i y_i/n and
d_i(y,z,t,a)=|y_i(1+z_i(a−1))−(y_i+z_i t)|.
`Balanced(n,m)` is the subtype of all Boolean assignments of n units whose
number of treated units equals m. `uniformExpectation Ω f` is
(Σ_{ω∈Ω} f(ω))/card(Ω), using the Fintype of this actual subtype.

The statement is the conjunction of the following universal and concrete
clauses, with separate binders in each numbered clause:

1. For every natural m, assuming m>0, for every vector y of length 2m and
   assignment z, assuming Σ_i z_i=m, for all real t,a and coordinates i,
   d_i=|(a−1)y_i−t| on treated units and d_i=0 on controls.
2. In that same universally quantified domain (m, then y,z, then the count
   equality, then t,a), the median of d equals
   (1/2) inf { |(a−1)y_i−t| : i is treated }.
3. For every m>0, every such y,z with m treated units, every real t and
   coordinate j, if j is treated and y_j≠0, set a_j=1+t/y_j. Then
   d_j(y,z,t,a_j)=0, the median is zero, the median is nonnegative at
   every real a, and for every treated i,
   d_i(y,z,t,a_j)=|t| |y_i/y_j−1|. Also, if t≠0 and y_i≠y_j,
   that discrepancy is nonzero. There is no condition a_j≠0 here.
4. For every natural n, vector Y, and assignment z, if its treated group
   is nonempty, then for every real t,a with a≠0, the treated mean reductions
   under additive and multiplicative inverse adjustment are respectively t and
   (1−1/a)M_1(Y,z).
5. For every m>0, every vector y of length 2m, and every real t,a with a≠0,
   uniform expectation over all m-of-2m assignments gives expected treated
   mean bar(y), expected additive reduction t, and expected multiplicative
   reduction (1−1/a)bar(y).
6. For every real μ,t,a, if μ≠0, μ≠t, and a≠0, then
   (1−1/a)μ=t if and only if a=μ/(μ−t).
7. Every coordinate and numerical assertion of `CalibrationWitness` is
   asserted again, for exactly the 256-unit y,z,t,a specified in the T18
   section (including counts, means, variance, discrepancies, median, generated
   shifts and adjusted shifts). In addition,
   10/(10−34/99)=495/478, 413/396≠495/478,
   10(1−1/(413/396))=170/413, and 170/413≠34/99.

The docstring explicitly presents a restriction to mathematical clauses and
omits empirical power comparisons and properties of the actual simulation
dataset. It describes the 256-unit data as constructed. It also identifies
positive m and a≠0 as domains for medians and inverse adjustments.

Junk-value check: the general median uses m−1 in natural subtraction and
default zero for missing entries. Since m>0 and the list has length 2m,
both central entries exist and no truncation or fallback changes the value.
The set in the real `sInf` is finite and nonempty (m treated units with m>0)
and bounded below by zero. Thus `sInf` is a genuine attained minimum, not
the conditional-completeness default for empty or unbounded sets. The root
divisions use the explicit y_j≠0. Inverse adjustment uses a≠0. The treated
mean is used only when the treated count is positive; balanced instances have
both groups of size m. `Balanced(2m,m)` is nonempty, for example by treating
the first m indices, so `uniformExpectation` has positive cardinality.
Pooled means divide by 2m>0. Clause 6's μ≠t excludes its denominator zero.
All special-witness divisions are the nonzero rationals detailed for T18.
There are no Bochner-integral or other analytic defaults.

## SAP.P016b.T20

Source: `Challenge/Part1.lean:82–86`, `Defs/Part6.lean:10–27`, and Part1.

The first conjunct quantifies over real y0,y1,Y,τ and then Boolean z.
Assuming Y=z*y1+(1−z)*y0 and y1=y0+τ (with Boolean z replaced by its real
indicator), it concludes y0=Y−z*τ.

The second conjunct quantifies over every natural n, real vector y, Boolean
assignment z, and real t,t0. Coordinatewise subtracting z_i t0 from
y_i+z_i t produces y_i+z_i(t−t0); subtracting z_i t produces y itself.

For the network conjunct, quantify over n, a real matrix S indexed by
`Fin n × Fin n`, assume every S_ij≥0, then quantify over real β,τ and
assume β>0. No symmetry, zero diagonal, binary adjacency, sign of τ, or
sign of outcomes is assumed here. For assignment v define
h_i(v)=Σ_j v_j S_ji and
k_i(v)=β+(1−v_i)(1−β) exp(−τ² h_i(v)).
The mapping applied to outcome vector y from z to w is the coordinate vector
H(y,z,w)_i=[k_i(w)/k_i(z)] y_i.
Under the preceding universally quantified network assumptions it concludes:

1. For every assignment v and coordinate i, k_i(v)>0.
2. For every vector y and assignment z, k_i(0)=1 for every i, and
   H(y,z,0)_i=y_i/k_i(z), where 0 is the all-false assignment.
3. For every vector y and assignments z,w,w', H(y,z,z)=y and
   H(H(y,z,w),w,w')=H(y,z,w').
4. For every vector y0 and function y assigning an outcome vector to each
   assignment, if for every assignment z and coordinate i,
   y(z)_i=k_i(z)y0_i, then for every z the vector
   (y(z)_i/k_i(z))_i equals y0.

Junk-value check: `modelMap` is total even at zero denominators in isolation,
but the statement's β>0 and S≥0 ensure every k_i(v)>0, so none occurs in
its mapping or recovery claims. Indeed exp(−τ²h) is positive and at most one;
on a control k is a convex combination of 1 and β, and on a treated unit it
is β. The exponential has its ordinary real domain. n=0 is permitted and
gives the genuine empty-vector identities, without erasing any positive-n
instances of the universal assertions. There are no means, integrals,
conditional extrema, truncated subtraction, or other partial operations.

## SAP.P016b.T21

Source: `Challenge/Part1.lean:88–92`, `Defs/Part6.lean:29–45`, and the
Part1/Part2 definitions in its closure.

Let Ω be the finite subtype of assignments of 256 units with exactly 128
treated units. Quantify first over a finite law P on Ω: this structure contains
real weights w_z≥0 and the equation Σ_z w_z=1. Assume further, for every
z∈Ω, that w_z=1/(256 choose 128), using the exact natural binomial coefficient
cast to the reals. Next quantify over a real 256×256 matrix S, assume
S_ij=S_ji for every i,j, then assume each entry is 0 or 1. Next quantify
over every real vector y0 of size 256 and every real statistic T whose arguments
are an outcome vector of size 256 and an assignment of size 256.

At fixed β=2 and τ=1/2 define
k_i(z)=2−(1−z_i)exp(−(1/2)² Σ_j z_j S_ji),
Y(z)_i=k_i(z)y0_i, u(z)_i=Y(z)_i/k_i(z), and s(z)=T(u(z),z).
Then the full conclusion is a conjunction:

1. For every z∈Ω, u(z)=y0.
2. Define U(z)=Σ_w 1{s(z)≤s(w)}w_w,
   L(z)=Σ_w 1{s(w)≤s(z)}w_w, and
   D(z)=min(1,2 min(L(z),U(z))). For each function p in the finite set
   {U,L,D}, both Σ_z 1{p(z)≤1/20}w_z≤1/20 and
   Σ_z 1{p(z)<1/20}w_z≤1/20.
3. For a vector of draws d:Fin 1001→Ω, define obs=s(d_0) and references
   r_b=s(d_{b+1}) for b:Fin 1000. Let C_L=Σ_b 1{r_b≤obs} and
   C_U=Σ_b 1{obs≤r_b}; let p_raw=min(1,2 min(C_L/1000,C_U/1000)).
   Then Σ_d 1{p_raw<1/20} Π_i w_{d_i}≤50/1001, and
   50/1001<1/20.
4. Repeat clause 3 with 10001 total draws and 10000 references: the bound
   is 500/10001, with 500/10001<1/20.

Thus the observer and all references are sampled jointly with the full product
weight; repeating a single dependent draw is not substituted for iid sampling.
All comparisons in the exact tails and counts include ties. The two Monte Carlo
rejection rules use strict `<1/20`. All quantities are finite sums; there are no
unstated Bochner-integrability hypotheses.

Junk-value check: Ω is nonempty (treat the first 128 indices) and its cardinality
is the positive binomial coefficient (256 choose 128), so the uniform-law
premise is compatible with normalization and does not divide by zero.
The binary nonnegative matrix and β=2 make 1≤k_i(z)≤2, excluding zero
adjustment denominators. Reference counts divide by 1000 and 10000; no B=0
instance is asserted. Real casts of naturals and binomial coefficients are
exact, without overflow. `Fin.succ` stays inside the draw index type; no missing
entry default is used. Product mass is a genuine finite product law on a
nonempty finite type. The finite set of tail functions can merge equal
functions, which does not remove any of the three stated properties. There
are no real-log, square-root, rpow, extended-real, infimum, supremum, or limit
conventions in this closure.
