# Blind reading

Saved at step 1, before opening `claims.json` or `record.json`. Sources read:
`Challenge/Part1.lean`, `Defs/Part1.lean`, `Defs/Part2.lean`,
`Defs/Part3.lean`, `Defs/Part4.lean`, `Defs/WholeW1.lean`, and the two
import aggregators. Every entry of `closure.json` was inspected. All 54 distinct
generated auxiliary declarations and structure constructor/projection entries
were additionally printed and read in `scratch/ClosurePrint.out`.

The following mathematical notation is expanded explicitly and is shared between
sections; it does not add hypotheses to any theorem.

* A sample of size n is a function y : {0,...,n-1} → R. An assignment is a
  function z on the same set with Boolean values, true meaning treated.
  Write n_g = sum_i 1[z_i=g], S_g(y,z) = sum_i 1[z_i=g] y_i, and
  m_g(y,z) = S_g(y,z)/n_g. Thus these are counts, sums and group means.
* F_g(y,z;x) = sum_i 1[z_i=g and y_i≤x]/n_g. The sample ECDF is
  F(y;x) = sum_i 1[y_i≤x]/n. D(y,z) = m_true(y,z)-m_false(y,z).
* K(y,z) = max({0} union {|F_true(y,z;y_i)-F_false(y,z;y_i)| : i<n}).
  K_signed(y,z) = max({0} union {F_true(y,z;y_i)-F_false(y,z;y_i) : i<n}).
  These are literal finite maxima implemented by a list fold with initial 0.
* A finite law on a finite type Omega consists of real weights w_o≥0 with
  sum_o w_o=1. Probability of an event E means sum_o 1[E(o)]w_o. The
  constructor requires exactly these data; its weight projection returns w.
  For a real score s, U(o)=sum_v 1[s(o)≤s(v)]w_v and
  L(o)=sum_v 1[s(v)≤s(o)]w_v. The doubled tail function is
  Q(l,u)=min(1,2 min(l,u)). A uniform law has weights 1/|Omega|.
* Given B reference scores r_b and observed score o, let
  L_B(r,o)=sum_{b<B} 1[r_b≤o] and U_B(r,o)=sum_{b<B} 1[o≤r_b],
  both natural numbers. The raw p value is
  Q(L_B(r,o)/B,U_B(r,o)/B), with counts and B cast to R before division.
* A reference vector t is a function {0,...,B}→R, with observation t_0
  and references t_{b+1}. Exchangeability of a Borel measure mu on this
  Euclidean space means that for every permutation pi of {0,...,B},
  the pushforward of mu under t↦(t_{pi(i)})_i is mu. Probabilities written
  mu.real(E) are (mu(E)).toReal. All measures appearing in probabilistic
  implications below have an explicit IsProbabilityMeasure assumption.
* The six four-unit assignments, in order, are TTFF, TFTF, TFFT, FTTF,
  FTFT, FFTT. The outcome vector called u4 is (0,1,2,3).
* Additive adjustment at t is A_t(Y,z)_i=Y_i-1[z_i=true]t.
  Multiplicative adjustment at a is
  M_a(Y,z)_i=Y_i/(1+1[z_i=true](a-1)).

## SAP.P016b.T12

The theorem has no outer data or assumptions: it asserts the conjunction below
(`T12WholeStatement`, WholeW1:20–33).

1. For every natural n, every assignment z with n_false>0 followed by
   n_true>0, every pair of real outcome vectors y,y', if for every i the
   treated outcomes satisfy y_i≤y'_i and the control outcomes satisfy
   y'_i≤y_i, then D(y,z)≤D(y',z). This is precisely the unfolded
   `EffectIncreasingOnGroups` property applied to `meanDifference`.
2. Neither K nor K_signed on four units has that property. Each negation
   means there exist an assignment with both groups nonempty and two outcome
   vectors satisfying all the directional inequalities but with the statistic
   strictly decreasing. The witnesses for the two negations need not coincide.
3. For every finite type Omega, every finite law w on it, if every weight is
   strictly positive, then for every score s : Omega→R and every alpha∈R,
   alpha≥0 followed by alpha≤1 imply all six bounds:
   P(U≤alpha)≤alpha, P(L≤alpha)≤alpha,
   P(Q(L,U)≤alpha)≤alpha, P(U<alpha)≤alpha,
   P(L<alpha)≤alpha, and P(Q(L,U)<alpha)≤alpha.
4. For each k=0,...,5, K(u4,z_k) equals the corresponding coordinate of
   (1,1/2,1/2,1/2,1/2,1).
5. On the uniform six assignments, for each k the inclusive upper-tail p value
   of K(u4,z_k) equals coordinate k of (1/3,1,1,1,1,1/3).
6. For every real alpha with 0≤alpha≤1, the uniform probability of upper p
   ≤alpha is 0 if alpha<1/3, 1/3 if 1/3≤alpha<1, and 1 at alpha=1.

The theorem docstring describes these clauses, including the finite-law positivity
condition and the nonempty group condition. The finite-law assertion is not
limited to outcome-based scores or to these six assignments.

Junk conventions: R division by zero is 0. Empty group means and ECDFs are
therefore 0 globally, but both groups are nonempty in the directional clauses
and all six concrete assignments have two of each. n=0 gives a vacuous
directional implication because its positive group assumptions are impossible;
the claim also covers nonempty actual instances. A list maximum on an empty
list is its seed 0, but the KS negations and concrete evaluations use n=4.
`uniformLaw` demands a nonempty type, so |Omega| is nonzero. A normalized
finite law cannot exist on an empty type, independently of strict positivity.
Natural counts are cast exactly to R; there is no natural subtraction here.
There are no integrals, infinities, logarithms, roots, real powers, extrema of
unbounded sets, limits or partial functions in this closure. Generated proofs
are numeral typeclass witnesses, nonemptiness of Fin 6, and the actual
nonnegativity/normalization proofs for uniform weights; none adds a hypothesis.

## SAP.P016b.T13

The theorem has no outer assumptions. It asserts all the following conjunctions
(`T13WholeStatement`, WholeW1:92–105).

1. For every B∈N, B>0, every Borel measure mu on R^(B+1) with probability
   measure instance, exchangeability followed by almost-sure injectivity of
   t (all B+1 scores distinct), every alpha∈R with alpha≥0, and every
   c∈N satisfying c=floor_N(alpha B/2) and 2c<B, all of these hold:
   * For every k∈{0,...,B}, the number R(t)=sum_{b<B}1[t_{b+1}<t_0]
     equals k with probability 1/(B+1).
   * Almost surely, L_B=R(t) and U_B=B-L_B, where the latter subtraction
     is natural subtraction.
   * P(raw p≤alpha)=2(c+1)/(B+1).
   Uniform ranks are nested inside the alpha,c hypotheses, but alpha=0,c=0
   supplies them for every B>0. There is no explicit alpha<1 assumption.
2. For every probability measure on R^1001, exchangeability and almost-sure
   distinctness imply P(raw p≤1/20)=4/77>1/20. Independently, for every
   such law on R^10001 that probability is 502/10001>1/20.
3. Fix y_i=2^i for i=0,...,15. Let Z be the finite subtype of Boolean
   assignments with exactly eight treated units. The assertions are:
   |Z|=12870; sum_i y_i=65535; sum_i y_i^2=1431655765; for every z∈Z,
   RSS(z)=sum_i(y_i-S_{z_i}(y,z)/n_{z_i})^2
   =1431655765-[S_true(y,z)^2+(65535-S_true(y,z))^2]/8;
   the image set of RSS on Z has cardinal 6435; and, for every z,w∈Z,
   RSS(z)=RSS(w) iff z=w or z_i=not(w_i) for every i. Additionally, for
   every v in that image, exactly two assignments have RSS=v.
4. Define, literally as finite sums of real numbers,
   H(M,B,c)=(2/M) sum_{r=0}^{M-1} sum_{k=0}^c
   choose(B,k) ((r+1)/M)^k ((M-r-1)/M)^(B-k).
   Here exponents and B-k are natural, and all divisions are real.
   Throughout the actual assertions M=6435. Probability on functions
   draw : {0,...,B}→Z means the count of satisfying functions divided by
   |Z|^(B+1). This is a uniform independent draw of every coordinate,
   including the observed assignment draw_0. References are
   RSS(draw_{b+1}), and the observation is RSS(draw_0).
   * For every B>0 then c∈N with 2c<B,
     P(L_B≤c or U_B≤c)=H(6435,B,c).
   * For every B,c∈N, B>0 then c<B imply
     2(c+1)/(B+1)-2/6435 ≤ H(6435,B,c) ≤ 2(c+1)/(B+1).
   * For each B in {1000,10000},
     P(raw p≤1/20)=H(6435,B,B div 40), and
     P(raw p<1/20)=H(6435,B,(B div 40)-1).
   * H(6435,1000,25)>1/20 and H(6435,10000,250)>1/20;
     H(6435,1000,24)<1/20 and H(6435,10000,249)<1/20.
   * For every B>0,
     P(raw p=0)=H(6435,B,0)
     =2 sum_{r=0}^{6433}(6434-r)^B /6435^(B+1)>0.
     Subtraction in this last displayed base is real subtraction.
5. For every B>0, the same independent finite design satisfies
   P(raw p≤1/20)=H(6435,B,B div 40), including B outside the two reported
   reference counts.
6. The exact rational identities 52/1001=4/77 and
   4/77-2/6435=2326/45045>1/20 hold.
7. Five open intervals locate the mixture values:
   H(6435,1000,25)∈(0.051792651792,0.051792651793),
   H(6435,10000,250)∈(0.050039580346,0.050039580347),
   H(6435,1000,24)∈(0.049794649794,0.049794649795),
   H(6435,10000,249)∈(0.049839600344,0.049839600345),
   H(6435,1000,0)∈(0.001846625,0.001846626).
   These are exact rational endpoints, not floating-point computations or
   equalities to the printed terminating decimals.

The docstring identifies the anti-conservative examples with an archived weak
cutoff, explicitly distinguishing the printed strict cutoff. Nothing in the
formal proposition itself has a label saying that another proposition is false.

Junk conventions: raw p at B=0 would divide by zero, but B>0 is imposed in
every generic raw-p assertion and the specialized B are positive. RSS divides
by group counts, which are both eight in Z. `uniformMass` would return 0 on an
empty sample space through 0/0, but Z has the explicit assignments with the
first eight treated and last eight controls; its function spaces are nonempty.
The general helper H has denominator M and natural B-k, but M=6435 everywhere
in the statement, and every used cutoff satisfies c<B, so k≤c<B and B-k is
ordinary nonnegative subtraction. B div 40 is natural integer division;
(B div 40)-1 occurs only for B=1000,10000, so truncation does not change it.
The rank identity uses B-L_B, with L_B≤B by its finite-count definition.
Nat.floor is clipped at zero on negative inputs, but alpha≥0 and B>0 prevent
that case. Thresholds at/above 1 with 2 floor(alpha B/2)<B can occur only at
the central odd-B case where the displayed probability is 1, consistent with
the cap in raw p. Natural powers follow 0^0=1; actual summands have B-k>0,
and (r+1)/M>0, so no problematic endpoint power occurs. `mu.real` would map
infinite mass to zero, but a probability measure has no infinite-mass sets.
The ambient spaces are finite products of R with their Borel sigma algebras;
comparison events and permutations are measurable. There are no Bochner
integrals, logarithms, roots, rpow, empty/unbounded sInf/sSup, limits or
partial functions. All generated closure proofs were inspected: they only
provide numeral, NeZero and outer-measure instances.

## SAP.P016b.T14

This is an unconditional conjunction (`T14Statement`, Part4:11–34).

1. For every B∈N with B>0, then every probability measure mu on R^(B+1),
   exchangeability implies all three groups of assertions:
   * For every c∈N with c≤B, P(L_B≤c)≤(c+1)/(B+1) and
     P(U_B≤c)≤(c+1)/(B+1). Ties are permitted.
   * For every alpha∈R, 0<alpha then alpha<1 imply
     P(raw p<alpha)≤2 ceil_N(alpha B/2)/(B+1).
   * For every alpha∈R with 0≤alpha≤1, set
     L_plus=(1+L_B)/(B+1) and U_plus=(1+U_B)/(B+1).
     Then P(L_plus≤alpha)≤floor_N(alpha(B+1))/(B+1),
     P(U_plus≤alpha)≤floor_N(alpha(B+1))/(B+1),
     floor_N(alpha(B+1))/(B+1)≤alpha, and
     P(min(1,2min(L_plus,U_plus))≤alpha)≤alpha.
2. For every probability measure on R^1001, exchangeability implies
   P(raw p<1/20)≤50/1001. For every probability measure on R^10001,
   exchangeability implies P(raw p<1/20)≤500/10001.
   Both rational bounds are strictly below 1/20.
3. For every finite type Omega, normalized nonnegative finite weight law w,
   natural B (including zero), score s : Omega→R, permutation pi of
   {0,...,B}, and arbitrary predicate E on R^(B+1), the two finite sums
   sum_draw 1[E((s(draw_{pi(i)}))_i)] product_i w(draw_i) and
   sum_draw 1[E((s(draw_i))_i)] product_i w(draw_i) are equal.
   Thus the full independent product score distribution is permutation
   invariant. There is no strict positivity condition on w in this clause.
4. For every finite type Omega, every normalized finite law w, if all weights
   are strictly positive, every real score s and alpha with 0≤alpha≤1 have
   the same six exact upper/lower/doubled weak/strict bounds listed explicitly
   in T12 clause 3. This is the expansion of `ExactValidity` here, too.

The docstring specifies that only this last exact-tail clause has a strict
weight-positivity domain. No distinctness assumption appears in the rank or
corrected-tail guarantees. Independence is encoded in the finite product
weights in clause 3; exchangeability alone is the hypothesis in clauses 1–2.

Junk conventions: all raw-p denominators have B>0, and every corrected-tail
denominator is B+1>0 even outside that hypothesis. floor/ceil inputs in the
actual assertions are nonnegative (strictly positive for ceil), avoiding their
clipping convention. Counts and floors/ceilings are natural numbers cast
exactly into R before arithmetic division. IsProbabilityMeasure prevents
`mu.real` from concealing infinite mass. Arbitrary E in the product identity
is harmless because the sums are finite with classical indicator predicates.
A normalized finite law excludes an empty Omega; product spaces of finite
nonempty Omega are nonempty. Empty products would be 1 globally, but the
product length B+1 is always positive. No natural subtraction, integrals,
logarithms, roots, real powers, unbounded extrema, limits or partial functions
occur. Generated proofs only supply numeral/NeZero instances.

## SAP.P016b.T15

There are no outer hypotheses. The proposition (`T15Statement`, Part4:36–46)
is the conjunction of these fully concrete or universally quantified facts:

1. With Y=(9,11,10,12), z=FFTT, additive adjustment at t=1/2 is
   (9,11,19/2,23/2), and multiplicative adjustment at a=2 is (9,11,5,6).
   The treated ECDF at 6 of the additive vector is 0; that of the
   multiplicative vector is 1.
2. The sample (1,3) has ECDF at 2 equal to 1/2, and at 3 equal to 1.
3. For every real t followed by every real b,
   (there exists real t0 with t=t0 and b=t0) iff b=t.
4. There does not exist real t0 with 1/2=t0 and 2=t0.

The adjustments mean exactly the coordinate formulas in the shared notation;
the ECDFs are literal normalized counts. The last two clauses talk about a
diagonal subset of R² through equality, without introducing random models,
null hypotheses, truth predicates or confidence-set definitions. The docstring
says these witnesses establish three local mathematical errors; the formal
statement supplies just the witnesses and the diagonal characterization.

Junk conventions: multiplicative division uses denominators 1 on controls and
2 on treated units, never zero. Both empirical treatment distributions divide
by two; the sample ECDF also divides by two. Real fractions are exact rational
numbers. There are no empty index types or zero sample sizes in the actual
evaluations, nor natural subtractions, integrals, infinities, logarithms,
roots, real powers, sInf/sSup, limits or partial-function defaults. The
generated closure declarations only certify natural numerals and the validity
of the concrete Fin 6 index 5; they impose no hypotheses or special outcomes.

## SAP.P016b.T16

`T16WholeStatement` (WholeW1:116) is exactly an alias for `T16Statement`
(Part4:48–62). It asserts the following conjunction, with no outer assumptions.

1. For every natural n, real outcome vector Y, Boolean assignment z, index
   i<n, and reals t,t',a,a', in that order, a≠0 then a'≠0 imply:
   * if z_i=false, A_t(Y,z)_i=Y_i and M_a(Y,z)_i=Y_i;
   * if z_i=true, A_t(Y,z)_i=Y_i-t and M_a(Y,z)_i=Y_i/a,
     followed by both implications
     t≠t' implies A_t(Y,z)_i≠A_t'(Y,z)_i, and
     a≠a' followed by Y_i≠0 implies M_a(Y,z)_i≠M_a'(Y,z)_i.
2. For every natural n, vector Y, assignment z, reals t,a,x, a positive
   control group count followed by a≠0 implies both
   F_false(A_t(Y,z),z;x)=F_false(Y,z;x) and
   F_false(M_a(Y,z),z;x)=F_false(Y,z;x).
3. For every natural n with n>0, every real vector u and real x,
   F(u;x)=|{i<n : u_i≤x}|/n (cardinality cast to R).
4. There exist reals t0,b0 such that 1/2=t0 and 2=b0.
5. There does not exist real t0 such that 1/2=t0 and 2=t0.

The generic ECDF assertion is an equality between a sum of indicators and a
filtered finite-set cardinal, with the ≤ direction and normalization fixed in
its definition. As in T15, the joint/diagonal assertions refer to real parameter
pairs through equality, without an encoded statistical hypothesis family.
The docstring describes the nonzero multiplicative parameters, the nonzero
response needed for multiplicative dependence, and the empirical distributions'
nonempty domains.

Junk conventions: multiplicative denominators are 1 or a; a and a' are
nonzero whenever the statement uses their treated comparisons. The control
ECDF identities explicitly require a positive control count. The full sample
ECDF identity requires n>0. At n=0 no index i exists in clause 1, but many
positive n instances exist; clauses 2–3 exclude their empty denominators.
The independent parameter witness (1/2,2) consists of exact real rationals.
Counts cast to real exactly. No natural subtraction, integration, infinite
measure conversion, logarithm, sqrt, rpow, empty/unbounded extrema, limits or
partial functions occur. The one auxiliary numeral instance in this closure
is ordinary arithmetic typeclass data, not a mathematical assumption.
