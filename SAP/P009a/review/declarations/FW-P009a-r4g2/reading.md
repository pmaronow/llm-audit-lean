# Blind reading of P009-T6 through P009-T10

This file was written before opening `claims.json` or `record.json`. Sources read:
the complete `closure.json`; both Challenge files; `Defs/Part1.lean`,
`Defs/Part2.lean`, `Defs/Part3.lean`, `Defs/Part4.lean`, the definition of
`T7Statement` in `Defs/Part5.lean`, and `Defs/WholeW3.lean` and
`Defs/WholeW4.lean`. All 14 generated auxiliary proof declarations appearing in
the closures were printed with Lean in `scratch/BlindCheck.lean`. They certify
numeral instances, positivity and normalization of the fair distribution,
positivity/growth of `t+1`, and nonzero sizes for finite indices. They add no
substantive hypotheses. Constructors and projections of the three structures
were also printed. The definitions below account for every SAP declaration in
each target's closure, including those structure fields and constructors.

## Common mathematical expansion used in the five sections

These are abbreviations in this reading, not additional assumptions.

* For a natural number (n), units are (I_n=\{0,\ldots,n-1\}\), the Lean type
  `Fin n`; assignments are functions (z:I_n\to\{\mathrm{false},\mathrm{true}\}).
  Write (b_i(z)=1) when (z(i)=\mathrm{true}), and zero otherwise.
* A finite distribution is an actual probability mass function (w\geq0) with
  (\sum_z w(z)=1). An experiment consists of such a distribution on the
  entire assignment cube and arbitrary real functions (y_i(z)) on that cube.
  (\mathbb E_w f=\sum_z w(z)f(z)), and (P_w(A)=\sum_z w(z)1_A(z)).
  There is no unspecified reference measure or integral.
* (p_i=P_w(z(i)=\mathrm{true})), and (p_i^0=P_w(z(i)=\mathrm{false})=1-p_i).
  Let (z^{i,a}) replace coordinate (i) by Boolean (a).
  (y_i(a;z)=y_i(z^{i,a})),
  (\tau_i(z)=y_i(1;z)-y_i(0;z)),
  (\tau(z)=n^{-1}\sum_i\tau_i(z)), and
  (\bar\tau=\mathbb E_w\tau\).
  The HT statistic is
  \[
    H(z)=\frac1n\sum_i\frac{1_{z(i)=1}y_i(z)}{p_i}
          -\frac1n\sum_i\frac{1_{z(i)=0}y_i(z)}{1-p_i}.
  \]
  Covariance is the finite mean of
  \((X-\mathbb EX)(Y-\mathbb EY)\); variance is
  (V_w(X)=\sum_z w(z)(X(z)-\mathbb E_w X)^2).
* The directed relation (i\rightsquigarrow j) means either (i=j), or there
  are assignments (z,z') agreeing at every coordinate other than (i), with
  (y_j(z)\ne y_j(z')). This is a full-cube, existential notion, including
  zero-probability assignments. Its indicator is (A_{ij}\in\{0,1\}).
  (D_{ij}=1) exactly when some unit \(\ell\) satisfies
  \(\ell\rightsquigarrow i\) and \(\ell\rightsquigarrow j\), and zero otherwise.
  In particular (D_{ii}=1).
  (d_i=\sum_jD_{ij}), (d_{\rm AVG}=n^{-1}\sum_i d_i), and
  (d_{\max}=\sup\{d_i:i\in I_n\}) as a real supremum.
  Outgoing counts are (c_i=\sum_jA_{ij}),
  (C_1=n^{-1}\sum_i c_i), (C_\infty=\sup_i c_i).
* `Regularity E k q s` means, in this order,
  (k>0,q\geq2,s\geq1);
  (k^{-1}\leq p_i\leq1-k^{-1}) for every unit;
  (\sum_z w(z)|y_i(z)|^q\leq k^q) for every unit;
  and (\sum_z w(z)|y_i(a;z)|^s\leq k^s) for every unit and both arms.
  Powers here are Mathlib `Real.rpow`, with real orders.
  `AssignmentBounds E k` keeps only (k>0) and the marginal bounds.
* A sequence consists of natural numbers (n_t>0), with (n_t\to\infty),
  and an experiment (E_t) of size (n_t) for every (t\in\mathbb N).
  `sampleSize` is the real cast of (n_t).
  `SequenceRegularity S k q s` requires the same constants at every time.
  `SparseDependence S` means (d_{\rm AVG}(E_t)/n_t\to0).
  `ConvergesInProbability S X` means, for every real \(\epsilon>0\),
  (P_{w_t}(|X_t|>\epsilon)\to0); its limit is zero.
* `ProductDesign E` means (0<p_i<1) and
  (w(z)=\prod_i[p_i\text{ if }z(i)=1\text{ else }1-p_i]).
  This is independent Bernoulli assignment, not only its one-dimensional
  marginals. `NoSpillovers E` says (z(i)=z'(i)\Rightarrow y_i(z)=y_i(z'))
  for every unit and every pair of assignments.
* `FixedSizeDesign E m` means natural (0<m<n) and
  (w(z)=\binom nm^{-1}) when \(\sum_i b_i(z)=m\), and zero otherwise.
  This is uniform complete randomization with exactly (m) treated units.
* The mask (R_i(z)) is the Boolean vector with coordinate (j) equal to
  (z(j)) if (j\rightsquigarrow i), and false otherwise. For arbitrary
  functions (X,Y) on a finite probability space,
  \[
  \alpha_w(X,Y)=\sup_{U,V}
  |P_w(X\in U,Y\in V)-P_w(X\in U)P_w(Y\in V)|.
  \]
  The supremum is over all sets of the two codomains. Since the sample space
  is finite, these are exactly events of the generated sigma-algebras.
* `ConvergesInLaw S X G` means: for every real (x), if (G) is continuous
  at (x), then (P_{w_t}(X_t\leq x)\to G(x)).
  `standardNormalCDF x` is the real value of the Mathlib probability
  `gaussianReal 0 1` of \(( -\infty,x]\).
  The standardized statistic is (U(z)=(H(z)-\bar\tau)/\sqrt{V_w(H)}).

Every occurrence of an eventual assertion below means there exists a natural
(T) after which it holds; every real limit is a `Tendsto` into the real
neighborhood filter; infinite sets of times are sets in \(\mathbb N\).

## SAP.P009a.T6

Statement: `Defs/WholeW3.lean:59–84`; Challenge docstring:
`Challenge/Part1.lean:68–74`. The theorem has no external parameters or
hypotheses; it asserts the conjunction of the following four assertions.

1. For every real sequence (a_t), then every pair (L,c\in\mathbb R),
   suppose that for every \(\epsilon>0\), eventually (a_t<L+\epsilon),
   and for every \(\epsilon>0\), frequently (L-\epsilon<a_t).
   This is the definition `FiniteLimsup a L`. If (0<c<L), the set
   \(\{t:c\leq a_t\}\) is infinite.
2. There exists a real sequence with that finite limsup equal to 1 and
   (a_t<1) for every time. This asserts the failure of attainment at the
   limsup, not the failure of threshold selection strictly below it.
3. For every natural (n>0), every experiment (E=(w,y)), then every real
   (k,L), assume `AssignmentBounds E k` and (0<L\leq1).
   Let (M=\lceil\sqrt L\,n\rceil_+\in\mathbb N), and retain (w) but replace
   outcomes by
   \[
   f_i(z)=\begin{cases}
   (n/M)b_0(z)[b_i(z)p_i-(1-b_i(z))(1-p_i)],&i<M,\\
   0,&i\geq M.
   \end{cases}
   \]
   Here the ceiling is Mathlib's natural ceiling. These are exactly
   `subsequenceResponse` and `limsupPopulation`, with no other use of the
   original outcomes. For the new experiment (F), the finite conclusions
   `LimsupFiniteFacts` are all of:
   \[
   d_{\rm AVG}(F)=M^2/n+(n-M)/n,\quad
   Ln\leq d_{\rm AVG}(F),\quad |f_i(z)|\leq1/\sqrt L;
   \]
   (\bar\tau(F)=p_0); and, for every assignment (z),
   (H_F(z)=b_0(z)),
   (|H_F(z)-\bar\tau(F)|=|b_0(z)-p_0|\geq k^{-1}).
4. For every experiment sequence (S), then every real (k), assume the
   common assignment bounds at every time and that sparse dependence fails.
   Put (a_t=d_{\rm AVG}(E_t)/n_t) and
   (L=\operatorname{Filter.limsup}_{t\to\infty}a_t).
   Here Mathlib's real limsup is the infimum of
   \(\{b:\text{eventually }a_t\leq b\}\).
   The conclusion gives `FiniteLimsup a L` and (0<L\leq1). For **every**
   (c\in(0,L)), put (H_c=\{t:c\leq a_t\}\). Construct (F_t) by the
   preceding formula with the same (L) whenever (t\in H_c), and give every
   unit zero outcome otherwise. All of these conclusions are asserted:
   * (H_c) is infinite and every new design equals the corresponding old
     design, at every time.
   * Every full-cube outcome is at most (1/\sqrt L) in absolute value.
   * For every real (q\geq2,s\geq1), there exists (K>0), chosen after
     (q,s), such that all times satisfy `Regularity F_t K q s`.
   * At every selected time the finite facts of item 3 hold, and the new
     experiment equals the displayed finite construction.
   * At every unselected time all outcomes, EATE, and HT are zero.
   * There are infinitely many times at which
     (P(|H_{F_t}-\bar\tau(F_t)|>1/(2k))=1).
   * Consequently the centered HT error fails convergence in probability
     to zero in the precise sense specified above.

The docstring describes the strict-threshold repair, supplies a positive
limsup from failure of sparse dependence, and claims design-preserving
inconsistency through these replacement outcomes. It does not claim that the
original outcomes must give inconsistency.

Junk-value audit: all means are finite sums of real values; there are no
non-integrable Bochner integrals. Although real inverse/division is total
and gives zero at a zero denominator, the hypotheses give (n>0), (k>0),
(p_i,1-p_i>0), (L>0), and hence \(\sqrt L>0\) and (1\leq M\leq n).
The only natural ceiling is therefore an ordinary positive ceiling, without
clipping at zero. Subtractions (n-M) in the dependence formula are real
subtractions, not truncated natural subtraction. Graph density is between
(1/n_t) and 1, so the real limsup uses a nonempty bounded-below set of
eventual upper bounds; no empty/unbounded infimum is involved. The abstract
finite-limsup clauses separately supply eventual upper bounds and recurring
lower bounds. Moment powers use nonnegative bases, (K>0), and positive
orders, so the (0^q=0) case is ordinary. Positive sizes also validate the
explicit coordinate 0 and exclude empty unit sets. There is no log, extended
real conversion, partial-function default, or other root in this closure.

## SAP.P009a.T7

Statement: `Defs/WholeW3.lean:121–156`, including
`Defs/Part5.lean:182–198`; Challenge docstring:
`Challenge/Part1.lean:78–84`. This is an unconditional conjunction about two
fully specified sequences and all continuous distribution functions.

Both sequences have (n_t=t+1), every assignment of mass (2^{-n_t}), and
independent fair treatment coordinates (`fairDistribution`, `fairPopulation`,
`sparseSequence`). Their respective schedules are
\[
y_i^{(a)}(z)=1_{i=0}b_i(z),\qquad
y_i^{(b)}(z)=\begin{cases}b_i(z),&i=0,\\b_i(z)-1/2,&i>0.\end{cases}
\]
The latter is `nonshrinkingPopulation`/`nonshrinkingSequence`.

First, the included `T7Statement` asserts for sequence (a): regularity with
((k,q,s)=(2,4,1)); (d_{\rm AVG}/n\to0); at every time product assignment,
no spillovers, (d_{\rm AVG}=d_{\max}=1), and (V_w(H)>0);
(nV_w(H)\to0); for every time and Boolean (b),
(P(U=1\text{ if }b\text{ else }-1)=1/2); and failure of convergence in law
of (U) to the standard normal CDF.

The remaining conjuncts say:

* For every real (q\geq2,s\geq1), both sequences have uniform regularity
  with (k=2).
* For every time in (a), all full-cube absolute outcomes are at most 1;
  (A_{ij}=D_{ij}=1_{i=j});
  (\bar\tau=\mathbb EH=1/n), (V_w(H)=1/n^2), and at every assignment
  (H(z)=2b_0(z)/n), (U(z)=2b_0(z)-1).
* For every time in (b), product design and no spillovers hold; all
  full-cube absolute outcomes are at most 1;
  (A_{ij}=D_{ij}=1_{i=j}), (d_{\rm AVG}=d_{\max}=1);
  (\bar\tau=\mathbb EH=1), (V_w(H)=1/n^2>0); and at every assignment
  (H(z)=(n-1+2b_0(z))/n), (U(z)=2b_0(z)-1).
* For each sequence (S\) belonging to the two-element set of these specified
  sequences: each sign of (U) has probability (1/2) at every time; at every
  (t,x) its CDF is
  \[
   F(x)=\begin{cases}0,&x<-1,\\1/2,&-1\leq x<1,\\1,&1\leq x;\end{cases}
  \]
  for every real function (G) that is continuous, monotone, valued in
  \([0,1]\), tends to zero at \(-\infty\), and tends to one at \(+\infty\),
  and then every time (t),
  \(\sup_x|F(x)-G(x)|\geq1/4\);
  (n_tV_{w_t}(H_t)\to0); and (U_t) fails standard normal convergence in law.
  `finiteCDF`, `ContinuousDistributionFunction`, `kolmogorovDistance`, and
  `rademacherCDF` mean precisely these finite probabilities, conditions,
  real supremum, and piecewise CDF.

The docstring calls this a refutation of a printed normal-approximation
sufficiency and emphasizes that the second EATE does not shrink. Without the
claim text, the mathematical counterexamples and the claimed scope of that
refutation must be kept distinct.

Junk-value audit: (n=t+1>0), the fair-design normalizer (2^n>0), and both
arm probabilities (1/2>0). Both asserted variances (1/n^2) are positive,
so square-root normalization is genuine at every time. The (n-1) in the
second HT formula is real subtraction; even the corresponding integer size
is at least one. Graph maxima are suprema of finite nonempty real sets.
The Kolmogorov supremum has a nonempty index domain \(\mathbb R\) and is
bounded by 1 because the two CDFs take values in \([0,1]\).
`gaussianReal 0 1` is a probability measure, so `toReal` never receives
infinity. All powers and finite expectations are well-defined as above.
There is no limsup/liminf, logarithm, truncated subtraction, empty sum
over units, partial-function default, or non-integrable integral involved.

## SAP.P009a.T8

Statement: `Defs/WholeW3.lean:166–177`; Challenge docstring:
`Challenge/Part1.lean:88–94`. This is the conjunction of a universal normal
limit assertion and `T7Statement`, whose complete sparse-sequence assertion
was unfolded in the preceding section (and is repeated in substance below).

For every positive growing experiment sequence (S), and then every real
(k,q,s), assume all of:

1. Uniform regularity with those constants: (k>0,q\geq2,s\geq1), the same
   marginal bounds (k^{-1}\leq p_{ti}\leq1-k^{-1}) at every time, the
   uniformly bounded observed (q)-moments, and the uniformly bounded two
   potential-response (s)-moments, as expanded above.
2. Product design at every time: the full joint mass is the product of the
   nondegenerate Bernoulli marginals.
3. There exists a real (D) such that, at every time,
   \(\sup_{i\in I_{n_t}}\sum_j1_{\exists\ell:\ell\rightsquigarrow i,\ell\rightsquigarrow j}\leq D\).
4. There exists (c>0) and a time (T) such that, for (t\geq T),
   (c\leq n_tV_{w_t}(H_t)) (`EventuallyPositiveLowerBound`).

The conclusion first asserts eventual positivity of (V_{w_t}(H_t)).
Then, for **every** family of real functions (X_t) on the assignment cubes,
if for every time with (V_{w_t}(H_t)>0) and every assignment
(X_t(z)=(H_t(z)-\bar\tau_t)/\sqrt{V_{w_t}(H_t)}), its CDF converges at every
continuity point of the standard normal CDF to that normal CDF. (X) is
unconstrained at indices with zero variance. There is no externally assumed
CLT, Lindeberg condition, conditional independence, or variance identity.

The second conjunct is the unconditional assertion about the fully specified
sparse sequence (n=t+1,w=2^{-n},y_0(z)=b_0(z),y_i(z)=0) for (i>0):
regularity (2,4,1); (d_{\rm AVG}/n\to0); product assignment and no
spillovers at every time; (d_{\rm AVG}=d_{\max}=1); positive HT variance;
(nV(H)\to0); both standardized values \(\pm1\) have probability (1/2)
at every time; and no standard normal limit. This conjunct witnesses failure
when the variance-floor hypothesis is removed.

The docstring describes exactly a sufficient condition with a variance floor,
including freedom of the finitely many initial zero-variance values, and a
counterexample without that condition.

Junk-value audit: sizes are positive. Uniform regularity gives positive arm
probabilities in both arms. Every expectation is a finite sum. Variance is a
nonnegative finite second central moment; the added hypothesis gives eventual
strict positivity. The total Lean expression for standardized HT would be
zero on a zero-variance index because division by zero is zero, but the
quantified (X) formulation expressly allows arbitrary values there. Only
finitely many such indices exist, so no limiting meaning relies on their
value. Maximum degrees use finite nonempty sets. The Gaussian conversion is
finite. Real moment powers have nonnegative bases and orders (q\geq2,s\geq1).
For the included sparse sequence every variance is positive. No empty or
unbounded supremum, limsup/liminf, log, truncated subtraction, or partial
function occurs.

## SAP.P009a.T9

Statement: `Defs/WholeW4.lean:81–83` with its three fact predicates;
Challenge docstring: `Challenge/Part1.lean:98–110`.

For every natural (r\geq1), there exists an experiment of size (n=4r+2)
with all the following properties simultaneously. Put (h=2r+1),
(A=\{0\}\cup\{2,3,\ldots,2r+1\}\), (B=I_n\setminus A).
These are `firstHalf` and `wholeSecondHalf`.

`WholeHalfDesignFacts` expands to uniform complete randomization of exactly
(h) treated units; the exact full-cube schedule
\[
y_0(z)=h^{-1}\sum_{j\in A}b_j(z),\quad
y_1(z)=h^{-1}\sum_{j\in B}b_j(z),\quad
y_i(z)=b_i(z)\quad(i\ne0,1);
\]
all outcomes between zero and one on the full cube; all treated marginals
(1/2); and, for every real (q\geq2,s\geq1), regularity with (k=2).

`WholeHalfGraphFacts` expands to \(|A|=|B|=h\), disjointness and union equal
to all units; (A_{ij}=1_{i\in P_j}) where
(P_0=A,P_1=B,P_j=\{j\}) otherwise (`wholeHalfParents`);
(D_{01}=0); \(\sum_{i,j}D_{ij}=3n-4\);
(d_{\rm AVG}=3-4/n<3); (c_0=c_1=1), (c_i=2) otherwise;
(C_1=2-2/n) and (C_\infty=2).

Let (T_A(z)=\sum_{j\in A}1_{z(j)=1}\) and similarly (T_B), both natural
counts (`wholeTreatedCount`). Define the majority event
(M=\{T_A\geq r+1\}) and the minority event (N=\{T_B\leq r\}).
`WholeHalfEventFacts` says:

* For every positive-mass assignment,
  (T_A+T_B=h), (T_B=h-T_A), and (M\leftrightarrow N).
* There exist sets (U,V) of Boolean assignment vectors such that, as
  full-cube sets, (M=R_0^{-1}(U)), (N=R_1^{-1}(V)). This is membership
  in the respective generated sigma-algebras in explicit finite form.
* (P(M)=P(N)=P(M\cap N)=1/2).
* \(|P(M\cap N)-P(M)P(N)|=1/4\) and
  \(\alpha_w(R_0,R_1)=1/4\).

The docstring labels the printed all-pairs vanishing assertion false and
claims this growing family, with disjoint parent sets but maximal positive
mixing for units 0 and 1, refutes it. Its precise refutation scope awaits the
canonical claim reading.

Junk-value audit: (r\geq1) gives (n\geq6,h\geq3,0<h<n) and
\(\binom nh>0\). Thus all normalizing denominators and both arm
probabilities are positive. Booleans in counts cast to naturals in the
ordinary way. The sole natural subtraction in the event facts is
(h-T_A); it is asserted only on positive mass, together with the explicit
identity (T_A+T_B=h), which implies (T_A\leq h). It therefore is not
truncated in any use. Subtractions (3n-4,3-4/n,2-2/n) in the graph
formulas are real subtractions. The set difference defining (B) is ordinary
finite-set difference. Graph maximum is over a nonempty finite set. The
mixing supremum is nonempty (take an empty event) and bounded, in fact by
(1/4), so no supremum default is used. Moment powers have bounded
nonnegative bases and positive orders. No roots, limsup/liminf, log,
extended-real conversion, undefined conditional expectation, or partial
function appears.

## SAP.P009a.T10

Statement: `Defs/WholeW4.lean:136–140`, with
`WholeExceptionalMixing` and `WholeExceptionsNecessary`; Challenge
docstring: `Challenge/Part2.lean:10–19`.

This is the conjunction of a universal exceptional-set limit theorem and an
existential necessity example.

First, for every positive growing experiment sequence (S), assume:
(i) for each time there exists a natural (m_t\in(0,n_t)) with the uniform
complete-randomization mass formula; and (ii) there exists real (D) such
that eventually (d_{\rm AVG}(E_t)\leq D). No uniform marginal bound or
outcome-moment hypothesis is imposed on this first assertion.

Put (N_{0,t}=\{(i,j)\in I_{n_t}^2:D_{ij}=0\}), a finite set of ordered
pairs (`wholeZeroPairs`), and \(\alpha_{ij,t}=\alpha_{w_t}(R_i,R_j)\)
(`wholePairMixing`). There exists a family of finite pair sets (E_t)
(`exceptions`), chosen after (S) and its hypotheses, such that
`WholeExceptionalMixing` holds, namely:

* At every time (E_t\subseteq N_{0,t}).
* Eventually \(|N_{0,t}|>0\) and (N_{0,t}\setminus E_t\ne\varnothing).
* \(|E_t|/|N_{0,t}|\to0\).
* \(\max_{(i,j)\in N_{0,t}\setminus E_t}\alpha_{ij,t}\to0\).
* Explicitly, for every real \(\epsilon>0\), eventually every pair with
  (D_{ij}=0) and \((i,j)\notin E_t\) has \(\alpha_{ij,t}<\epsilon\).

The finite maximum is `Finset.sup'` when its pair set is nonempty, and is
defined to be zero on an empty pair set (`wholeMaximumMixing`). The two limit
formulations are both asserted, not assumed equivalent as a hypothesis.

Second, `WholeExceptionsNecessary` says there exists a positive growing
sequence (S) with (n_t=4(t+1)+2) at every time, uniform regularity with
((k,q,s)=(2,4,1)), complete randomization with some (0<m_t<n_t) at every
time, and (d_{\rm AVG}(E_t)<3) at every time. There then exist index
functions (a_t,b_t\in I_{n_t}) such that, at every time,
(a_t=0,b_t=1,D_{a_tb_t}=0), and \(\alpha_{a_tb_t,t}=1/4\).
In addition it explicitly denies the assertion that for every
\(\epsilon>0\), eventually every zero-dependence pair has mixing less than
\(\epsilon\). The exact half-population schedule is not specified in this
existential conjunct; it asserts the described sequence's properties.

The docstring describes eventual domains, a vanishing exceptional fraction,
the remaining-pair maximum limit, and necessity of allowing exceptions.

Junk-value audit: every size is positive and tends to infinity; complete
randomization requires (0<m<n), so \(\binom nm>0\) and both marginal
probabilities are positive at each time, without requiring uniform
positivity. The quotient \(|E_t|/|N_{0,t}|\) uses total real division and may
be zero over zero at initial times. The maximum is explicitly zero on an
empty initial pair set. Both relevant domains are proved eventually
nonempty, so neither convention changes the stated limits or the ordinary
eventual mathematical assertion. Counts and cardinalities are cast
faithfully to reals; finite-set subtraction is not numerical truncation.
Mixing suprema are nonempty bounded real suprema. The existential regularity
condition uses only finite sums, nonnegative power bases, positive real
orders and (k=2). There are no roots, logarithms, limsup/liminf,
extended-real conversions, non-integrable means, or partial functions in
this target's closure.
