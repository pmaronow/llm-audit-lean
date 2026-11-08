# Blind reading

This file was written before opening `claims.json` or `record.json`. Sources read:
`closure.json`, `SAP/P061b/Challenge/Part1.lean`, and every dependency listed in
the five closures, in `Defs/Part1.lean`, `Defs/Part2.lean`, `Defs/Part4.lean`, and
`Defs/WholeW1.lean`. A Lean check in `scratch/BlindPrint.lean` also printed the
constructor, projection, and all four generated auxiliary declarations appearing
in those closures. The auxiliaries only supply `NeZero 2` or `2.AtLeastTwo` for
numerals; they add no probabilistic assumptions.

## Common fully expanded notation

All assignment spaces are Lean `Type` (universe zero). An atomic design on a set
of assignments Ω is a function p: Ω → ℝ with p(z) ≥ 0 for every z, `Summable p`,
and ∑'z p(z) = 1. Here `Summable` and ∑' are Mathlib's unordered summability and
total infinite sum in ℝ. In particular, positive mass occurs at at most countably
many assignments, and an empty Ω cannot carry such a design. The constructor
`AtomicDesign.mk` takes precisely p and these three proofs; `AtomicDesign.p`
returns p. No measurable-space structure is an additional field.

For the descriptions below, the following notation is exclusively shorthand for
these formulas, not for any additional assumptions:

* A population of size N has index set `Fin N` = {0,...,N−1}. A schedule is a
  function `Fin N → Ω → ℝ`. Thus g_i(z), y_i(z), and F_i(z), when used, are real
  numbers, and all sums over i,j are finite sums over the entire `Fin N`.
* S = {z : p(z) > 0} is support (`InSupport`).
* P(A) = ∑'z (if A(z) then p(z) else 0) (`eventProbability`).
* E[X] = ∑'z p(z)X(z) (`designMean`). Its absolute first-moment condition is
  `Summable (z ↦ p(z)|X(z)|)` (`HasFirstMoment`).
* I_i^d(z) is 1 if g_i(z)=d and 0 otherwise (`exposureIndicator`).
  π_i^d = P(g_i=d) (`exposureProbability`), and
  q_ij^{de} = P(g_i=d ∧ g_j=e) (`jointExposureProbability`).
* M_i^d = E[z ↦ if g_i(z)=d then y_i(z) else 0]/π_i^d
  (`exposureMean`). A^d = N⁻¹∑i M_i^d (`averageExposureMean`), and
  A^d−A^e is `averageContrast`.
* H^d(z) = N⁻¹∑i (if g_i(z)=d then y_i(z) else 0)/π_i^d (`htMean`),
  and H^d−H^e is `htDifference`.
* L_n^d(z) = n⁻¹∑i (if g_i(z)=d then y_i(z) else 0) (`exposedMean`).
  This is a fixed-denominator sum; it equals the ordinary exposed-unit sample
  mean only when there are n exposed units.
* Exposure first moments at d mean, for every i,
  `Summable (z ↦ p(z)|if g_i(z)=d then y_i(z) else 0|)`
  (`ExposureMoment`).
* Support stability means: for every i and every z,w with p(z)>0 and p(w)>0,
  g_i(z)=g_i(w) implies y_i(z)=y_i(w) (`SupportStable`). It imposes no
  constraint on zero-mass assignments.
* V(X) = E[(X−E[X])²] (`designVariance`) and
  C(X,Y) = E[(X−E[X])(Y−E[Y])] (`designCovariance`).
* K^{de} = N⁻²∑i∑j [(q_ij^{de}−π_i^d π_j^e)/(π_i^d π_j^e)]M_i^d M_j^e
  (`covarianceSum`). All i,j pairs, including diagonals and both orders, occur.

Every inverse, quotient, square, and inequality above is in ℝ after the natural
number population/sample sizes have been cast to ℝ. There is no integer division.

## SAP.P061b.T17

The theorem is the conjunction of three universally quantified assertions
(`T17WholeStatement`, `Defs/WholeW1.lean:54`).

1. For every Ω, N, atomic p on Ω, schedules g,y, exposure d∈ℝ, and n∈ℕ,
   if N>0, n>0, and π_i^d=n/N for every i, then for every z∈Ω,
   H^d(z)=L_n^d(z). There is no stability, moment, sample-count, or on-support
   hypothesis in this conjunct. This is a pointwise algebraic identity, even at
   zero-mass assignments.
2. For every Ω,N,p,g,y,d,n, assume n>0, n≤N, exposure first moments at d,
   and the following sampling law (`SimpleRandomExposureW1`): for every binary
   vector a:`Fin N → Fin 2`, the probability that
   i ↦ (if g_i(z)=d then 1 else 0) equals a is 1/binomial(N,n) when
   #{i:a_i=1}=n, and zero otherwise. The map in this event is `exposureMaskW1`.
   The conclusions are: every z in S exposes exactly n units;
   π_i^d=n/N for every i; H^d(z)=L_n^d(z) for every z (also off support);
   ∑'z p(z)|L_n^d(z)| is summable; and E[L_n^d]=A^d. Outcomes may depend
   arbitrarily on the raw assignment, and many raw assignments can yield the
   same sampled set. The census n=N is allowed.
3. For every N, feasible set Z⊆(Fin N→ℝ), atomic p on the subtype Z,
   schedule y on Z, and n∈ℕ, suppose Z contains every vector
   i↦(a_i.val:ℝ) for a:`Fin N→Fin 2` (`ContainsBinaryCubeW1` and
   `binaryAssignmentW1`); n>0; n<N; and for every z∈Z,
   p(z)=1/binomial(N,n) if every z_i is 0 or 1 and exactly n coordinates
   are 1, and p(z)=0 otherwise (`UniformBinaryDesignW1`). Exposure is
   g_i(z)=z_i (`coordinateExposureW1`). Then: every z in S has n ones and
   N−n zeros; π_i^1=n/N and π_i^0=(N−n)/N for every i; exposure first
   moments exist at both 1 and 0; the difference L_n^1−L_{N−n}^0 has an
   absolute first moment; and E[L_n^1−L_{N−n}^0]=A^1−A^0.

Quantifier order matters: all designs and schedules are given before the stated
sampling-law assumptions. No outcome stability is required anywhere. The
docstrings at `Challenge/Part1.lean:34–42` and `Defs/WholeW1.lean:45–53`
describe these reductions and sampling/experiment consequences, with the usual
measure-theoretic existence conditions.

Junk-value audit:

* ℝ inverse and division at zero are zero. N,n are positive whenever their
  inverses are used here. All used π's are positive: assumed in the first
  conjunct via π=n/N, and concluded from the sampling laws in the other two.
* `Nat.choose N n` can be zero in the definitions in isolation, but n≤N or
  n<N in each relevant use makes it positive.
* `N-n` is truncated natural subtraction. In the experiment n<N, so it is
  the ordinary positive difference. All casts to ℝ preserve these values.
* Infinite sums of nonsummable real families default to zero in Mathlib.
  Probability sums are summable by domination by p. The first conjunct has
  no expected outcome and needs no outcome moment. The second explicitly
  assumes all needed exposure first moments. The third has finite positive
  support (the binary assignments with n ones), so arbitrary real y has the
  stated moments. Thus no used mean is justified by a default sum.
* Empty population indices are excluded in all three conjuncts. Impossible
  designs on empty Ω cannot be supplied. Feasible Z is nonempty by its cube
  assumption. The sampling definition is not a default choice of a set.
* No log, square root, rpow, extended-real conversion, infimum/supremum,
  liminf/limsup, Bochner integral, or partial-function default occurs.

## SAP.P061b.T18

`T18Statement` (`Defs/Part4.lean:31`) universally quantifies, in this order,
Ω,N, atomic p, schedules g,y, and real exposures d,e. The hypotheses are N>0,
π_i^d>0 and π_i^e>0 for every i, and support stability. The exposures need not
be distinct. The conclusion is the conjunction of all of the following:

1. For every i,z with p(z)>0,
   (if g_i(z)=d then y_i(z) else 0) =
   (if g_i(z)=d then M_i^d else 0).
2. For every z with p(z)>0,
   H^d(z)=N⁻¹∑i (if g_i(z)=d then M_i^d else 0)/π_i^d.
3. V(H^d)=N⁻²∑i∑j C(I_i^d,I_j^d) M_i^d M_j^d/(π_i^d π_j^d).
   The right side is `indicatorVarianceSum` (`Defs/Part2.lean:65`).
4. V(H^d)=K^{dd}.
5. C(H^d,H^e)=K^{de}.
6. V(H^d−H^e)=V(H^d)+V(H^e)−2C(H^d,H^e).
7. For every i, q_ii^{dd}=π_i^d.
8. If d≠e, then for every i, q_ii^{de}=0.

The covariance and variance notions in this list are the centered weighted sums
expanded in the common notation, not primitive covariance/variance axioms. In
particular, the factors involving I are means of products of centered real
zero-one functions. The docstring (`Challenge/Part1.lean:45–47`) describes
the revealed-value, variance, covariance, and contrast identities on atomic
designs under support stability.

Junk-value audit:

* N and all marginal-probability denominators used in the formulas are
  nonzero by explicit hypotheses. No joint-probability denominator occurs.
  A zero joint probability is a legitimate numerator contribution.
* Although moment hypotheses are not written, support stability and positive
  cells make y constant on each selected cell in S. There are only finitely
  many such cells for the two exposures used. Therefore all selected moments,
  H's moments, centered squares, and covariance products have finite absolute
  sums against p. Unselected and off-support y may be unbounded but contributes
  zero. No nonsummable-tsum default is needed.
* Empty `Fin N` is excluded; empty Ω cannot carry p. Real exponent 2 is the
  ordinary natural square. There is no subtraction on naturals and no other
  domain-sensitive or partial operation from the requested checklist.

## SAP.P061b.T19

`T19WholeStatement` (`Defs/WholeW1.lean:107`) universally quantifies Ω,N,
atomic p, schedules g,y, and d∈ℝ. Assume N>0, π_i^d>0 for every i, and
support stability. For compactness below write π_i=π_i^d, q_ij=q_ij^{dd},
M_i=M_i^d, and H=H^d. In addition to the common fully expanded formulas,
the three statistics in this statement are:

* U(z)=N⁻²∑i∑j [(q_ij−π_iπ_j)/(π_iπ_j)]y_i(z)y_j(z)
  (if g_i(z)=d ∧ g_j(z)=d then 1 else 0)/q_ij
  (`htVarianceEstimate`, `Defs/Part2.lean:72`).
* B_ij(z)=(if g_i(z)=d then y_i(z)²/2 else 0)/π_i +
  (if g_j(z)=d then y_j(z)²/2 else 0)/π_j
  (`youngPairEstimateW1`, `Defs/WholeW1.lean:81`).
* U_cons(z)=N⁻²∑i∑j of the U summand if q_ij>0, B_ij(z) if
  q_ij=0, and 0 otherwise (`conservativeVarianceEstimate`,
  `Defs/Part2.lean:80`). The factor N⁻² applies to the entire sum.

The conclusions, all conjoined, are:

1. Every exposed y-cell has an absolute first moment; H has an absolute
   first moment; and (H−E[H])² has an absolute first moment.
2. If q_ij>0 for every i,j, then U has an absolute first moment and
   E[U]=V(H)=K^{dd}.
3. U_cons has an absolute first moment and E[U_cons]≥V(H).
4. For every ordered pair i,j (including i=j),
   |M_i M_j|≤M_i²/2+M_j²/2, B_ij has an absolute first moment, and
   E[B_ij]=M_i²/2+M_j²/2.
5. For every i,j, if q_ij=0, then i≠j, no z with p(z)>0 satisfies
   g_i(z)=d and g_j(z)=d simultaneously, and the following statistic does
   not exist: a function T:Ω×(Fin N→ℝ)→ℝ such that, for every schedule
   v:Fin N→Ω→ℝ satisfying support stability with this same p,g, the
   function z↦T(z,(k↦v_k(z))) has an absolute first moment and its mean
   equals
   [E(if g_i=d then v_i else 0)/π_i]
   [E(if g_j=d then v_j else 0)/π_j].

The last expanded property is `UnbiasedProductStatisticW1`
(`Defs/WholeW1.lean:89`). In its nonexistence assertion, p,g,d,i,j are
fixed before choosing T, and T is chosen before the universal v. T receives
the whole assignment and the whole vector of observed outcomes, not the
unobserved schedule. The assertion is about one statistic working for all
unknown support-stable schedules. It is not the false assertion that a
constant tailored to one already-known product cannot be unbiased.

The docstrings (`Challenge/Part1.lean:50–59`, `Defs/WholeW1.lean:97–106`)
describe the estimator properties, pair bound, universal observed-data
impossibility, ordered diagonal pairs, and existence of moments from positivity
and stability. This is a positive theorem with an impossibility conclusion,
not a docstring purporting to refute a printed claim.

Junk-value audit:

* N and every π_i are positive. All used marginal denominators and 2 are
  nonzero. In U, q_ij=0 would make that summand zero by ℝ division, but
  the U unbiasedness clause explicitly assumes every q_ij>0. Thus its
  conclusion does not rely on pretending an unobservable product was
  estimated by a zero-denominator term. The conservative statistic handles
  q_ij=0 by a separate B_ij term. Negative q_ij cannot occur for p≥0.
* Support stability makes selected y_i values fixed constants on S;
  consequently all asserted first and second moments and statistic moments
  are genuine summable means, even if raw Ω is infinite. For every v in
  the impossibility property, the two conditional target means are also
  well-defined for the same reason. T's first moment is a requirement of
  being a uniformly unbiased statistic, not an implicit default.
* Squares are natural powers in ℝ. The population is nonempty; diagonal
  zero-joint antecedents are impossible because π_i>0. There are no empty
  extrema, limits, non-real conversions, logs, roots, rpow, or partial values.

## SAP.P061b.T20

`T20Statement` (`Defs/Part4.lean:58`) universally quantifies Ω,N, atomic p,
schedules g,y,F, and d∈ℝ. Assume N>0; π_i^d>0 for every i; exposure first
moments of y at d; an absolute first moment of each F_i; and exposure first
moments of F at d. Write π_i=π_i^d, I_i=I_i^d. The adjusted statistic is

J(z)=N⁻¹∑i (if g_i(z)=d then y_i(z)−F_i(z) else 0)/π_i
     +N⁻¹∑i F_i(z)

(`adjustedMean`, `Defs/Part2.lean:93`). Calibration means, for every i,
E[z↦(if g_i(z)=d then F_i(z) else 0)/π_i]=E[F_i]
(`PredictionCalibrated`, `Defs/Part2.lean:98`). The theorem asserts the
conjunction of three implications:

1. Calibration implies that J has an absolute first moment and E[J]=A^d.
2. If every I_i is event-independent of F_i, calibration holds and J has
   an absolute first moment and E[J]=A^d. Event independence here
   (`EventIndependent`, `Defs/Part1.lean:99`) means, for every predicate
   E:ℝ→Prop and every predicate F:ℝ→Prop,
   P(E(I_i) ∧ F(F_i))=P(E(I_i))P(F(F_i)). These are all predicates, not
   just a separately specified sigma-algebra of measurable events.
3. If each F_i is mean-independent of I_i, calibration holds and J has
   an absolute first moment and E[J]=A^d. Mean independence
   (`MeanIndependent`, `Defs/Part1.lean:105`) means that, for every real b
   with P(I_i=b)>0,
   E[z↦if I_i(z)=b then F_i(z) else 0]/P(I_i=b)=E[F_i].
   Since I_i takes values only 0 and 1, the only substantive cells are
   its positive-probability zero and one cells.

There is no support-stability condition, and no independence between units or
between predictions and the outcome schedule is required. Calibration is an
exposure-specific first-moment condition on F, not an assumption directly
equating the adjusted outcome estimator's expectation with its target. The
docstring (`Challenge/Part1.lean:62–64`) describes these three cases and
the ordinary moment requirements.

Junk-value audit:

* N and all π_i are positive. Mean independence only divides at positive
  cells; calibration uses positive π_i. No division by zero is used.
* All actual means have absolute summability from the explicit moment
  assumptions and finite sums. Exposure moments of F are redundant with
  full first moments, because restriction decreases the absolute sum.
  The theorem does not rely on nonsummable signed means becoming zero.
* Event probabilities always exist by domination by p. All-predicate
  independence is naturally interpreted on a discrete atomic model; no
  nonmeasurable integral is evaluated. Whether the atomic framework covers
  the intended scope of a claim cannot be judged until step 2.
* N=0 is excluded; Ω cannot be empty. No other junk-value-sensitive
  operation from the requested checklist occurs.

## SAP.P061b.T21

`T21Statement` (`Defs/Part4.lean:72`) universally quantifies a family of
assignment types Ω:ℕ→Type; for every population size n, an atomic p_n on
Ω_n; schedules g_n,y_n:Fin n→Ω_n→ℝ; a single real exposure d; and two
real sequences b,c:ℕ→ℝ. In the notation above with subscript n, its
hypotheses are:

1. b_n≥0 and c_n≥0 for every n (including n=0).
2. π_{n,i}^d>0 for every n and i:Fin n.
3. For every n, g_n,y_n satisfy support stability for p_n.
4. For every n,i,
   P_n(|(if g_{n,i}=d then y_{n,i} else 0)/π_{n,i}^d|>c_n)=0.
   This is an almost-sure bound on the individual inverse-probability
   weighted outcome, not a pointwise bound at zero-mass assignments.
5. For every n,
   ∑i∑j |q_{n,ij}^{dd}−π_{n,i}^d π_{n,j}^d|=b_n.
6. b_{n+1}/(n+1)² → 0 as n→∞ in ℕ.
7. b_{n+1} c_{n+1}²/(n+1)² → 0 as n→∞ in ℕ.

All quantifiers on b,c precede these hypotheses. Limits are Mathlib
`Filter.Tendsto` from `atTop` on ℕ to the ordinary real neighborhood filter
of zero. The conclusion is: for every real ε>0,

P_{n+1}(|H_{n+1}^d−A_{n+1}^d|>ε) → 0 as n→∞.

It is convergence of the estimation error to zero in probability in the
sequence of separate designs, not almost-sure convergence or convergence of
the estimands themselves. The docstrings at `Challenge/Part1.lean:67–69`
and `Defs/Part4.lean:71` describe boundedness/dependence conditions, support
stability, and the positive-population indexing.

Junk-value audit:

* The family includes n=0, for which sums over `Fin 0` are empty, forcing
  b_0=0; unit-indexed conditions and stability are then vacuous. Although
  H_0 and A_0 would use inverse zero if evaluated, neither is used in
  a limit or in the conclusion: every denominator there is n+1>0.
* All marginal denominators in unit-indexed conditions are positive.
  Zero c_n is permitted and is a legitimate bound, not a denominator.
* Probability-zero tail bounds and positivity imply an ordinary bound
  at every positive-mass assignment. Finitely many units then give finite
  selected first and second moments for each positive population; support
  stability also independently supplies the selected moments. Hence
  target means and error probabilities do not rely on nonsummable defaults.
* The dependence sums are finite. There is no limsup/liminf, `sInf`/`sSup`,
  extended-real `toReal`, log, square root, rpow, natural subtraction, or
  partially defined function. Casts of n+1 to ℝ are positive and exact.
