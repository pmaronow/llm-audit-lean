# Blind reading of the Lean statements

This file was written after reading only the supplied Defs and Challenge Lean
files and relevant Mathlib definitions, before opening `claims.json` or
`record.json`. Descriptions below unpack the propositions, not their docstrings.

## Common objects and conventions

An `AtomicDesign Ω` is a function p : Ω → ℝ on an arbitrary assignment type Ω,
with p(z) ≥ 0 for every z, an unconditionally summable family p, and
Σ_z p(z) = 1. Ω need not be finite or countable, but the positive-mass support
is at most countable. An empty Ω cannot carry such a design. Its support is
S = {z : p(z) > 0}. All zero-mass feasible assignments remain in Ω.

A schedule for population size N ∈ ℕ is an array x_i(z) ∈ ℝ indexed by
i ∈ Fin N = {0,…,N−1}, z ∈ Ω. The exposure schedule g and outcome schedule y
are arbitrary such arrays unless a hypothesis below restricts them. Exposures
are real labels; they are not required to be binary except in named examples.

For every predicate A on Ω, P_D(A) = Σ_z 1_A(z)p(z). For every real function X,
E_D X = Σ_z p(z)X(z). This is Mathlib's unconditional `tsum`, not an extended
real sum: for a nonsummable real family, its value is *defined to be zero*.
`HasFirstMoment D X` expressly means Σ_z p(z)|X(z)| is summable. Event sums
are always summable by domination by p, but means need a separate argument.
The assertion that means are intended only for integrable functions is a
comment, not a type restriction on `designMean`.

Write π_i(a) = P_D(g_i=a), π_ij(a,b) = P_D(g_i=a and g_j=b), and
I_i(a,z) = 1 if g_i(z)=a and 0 otherwise. Then:

- μ_i(a) = E_D[1_{g_i=a} y_i] / π_i(a) (`exposureMean`).
- μ̄(a) = N⁻¹ Σ_i μ_i(a) (`averageExposureMean`).
- τ_i(a,b) = μ_i(a)−μ_i(b), τ̄(a,b) = μ̄(a)−μ̄(b).
- H_a(z) = N⁻¹ Σ_i 1_{g_i(z)=a}y_i(z)/π_i(a) (`htMean`).
- H_ab(z) = H_a(z)−H_b(z) (`htDifference`).
- M_{a,n}(z) = n⁻¹ Σ_i 1_{g_i(z)=a}y_i(z) (`exposedMean`): n is a
  supplied fixed natural denominator; this definition does not assert that n
  units are exposed at z.
- Var_D(X) = E_D[(X−E_D X)²]; Cov_D(X,Y) =
  E_D[(X−E_D X)(Y−E_D Y)]. No moment is built into either definition.

All inverses and division here are in ℝ, including casts of N and n. Lean
sets 0⁻¹=0 and x/0=0. Finite sums over Fin 0 are zero. Positive-denominator
hypotheses must therefore be read explicitly.

`PositiveExposure D g a` means there exists a real c>0 such that, for *every*
i ∈ Fin N, c ≤ π_i(a). Since N is finite, for N>0 this is equivalent to
positivity of every π_i(a). `ExposureMoment D g y a` means, for every i,
Σ_z p(z)|1_{g_i(z)=a}y_i(z)| is summable.

`SupportStable D g y` says: for every i,z,w, if z,w ∈ S and g_i(z)=g_i(w),
then y_i(z)=y_i(w). `GloballyStable g y` says the same equality for every
i,z,w ∈ Ω without support conditions.

The observed-data law evaluated at any predicate A on Ω × ℝ^N is
P_D(A(z,(y_i(z))_i)). Predicates are unrestricted; no sigma algebra or
measurability restriction is present. In this atomic setting the probabilities
are sums over all satisfying assignments.

`EventIndependent D X Y` means, for every predicate E on the range type of X
and every predicate F on the range type of Y,
P_D(E(X) and F(Y)) = P_D(E(X))P_D(F(Y)).
`MeanIndependent D F I` means, for every real b such that P_D(I=b)>0,
E_D[1_{I=b}F]/P_D(I=b) = E_D F.

The normalized covariance expression is
C(a,b) = N⁻² Σ_i Σ_j
[(π_ij(a,b)−π_i(a)π_j(b))/(π_i(a)π_j(b))] μ_i(a)μ_j(b).
The indicator expression is
V_I(a) = N⁻² Σ_i Σ_j Cov_D(I_i(a),I_j(a))
μ_i(a)μ_j(a)/(π_i(a)π_j(a)).

The usual variance estimate is
Vhat_a(z) = N⁻² Σ_i Σ_j
[(π_ij(a,a)−π_i(a)π_j(a))/(π_i(a)π_j(a))]
y_i(z)y_j(z)1_{g_i(z)=a,g_j(z)=a}/π_ij(a,a).
The conservative estimate Vtilde_a uses this summand if π_ij(a,a)>0;
if π_ij(a,a)=0 it instead uses
1_{g_i(z)=a}y_i(z)²/(2π_i(a)) +
1_{g_j(z)=a}y_j(z)²/(2π_j(a)); otherwise its summand is zero.
All i,j are ordered pairs, including diagonal pairs. The definitions give
real values even at zero denominators; theorems must make these harmless.

For a prediction schedule F, the adjusted mean is
A_a(z) = N⁻¹ Σ_i 1_{g_i(z)=a}(y_i(z)−F_i(z))/π_i(a)
       + N⁻¹ Σ_i F_i(z).
`PredictionCalibrated D g F a` says, separately for every i,
E_D[1_{g_i=a}F_i/π_i(a)] = E_D F_i.

### Explicit finite examples

The household space is Ω = {0,1}² and N=2. Own assignment is g_0(z)=z_0,
g_1(z)=z_1; housemate assignment is h_0(z)=z_1, h_1(z)=z_0.
`oneTreated` puts mass 1/2 at (0,1) and (1,0), zero elsewhere.
`bothOrNeither` puts mass 1/2 at (0,0) and (1,1), zero elsewhere.
`independentHousehold` puts mass 1/4 at all four assignments.
`attenuatedOutcome` is 1/2 at (0,0),(1,1), and otherwise is own assignment.
`amplifiedOutcome` is 1 at (1,1), and 0 at the other three assignments, for
each unit.

The version space is Ω={0,1,2}², N=2. `versionResponse` is the unit's own
coordinate, and `versionCategory` is 0 for own coordinate 0 and 1 for own
coordinate 1 or 2. For v=1 or v=2, `oneVersionTreated v` puts mass 1/2 on
(0,v),(v,0) and zero on all other version assignments.

## T12

This theorem is the conjunction of seven assertions:

1. For every Ω,N,D,g,y and every family h_i : ℝ→ℝ, if for every i,z,
   y_i(z)=h_i(g_i(z)), then for every pair d,e of real exposure labels,
   assuming N>0, π_i(d)>0 for all i and π_i(e)>0 for all i, one has for
   every i: μ_i(d)=h_i(d), μ_i(e)=h_i(e),
   τ_i(d,e)=h_i(d)−h_i(e); and
   τ̄(d,e)=N⁻¹Σ_i(h_i(d)−h_i(e)). The factorization assumption precedes
   the choice of d,e. No separate moment assumption occurs.
2. For every Ω,N and two designs D,D′ on that same Ω, and every g,y, if y
   is globally stable with respect to g, then for every d,e, assuming N>0
   and all d,e margins positive under both designs, all μ_i(d) and μ_i(e)
   agree between D and D′, and τ̄(d,e) agrees between D and D′.
3. For every Ω,N,D,g,y with global stability, for every i,d with π_i(d)>0
   and every z ∈ Ω with g_i(z)=d, μ_i(d)=y_i(z). This includes z outside
   support; N>0 is implicit from the existence of i, not an explicit premise.
4. Housemate assignment as both g and y is globally stable.
5. For every design D on the four household assignments, if every unit has
   positive housemate exposure probabilities at 1 and 0, the average
   contrast with g=y=housemate assignment, d=1,e=0, is 1.
6. That same contrast is 1 for `bothOrNeither`.
7. That same contrast is 1 for `independentHousehold`.

## T13

For every Ω,N,D,g,y, the following four statements hold together:

1. If support stability holds, then (i) for every i,d with π_i(d)>0 and
   every supported z with g_i(z)=d, μ_i(d)=y_i(z); (ii) for every i,d,e
   with both margins positive and all supported z,w in those respective
   cells, τ_i(d,e)=y_i(z)−y_i(w); and (iii) there exists one schedule y′
   on the *whole original Ω* that is globally stable, agrees with y at
   every unit and supported assignment, and gives the same observed-data
   probability for every predicate A on Ω × ℝ^N.
2. Global stability implies support stability.
3. For every schedule y′, if it agrees with y at every unit and supported
   assignment, then its observed-data probabilities agree with those of y
   for every predicate A. No stability is required for this assertion.
4. For every function L from predicates on Ω × ℝ^N to ℝ, there exists a
   support-stable schedule w whose observed-data probabilities equal L on
   every A if and only if there exists a globally stable schedule w with
   those same probabilities. L need not initially be a probability law.

There is no N>0, positivity or moment assumption on the whole theorem;
positive-cell premises occur exactly in the identification clauses.

## T14

There are no external parameters or hypotheses. For g=own assignment and
y=housemate assignment, the theorem asserts all of:

- Under `oneTreated`, μ̄(1)=0, μ̄(0)=1 and τ̄(1,0)=−1.
- Support stability holds under `oneTreated`, but global stability fails.
- τ̄(1,0)=1 under `bothOrNeither` and 0 under `independentHousehold`.
- For unit 0, own assignment is 1 at both (1,0) and (1,1), whereas its
  housemate outcomes are respectively 0 and 1.
- (1,1) is outside `oneTreated`'s positive support.

## T15

There are no external parameters or hypotheses. Two blocks are conjoined:

1. For g=own assignment and y=attenuated outcome, τ̄(1,0) equals 1 under
   `oneTreated` and 0 under `bothOrNeither`; each design has support
   stability, and global stability fails. For g=own assignment and
   y=amplified outcome, those contrasts are respectively 0 and 1; each
   design again has support stability, and global stability fails.
2. In the version example, for every i, both exposure-category margins
   (0 and 1) are 1/2 under each of the v=1 and v=2 designs. Using the same
   category g and response y on all nine assignments, τ̄(1,0)=1 under v=1
   and 2 under v=2. Each design has support stability, but global stability
   of the response under the category mapping fails. Finally, for every
   i,z,w, equality of the unit's *actual own version coordinate* between z
   and w implies equality of its responses. Thus the response has no
   dependence on the housemate once the actual own version is fixed.

## T16

The theorem negates `GeneralHTUnbiased`. That proposition universally
quantifies over every Ω,N,D,g,y,d,e, and assumes only N>0 and
`PositiveExposure` at d and e. Its conclusion is the conjunction:
H_d has a first absolute moment; H_de has a first absolute moment;
E_D H_d=μ̄(d); and E_D H_de=τ̄(d,e).

Consequently T16 says that there exists some such Ω,N,D,g,y,d,e with
positive N and the two uniform positive margin bounds, for which at least
one of these four conclusions fails. It does not exhibit that instance
or assert that both finite means exist and are unequal to their targets.
There is no integrability assumption on y or its exposed cells in the
proposition being negated. The target means themselves are totalized tsums.

## T17

Two universally quantified assertions are conjoined:

1. For every Ω,N,D,g,y,d,n, if N>0, n>0 and π_i(d)=n/N for every i,
   then for every z ∈ Ω, H_d(z)=M_{d,n}(z). There is no assumption of
   stability, a fixed exposed count, or membership of z in support.
2. For every N, every design D on the *entire binary cube* Ω={0,1}^N,
   every real outcome schedule y on that cube, and every n ∈ ℕ, assume
   0<n<N and `UniformFixedCount D n`. The latter means, for every z,
   p(z)=1/binomial(N,n) if exactly n coordinates of z equal 1, and p(z)=0
   otherwise. With g_i(z) the real value of binary coordinate z_i, for
   every i one has π_i(1)=n/N and π_i(0)=(N−n)/N; furthermore
   E_D[M_{1,n}−M_{0,N−n}]=τ̄(1,0). N−n is natural subtraction before
   casting to ℝ, and n<N prevents its being zero. All schedules y on the
   finite cube are allowed, including interference. There is no result
   here about surveys on general assignment spaces or census contrasts.

## T18

For every Ω,N,D,g,y,d,e, assume N>0, each unit has positive margins at
both d and e, and support stability holds for g,y under D. Then all of:

1. For every i and every supported z,
   1_{g_i(z)=d}y_i(z)=1_{g_i(z)=d}μ_i(d).
2. For every supported z,
   H_d(z)=N⁻¹Σ_i 1_{g_i(z)=d}μ_i(d)/π_i(d).
3. Var_D(H_d)=V_I(d).
4. Var_D(H_d)=C(d,d).
5. Cov_D(H_d,H_e)=C(d,e).
6. Var_D(H_de)=Var_D(H_d)+Var_D(H_e)−2Cov_D(H_d,H_e).
7. For every i, π_ii(d,d)=π_i(d).
8. If d≠e, then for every i, π_ii(d,e)=0.

No explicit first or second moment assumptions occur. Stability on the
finite set of relevant unit cells is what can make these expressions
integrable despite arbitrary outcomes elsewhere on Ω.

## T19

For every Ω,N,D,g,y,d, assume N>0, all π_i(d)>0, and support stability.
Then the following three assertions hold together:

1. If π_ij(d,d)>0 for *every ordered pair* i,j, then
   E_D Vhat_d=Var_D(H_d) and E_D Vhat_d=C(d,d).
2. Without that additional joint-positivity assumption,
   E_D Vtilde_d ≥ Var_D(H_d).
3. For every i,j,
   |μ_i(d)μ_j(d)| ≤ μ_i(d)²/2 + μ_j(d)²/2.

This asserts no impossibility theorem for estimators of products when
some joint probability vanishes. It quantifies over no class of estimators.

## T20

For every Ω,N,D,g,y,F,d, assume N>0, π_i(d)>0 for every i,
`ExposureMoment D g y d`, a first absolute moment for every F_i, and
`ExposureMoment D g F d`. All three of the following implications hold:

1. If F is prediction calibrated at d, then A_d has a first absolute
   moment and E_D A_d=μ̄(d).
2. If for every i the exposure indicator I_i(d) and F_i are independent
   in the predicate-based sense above, then F is prediction calibrated,
   A_d has a first absolute moment and E_D A_d=μ̄(d).
3. If for every i, F_i is mean-independent of I_i(d), then F is prediction
   calibrated, A_d has a first absolute moment and E_D A_d=μ̄(d).

There is no stability hypothesis, no condition comparing predictions to
outcomes, and no hypothesis that predictions are nonrandom. Calibration
is a sufficient condition explicitly supplied in the first implication;
the other two implications derive it from their respective hypotheses.

## T21

For every family Ω_N of assignment types indexed by all N ∈ ℕ, every
family of designs D_N on Ω_N, every pair of schedule families g_N,y_N
with N units, every fixed real exposure label d, and every pair of real
sequences b_N,c_N, assume, in this order:

1. b_N≥0 for every N.
2. c_N≥0 for every N.
3. π_{N,i}(d)>0 for every N and every i ∈ Fin N.
4. Support stability for D_N,g_N,y_N for every N.
5. For every N,i, the event
   |1_{g_{N,i}=d}y_{N,i}/π_{N,i}(d)|>c_N has D_N-probability zero.
6. For every N,
   Σ_iΣ_j |π_{N,ij}(d,d)−π_{N,i}(d)π_{N,j}(d)|=b_N.
7. b_{N+1}/(N+1)² → 0 as N→∞.
8. b_{N+1}c_{N+1}²/(N+1)² → 0 as N→∞.

The conclusion is: for every ε ∈ ℝ with ε>0,
P_{D_{N+1}}(|H_{N+1,d}−μ̄_{N+1}(d)|>ε) → 0 as N→∞.
Each sequence limit is the Mathlib filter statement `Tendsto … atTop
(nhds 0)`, equivalently the usual real sequence limit. All population
denominators used in these limits are positive N+1. Assumptions at N=0
have empty unit sums, but the conclusion ranges over all positive sizes.

## Mathlib sources checked

- `Topology/Algebra/InfiniteSum/Defs.lean`: `HasSum` is convergence of
  finite-subset sums along the unconditional summation filter; `Summable`
  means existence of such a real limit; `tsum` is zero when none exists.
- `Order/Filter/Defs.lean`: `Tendsto f l₁ l₂` is `map f l₁ ≤ l₂`.
- `Order/Filter/AtTopBot/Defs.lean`: natural `atTop` is the filter of tails.
- `Topology/Defs/Filter.lean`: `nhds` is the neighborhood filter.
- `Algebra/GroupWithZero/Defs.lean`: `inv_zero`, hence real division by zero.
- `Algebra/BigOperators/Group/Finset/Defs.lean` and
  `Algebra/BigOperators/Fin.lean`: finite sums and Fin-index sums.
- `Data/Nat/Choose/Basic.lean`: natural binomial coefficients, including
  zero outside their range. T17's n<N keeps its coefficient positive.
