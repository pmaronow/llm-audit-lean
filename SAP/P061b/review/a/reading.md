# Blind mathematical reading

This file was written after reading only `SAP/P061b/Defs*.lean`, their parts,
`SAP/P061b/Challenge*.lean`, their parts, and the relevant permitted Mathlib
definitions. Neither `claims.json` nor `record.json` has been opened. The
theorems below are read as propositions, without relying on their `sorry` proofs
or treating their docstrings as additional hypotheses or conclusions.

## Common objects and fully expanded notation

* `N` is a natural number and the unit index set is `Fin N`, that is,
  `{0,...,N-1}`. Sums over units are finite sums over this entire set. Unless a
  theorem explicitly assumes `N > 0`, zero is permitted.
* `Ω : Type` is an arbitrary assignment set. There is no finiteness,
  countability, topology, sigma algebra, or full-support assumption on it.
  An `AtomicDesign Ω` consists of a real function `p` with `p(z) ≥ 0` for every
  assignment, `Summable p`, and `∑' z, p(z) = 1`. Its support is
  `S = {z : p(z) > 0}`. Zero-mass assignments remain in Ω. An empty Ω cannot
  carry such a design. The positive support is at most countable.
* A schedule is an arbitrary function `(i,z) ↦ g_i(z)` or `y_i(z)` in ℝ,
  indexed by `i ∈ Fin N` and `z ∈ Ω`. Predictions `F` have the same type.
* Write `P(A) = ∑' z, 1_A(z) p(z)` and `E X = ∑' z, p(z)X(z)`.
  The first-moment predicate is `∑' z, p(z)|X(z)|` being summable, not merely
  that a totalized real-valued `E X` can be written down.
* In Mathlib, `HasSum f a` is convergence to `a` of the net of finite subsums,
  `Summable f` means that such an `a` exists, and `tsum f` (`∑'`) is this sum
  if it exists and **zero otherwise**. For real families unconditional
  summability is absolute summability. This is not a conditionally convergent
  ordered series. Sources: `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`,
  definitions `HasSum`, `Summable`, `tsum` (generated additively from the
  displayed product definitions). Events above are always summable by
  domination by `p`. A signed mean requires separate justification.
* `π_i(d) = P(g_i=d)` and `π_ij(d,e) = P(g_i=d and g_j=e)`.
  `PositiveExposure D g d` means `∃ c ∈ ℝ, c>0 and ∀i, c≤π_i(d)`;
  the witness is uniform over units in this one finite population, not over
  all population sizes. `ExposureMoment D g y d` means that, for every unit,
  `z ↦ 1_{g_i(z)=d} y_i(z)` has a first moment.
* Define `μ_i(d) = E[1_{g_i=d} y_i] / π_i(d)`,
  `μ̄(d) = N⁻¹ ∑_i μ_i(d)`, `τ_i(d,e) = μ_i(d)-μ_i(e)`, and
  `τ̄(d,e) = μ̄(d)-μ̄(e)`. These are respectively `exposureMean`,
  `averageExposureMean`, `unitContrast`, and `averageContrast`.
* Define `H_d(z) = N⁻¹ ∑_i 1_{g_i(z)=d} y_i(z)/π_i(d)` and
  `H_de = H_d-H_e`. These are `htMean` and `htDifference`.
  `M_{d,n}(z) = n⁻¹ ∑_i 1_{g_i(z)=d} y_i(z)` is `exposedMean`, a
  fixed-denominator sum; it is not defined using the realized exposed count.
  Casts of natural denominators are into ℝ. Real inverse and division are
  totalized: `0⁻¹=0` and `a/0=0`. Positivity hypotheses below must be read
  explicitly; a definition by itself does not exclude this convention.
* Global stability means `∀i,z,w, g_i(z)=g_i(w) ⇒ y_i(z)=y_i(w)`.
  Support stability for D means the same implication only when both `z,w∈S`.
* `observedEventProbability D y A` is the probability of
  `A(z,(y_i(z))_i)`, for **every predicate** `A` on
  `Ω × (Fin N → ℝ)`. Equality for all such `A` is equality of the laws of
  the observed assignment together with the complete observed response vector.
* `Var(X) = E[(X-E X)^2]` and `Cov(X,Y) = E[(X-E X)(Y-E Y)]` are the
  literal definitions of `designVariance` and `designCovariance`. Their
  definitions alone impose no first or second moments.
* Put `I_i^d(z)=1` when `g_i(z)=d`, otherwise `0`, and set
  `K_ij(d,e)=(π_ij(d,e)-π_i(d)π_j(e))/(π_i(d)π_j(e))`.
  The functions used in T18 and T19 are exactly

  ```text
  C(d,e) = N⁻² Σ_i Σ_j K_ij(d,e) μ_i(d) μ_j(e)
  V_I(d) = N⁻² Σ_i Σ_j Cov(I_i^d,I_j^d) μ_i(d) μ_j(d)/(π_i(d)π_j(d))
  Vhat_d(z) = N⁻² Σ_i Σ_j K_ij(d,d) y_i(z)y_j(z) I_i^d(z)I_j^d(z)/π_ij(d,d).
  ```

  Here `C` is `covarianceSum`, `V_I` is `indicatorVarianceSum`, and `Vhat`
  is `htVarianceEstimate`. The conservative estimate `Vplus_d(z)` is
  `N⁻² Σ_i Σ_j B_ij(z)`, with the **ordered** pair contribution

  ```text
  B_ij(z) = K_ij(d,d)y_i(z)y_j(z)I_i^d(z)I_j^d(z)/π_ij(d,d), if π_ij(d,d)>0;
          = I_i^d(z)y_i(z)^2/(2π_i(d)) + I_j^d(z)y_j(z)^2/(2π_j(d)), if π_ij(d,d)=0;
          = 0, otherwise.
  ```

  The last branch is unreachable for an atomic design, since event
  probabilities are nonnegative. This branching avoids using a zero joint
  probability as a denominator in the conservative estimate.
* `A_d(z) = N⁻¹ Σ_i I_i^d(z)(y_i(z)-F_i(z))/π_i(d) + N⁻¹ Σ_i F_i(z)`
  is `adjustedMean`. Prediction calibration means
  `∀i, E[I_i^d F_i/π_i(d)] = E F_i`.
* `EventIndependent D X Y` means
  `∀ predicates E,F, P(E(X) and F(Y))=P(E(X))P(F(Y))`.
  `MeanIndependent D F I` means
  `∀ b∈ℝ, P(I=b)>0 ⇒ E[1_{I=b}F]/P(I=b)=E F`.
  Neither definition itself includes moment assumptions.
* `UniformFixedCount D n` is defined only on `Ω=(Fin N → Fin 2)`:
  every assignment `z` has mass `1/binomial(N,n)` if exactly `n` coordinates
  equal 1, and mass 0 otherwise. The cardinality and subtraction in this
  definition and in T17 are natural-number operations; `N-n` is truncated
  subtraction, though T17 explicitly assumes `n<N` where it is used.
* `Tendsto f atTop (𝓝 0)` for a real sequence has its ordinary meaning:
  for every `δ>0`, eventually `|f(N)|<δ`. Mathlib defines `Tendsto` as
  `Filter.map f atTop ≤ 𝓝 0`; `atTop` on ℕ is the filter of tails and
  `𝓝 0` is the usual real neighborhood filter. There is no `limsup` here.

## Concrete schedules and designs

`Household = Fin 2 × Fin 2` consists of `(a,b)∈{0,1}²`. Unit 0's own
assignment is `a`, unit 1's is `b`; their housemate assignments are `b,a`.
Write `D1=oneTreated`, with masses 1/2 at `(0,1),(1,0)` and 0 elsewhere;
`D2=bothOrNeither`, with masses 1/2 at `(0,0),(1,1)` and 0 elsewhere;
and `DI=independentHousehold`, with mass 1/4 at all four assignments.
The attenuation outcome is 1/2 if `a=b`, otherwise the unit's own assignment.
The amplification outcome, for either unit, is 1 if `(a,b)=(1,1)`, otherwise 0.

`VersionHousehold = Fin 3 × Fin 3` consists of `(a,b)∈{0,1,2}²`.
`versionResponse` is the unit's own coordinate, interpreted as a real.
`versionCategory` is 0 when that coordinate is 0, otherwise 1.
For `v=1` or `2`, `Dv=oneVersionTreated v` puts mass 1/2 at `(0,v),(v,0)`
and 0 elsewhere. Its definition takes a proof that `v=1 or v=2`.

## SAP.P061b.T12

The conjunction of the following seven assertions, with separate quantifiers:

1. For every Ω,N,D,g,y and every family `h_i:ℝ→ℝ`, if
   `∀i,z, y_i(z)=h_i(g_i(z))`, then for every **subsequently chosen** real
   `d,e`, if `N>0`, `∀i π_i(d)>0`, and `∀i π_i(e)>0`, then for every unit
   `μ_i(d)=h_i(d)`, `μ_i(e)=h_i(e)`, and
   `τ_i(d,e)=h_i(d)-h_i(e)`, and
   `τ̄(d,e)=N⁻¹ Σ_i(h_i(d)-h_i(e))`.
2. For every Ω,N, two designs D,D' on Ω, and g,y, if global stability
   holds, then for every d,e with `N>0` and both exposure probabilities
   positive for every unit under each of D and D', the unit exposure means
   at d and e agree between designs, and so do their average contrasts.
3. For every Ω,N,D,g,y, if global stability holds, then for every i,d
   with `π_i(d)>0` and every z with `g_i(z)=d`, `μ_i(d)=y_i(z)`.
   Here z need not be supported. No separate `N>0` hypothesis appears.
4. Housemate exposure with housemate outcome is globally stable.
5. For every design D on Household with both 0 and 1 housemate exposures
   positive for both units, its average contrast for housemate exposure
   and housemate outcome at `(1,0)` is 1.
6. This same average contrast under D2 is 1.
7. This same average contrast under DI is 1.

## SAP.P061b.T13

For every Ω,N,D,g,y (no `N>0` or exposure-positivity hypothesis), all four
of the following hold:

1. **If** support stability holds, then (a) for every i,d with `π_i(d)>0`,
   every supported z with `g_i(z)=d` has `μ_i(d)=y_i(z)`; (b) for every
   i,d,e with both probabilities positive, every supported z,w with
   exposures d,e has `τ_i(d,e)=y_i(z)-y_i(w)`; and (c) **there exists** a
   schedule y' that is globally stable, agrees with y for all units at
   all supported assignments, and has the same observed-event probabilities
   as y for **every** predicate A.
2. Global stability implies support stability for this design.
3. For **every** schedule y', if it agrees with y on every supported
   assignment and unit, its observed-event probability equals y's for
   every predicate A. This implication does not require stability.
4. For **every** real-valued functional L on all observed-data predicates,
   there exists a support-stable schedule w whose observed-event probabilities
   equal L at every predicate if and only if there exists a globally stable
   schedule w with that property. L is not assumed a priori to be a law.

## SAP.P061b.T14

A closed conjunction, without universally quantified inputs or hypotheses.
Use own assignment as exposure and housemate assignment as outcome:
under D1, `μ̄(1)=0`, `μ̄(0)=1`, `τ̄(1,0)=-1`, and support stability holds;
global stability fails. The same schedule's contrasts under D2 and DI are
respectively 1 and 0. Unit 0's own assignments at `(1,0)` and `(1,1)` are
both 1, its outcomes there are respectively 0 and 1, and `(1,1)` is outside
D1's support. All these equalities and (non)stability statements are conjuncts.

## SAP.P061b.T15

A closed conjunction of two groups:

1. With own assignment as exposure, the attenuation outcome has contrasts
   1 under D1 and 0 under D2. It is support stable under each design and
   is not globally stable. The amplification outcome has contrasts 0 under
   D1 and 1 under D2, is support stable under each design, and is not globally
   stable.
2. With versionCategory as exposure and versionResponse as outcome, for
   every `i∈Fin 2` both the 0 and 1 exposure probabilities equal 1/2 under
   **each** of Dv=1 and Dv=2. The contrasts are respectively 1 and 2.
   The schedules are support stable under each of these designs but not
   globally stable. Finally, for **every** unit i and version assignments
   z,w, equality of the unit's own version coordinate implies equality
   of its versionResponse. That last statement concerns full own version,
   not merely the binary exposure category.

## SAP.P061b.T16

The negation of the following universal assertion (`GeneralHTUnbiased`):
for every Ω,N,D,g,y and real d,e, `N>0`, positive exposure at d, and positive
exposure at e imply the **conjunction**

```text
H_d has an absolute first moment;
H_de has an absolute first moment;
E H_d = μ̄(d);
E H_de = τ̄(d,e).
```

Thus, classically, there is some Ω,N,D,g,y,d,e with those three hypotheses
for which at least one of these four conclusions fails. No moment or
stability hypothesis is included in the negated universal statement. The
theorem does not itself specify a witness, require `d≠e`, or select which
conjunct fails. In particular, failure of existence of a first moment is
sufficient; it need not assert unequal existing finite expectations.

## SAP.P061b.T17

The conjunction of two separately quantified assertions:

1. For every Ω,N,D,g,y,d,n in that order, if `N>0`, `n>0`, and every unit
   has `π_i(d)=n/N`, then **for every assignment z**, including zero-mass
   assignments, `H_d(z)=M_{d,n}(z)`. There is no assumption about the
   realized exposure count, stability, or moments.
2. For every N, design D on the **entire binary cube** `(Fin N→Fin 2)`,
   arbitrary outcome schedule y on that cube, and n, if `0<n<N` and D is
   UniformFixedCount n, then for every unit the own-assignment exposures
   have probabilities `π_i(1)=n/N` and `π_i(0)=(N-n)/N`, and
   `E[M_{1,n}-M_{0,N-n}]=τ̄(1,0)`. There is no stability assumption.
   This second assertion is not quantified over arbitrary larger Ω.

## SAP.P061b.T18

For every Ω,N,D,g,y,d,e, **if**, in order, `N>0`, every unit's probabilities
at d and e are positive, and support stability holds, all these hold:

1. For every unit and every supported z,
   `1_{g_i(z)=d}y_i(z)=1_{g_i(z)=d}μ_i(d)`.
2. For every supported z,
   `H_d(z)=N⁻¹ Σ_i 1_{g_i(z)=d}μ_i(d)/π_i(d)`.
3. `Var(H_d)=V_I(d)`.
4. `Var(H_d)=C(d,d)`.
5. `Cov(H_d,H_e)=C(d,e)`.
6. `Var(H_de)=Var(H_d)+Var(H_e)-2 Cov(H_d,H_e)`.
7. For every unit i, `π_ii(d,d)=π_i(d)`.
8. If **additionally** `d≠e`, then for every unit `π_ii(d,e)=0`.

All stability assumptions refer to the whole schedule, though the first
two conclusions only refer to exposure d. No joint positivity is assumed.

## SAP.P061b.T19

For every Ω,N,D,g,y,d, if `N>0`, all `π_i(d)>0`, and support stability holds,
the following three assertions hold:

1. **If additionally** `∀i,j, π_ij(d,d)>0`, then
   `E Vhat_d=Var(H_d)` and `E Vhat_d=C(d,d)`.
2. Without that additional joint-positivity hypothesis,
   `E Vplus_d ≥ Var(H_d)`.
3. For every ordered pair of units,
   `|μ_i(d)μ_j(d)| ≤ μ_i(d)^2/2 + μ_j(d)^2/2`.

There is no statement quantifying over all possible estimators or asserting
their impossibility. Marginal positivity applies to all three parts; joint
positivity applies only to part 1.

## SAP.P061b.T20

For every Ω,N,D,g,y,F,d, assume in order:
`N>0`; all `π_i(d)>0`; every exposed outcome `I_i^d y_i` has a first moment;
every `F_i` has a first moment; and every exposed prediction `I_i^d F_i`
has a first moment. No stability assumption appears. Then the conjunction:

1. If predictions are calibrated, `A_d` has a first moment and `E A_d=μ̄(d)`.
2. If **for every unit** its exposure indicator and prediction are event
   independent (as defined for all predicates above), then predictions are
   calibrated, `A_d` has a first moment, and `E A_d=μ̄(d)`.
3. If **for every unit** its prediction is mean independent of its exposure
   indicator (in the order `MeanIndependent F_i I_i^d` defined above), the
   same three conclusions hold.

The hypotheses preceding the conjunction also apply to parts 2 and 3.

## SAP.P061b.T21

For every family of assignment types `Ω_N` for `N∈ℕ`, every family of
designs `D_N`, exposure and outcome schedules `g_N,y_N` with **exactly N
units** at index N, real d, and real sequences b,c, assume in order:

1. `∀N, b_N≥0`.
2. `∀N, c_N≥0`.
3. For every N and unit i in that population, `π_{N,i}(d)>0`.
4. For every N, `y_N` is support stable relative to `D_N,g_N`.
5. For every N,i,
   `P_N(|I_{N,i}^d y_{N,i}/π_{N,i}(d)|>c_N)=0`.
6. For every N,
   `Σ_i Σ_j |π_{N,ij}(d,d)-π_{N,i}(d)π_{N,j}(d)|=b_N`.
7. `b_{N+1}/(N+1)^2 → 0` as N tends to infinity.
8. `b_{N+1} c_{N+1}^2/(N+1)^2 → 0` as N tends to infinity.

Then, **for every subsequently quantified real ε>0**,

```text
P_{N+1}(|H_{N+1,d} - μ̄_{N+1}(d)| > ε) → 0.
```

All denominators in the limits and conclusion are population sizes N+1,
which are strictly positive. Hypotheses also mention the zero-unit population,
where unit quantifiers and double sums are empty and hence `b_0=0`. This
population does not occur in the conclusion. The bound in hypothesis 5 is
almost sure under the atomic design, not a bound at zero-mass assignments.
Hypothesis 6 defines b exactly, not just as an upper bound. This statement
requires the entire displayed set of hypotheses simultaneously.
