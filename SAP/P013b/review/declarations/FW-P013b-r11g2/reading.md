# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. The readings below come only from the Challenge docstrings,
the statements, and their complete closures in `closure.json`.

All finite sums below mean Mathlib `Finset.sum` over `univ`, unless a set or range
is written. `Fin N` means the natural numbers strictly below the natural number
`N`. Real division is Mathlib's total field division, so `x / 0 = 0`.

The shared finite framework, unfolded here for use in each section, is:

* A `Design Ω` is a function `p : Ω → ℝ` on a finite type, together with
  `p(z)>0` for every `z` and `Σ_z p(z)=1`. The constructor and `weight` projection
  carry precisely these data. In particular, a design cannot exist on an empty Ω.
* A `Population P N K` is an arbitrary map `D : Ω → Fin N → Fin K` and a fixed
  array `y : Fin N → Fin K → ℝ`. Its constructor, exposure projection, and outcome
  projection introduce no further assumptions.
* Write `I_id(z)=1` if `D(z,i)=d`, and `0` otherwise. Then
  `π_id=Σ_z p(z)I_id(z)`. `Positivity F d` means **both** `0<π_id` and `π_id<1`
  for every unit i. Observed outcome is `y_i,D(z,i)`.
* For any real function X on Ω, `E X=Σ_z p(z)X(z)`,
  `Cov(X,Y)=Σ_z p(z)X(z)Y(z)-(Σ_z p(z)X(z))(Σ_z p(z)Y(z))`, and
  `Var X=Σ_z p(z)X(z)^2-(Σ_z p(z)X(z))^2`.
* Potential total is `T_d=Σ_i y_id`, potential mean is `T_d/(N:ℝ)`, and causal
  effect is `τ_de=T_d/N-T_e/N`.
* HT total is `H_d(z)=Σ_i I_id(z)(y_id/π_id)`, HT mean is `H_d(z)/N`, and HT
  effect is `(H_d(z)-H_e(z))/N`.
* For a fixed prediction vector g, difference total is
  `A_d(g,z)=Σ_i I_id(z)(y_id/π_id)-Σ_i I_id(z)(g_i/π_id)+Σ_i g_i`.
  Difference effect is `B_de(gk,gl,z)=(A_d(gk,z)-A_e(gl,z))/N`.
* `shiftPopulation F c` keeps D and replaces every y_id by `y_id+c`.
  Superscript c on A, B, T, H, or τ below refers to this replacement. Its π's
  and I's are unchanged. Write `W_id(z)=I_id(z)/π_id`, `C_d(z)=Σ_i W_id(z)`,
  and `L_d(h,c,z)=Σ_i(1-W_id(z))(h_i-c)`. These are, respectively,
  `exposureWeight`, `htCount`, and `translationError`.
* `Recording N K` is just `Fin N → Fin K → Bool`. For a recording array R,
  recorded potential is `q_id=y_id` when R(i,d) is true, and 0 otherwise.
  `recordedPopulation` keeps D and replaces y by q. Write
  `ℓ_d=(Σ_i (if R(i,d) then 0 else y_id))/N` for `lostMean`.
* For arbitrary D on units, real vectors w and G, and a finite unit set U, write
  `U_d(U)=Σ_{i∈U}(if D_i=d then w_i G_i else 0)` and
  `V_d(U)=Σ_{i∈U}(if D_i=d then w_i else 0)`.
  These unfold `recordedNumerator` and `recordedDenominator` completely.
* `recordedData F R` is the function `(z,i) ↦
  (D(z,i), q_i,D(z,i), R(i,D(z,i)))`, with values in `Fin K × ℝ × Bool`.

Every unit declaration listed in the closure has been read, including constructor
and projection declarations. The 41 distinct generated `_proof_` declarations
were inspected by `scratch/ClosureHelpers.lean`: they prove `NeZero` or
`Nat.AtLeastTwo` instances for displayed numerals, positivity and normalization
of the three explicit finite laws, and the scalar-tower instance used in
`designMeasure`. They add no substantive hypotheses or mathematical assertions.
The instances use the intended small `Fin` indices; none wraps an out-of-range
literal to a different index.

## SAP.P013b.T20

Source: `Challenge/Part2.lean:6–17`, `Defs/Part11.lean:12–37`, and the Design and
indicator declarations in `Defs/Part1.lean`.

Quantification is universal, in this order: arbitrary types Ω and A; a finite-type
instance and measurable space on Ω, with every singleton measurable; a measurable
space on A; a measure μ on A with μ(A)=1; natural numbers N and K; a finite
strictly positive normalized design p on Ω; any exposure array
`D:Ω→Fin N→Fin K`; and any sequence `Z:ℕ→A→Ω`.

The three successive premises say that every Z_r is measurable, the entire
sequence is mutually independent (`ProbabilityTheory.iIndepFun`, equivalently
the independence of all finite collections of measurable inverse images), and
the pushforward of μ by every Z_r equals
`ν=Σ_{z∈Ω} ENNReal.ofReal(p(z)) • Measure.dirac z`.
Here `Measure.dirac z` is the unit point mass; scalar multiplication multiplies
the measure by that nonnegative extended-real scalar. Since p(z)>0 and the
weights sum to one, ν is exactly the probability mass law p. On this finite space,
measurable singletons make every subset measurable, hence D's coordinate
indicators are measurable without another premise.

Conclusion: outside a single μ-null set, for **every** `d∈Fin K` and
`i,j∈Fin N`, both of the following hold:

1. As the natural number R tends to infinity,
   `(Σ_{0≤r<R} I_id(Z_r(a))I_jd(Z_r(a)) + 1_{i=j})/(R+1)` tends in the ordinary
   real topology to `Σ_z p(z)I_id(z)I_jd(z)`.
2. For **every** `e∈Fin K` with `d≠e`,
   `(Σ_{0≤r<R} I_id(Z_r(a))I_je(Z_r(a)))/R` tends in the ordinary real topology
   to `Σ_z p(z)I_id(z)I_je(z)`.

This is an entrywise statement, simultaneous for all entries and exposures on one
probability-one event. It does not state rates. The same-exposure conclusion is
outside the quantification over distinct e, so it also applies when K=1.

Junk-value review: the cross ratio at R=0 is 0/0=0; a single initial term cannot
affect `Tendsto` along `atTop`. Its denominator is positive for every R≥1.
The same-exposure denominator R+1 is always positive. `ENNReal.ofReal` truncates
nonpositive inputs, but every p(z)>0, and no weight is infinite; truncation has no
effect. N=0 makes the entry assertions empty; K=0 makes the exposure assertions
empty (and for N>0 no exposure map exists on nonempty Ω). These are the standard
empty-matrix cases, not hidden premises. Real casts of R and R+1 are exact;
there is no natural subtraction or overflow. There is no log, sqrt, rpow,
Bochner integral, `toReal`, extremum, limsup/liminf, or partial-function default.

The docstring describes independent exact-law replicates and both simultaneous
matrix limits, and explicitly acknowledges the harmless R=0 convention and the
usual measurable-space conditions.

## SAP.P013b.T22

Source: `Challenge/Part1.lean:41–44`, `Defs/Part7.lean:16–108`, and the shared
definitions in Parts 1 and 3, including the calibration example.

This is a conjunction of 13 groups, **each with its own universal binders**.
In every generic group Ω is an arbitrary finite type, N and K are natural,
P is a design as defined above, and F is an arbitrary population (D,y).
All predictions and their changes are fixed real vectors on `Fin N`, not functions
of z. Unless indicated otherwise, z is universally quantified after the listed
real scalar and vectors. All symbols in the formulas are the finite sums defined
above, so there is no additional SAP notion left opaque.

1. For every d,g,h,c,z, assuming `N>0` and every π_id>0,
   `A_d^c(g+h,z)-A_d(g,z)=c C_d(z)+Σ_i(1-W_id(z))h_i`.
2. With the same quantifiers and assumptions,
   `A_d^c(g+h,z)-A_d(g,z)-cN=L_d(h,c,z)`.
3. With the same quantifiers and assumptions,
   `A_d^c(g+h,z)=A_d(g,z)+cN ↔ L_d(h,c,z)=0`.
4. For every d,g,c,z with the same assumptions,
   `A_d^c(g+c,z)=A_d(g,z)+cN`, where `(g+c)_i=g_i+c`.
5. For every F with N>0, every d,e,gk,gl,c,z, assuming positive π's at d and e
   and d≠e: `A_d^c(gk+c,z)/N=A_d(gk,z)/N+c` and the analogous e identity;
   for each i exposed to d the residual
   `observed(F^c,z,i)-(gk_i+c)=observed(F,z,i)-gk_i`, and analogously for e;
   `B_de^c(gk+c,gl+c,z)=B_de(gk,gl,z)`;
   `T_d^c=T_d+cN`, `T_e^c=T_e+cN`, and `τ_de^c=τ_de`.
6. For every F with N>0 and every d,e,gk,gl,hk,hl,c,z, assuming positive π's
   at d and e and d≠e:
   `B_de^c(gk+hk,gl+hl,z)-B_de(gk,gl,z)=(L_d(hk,c,z)-L_e(hl,c,z))/N`, and
   equality of the two B's holds iff those two L's are equal.
7. For every F with N>0, d,e,gk,gl,c,z and the same positivity/distinctness:
   `A_d^c(gk,z)-A_d(gk,z)=c C_d(z)`;
   `A_d^c(gk,z)-A_d(gk,z)-cN=c(C_d(z)-N)`;
   `B_de^c(gk,gl,z)-B_de(gk,gl,z)=c(C_d(z)-C_e(z))/N`.
   Additionally, if c≠0, the first A is the old A+cN iff C_d(z)=N, and the new
   B is the old B iff C_d(z)=C_e(z).
8. For every F,d and unit i, if π_id>0, then `Σ_z p(z)W_id(z)=1`. There is no
   global N>0 hypothesis in this group; the given unit already implies N>0.
9. For every F with N>0, d,e,c,z and the positivity/distinctness assumptions,
   `A_d(0,z)=H_d(z)`, `B_de(0,0,z)=(H_d(z)-H_e(z))/N`,
   `H_d^c(z)-H_d(z)=c C_d(z)`, and the difference of shifted and old HT effects
   is `c(C_d(z)-C_e(z))/N`.
10. For every F,d,g,h,c with all π_id>0, without N>0 or a second exposure,
    `Σ_z p(z)L_d(h,c,z)=0`;
    `E A_d^c(g+h)=E A_d(g)+cN=T_d+cN`; and `E C_d=N`.
11. For every F,d,e,c, assuming N>0, d≠e and positive π's at d,e,
    `E[z↦c(C_d(z)-N)]=0` and `E[z↦c(C_d(z)-C_e(z))/N]=0`.
12. For every F with N>0, d, natural m≥1, assuming every assignment has exactly
    m units at d and every π_id=(m:ℝ)/N, for every g,c and **then every z**,
    `C_d(z)=N` and `A_d^c(g,z)=A_d(g,z)+cN`.
13. A fixed example: Ω=Fin 2, each assignment has probability 1/2, N=K=2,
    `D(z,i)=1` iff z=i (otherwise 0), and every y_id=0. Every exposure satisfies
    0<π_id<1; for every z, `C_1(z)=2`, and shifting all outcomes by 1 with
    prediction vector 0 increases the difference total at exposure 1 by 2.

Junk-value review: all inverse π's in generic groups are protected by a positive
π premise, or (group 12) follow from m≥1 and N>0. The calibration π's are 1/2.
Every use of division by N in a conclusion has N>0; group 10 permits N=0 but
uses only sums, totals, and counts, which then vanish. The finite law excludes
empty Ω. Distinct positive exposures with N>0 imply K≥2 and selected π<1,
although the total-only groups permit π=1. There is no division by c; c≠0 is
needed only for the two iff characterizations. There are no logarithms, powers
outside their domains, non-integrable integrals, extended-real conversions,
partial functions, extrema, or limsup/liminf in this closure. The `Fin` numeral
instances for 0 and 1 designate the intended two exposures.

The docstring describes translation identities, equivariance, invariance,
characterizations, mean-zero errors, and fixed-prediction calibration, all of which
are expressly present.

## SAP.P013b.T21

Source: `Challenge/Part1.lean:36–39`, `Defs/Part6.lean:16–87`, with the explicit
location objects in `Defs/Part3.lean:31–40` and the shared finite definitions.

There are no external hypotheses or existentially unspecified objects. Ω=Fin 3,
N=3, K=2. Assignment probabilities are p_0=p_1=1/4 and p_2=1/2.
`D(z,i)=1` iff z=i, otherwise 0. Predictions are `(g_0,g_1,g_2)=(2,3,5)`.
For both exposures y_id=g_i. The shifted population adds 1 to every potential
outcome, leaving this numerical prediction vector fixed unless specified.
All universal indices below range over these finite sets.

The conjunction asserts every one of the following:

1. For every i, π_i1=p_i and π_i0=1-p_i; for every d and i,
   0<π_id<1; for every i,d, y_id=g_i; for each i the covariance of the constant
   random variable g_i and I_i1 is zero; for every z exactly one unit has exposure
   1 and exactly two have exposure 0.
2. For every d, T_d=10 and T_d^1=13; τ_10=τ_10^1=0;
   for every z,d, A_d(g,z)=10; for every z, B_10(g,g,z)=0.
3. For every z, C_1(z)=2 if z=2, otherwise 4; C_0(z)=8/3 if z=2,
   otherwise 10/3; A_1^1(g,z)=12 if z=2, otherwise 14;
   A_0^1(g,z)=38/3 if z=2, otherwise 40/3;
   B_10^1(g,g,z)=-2/9 if z=2, otherwise 2/9.
4. Positivity, covariance-zero, and the fixed exposure counts are repeated;
   τ_10^1=τ_10; for **every** z,
   A_1^1(g,z)≠A_1(g,z)+3,
   A_0^1(g,z)≠A_0(g,z)+3, and B_10^1(g,g,z)≠B_10(g,g,z).
5. E A_1^1(g)=13, E A_0^1(g)=13, E B_10^1(g,g)=0;
   Var A_1(g)=Var A_0(g)=Var B_10(g,g)=0;
   Var A_1^1(g)=1, Var A_0^1(g)=1/9, Var B_10^1(g,g)=4/81.
6. For every z, every d has A_d^1(g+1,z)=13, and B_10^1(g+1,g+1,z)=0.
7. For every z,i, the original observed outcome minus g_i is 0; the shifted
   observed outcome minus g_i is 1; the shifted outcome minus (g_i+1) is 0.
8. For every z, A_1^1(g,z)=10+C_1(z), A_0^1(g,z)=10+C_0(z);
   A_1^1(g,z)-A_1(g,z)-3 is -1 if z=2, otherwise 1;
   A_0^1(g,z)-A_0(g,z)-3 is -1/3 if z=2, otherwise 1/3;
   B_10^1(g,g,z)-B_10(g,g,z)=(C_1(z)-C_0(z))/3,
   also equal to -2/9 if z=2 and 2/9 otherwise.

The docstring limits the asserted refutation to a fixed-numerical-prediction
reading. The theorem proves the finite calculations and pointwise failures just
listed, and also the repair when outcomes and predictions are jointly shifted.

Junk-value review: every probability appearing in a denominator is one of
1/4,1/2,3/4; population-size division is by 3; other numeric denominators are
positive real integers. There are no empty types or empty sums in this example,
no natural subtraction, and the assignment `Fin.val`/numeral usages are exact.
All expectations and covariances are finite weighted real sums, so no undefined
integral or finite-moment convention is involved. No log/sqrt/rpow, `toReal`,
extrema, limsup/liminf, or partial-function default occurs.

## SAP.P013b.T24

Source: `Challenge/Part1.lean:52–62`, `Defs/Part8.lean:74–142`, and the shared
finite, recording, loss, and subset-sum definitions in Parts 1 and 3.

This is a conjunction of six independently bound groups.

1. Universally choose a finite Ω, N,K, a design p, a population F=(D,y),
   a Boolean recording array R, a proof N>0, exposures d,e with d≠e, and
   positive π_id and π_ie for every i. Write q for the zero-filled recorded
   potentials and ℓ for the lost means as explicitly defined above. Then:
   `E H_d(q)/N=T_d(q)/N`;
   `E[(H_d(q)-H_e(q))/N]=τ_de(q)`;
   for every a∈Fin K, `T_a(q)/N=T_a(y)/N-ℓ_a`;
   `τ_de(q)=τ_de(y)-ℓ_d+ℓ_e`;
   the expected recorded HT effect minus τ_de(y) is `ℓ_e-ℓ_d`;
   that expectation equals τ_de(y) iff `ℓ_d=ℓ_e`;
   the expected recorded HT mean at d equals T_d(y)/N iff `ℓ_d=0`;
   and for every a, if all y_ia≥0, then ℓ_a≥0 and
   `ℓ_a=0 ↔ ∀i, R(i,a)=false → y_ia=0`.
   The last assertion does not require positivity at a because it is just a sum
   identity and inequality, not an HT assertion for a.
2. Universally choose the same objects and positivity/distinctness/N>0
   hypotheses, and additionally all y_id,y_ie≥0 and every unrecorded potential
   at d,e is zero. Then the recorded HT effect has expectation τ_de(y).
3. Universally choose natural N,K, `D:Fin N→Fin K`, real vectors w,G,
   finite subsets S,SR of Fin N, SR⊆S, positive cardinalities for both sets,
   positive w_i for every i∈S, and retention of all nonzero scores:
   `i∈S ∧ G_i≠0 → i∈SR`. For every d,e:
   for every a, U_a(SR)=U_a(S);
   `U_d(S)/|S|=(|SR|/|S|)(U_d(SR)/|SR|)`;
   `(U_d(S)-U_e(S))/|S|=(|SR|/|S|)((U_d(SR)-U_e(SR))/|SR|)`;
   and if V_d(SR)>0,
   `U_d(S)/V_d(S)=(V_d(SR)/V_d(S))(U_d(SR)/V_d(SR))`.
   Neither d≠e nor nonnegative G is assumed in this deterministic group.
4. Universally choose N,K,D,w,G,S,item,survey with item⊆S and survey⊆S,
   cardinalities |S|=2050, |item|=1708, |survey|=1899, positive weights on S,
   retention of every nonzero G_i in each of item and survey, and exposures d,e.
   Then `(U_d(S)-U_e(S))/2050` equals both
   `(854/1025)((U_d(item)-U_e(item))/1708)` and
   `(1899/2050)((U_d(survey)-U_e(survey))/1899)`.
   No item⊆survey hypothesis or conclusion is present. These are conditional
   statements about arbitrary sets, not empirical verification of named sets.
5. A fixed deterministic example: N=3,K=2, D=(1,1,0), w=(2,2,2), G=(1,0,1),
   S={0,1,2}, SR={0,2}. It retains every nonzero score;
   V_1(SR)/V_1(S)=1/2 and V_0(SR)/V_0(S)=1.
   There is no real c with
   `U_1(S)/V_1(S)-U_0(S)/V_0(S)=c(U_1(SR)/V_1(SR)-U_0(SR)/V_0(SR))`.
   Numerically the full contrast is -1/2 and the retained contrast is 0.
6. The integer equalities 2050−342=1708 and 2050−151=1899, the real equalities
   1708/2050=854/1025 and 342/2050=171/1025, and
   1899/2050+151/2050=1.

The docstring discloses omitted empirical verification of the reconstruction,
its connection to a released indicator, twelve rounded estimates, item⊆survey,
and a separate strictness assertion. It describes the numeric scaling as
conditional with exactly the assumptions in group 4.

Junk-value review: groups 1–2 assume N>0 and positive selected π's. Any a outside
d,e appears only in non-ratio finite loss identities, with N>0. Groups 3–4 have
positive set sizes (in group 4 by the explicit cardinalities). In group 3 the
Hajek-style division by V_d(SR) is guarded by V_d(SR)>0; positive weights and
SR⊆S imply V_d(S)>0 as well. Group 5's exposure denominators are 4 and 2 in S
and 2 and 2 in SR. Thus its failure of scalar multiplication does not use an
undefined ratio. The natural subtractions in group 6 are truncated subtraction,
but both minuends exceed their subtrahends, so ordinary integer values result.
Natural-cardinality casts to ℝ are exact. Ω cannot be empty; the deterministic
groups allow no usable empty S. There are no non-integrable means, log/sqrt/rpow,
infinite extended-real conversions, extrema, limsup/liminf, or partial defaults.

## SAP.P013b.T23

Source: `Challenge/Part1.lean:46–50`, `Defs/Part8.lean:16–71`, and all recording
and two-unit definitions in `Defs/Part3.lean:42–80` plus the shared finite
framework.

No external hypotheses are assumed. A world is w∈Fin 3. In every world,
Ω=Fin 2×Fin 2 and each assignment z=(a,b) has probability 1/4.
There are two units, numbered 0 and 1, and exposures 0 and 1. Unit 0 receives a,
unit 1 receives b. Their binary potentials, written as (at 0, at 1), are:

| world | unit 0 | unit 1 |
|---|---|---|
| 0 | (0,1) | (0,0) |
| 1 | (0,1) | (0,1) |
| 2 | (0,1) | (1,0) |

The recording array is true at unit 0 for both exposures and false at unit 1
for both exposures. Thus the recorded potentials in all worlds are (0,1) at
unit 0 and (0,0) at unit 1. The respondent population has one unit only,
receiving exposure a, with potentials (0,1), under the same four-point design.

The conjunction asserts the following, with universal quantifiers local to each
clause:

1. For every world, every potential outcome is 0 or 1; every unit-exposure π
   is 1/2 and strictly between 0 and 1; and for every z,i, the observed recorded
   outcome equals `Σ_d I_id(z)q_id` (consistent exposure-specific observation).
2. For every world, the **entire function** `recordedData(w)` equals that in
   world 0, not just one realized sample.
3. For every world and z=(a,b), the recorded HT effect is `(a.val:ℝ)`.
4. For every world, its expectation is 1/2, variance is 1/4, and the recorded
   potential causal effect is 1/2.
5. For every world, the true wearing effect is 1/2 in world 0, 1 in world 1,
   and 0 in world 2. Lost mean at exposure 0 is 1/2 only in world 2; lost mean
   at exposure 1 is 1/2 only in world 1; other losses are zero.
6. For every world, expected recorded HT effect minus true wearing effect is
   0 in world 0, -1/2 in world 1, and +1/2 in world 2.
7. There is **no** function
   `h:((Fin 2×Fin 2)→Fin 2→Fin 2×ℝ×Bool)→ℝ` such that for **every** world,
   h applied to the world's full record function is its true wearing effect.
   This is a set-theoretic nonidentification statement and does not introduce
   an expectation of a possibly nonmeasurable statistic.
8. For every world, for every z, the respondent HT effect is `2(a.val:ℝ)`;
   its expectation is 1; the recorded full-population estimator is half of it;
   and the respondent expectation minus true wearing effect is 1/2 in world 0,
   0 in world 1, and 1 in world 2.
9. For every world,z,i the record is exactly
   `(if i=0 then a else b, if i=0 then (a.val:ℝ) else 0, if i=0 then true else false)`.
10. For every world, the recorded-estimator bias for the true wearing contrast
    equals lostMean(0)−lostMean(1).
11. For every world, respondent-estimator expectation minus recorded-estimator
    expectation is 1/2.

The docstring says that these facts concern a wearing interpretation combined
with an additional rule scoring unrecorded outcomes as zero. It does not claim
that consistent observation of the original wearing outcome holds in the
nonzero unrecorded cells; instead it proves consistency for the recorded
population.

Junk-value review: all design probabilities are 1/4, all exposure probabilities
are 1/2, and population sizes in means/effects are 2 or 1. Every denominator is
positive. `Fin.val` is the exact integer 0 or 1 cast into ℝ. No empty index types,
truncated subtraction, undefined integrals, `toReal`, log/sqrt/rpow, extrema,
limsup/liminf, or partial defaults occur. Quantification over every possible h in
the nonidentification clause is deliberate; it does not rely on a nonmeasurable
counterexample or an undefined quantity.
