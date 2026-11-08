# Blind reading

Saved before opening either `claims.json` or `record.json`. Only Challenge,
Defs, closure metadata, and relevant Mathlib notions were consulted. The
generated declarations in the closure were inspected with Lean in
`scratch/BlindClosure.lean` (compilation succeeded).

The notation below is fully expanded as follows. For natural numbers K,d,
the population space is
`Ω = (Fin K → ℝ) × (Fin K → Bool) × Fin K × (Fin d → ℝ)` with its usual
product measurable structure. Write a state as `(y,s,z,x)`. Then Y_a=y(a),
S_a=s(a), Z=z, X=x, Y=y(z), and S=s(z). Write
`A_a={Z=a}`, `P={S=true}`, `A={∀a, S_a=true}`, and
`C={∀a b, S_a=S_b}`. These symbols abbreviate the displayed coordinate
maps and sets, not additional SAP definitions. All measures below are
Mathlib measures on that product space.

For a finite positive event E, write
`M_μ(f,E) = (∫_E f dμ)/(μ(E)).toReal`; the numerator is the restricted
Bochner integral and the denominator is the finite extended-nonnegative
mass converted to a real number. Write
`p_a = (μ(P ∩ A_a)).toReal/(μ(A_a)).toReal`.
Independence of U and V means that for every measurable pair of target
sets B,D, `μ(U⁻¹(B) ∩ V⁻¹(D)) = μ(U⁻¹(B)) μ(V⁻¹(D))`.
An almost-everywhere assertion allows a μ-null exceptional set.

The condition called random assignment is exactly the conjunction of
`∀a, (Y_a,S_a) independent of Z` and `∀a, 0<μ(A_a)`. It does NOT
assert joint independence of all potential coordinates from Z. The
population assumptions are: μ(Ω)=1, that random-assignment condition,
and `∀a, p_a>0`. Covariate random assignment instead requires
`∀a, (Y_a,S_a,X) independent of Z`, again with all arm masses positive.
Covariate balance requires, for each b∈Bool with μ(S=b)>0, independence
of X and Z under `μ(S=b)⁻¹ • μ.restrict {S=b}`.

The closure also contains generated instance/proof declarations. Lean
printed their full definitions: `T16Statement._proof_1` is the standard
outer-measure-class instance for measures; `T3Statement._proof_2` and
`jointDependenceAtoms._proof_1` are the standard `NeZero (1+1)` proof;
`T3Statement._proof_3` proves `(1+1).AtLeastTwo`;
`T3Statement._proof_4` and `selectionPopulation._proof_1` prove
`(2+1).AtLeastTwo`; `conditionalLaw._proof_1` and
`covariateBalance._proof_1` are the standard scalar-tower instance for
extended nonnegative reals. They implement numerals, vector notation,
measure application, and scalar multiplication. They add no statistical
hypotheses or conditional-law construction to these statements.

## SAP.P010.T16

Sources: `Challenge/Part1.lean:86–88`, `Defs/Part6.lean:213–232`,
`Defs/Part5.lean:73–94`, and the listed coordinate/assumption definitions
in `Defs/Part3.lean:11–54`.

The quantifiers are `∀q∈ℝ, 0<q → q<1 → ...`. Set K=2,d=1. The
measure μ_q is the sum of six scaled Dirac measures. Its atoms and
weights are:

| Y_0 | Y_1 | S_0 | S_1 | Z | X | weight |
|---|---|---|---|---|---|---|
| 1 | 1 | false | true | 0 | (0) | q/3 |
| 0 | 0 | true | false | 0 | (0) | q/3 |
| 0 | 0 | true | true | 0 | (0) | q/3 |
| 1 | 1 | false | true | 1 | (0) | (1−q)/3 |
| 0 | 0 | true | false | 1 | (0) | (1−q)/3 |
| 0 | 0 | true | true | 1 | (0) | (1−q)/3 |

Here a real weight w is implemented by `ENNReal.ofReal w`; the finite
population definition is `Measure.sum (λi, mass_i • Measure.dirac atom_i)`
over `Fin 6`. This unfolds every population-construction definition.

For every such q the conclusion is the conjunction, in order, of:

1. μ_q is a probability measure; for both a∈Fin 2, `(Y_a,S_a)` is
   independent of Z, μ_q(A_a)>0, and p_a>0.
2. For each a, `(Y_a,S_a,X)` is independent of Z and μ_q(A_a)>0;
   for each b with μ_q(S=b)>0, X and Z are independent under the
   normalized restriction to `{S=b}`.
3. μ_q(A)=1/3; for every a, p_a=2/3; and S and Z are independent.
4. `Y_1−Y_0=0` μ_q-almost everywhere.
5. `∫(1_{S_1=true}−1_{S_0=true})dμ_q=0`.
6. The mean of Y_1−Y_0 conditional on A is zero; its conditional mean
   on `{S_0=true,S_1=false}` is zero; and its conditional mean on
   `{S_0=false,S_1=true}` is zero.
7. `M_μq(Y,P∩A_0)=0`, `M_μq(Y,P∩A_1)=1/2`, their arm-1-minus-arm-0
   difference is 1/2, and `(1/2:ℝ)≠0`.

The docstring describes this as a three-stratum witness with zero unit
effects and selected contrast one half for every interior assignment
probability. It does not call the printed claim false.

Junk-value audit: `ofReal` would truncate negative weights to zero for
other q, but 0<q<1 makes all six weights strictly positive. The arm masses
are q and 1−q, the selected arm masses are 2q/3 and 2(1−q)/3,
and each displayed principal stratum has mass 1/3. Thus no conditional
mean divides by zero, no mass is infinite, and each integrand is bounded
on this finite support and integrable. The two check strata in covariate
balance have masses 2/3 and 1/3, so normalization never uses the inverse
of zero or infinity. Fin 6, Fin 2, and Fin 1 are nonempty; the comparisons
`i.val<3` choose exactly the first three atoms. All arithmetic subtraction
is in ℝ, not truncated natural subtraction. There is no log, sqrt, rpow,
supremum, infimum, limsup, or partial-function default in this closure.

## SAP.P010.T17

Sources: `Challenge/Part1.lean:90–99`,
`Defs/WholeW1.lean:79–113`, and `Defs/Part3.lean:11–46`.

The quantifiers are: for all K,d∈ℕ and all measures μ on Ω, if μ is a
probability measure and the per-arm random-assignment condition above
holds, then all four clauses below hold.

1. The population-assumption conjunction (probability, per-arm pair
   independence, positive arm masses, positive p_a) holds if and only
   if `∀a∈Fin K, (μ(P∩A_a)).toReal/(μ(A_a)).toReal>0`.
2. If that population-assumption conjunction holds, then for every a,
   `(μ(A_a)).toReal>0` and the same displayed ratio is positive.
3. `∀a, p_a>0` if and only if, for every a, the ratio
   `Q({(b,z) | b=true ∧ z=a}).toReal /
    Q({(b,z) | z=a}).toReal` is positive, where
   `Q=μ.map (λ(y,s,z,x), (s(z),z))`, a measure on `Bool × Fin K`.
4. For every natural d′ and every measure ν on
   `(Fin K→ℝ)×(Fin K→Bool)×Fin K×(Fin d′→ℝ)`, if ν is a probability
   measure with per-arm pair independence and positive arm masses,
   and its pushforward under `(y,s,z,x)↦(s(z),z)` equals Q, then
   `∀a, p_a(μ)>0` if and only if `∀a, p_a(ν)>0`.

The docstring describes a positivity assumption in each arm, its
equivalence to the additional population requirement, positive
conditioning denominators, observability from the joint law of (S,Z),
and invariance under equal observable laws. It explicitly describes an
imposed assumption and disclaims both an extra potential-passing premise
and finite-sample certainty.

Junk-value audit: as generic definitions, `passRate` and its observable
counterpart return zero on a zero real denominator, and `.toReal` sends
infinite mass to zero. Here probability measures bound every mass by one,
and random assignment supplies strictly positive arm masses. The
pushforward coordinate map is measurable, so `Measure.map`'s fallback
for a non-a.e.-measurable map cannot occur. No integral or unbounded
order operation is present. K=0 makes Ω empty, so a probability measure
on it cannot exist; the theorem then has no instance. For K≥1 the type
is inhabited, including d=0 (the unique empty covariate vector). There
is no hypothesis forcing zero outcomes or a conclusion about an
expectation.

## SAP.P010.T18

Sources: `Challenge/Part1.lean:101–103`,
`Defs/Part4.lean:92–99`, and `Defs/Part3.lean:11–46`.

The quantifier order is: every K,d∈ℕ, every measure μ on Ω, a proof of
the population assumptions, a proof μ(C)=1, every ordered pair a,b∈Fin K,
and proofs that Y_a and Y_b are Bochner integrable under μ. The
conclusion is

`(∫_{P∩A_a}Y dμ)/(μ(P∩A_a)).toReal
 − (∫_{P∩A_b}Y dμ)/(μ(P∩A_b)).toReal
 = (∫_A(Y_a−Y_b)dμ)/(μ(A)).toReal`.

Thus μ is a probability measure; for every t, `(Y_t,S_t)` is independent
of Z, μ(A_t)>0, and the observed conditional passing ratio p_t is
positive. With μ-probability one all potential binary checks are equal.
No a≠b condition or joint-vector independence is imposed. The
docstring says common potential check status identifies the
always-passer effect by the selected observed contrast.

Junk-value audit: every selected arm event has positive finite mass,
by the probability and positive-rate assumptions. On C, the observed
passing event P equals A. Since an arm a exists and its selected event
has positive mass, μ(A)>0. On A_a the observed Y equals Y_a, so the
restricted integrability needed for the first numerator follows from
the stated integrability of Y_a, and likewise for b; the difference is
integrable on A. No use is made of the integral's zero fallback or the
real division-by-zero convention. If K=0 no a,b can be given and no
probability measure on Ω exists. d=0 and a=b are allowed and harmless.
There are no other partial or out-of-domain operations.

## SAP.P010.T19

Sources: `Challenge/Part1.lean:105–107`,
`Defs/Part4.lean:102–109`, and `Defs/Part3.lean:11–40`.

The quantifier order is: every K,d∈ℕ, every measure μ on Ω, a proof
μ(Ω)=1, a proof of per-arm pair independence and strictly positive arm
masses, every a,b∈Fin K, and proofs of integrability of Y_a and Y_b
under μ. All three conclusions hold:

1. `(∫_{A_a}Y dμ)/(μ(A_a)).toReal = ∫Y_a dμ`.
2. `(∫_{A_b}Y dμ)/(μ(A_b)).toReal = ∫Y_b dμ`.
3. The first conditional arm mean minus the second equals
   `∫(Y_a−Y_b)dμ`.

There is no passing-positivity assumption, no common-check hypothesis,
and no requirement a≠b. The check coordinates occur in the stronger
per-arm pair-independence hypothesis even though the conclusions use
only outcomes and assignment. The docstring describes identification
of arm potential means and their intent-to-treat difference.

Junk-value audit: arm masses are finite and positive by the two explicit
assumptions. On each assigned event Y is the corresponding integrable
potential outcome, so the restricted Bochner integrals are ordinary
finite integrals; integrability of the potential difference also follows.
No junk mean or infinite-toReal case is used. K=0 admits no probability
measure or arm indices; d=0 and a=b are harmless. No further partial,
domain-restricted, or unbounded-order operation is used.

## SAP.P010.T20

Sources: `Challenge/Part1.lean:109–111`,
`Defs/Part4.lean:112–115`, and `Defs/Part3.lean:11–40`.

The quantifiers are: every K,d∈ℕ, every measure μ on Ω, then proofs
that μ(Ω)=1, that for every a the pair `(Y_a,S_a)` is independent of Z
and μ(A_a)>0, and that μ(C)=1. The conclusion is independence of
S=s(Z) and Z. Equivalently, for every B⊆Bool and D⊆Fin K,
`μ({S∈B}∩{Z∈D})=μ({S∈B}) μ({Z∈D})` (all such subsets are measurable).
There is no requirement that any unit pass, no outcome integrability,
and no joint independence of the full potential vector. The docstring
says common potential check status implies independence of observed
check status and assignment.

Junk-value audit: no integral, ratio, toReal, logarithm, root, power,
supremum, infimum, limit, or partial function is used. Independence and
the probability-one condition are ordinary Mathlib measure predicates.
K=0 is excluded by existence of a probability measure on Ω; K=1 and
d=0 are legitimate special cases. No zero-mass convention supplies the
conclusion.
