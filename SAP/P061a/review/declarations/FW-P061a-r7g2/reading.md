# Blind reading

Saved at stage 1, before opening `claims.json` or `record.json`.
Sources: the five Challenge declarations and every entry of their respective
`closure.json` closures. `scratch/BlindClosure.lean` prints all 56 distinct closure
declarations; its successful output is in `scratch/BlindClosure.out`. This includes
the source-line-zero auxiliary declarations, not just the named definitions.

## Common fully expanded mathematical notation

The following notation is only an abbreviation for Mathlib notions, not an extra
assumption. An `AtomicDesign Ω` consists of a function p : Ω → ℝ, proofs that
p(z) ≥ 0 for every z, that p is summable, and that Σ' z, p(z) = 1. Summability
and Σ' are Mathlib's unordered sums (limits of finite subsums), not a chosen
enumeration of a conditionally convergent series. The constructor and `mass`
projection add nothing to these four fields. Such a design cannot exist on an
empty Ω and necessarily has at most countable positive support.

For a natural number N, both an exposure schedule g and a response schedule y
have type `Fin N → Ω → ℝ`; no stability is implicit in this type. Write

* I_i(t,z) = 1 if g_i(z)=t and 0 otherwise;
* P_i(t) = Σ' z, (if g_i(z)=t then p(z) else 0);
* M(f) = Σ' z, p(z) f(z);
* A_i(t,z) = if g_i(z)=t then y_i(z) else 0;
* E_i(t) = M(A_i(t,·))/P_i(t);
* C_i(t) = Σ' z, (if g_i(z)=t then (p(z)/P_i(t)) y_i(z) else 0);
* B(t) = (N:ℝ)⁻¹ Σ_{i:Fin N} E_i(t);
* U_i(t,s) = E_i(t) − E_i(s), and T(t,s) = B(t) − B(s);
* H_t(z) = (N:ℝ)⁻¹ Σ_{i:Fin N} A_i(t,z)/P_i(t), and
  H_{t,s}(z) = H_t(z) − H_s(z).

These expand `eventProbability`, `mean`, `exposureProbability`, `exposureMean`,
`conditionalExposureMean`, `populationExposureMean`, `unitContrast`,
`populationContrast`, `estimateExposureMean`, and `estimateContrast`, respectively.
`supported D z` means p(z)>0. `HasMean D f` means that z ↦ p(z)|f(z)| is
summable in ℝ. `targetMoment D g y t` means this absolute summability for
A_i(t,·), for every i. `positiveExposure D g t` means ∃c:ℝ, c>0 and
∀i, c≤P_i(t); for a fixed finite nonempty population this is equivalent to
strict positivity of every P_i(t).

## SAP.P061a.T6

Location: `SAP/P061a/Challenge/Part1.lean:49–52`, with statement at
`SAP/P061a/Defs/Part7.lean:11–26`. The docstring says that on a common finite
domain exposure potential outcomes are conditional expected outcomes and their
average contrast specializes to a binary distributional-shift functional.

The theorem is the conjunction of two universally quantified statements.

1. For every type Ω equipped with a `Fintype`, every N:ℕ, every normalized
   nonnegative mass p on Ω, every pair of real schedules g,y indexed by Fin N,
   and every d,d':ℝ, assume, in that order, N>0, ∀i P_i(d)>0, and
   ∀i P_i(d')>0. Then:
   * ∀i, E_i(d)=C_i(d) and E_i(d')=C_i(d');
   * T(d,d') = (N:ℝ)⁻¹ Σ_i (C_i(d)−C_i(d'));
   * T(d,d') = B(d)−B(d');
   * T(d,d') = (N:ℝ)⁻¹ Σ_i U_i(d,d').
2. For every N:ℕ, every normalized nonnegative mass p on the **full** binary
   cube Ω=(Fin N → Fin 2), and every real response schedule y on it, assume
   N>0 and, for each i, positivity of the probabilities of z_i=1 and z_i=0.
   Use g_i(z)=(z_i.val:ℝ). Then
   T(1,0)=(N:ℝ)⁻¹ Σ_i(C_i(1)−C_i(0)). No assignment independence, stability,
   or equality between the two conditional laws of other units is assumed.

All displayed notation expands to the finite sums in the common notation above.
In particular the third conclusion of part 1 repeats the definition of T; the
conditional-sum equality additionally gives the conditional interpretation.

Junk-value review: real division/inversion by zero would return zero, but N>0
and both families of strictly positive cell probabilities exclude it here. All
sums over Ω and Fin N are finite, so the zero default of a nonsummable real
`tsum` is irrelevant. `Fin 0` is excluded by N>0; an empty Ω is incompatible
with mass total one. Natural-to-real casts and the `Fin 2` value casts are exact.
There is no truncated subtraction, logarithm, square root, rpow, Bochner integral,
extended-real conversion, supremum/infimum, limit, or partial-function default.

## SAP.P061a.T7

Location: `SAP/P061a/Challenge/Part1.lean:54–64`; expanded statement and helper
predicates at `SAP/P061a/Defs/WholeW1.lean:191–297`. The docstring describes an
explicit one-unit probability model with nonexistent ordinary signed means.

There exists D=`AtomicDesign ℝ`; there are no external hypotheses. Its mass is
fixed as follows: p(k)=2^{−(k+1)} for k:ℕ viewed as a real, and p(z)=0 at every
other real. `Function.extend` chooses a preimage when one exists and uses zero
otherwise. The natural-to-real embedding is injective, so that choice is unique.
The positive support is exactly the embedded nonnegative integers. N=1.
The single exposure is g(0)=0, g(k)=1 for positive natural k, and g(z)=0
off the embedded naturals. The raw response is y(0)=0,
y(k)=(-1)^{k+1}2^{k+1} for positive natural k, and y(z)=0 elsewhere.
Every raw response is a real, without a uniform bound or absolute-moment bound.

For completeness, all conjuncts inside the existential are:

* The preceding mass and positive-support identities; positive lower bounds for
  the two exposure probabilities; P_0(1)=P_0(0)=1/2; E_0(0)=0;
  z ↦ p(z)A_0(1,z) is not summable; H_1 has no finite absolute moment;
  A_0(0,·) does have a finite absolute moment.
* Define a_k=p(k+1)y(k+1), and b_k=p(k+1)H_1(k+1), for k:ℕ. For every k,
  a_k=(-1)^k and b_k=2(-1)^k. For every m:ℕ, the sums of max(a_k,0) and
  max(−a_k,0) over k<2m both equal (m:ℝ); the sum of |a_k| over that range
  is 2m; the signed sum over k<2m is 0 and over k<2m+1 is 1.
  Both real sequences max(a_k,0), max(−a_k,0) are nonsummable, as are the
  two corresponding sequences formed from b_k. For every real z,
  H_1(z)=2 y(z) I_0(1,z).
* On the measurable space ℝ with **every subset measurable**, let
  μ=Σ_z ENNReal.ofReal(p(z)) • δ_z, where δ_z is the Dirac measure.
  μ is a probability measure. For every set A⊆ℝ,
  μ(A)=Σ'_z (if z∈A then ENNReal.ofReal(p(z)) else 0) and
  (μ(A)).toReal=Σ'_z(if z∈A then p(z) else 0).
* The map z ↦ (the constant function Fin 1 → ℝ with value z) is bijective.
  There is no a:ℝ such that the sequence n ↦ Σ_{k<n} a_k converges to a.
* Define P⁺(f)=Σ'_z ENNReal.ofReal(p(z)max(f(z),0)),
  P⁻(f)=P⁺(−f), and J⁺(ν,f)=∫⁻z, ENNReal.ofReal(max(f(z),0)) ∂ν.
  Then P⁺(A_0(1,·))=P⁻(A_0(1,·))=∞, and
  J⁺(μ,A_0(1,·))=J⁺(μ,−A_0(1,·))=∞.
* For A={z:g(z)=1}, define ν=ENNReal.ofReal(P_0(1))⁻¹ • μ.restrict A.
  J⁺(ν,y)=J⁺(ν,−y)=∞. Thus this is normalized conditioning on a cell of
  probability 1/2, not a zero-probability conditional law.
* An ordinary EPO of value a at unit i and exposure t is the conjunction
  P_i(t)>0, summability of p(z)|A_i(t,z)|, and E_i(t)=a.
  An ordinary AEPO of value a requires N>0 and real u_i giving ordinary
  EPOs at every unit, with a=(N:ℝ)⁻¹Σ_i u_i.
  An ordinary EED of value a requires ordinary EPO values u,v at its two
  exposures, with a=u−v; ordinary AEED analogously requires two ordinary
  AEPO values. There is no real value for the exposure-one EPO, exposure-one
  AEPO, the unit EED (1 versus 0), or AEED (1 versus 0). The exposure-zero
  ordinary EPO does exist and equals zero.
* P⁺(H_1)=P⁻(H_1)=J⁺(μ,H_1)=J⁺(μ,−H_1)=∞.
  There is no a:ℝ such that p(z)|H_1(z)| is summable and M(H_1)=a.

These are conclusions about one explicitly prescribed witness. In particular
`GeometricBaseW1` is an existential conjunct, not an antecedent that assumes
the divergent-mean conclusion for an arbitrary design.

Junk-value review: `mean`, E_0(1), and M(H_1) are syntactically real-valued
even when their series diverge: Mathlib assigns zero to a nonsummable real
`tsum`. The theorem never asserts that this zero is an ordinary divergent-cell
mean; the ordinary-mean predicates explicitly require absolute summability,
and the divergent expectations are expressed through genuine ENNReal sums and
nonnegative integrals. E_0(0) uses a summable zero integrand. All denominators
actually used for conditional/HT quantities are 1/2 and N=1. ENNReal inverse
at zero is ∞, but conditioning avoids zero. `ENNReal.ofReal` truncates negative
inputs to zero; its inputs here are nonnegative masses and positive parts, so
no sign is silently lost. `toReal ∞=0` is a potential convention, but μ is a
probability measure, so the converted event masses are at most one. Infinite
nonnegative sums/integrals equal ∞ legitimately. The zero extensions outside
ℕ are specified schedules, not undefined responses; all these points have
mass zero. Powers have natural exponents and finite real values. No subtraction
on ℕ, logarithm, sqrt/rpow, Bochner integral, empty/unbounded supremum, or
limsup/liminf occurs. The claimed limit is ordinary convergence to a real.

The auxiliary closure declarations were also read from Lean: `GeometricBaseW1._proof_1`
and `integerResponseTerm._proof_1` supply `NeZero 1`; `PairBaseW1._proof_2` and
`edgeExposure._proof_1` supply `Nat.AtLeastTwo 2`; `fairSignLawW1._proof_1`
supplies the ENNReal scalar-tower instance. They impose no statistical condition.

## SAP.P061a.T8

Location: `SAP/P061a/Challenge/Part1.lean:66–70`, with full statement at
`SAP/P061a/Defs/Part8.lean:11–41`. The docstring promises conditional-mean
identities and unbiased integrable HT estimators from targeted absolute moments,
and two sufficient conditions for those moments.

This is a conjunction of two universal statements. For each, the quantified data,
in order, are Ω:Type (not required finite), N:ℕ, normalized nonnegative mass p,
g,y:Fin N → Ω → ℝ, and d:ℝ.

In the first statement assume N>0, ∀i P_i(d)>0, and, for every i,
summability of z ↦ p(z)|A_i(d,z)|. The conclusions are:

* For every i, z ↦ p(z)A_i(d,z) is summable, E_i(d)=C_i(d),
  z ↦ p(z)|A_i(d,z)/P_i(d)| is summable,
  M(|A_i(d,·)/P_i(d)|)=M(|A_i(d,·)|)/P_i(d), and
  M(A_i(d,·)/P_i(d))=E_i(d).
* z ↦ p(z)|H_d(z)| is summable, and M(H_d)=B(d).
* For **every** d':ℝ, if ∀i P_i(d')>0 and all targeted absolute moments at
  d' are summable, then H_{d,d'} has finite absolute moment,
  M(H_{d,d'})=T(d,d'), and T(d,d')=(N:ℝ)⁻¹Σ_i U_i(d,d').
* For every i, Σ'_z(if g_i(z)=d then (p(z)/P_i(d))|y_i(z)| else 0)
  equals M(|A_i(d,·)|)/P_i(d); also B(d)=(N:ℝ)⁻¹Σ_i C_i(d).

In the second statement assume only N>0 and ∀i P_i(d)>0. There are two
independent implications:

* If {z:p(z)>0} is finite, all targeted absolute moments at d are summable.
* If for every i,z,z' with p(z)>0, p(z')>0, g_i(z)=d and g_i(z')=d one has
  y_i(z)=y_i(z'), all those moments are summable and, for every i, there
  exists a real a such that y_i(z)=a on its positive-mass d-cell and
  M(|A_i(d,·)|)=|a|P_i(d). The quantifier is ∀i∃a, not a common a for all units.

Junk-value review: although the generic definitions totalize division and sums,
N>0 and positive P_i exclude zero division in each asserted expectation.
The first statement explicitly assumes the needed absolute summability;
the second proves it from finite positive support or constant targeted cells.
Neither assumes integrability outside the target cells. Zero-mass arbitrary
responses contribute exactly zero. A chosen constant a is legitimate because
positive cell probability supplies a positive-mass member; empty-cell constants
are not being used to manufacture a conclusion. AtomicDesign rules out an
empty Ω, and N>0 rules out empty unit indexing. Casts are exact; subtraction
is in ℝ. No log, sqrt/rpow, Bochner integral, ENNReal conversion, infimum,
supremum, limit, or partial-function default is used.

## SAP.P061a.T9

Location: `SAP/P061a/Challenge/Part1.lean:72–75`, with full statement at
`SAP/P061a/Defs/Part12.lean:11–34`. The docstring describes two designs with
different sampling sizes, support stability, different AEEDs, and failure of
global stability for their common raw response schedule.

There exist D,D', each a normalized nonnegative atomic mass on the full finite
assignment cube Ω=(Fin 4 → Fin 3). Let s(z)=#{j:Fin 4 | z_j≠0}; let
S_n={z | #{j:z_j=2}=1 and s(z)=n}. The statement fixes
p(z)=1/12 on S_2 and zero elsewhere, and p'(z)=1/12 on S_3 and zero elsewhere,
and asserts that these are exactly the respective positive supports.
The common exposure is g_i(z)=(z_i.val:ℝ), and the common raw outcome is
y_i(z)=(s(z):ℝ)·(if z_i=2 then 1 else 0).

All remaining existential conjuncts are:

* For every i, under D the probabilities of exposures 2 and 1 are both 1/4;
  under D' they are respectively 1/4 and 1/2. Every one of these probabilities
  is explicitly asserted positive as well.
* For each design separately: for every i,z,z', if p(z)>0 and p(z')>0
  (respectively p'), and g_i(z)=g_i(z'), then y_i(z)=y_i(z').
* For every i, E_i^D(2)=2, E_i^D(1)=0, E_i^{D'}(2)=3,
  E_i^{D'}(1)=0; consequently T_D(2,1)=2 and T_{D'}(2,1)=3.
* It is false that ∀i,z,z', g_i(z)=g_i(z') implies y_i(z)=y_i(z') on
  the full cube. Thus stability across assignments from different supports is
  explicitly **not** asserted. There are no external hypotheses or replicate draws.

Junk-value review: all spaces and sums are finite. The support sets each have
12 assignments (four choices for the unique treated unit and three choices for
the other included units), so the mass prescriptions are compatible with total
one. Denominators are 4, 12, or the displayed positive target probabilities.
The empty-filter card convention is the intended count of an empty set; cards
and Fin-value casts are exact natural-to-real embeddings. No truncated
subtraction, divergent sum/integral, log, sqrt/rpow, ENNReal conversion,
infimum/supremum, limit, or partial default enters.

The line-zero closure auxiliaries were printed: `T9Statement._proof_1` through
`_proof_4` provide `Nat.AtLeastTwo` for 12, 2, 4, and 3, respectively;
`coarsenVersion._proof_1` provides `NeZero 3`. They add no conditions.

## SAP.P061a.T10

Location: `SAP/P061a/Challenge/Part2.lean:9–22`. Its closure contains no SAP
definitions. The docstring explicitly limits the result to transcribing three
rates, disclaiming graph identification, existence, a CLT, and sharpness.

For **every** dmax,davg:ℕ→ℝ, and proofs hmax:∀N,0≤dmax(N) and
havg:∀N,0≤davg(N), the conclusion is the conjunction of these equivalences:

1. dmax=o(N^(1/4)) at N→∞ iff the real sequence
   dmax(N)/Real.rpow((N:ℝ),1/4) converges to 0.
2. davg=O(1) at N→∞ iff ∃C:ℝ,∀N:ℕ,davg(N)≤C.
3. dmax=O(N^(1/2)) at N→∞ iff ∃C:ℝ,∀N:ℕ,
   N>0 → dmax(N)/Real.rpow((N:ℝ),1/2)≤C.

Expanded to Mathlib's definitions, f=O(g) means ∃c:ℝ, eventually atTop,
|f(N)|≤c|g(N)|. Here “eventually” means for all N≥some natural threshold.
f=o(g) means ∀ε:ℝ,ε>0 → eventually |f(N)|≤ε|g(N)|.
Convergence to zero has its usual ε/threshold meaning. C and c are not required
positive. Pointwise nonnegativity of the sequences makes upper bounds sufficient.
The bounds on the right of equivalences 2 and 3 are uniform, not just eventual;
the finitely many initial values can be absorbed in C. No relation between dmax
and davg or any graph or estimator is present.

Junk-value review: real division by zero gives zero at N=0 in equivalence 1,
because Real.rpow(0,1/4)=0. This single index does not affect the atTop limit.
Equivalence 3's quotient bound explicitly excludes N=0. At positive N, both
powers are positive and agree with the conventional real powers. Natural casts
are nonnegative, so rpow's arbitrary negative-base extension is never used;
0^0 also never occurs. There is no truncated subtraction, empty index type,
expectation/integral, ENNReal conversion, supremum/infimum, limsup/liminf,
or partial-function default.
