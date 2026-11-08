# Blind reading

Saved before opening `claims.json` or `record.json`. The input for this reading is
the five Challenge statements and docstrings, all declarations in `closure.json`,
their source definitions, and Mathlib's conditional-expectation conventions.
This is a description of the statements, not an assessment against the paper.

## Shared notation, expanded definitions, and conventions

The measurable spaces below are arbitrary Lean types with specified sigma
algebras, except where an additional standard Borel assumption is explicit.
All scores, policies, outcomes, and integrals below are real valued. Integrals
are Mathlib Bochner integrals, and all equalities of conditional expectations
are almost-everywhere equalities for the indicated measure.

For a covariate space C, `Admissible π` means that π:C→R is measurable and
0≤π(c)≤1 for **every** c. `bit t` is 1 for Boolean true and 0 for false.
`positiveRule m` is the measurable candidate c↦1 if m(c)>0 and 0 otherwise;
measurability is a consequence of hypotheses where this rule is used.

`Experiment Ω C n` is a data structure, not a bundled stochastic assumption.
It contains a proof n>0, a measure P on C, two functions μ0,μ1:C→R,
a policy-indexed measure Lπ on Ω, covariates C_i:Ω→C, outcomes
Y0_i,Y1_i:Ω→R, treatment functions Tπ_i:Ω→Bool, and a policy-indexed random
function Hπ:Ω→C→R. The constructor `Experiment.mk` adds no requirements beyond
these fields and n>0. The functions C_i,Y0_i,Y1_i themselves are fixed as π
varies, although Lπ can vary. Write Iπ_i=bit(Tπ_i),
τ(c)=μ1(c)−μ0(c), Oπ_i=Y1_i if Tπ_i=true and Y0_i otherwise, and
G_i=σ(C_i), formally the comap of C_i from the sigma algebra on C.

The defined welfare is

    V(π) = ∫ (Oπ_0−Y0_0) dLπ,

using the index 0 justified by n>0. `meanWelfare` is
W(π)=∫π(c)τ(c)dP(c); these two are separate definitions.
The weighted TT sample reward is

    Σ_i (Oπ_i−Hπ(C_i)) Iπ_i g(C_i),

and its expected reward Rg(π) is its integral under Lπ. Ordinary expected TT,
R(π), sets g identically 1. `normalizedTT` is R(π)/(n:R).

For any set F and real objective f, `IsBest F f b` means
b∈F and ∀s∈F, f(s)≤f(b). `bestValue F f` is the real supremum
sup(f[F]), and `regret F V b` is sup(V[F])−V(b). No optimizer is built
into the supremum definition.

`PolicyDesign E π` asserts all of the following at the particular π:

1. P and Lπ are probability measures; μ0 and μ1 are measurable and integrable
   under P.
2. Each C_i,Y0_i,Y1_i,Tπ_i is measurable; Y0_i,Y1_i are integrable under Lπ.
3. Each C_i has distribution P (`IdentDistrib` means both maps are almost
   everywhere measurable and their pushforward measures agree).
4. E[Y0_i|G_i]=μ0(C_i) and E[Y1_i|G_i]=μ1(C_i).
5. E[Iπ_i|G_i]=π(C_i).
6. For every Borel B⊆R×R,
   E[Iπ_i 1_B(Y0_i,Y1_i)|G_i]
   =π(C_i)E[1_B(Y0_i,Y1_i)|G_i].

Thus the last field is the indicator formulation of conditional independence
of the treatment coin and the potential outcomes given the covariate.
`PolicyDesign.mk` merely constructs these fields. It assumes neither
independence between units nor that the potential-outcome law is fixed between
different policies, and it assumes no integrability of the estimator.

`Standing E` asserts these same design conditions for **every admissible** π,
and adds: integrability of Hπ(C_i); equality in law of (C_i,Y0_i,Y1_i)
between every pair of admissible policies; independence of the vector-indexed
random variables (C_i,Y0_i,Y1_i,Tπ_i) over i; and identical distribution of
these random variables for every i,j at each π. `iIndepFun` is mutual
independence of their generated sigma algebras. `Standing.mk` adds no fields
or implicit assumptions beyond those printed in the structure.

`TreatedUnbiased E a F` means, for every π∈F and every i,

    E[Iπ_i(Hπ(C_i)−a(C_i)) | G_i] = 0.

It does not, by itself, assert integrability of the residual.
`PointwiseUnbiased E F` means, for every π∈F and **every fixed c**,
ω↦Hπ(ω,c) is Lπ-integrable and ∫Hπ(ω,c)dLπ(ω)=μ0(c).
`IndependentEstimator E F` means there exist a type A with a sigma algebra,
a measurable Z:Ω→A, and f:(C→R)→A→C→R, with the following properties
for every π∈F: (z,c)↦f(π,z,c) is jointly measurable;
Hπ(ω,c)=f(π,Z(ω),c) for every ω,c; and Z is independent under Lπ of the
entire vector ((C_i)_i,(Tπ_i)_i). Independence is in Mathlib's pushforward/
generated-sigma-algebra sense, not just zero covariance. Neither f nor the law
of Z is required to be policy invariant.

Relevant conventions shared by these definitions:

- A nonintegrable Bochner integral is defined as zero. Conditional expectation
  is the zero function if its input is nonintegrable, the conditioning sigma
  algebra is not a subalgebra, or the trimmed measure is not sigma finite.
  The actual statements provide integrability for the residuals being
  conditioned. Measurability of C_i supplies the subalgebra condition and
  finite probability measures supply sigma finiteness.
- The real supremum of an empty or unbounded-above set has a totalized default
  value (zero for the real implementation). Where a regret equality is
  asserted here, a feasible welfare optimizer is either assumed or follows
  from reward/welfare alignment. It makes the image nonempty and bounded
  above and removes that convention from the asserted equality.
- All finite sums are over `Fin n` or finite Boolean types; n>0 is part of
  every Experiment. A real cast of n cannot be zero there. There are no
  logarithms, roots, real powers, truncated natural subtraction, limsups,
  extended-real-to-real conversions, or partial-function defaults in the
  relevant definitions unless mentioned explicitly below.

## SAP.P006a.T6

Location: `SAP/P006a/Challenge/Part1.lean:46–49`;
body: `SAP/P006a/Defs/Part5.lean:168–188`.

The docstring describes TT/welfare alignment under corrected treated-evaluation
unbiasedness, an unconstrained positive-effect rule, and independent estimation.
The actual proposition is a conjunction of two universally quantified results.

First, for every Ω,C, their measurable structures, n, Experiment E, and set
F⊆(C→R), assume in order:

1. Every π∈F is admissible.
2. Every π∈F satisfies all six `PolicyDesign` clauses above.
3. For every π∈F and every i, Iπ_i(Hπ(C_i)−μ0(C_i)) is Lπ-integrable.
4. For every π∈F and i, its conditional expectation given G_i is zero.

Then all of the following hold:

- For every π∈F, R(π)=nW(π) and V(π)=W(π).
- For every π, π is an R-maximizer in F iff it is a V-maximizer in F.
- For every R-maximizer π in F, sup(V[F])−V(π)=0.
- If F is exactly the set of all admissible policies, c↦1_{τ(c)>0} is
  an R-maximizer in F.

Second, for every Ω,C,n,E,F, assume per-feasible-policy `PolicyDesign`, the same
integrability of every selected residual, pointwise unbiasedness at μ0 for
every fixed c, and `IndependentEstimator E F` as expanded above. Then every
selected residual has conditional expectation zero given G_i. This second
branch has no separate assumption that all feasible policies are admissible;
its conclusion is the moment statement alone.

F may be empty in either branch. In the first branch the per-policy assertions
and assertions about existing maximizers then quantify over no candidates;
the unconstrained clause cannot be triggered by an empty F. The theorem does
not assume existence of a maximizer for an arbitrary F. Its nonempty special
cases have ordinary mathematical content.

Junk audit: integrability of selected residuals is explicit; the moment
condition therefore does not hold merely by conditional-expectation fallback.
Integrability of outcomes and μ0 follows from `PolicyDesign`. Bounded treatment
indicators and admissible π make the reward and welfare integrable. Every regret
conclusion is made at a genuine attained maximum. No division appears in this
statement; the n appearing as a multiplier is positive. All other shared
conventions are inert in these conclusions.

## SAP.P006a.T7

Location: `SAP/P006a/Challenge/Part1.lean:51–54`;
body: `SAP/P006a/Defs/Part5.lean:192–212`.

For every Ω,C, their measurable structures, n, and E, assume
`Standing` for the experiment with H replaced by the identically zero
estimator. This preserves all of the design, cross-policy and iid requirements
listed above, but its estimator-integrability requirement concerns zero,
not the actual H. Next choose g:C→R with g measurable and g(c)>0 at **every** c.
Assume, in this order:

1. For every admissible π and every i, Iπ_i(Hπ(C_i)−μ0(C_i)) is integrable.
2. For every admissible π and i its conditional expectation given G_i is zero.
3. gτ is P-integrable.
4. For every admissible π and i,
   (Oπ_i−Hπ(C_i))Iπ_i g(C_i) is Lπ-integrable.

The conclusions are:

- For every admissible π,
  Rg(π)=n∫g(c)τ(c)π(c)dP(c).
- The positive-effect rule c↦1_{τ(c)>0} maximizes Rg over the entire admissible
  class A.
- Every Rg-maximizer b in A satisfies, P-almost everywhere,
  τ(c)>0 ⇒ b(c)=1 and τ(c)<0 ⇒ b(c)=0. There is no condition at τ=0.
  Furthermore V(b)=∫τ(c)1_{τ(c)>0}dP(c), b maximizes V over A, and
  sup(V[A])−V(b)=0.

The docstring describes strictly positive weighted TT and every maximizing
policy under corrected moments and integrability. The formal class here is
specifically all admissible policies, not an arbitrary constrained class.

Junk audit: no estimator integrability is imposed on untreated observations.
The selected residual and each weighted reward summand have explicit L1
assumptions. The corresponding unweighted outcome and welfare moments come
from `Standing` with zero estimator. The exhibited positive-effect maximizer
and optimal welfare conclusions remove empty/unbounded supremum defaults.
Strict positivity is substantive and pointwise, not nonnegativity or merely
positive P-almost everywhere. There are no divisions or extended-real
conversions in the statement.

## SAP.P006a.T8

Location: `SAP/P006a/Challenge/Part1.lean:56–74`;
body: `SAP/P006a/Defs/WholeW2.lean:224–227`.

The statement is the conjunction of seven separate universal propositions.
All Experiment sample sizes are positive. No one branch supplies assumptions
to another. The types in these seven propositions are Lean `Type` (universe
zero). This is a universe convention, not a finite/countable-space assumption.

1. **InformationBoundW2.** For every Ω,X,U with measurable structures,
   n,E on covariates c=(x,u)∈X×U, and feasible F, assume every π∈F is
   admissible and satisfies `PolicyDesign`. Choose b0:X→R. Assume b0 is
   measurable, b0∘fst is P-integrable, and, for every π∈F and i,
   E[μ0(C_i)|σ(fst(C_i))]=b0(fst(C_i)). Assume for every π∈F the map
   (ω,c)↦Hπ(ω,c) is jointly measurable and
   Hπ(ω,(x,u))=Hπ(ω,(x,u')) for all ω,x,u,u'. Assume each selected
   residual Iπ_i(Hπ(C_i)−b0(fst(C_i))) is Lπ-integrable and has zero
   conditional expectation given G_i. Then, writing
   h=∫|b0(x)−μ0(x,u)|dP(x,u), every π∈F satisfies

       R(π)/n = ∫π(c)(μ1(c)−b0(x))dP(c),
       |R(π)/n−V(π)| = |∫π(c)(μ0(c)−b0(x))dP(c)| ≤ h.

   For every real γ with h≤γ, and then every b,s with b an R-maximizer
   and s a V-maximizer in F,
   sup(V[F])−V(b)=V(s)−V(b)≤2γ. There is no existence hypothesis or
   conclusion for maximizers in the per-policy part.

2. **SelectedEquivalenceW2.** For every Ω with ambient sigma algebra mΩ,
   probability μ, sub-sigma algebra m≤mΩ, measurable Boolean T, measurable
   H:Ω→R, m-measurable a,p:Ω→R, assume a∈L1(μ), 0≤p≤1 pointwise,
   Eμ[bit(T)|m]=p, and bit(T)(H−a)∈L1(μ). Set
   ν=μ restricted to {T=true}. Then H∈L1(ν), and

       Eμ[bit(T)(H−a)|m]=0 (μ-a.e.)
         iff Eν[H|m]=a (ν-a.e.),
       Eν[H|m]=a (ν-a.e.)
         iff μ-a.e. [p>0 ⇒ Eν[H|m]=a].

   ν is not divided by its total mass and may be the zero measure.

3. **IndependentUnbiasedW2.** For every Ω,X,U,n,E,F with admissibility
   and `PolicyDesign` only on F, choose measurable b0 with b0∘fst∈L1(P).
   Suppose for every π∈F and **every c** the random Hπ(·,c) is L1(Lπ)
   with mean b0(c.1). For every π∈F separately, assume an
   `IndependentEstimator E {π}` representation. Its auxiliary type, map,
   estimator, and distribution can differ with π. Assume all selected
   residuals at b0∘fst are integrable. Then their conditional expectations
   given G_i are zero for every π∈F,i. This branch does not itself assume
   the marginal-baseline conditional equation or public-only dependence.

4. **QualifiedLemma2W2.** For every Ω,C,n,E, admissible π and
   `PolicyDesign E π`, assume for each i both Iπ_i Hπ(C_i) and
   π(C_i)Hπ(C_i) are integrable and
   E[(Iπ_i−π(C_i))Hπ(C_i)|G_i]=0. Put
   M=∫π(c)μ1(c)dP(c) and e_i=∫π(C_i)Hπ(C_i)dLπ. Then

       R(π)=Σ_i(M−e_i),
       [∀i, R(π)=n(M−e_i)] iff [∀i,j, e_i=e_j].

   Finally, for every measure D on C×R, if (C_i,Hπ(C_i)) has distribution
   D for all i, then all e_i are equal. The common-law implication has no
   distinct finiteness hypothesis on D, but its being the pushforward of
   probability Lπ supplies finiteness.

5. **CoinFactorizationW2.** For every standard Borel Ω with sigma algebra
   mΩ, probability μ, subalgebra m≤mΩ, measurable Boolean T and real H,
   m-measurable p with 0≤p≤1, E[bit(T)|m]=p, and both bit(T)H and pH
   integrable: conditional independence of T and H given m implies
   E[(bit(T)−p)H|m]=0. Additionally, if H∈L1(μ), that last zero-moment
   condition is equivalent to E[bit(T)H|m]=pE[H|m]. `CondIndepFun` means
   conditional independence of the generated sigma algebras; it is not
   assumed in the factorization equivalence. The standard Borel condition
   is used in this branch only.

6. **CommonLawProposition10W2.** For every Ω,C,n,E,F with admissibility
   and `PolicyDesign` on F, the two integrable weighted evaluations and
   zero conditional coin moment of branch 4 at every π∈F, and a probability
   D on C×R such that (C_i,Hπ(C_i)) has distribution D for **all** π∈F,i,
   assume |h−μ0(c)|∈L1(D) and put ε=∫|h−μ0(c)|dD(c,h). Then
   |R(π)/n−V(π)|≤ε for all π∈F; for **every** reward/welfare maximizing
   pair b,s in F,

       regret(b)=V(s)−V(b)
         ≤ |V(s)−R(s)/n|+|R(b)/n−V(b)| ≤ 2ε.

   This is the entire expansion of `Proposition10ConclusionW2`; the
   conclusion is not bundled into the assumptions. Unbiasedness is not
   required here.

7. **AuxiliaryProposition10W2.** For every Ω,X,U,A with measurable
   structures, n,E,F with admissibility and `PolicyDesign` on F, choose
   Q on A, Z:Ω→A and f:A×X→R. `AuxiliaryDataW2` asserts Q is a
   probability measure, Z and f are measurable, and for each π∈F:
   Hπ(ω,c)=f(Z(ω),c.1) pointwise; Z has distribution Q under Lπ;
   and Z is independent of ((C_i)_i,(Tπ_i)_i) under Lπ.
   `AuxiliaryDataW2.mk` is just the constructor of these six fields.
   Set D to the pushforward of the product measure Q×P by
   (z,c)↦(c,f(z,c.1)). Assume |h−μ0(c)| is D-integrable. Then for
   every π∈F,i, (C_i,Hπ(C_i)) has law D and its expected absolute
   estimation error is ∫|h−μ0(c)|dD. All per-policy and maximizing-pair
   conclusions of branch 6 follow with this same ε. The zero coin moment
   is not an extra assumption in this branch.

The long Challenge docstring explicitly describes these seven branches and
says that usual measure-theoretic conditions are assumed.

Junk audit: R/n never divides by zero because E contains n>0. Each conditional
expectation used for a selected residual has an L1 assumption. In branch 4
the coin residual is a difference of two L1 functions. Branch 5 conditions on
L1 weighted evaluations, and uses E[H|m] only after assuming H∈L1. Branch 6
assumes a genuine finite absolute error. Branch 7's finite error combined
with the marginal integrability of μ0 ensures integrability of its evaluation;
the joint law and selected moments are derived. Public-only dependence does
not encode an accuracy assertion. No zero-measure conditional law is
normalized: when ν=0 in branch 2, all its a.e. statements are vacuous, while
p=0 μ-a.e. makes the positive-propensity formulation vacuous too. This is
consistent with a condition imposed only on selected observations. Empty F
is allowed, but all conclusions requiring b,s include genuine maximizers.
Every regret equality uses a nonempty, bounded-above welfare image. There
are no `toReal`, logarithm, root, limsup, or partial-selection conventions.

Generated closure declarations were printed in `scratch/ClosurePrint.lean`.
`CoinFactorizationW2._proof_1` constructs `IsFiniteMeasure μ` from
`IsProbabilityMeasure μ`; `InformationBoundW2._proof_1` proves that the
numeral 2 is at least two. These are elaboration proofs, not additional
mathematical hypotheses.

## SAP.P006a.T9

Location: `SAP/P006a/Challenge/Part1.lean:76–79`;
body: `SAP/P006a/Defs/Part5.lean:232–256`.

For a vector t:Fin n→R, let B={i∈Fin n:t_i>0}, k=|B|,
S=Σ_{i∈B}t_i. `fittedOptimalUtility` is v=S/(n:R), and
`beneficiaryMean` is b=S/(k:R). The proposition has four independent
universal branches:

1. For every n,t, n>0 and k>0 imply b=v(n/k); if k<n then v<b.
2. For every real vH,bH,vS,bS, assume
   293907/2000000≤vH≤293909/2000000,
   bH=vH(255/62),
   50371/2000000≤vS≤50373/2000000,
   bS=vS(7264/1360). Then

       14989257/24800000≤bH≤14989359/24800000, 59/400<bH,
       672601/5000000≤bS≤11434671/85000000, 51/2000<bS.

3. For every real vH,rH,vS,rS, assume
   0<rH≤2432/10000, vH≥14694/100000,
   0<rS≤1873/10000, vS≥2517/100000. Then
   vH/rH>604/1000 and vS/rS>134/1000.
4. For every real vH,bH,vS,bS satisfying exactly the six interval/equality
   assumptions in branch 2, conclude

       .1465<vH<.1475, .0245<vS<.0255,
       .6035<bH<.6045, .1345<bS<.1355.

The decimal endpoints above are exact rationals. Branch 4 states open
rounding intervals rather than invoking a particular rounding function.
The theorem contains no empirical dataset, fitted model, actual vector with
255 or 7264 entries, or proposition that an actual fitted utility lies in
the asserted input interval. The numerical branches are conditional real
arithmetic assertions about separately quantified variables.

Junk audit: definitions v,b return zero when their denominator is zero in
Lean's real field. Branch 1 rules out n=0 and k=0, so these defaults do not
affect it. Empty beneficiaries would otherwise give S=0. Branch 3 explicitly
requires positive rH,rS. All literal denominators are positive integers in R;
casts of n,k are exact and positivity is preserved. There is no natural
subtraction, supremum, integral, logarithm, root, or limit. All 36 generated
`T9Statement._proof_1` through `_proof_36` were printed and read; each proves
a literal `(a+1).AtLeastTwo` by `Nat.instAtLeastTwoHAddOfNat a`, solely to
elaborate a real numeral. None supplies an empirical premise or a conclusion.

## SAP.P006a.T10

Location: `SAP/P006a/Challenge/Part1.lean:81–85`;
body: `SAP/P006a/Defs/Part5.lean:260–284`.

An `OutcomeLaw C` is simply a measure D on C×(R×R), written (c,(y0,y1)).
`FiniteOutcomeLaw D` means it is a probability measure and both coordinate
outcomes y0,y1 are integrable. `treatedProjection` is (c,(y0,y1))↦(c,y1).
`coinMass q true=q`, `coinMass q false=1−q`.
For a Boolean treatment vector, treatedCount is the real sum of its bits.
The ATO sample reward is the mean of the treated outcomes when treatedCount>0,
and zero otherwise. `oneATOExpectation D π` integrates the Boolean sum

    Σ_{t∈{false,true}} coinMass(π(c),t)
        · wATO([t],[if t then y1 else y0])

against D. `outcomeWelfare D π` is ∫π(c)(y1−y0)dD.
`NondegenerateReward F reward` is the existence of D,π such that D has the
finite probability/moment property, π is a reward(D)-maximizer in F, and
∫π(c)dD>0. The definition does not itself require π admissible.

The proposition is a conjunction of six assertions:

1. For **every** real B>0, set D=δ_((),(1+B,1)) on the singleton covariate
   space Unit, F={π1} where π1 is identically 1. Then D is a finite-moment
   probability law; π1 maximizes its one-unit ATO expected reward in F;
   ∫1dD=1; welfare(π1)=−B; regret in F at π1 is zero; indeed
   **for every** function V:(Unit→R)→R its regret in F at π1 is zero;
   the identically zero policy is not in F; and it is not the case that 0≥B.
2. For every measurable C, D with finite probability/moment property and
   admissible π, oneATOExpectation(D,π)=∫π(c)y1dD.
3. For every measurable C, finite-moment probability D,D', admissible π,
   equality of the (c,y1)-pushforward laws implies equality of their
   one-unit ATO expectations at π.
4. The one-unit ATO reward on F={π1} on Unit satisfies the existential
   `NondegenerateReward` property above.
5. For every function f:(Unit→R)→R, π1 maximizes f on this F.
6. For every B>0, the supremum of welfare over F for the same Dirac D is −B.

The Challenge docstring calls this a singleton always-treated counterexample
to a printed impossibility statement and withholding step. The formal
counterexample compares welfare only within the singleton F. It does not
assert that zero treatment is feasible; it explicitly asserts the opposite.
No universal impossibility proposition occurs in the formal statement, only
the witness facts, invariance identity, and nondegeneracy certificate.

Junk audit: the ATO definition deliberately returns zero on no treated units.
For its one-unit vector it returns y1 when true and zero when false; no
division by zero occurs in a taken positive-count branch. π admissibility
makes coinMass genuine probabilities in the two general identities. All
Dirac witness moments are finite. General identities assume probability laws
and integrable outcome coordinates, and admissibility bounds their products.
The supremum is always over a singleton, hence nonempty and bounded for every
real objective, so its value and the resulting zero regret use no supremum
fallback. No zero sample size, extended-real conversion, logarithm, root,
unbounded limit, truncated subtraction, or partial-function default occurs.
