# Blind reading (saved before opening claims.json or record.json)

I read the three Challenge docstrings/statements, every named declaration in their
closure, and the bodies of all 24 generated auxiliary proof declarations using
`scratch/BlindInspect.lean` (compiled successfully). This document records only
that source-based reading. Source locations below refer to the supplied files.

## Mathematical notation used to unfold the finite definitions

For a finite type L (Lean `[Fintype L]`), a mass function p:L→ℝ is a probability
law precisely when every p(i)≥0 and Σᵢp(i)=1. For any real-valued f and predicate
A on L, write

* Eₚf=Σᵢp(i)f(i), Pₚ(A)=Σᵢ(if A(i) then p(i) else 0);
* Eₚ[f|A]=(Σᵢp(i)(if A(i) then f(i) else 0))/Pₚ(A);
* Covₚ(f,g)=Σᵢp(i)f(i)g(i)−(Σᵢp(i)f(i))(Σᵢp(i)g(i));
* Varₚ(f)=Covₚ(f,f), Corrₚ(f,g)=Covₚ(f,g)/√(Varₚ(f)Varₚ(g)).

All sums are Mathlib `Finset.univ` sums, and all division and square roots are
Lean real division and `Real.sqrt`. Independence of maps V:L→A and W:L→B means
∀a:A ∀b:B, Pₚ(V=a∧W=b)=Pₚ(V=a)Pₚ(W=b). There is no measurability premise in
these finite definitions. The notation b̄ denotes 1 if the Boolean b is true and
0 otherwise (`indicatorValue`).

A `PotentialResponse X` is exactly a record (x:X,d₀:Bool,d₁:Bool,y₀:ℝ,y₁:ℝ),
with no axioms on its fields. Its constructor and five projections are the
ordinary record constructor/projections. Effect is y₁−y₀, complier means
d₀=false∧d₁=true, and defier means d₀=true∧d₁=false. Given z:Bool, D(z) is d₁
if z is true and d₀ otherwise; Y(z) is y₁ if D(z) is true and y₀ otherwise.
Thus the observed outcome uses treatment receipt alone. `assignResponse U`
on L×Bool is (i,z)↦U(i). `bernoulliProductMass p e` is
(i,z)↦p(i)(if z then e else 1−e).

`FiniteIVConditions` for such records and Z:L→Bool is exactly the conjunction:
p is a probability law; 0<Pₚ(Z=true)<1; Z is independent (in the fiber-sum
sense above) of the tuple (x,d₀,d₁,y₀,y₁); Pₚ(defier)=0; and
Eₚ[D̄(Z)|Z=true]−Eₚ[D̄(Z)|Z=false]≠0. There is no additional assumption hidden
in that predicate. `FiniteLatentIgnorability` means ∀x:X,
Pₚ(xᵢ=x)>0 → Eₚ[y₁−y₀|xᵢ=x]=Eₚ[y₁−y₀|complier∧xᵢ=x].
`finiteComplianceScore p U x` is Pₚ(complier∧xᵢ=x)/Pₚ(xᵢ=x).

`finiteWald` for real weights w is the following real number. For f=Y(Z) or
f=D̄(Z), set M_z(f)=Eₚ[wf|Z=z]/Eₚ[w|Z=z], using the explicit finite sums
above. The number is (M_true(Y)−M_false(Y))/(M_true(D̄)−M_false(D̄)).

## SAP.P029a.T11

Location: `SAP/P029a/Challenge/Part1.lean:100–103`. The docstring calls these
two explicit constant-effect SEM laws with exogeneity, relevance, endogeneity,
and two distinct failures of IV conditions. The theorem has no parameters or
hypotheses: it asserts the conjunction of the following closed propositions.

First law (`Defs/Part2.lean:96–104`, `Defs/Part4.lean:131–151`): L=Bool×Bool,
i=(t,z), x=(), d₀=t, d₁=¬t, u=y₀=t̄−1/4, y₁=u+1. Mass is
(if t then 1/4 else 3/4)(if z then 1/4 else 3/4). Define the real residual
v=D̄(z)−1/4−z̄/2. Explicitly:

| (t,z) | mass | u | D̄ | v | Y |
|---|---:|---:|---:|---:|---:|
| (false,false) | 9/16 | −1/4 | 0 | −1/4 | −1/4 |
| (false,true) | 3/16 | −1/4 | 1 | 1/4 | 3/4 |
| (true,false) | 3/16 | 3/4 | 1 | 3/4 | 7/4 |
| (true,true) | 1/16 | 3/4 | 0 | −3/4 | 3/4 |

The theorem asserts that this is a probability law; the full response tuple is
independent of Z=z; ∀i, effect=1, Y=D̄+u, and D̄=1/4+z̄/2+v; ∀z:Bool,
E[v|Z=z]=0; E[Z̄]=1/4, Var(Z̄)=3/16, E[u]=0, Var(u)=3/16,
Cov(Z̄,u)=0, Corr(Z̄,u)=0, Cov(Z̄,D̄)=3/32, Cov(D̄,u)=3/32,
and P(defier)=1/4. Each quantity is the finite sum/quotient defined above.

Second law (`Defs/Part2.lean:106–113`, `Defs/Part4.lean:153–168`): L=Fin 4,
each mass is 1/4; x=(), u=y₀ is the indexed vector [−2,−1,1,2], y₁=u+1,
d₀ is the Boolean decision of 0<u, d₁=true, and Z is true precisely at indices
0 and 3. Define v=D̄(Z)−1/2−Z̄/2. Explicitly:

| i | u | Z̄ | d̄₀ | D̄ | v | Y |
|---|---:|---:|---:|---:|---:|---:|
| 0 | −2 | 1 | 0 | 1 | 0 | −1 |
| 1 | −1 | 0 | 0 | 0 | −1/2 | −1 |
| 2 | 1 | 0 | 1 | 1 | 1/2 | 2 |
| 3 | 2 | 1 | 1 | 1 | 0 | 3 |

It asserts this is a probability law; ∀i, effect=1, Y=D̄+u, and
D̄=1/2+Z̄/2+v; ∀z:Bool, E[v|Z=z]=0 and E[u|Z=z]=0;
Var(Z̄)=1/4, Var(u)=5/2, Corr(Z̄,u)=0, Cov(Z̄,D̄)=1/8,
Cov(D̄,u)=1/4, P(defier)=0, and u and Z are not independent. The latter
negates the universally quantified fiber-probability factorization.

Finally (`Defs/Part6.lean:16–44`) it asserts the extra moment values: for the
first law, E[D̄|Z=false]=1/4, E[D̄|Z=true]=3/4, and
Cov(Z̄,Y)/Cov(Z̄,D̄)=1; for the second, the corresponding receipt means are
1/2 and 1, Cov(Z̄,u)=0, Cov(Z̄,Y)/Cov(Z̄,D̄)=1, and
E[1_{|u|=2}|Z=true]=1 whereas E[1_{|u|=2}|Z=false]=0.
`T11Statement` (`Defs/Part6.lean:141`) is exactly these three conjunctions.

Junk-value audit: generic conditional means divide by zero on null events and
then equal 0; generic correlations are 0 if their square-root denominator is
0 (and `Real.sqrt` is 0 on negative arguments). Here both arms have strictly
positive mass, the correlation variance products are (3/16)² and 5/8, and
the two Wald covariance denominators are 3/32 and 1/8. No such default affects
the statement. The index types are nonempty. Fin 4 vector lookup is total at
all four indices; Bool decisions and negation are total. All subtraction is
in ℝ, including differences of indicators; no truncated natural subtraction
occurs. All constants have nonzero rational denominators. There are no
integrals, logs, rpow, extended reals, extrema, limits or partial functions.

Its closure also includes generated proofs under `SEMDefierFacts` (five),
`SEMDependenceFacts` (two), and `SEMWitnessMeans` (three), plus
`specifiedInsideLogRates._proof_1` and
`specifiedUnweightedScores._proof_1/_proof_2`. Their actual printed bodies
are elementary `Nat.instAtLeastTwoHAddOfNat` proofs: they certify that the
numeral bases 4,2,3,16,32; 5,8; 4,3,2; and 2,3,4, respectively, are at least
two. They impose no hypotheses and introduce no statistical definition.
The two `specified...` parent functions are simply Boolean selections of
rational constants; only the auxiliary numeral proofs enter this statement.

## SAP.P029a.T12

Location: `SAP/P029a/Challenge/Part1.lean:105–108`. Its docstring claims
non-nesting between SEM and IV assumptions, constant effect under the SEM
potential-outcome equations, and ATE/LATE 3/2 for a heterogeneous all-complier
law. The theorem is closed, with universe parameters u,v and no external
hypotheses. `T12Statement` (`Defs/Part6.lean:144–146`) is a conjunction of
five propositions, with their quantifiers scoped separately:

1. All assertions of the first SEM law in the T11 section, through
   P(defier)=1/4, including law validity and full-tuple independence.
2. All assertions of the second SEM law there, through failure of u/Z
   independence, including both zero arm means. These first two components
   do not include `SEMWitnessMeans` or its extra Wald/arm/absolute-value values.
3. (`Defs/Part4.lean:178–183`) For every type I, every type K with a Fintype,
   every Y₀,Y₁,u:I→ℝ, Q:I→K→ℝ, β₀,β₁:ℝ, and coeff:K→ℝ, if
   (∀i, Y₀(i)=β₀+Σₖcoeff(k)Q(i,k)+u(i)) and
   (∀i, Y₁(i)=β₀+β₁+Σₖcoeff(k)Q(i,k)+u(i)), then
   ∀i:I, Y₁(i)−Y₀(i)=β₁. These are shared-error potential-outcome equations;
   there is no independence premise in this elementary subtraction assertion.
4. (`Defs/Part2.lean:115–116`, `Defs/Part4.lean:170–176`) On L=Bool×Bool,
   (h,z) has mass 1/4 at each of four points. Its record has x=(), d₀=false,
   d₁=true, y₀=0, y₁=2 if h=true and 1 otherwise, and Z=z. This law meets
   every `FiniteIVConditions` clause expanded above. The two effects are
   respectively 1 and 2; there does not exist any β:ℝ for which all h:Bool
   have effect β; the unconditional mean effect is 3/2; and the weighted
   finite Wald ratio with all weights 1 is 3/2. The negated existential
   quantifies over a common β and then universally over both h values.
5. (`Defs/Part6.lean:46–58`) For that same law, E[effect|complier]=3/2,
   Cov(Z̄,D̄)=1/4, E[D̄|Z=true]−E[D̄|Z=false]=1, and ∀t:Bool,
   P(effect=(if t then 2 else 1))=1/2.

Every response, expectation, law, independence and ratio here has the record,
finite-sum, and real-arithmetic expansion given above, so no additional SAP
notion remains implicit. The first two laws have exactly the data tables in
the preceding section; the third has D=Z and effect 1+h̄.

Junk-value audit: the SEM witnesses have the positive arm masses and positive
variance products already computed. In the heterogeneous law arm masses are
1/2, all individuals are compliers, covariate () has probability 1, the
complier event has probability 1, each weighted arm denominator is 1, and the
receipt difference is 1. Thus no zero denominator or non-real correlation
occurs. The algebraic SEM assertion permits I empty, making that instance
vacuous, and permits K empty, making the sum 0; it also includes nonempty I,K
instances and remains an ordinary identity there. This does not empty the
whole theorem. `Fin 4`, Bool, and product indices are nonempty and all maps
total; casts and subtraction have their ordinary real meanings. No integrals,
logs, rpow, extrema, limits, or partial-function defaults occur.

Its generated closure proofs are the same numeral certificates as for T11
(including three `SEMWitnessMeans` proofs even though that proposition is not
a conjunct). The record constructor/projections and `assignResponse` are
total; none has a default value or additional axiom.

## SAP.P029a.T13

Location: `SAP/P029a/Challenge/Part1.lean:110–114`. The docstring claims
closed-domain likelihood optima, a biased compliance-score estimate, its
certificates and raw-difference expectation, and a five-per-arm positive-part
example; it explicitly includes boundary probabilities and natural powers.
The theorem has no parameters or hypotheses. `T13Statement`
(`Defs/Part6.lean:149–151`) conjoins the following five closed assertions.

Population and two-record witness (`Defs/Part4.lean:198–210`): take types
j:Fin 3 with probabilities (1/2,1/4,1/4) and independent Z:Bool with
P(Z=true)=1/2. The six atoms (j,z) have mass p(j)/2 (`sixAtomMass`).
Every record has x=(), y₀=0,y₁=1; d₀ is true exactly when j=1, d₁ is true
exactly when j≠2 (`constantResponse`, `assignResponse`). Thus j=0,1,2 are
respectively complier, always-taker, never-taker. This population meets all
the expanded finite IV conditions and the expanded latent mean equality.
Its compliance probability at () is 1/2>1/4, and its receipt means given
Z=true and false are respectively 3/4 and 1/4.

Separately the sample space d=(d₁,d₀):Bool×Bool has mass
(if d₁ then 3/4 else 1/4)(if d₀ then 1/4 else 3/4)
(`twoReceiptMass`). This is asserted to be a probability law and encodes
independent arm observations. The allowed real pair (p,q) lies in
{(p,q):0≤q≤p≤1} (`closedReceiptTriangle`). The likelihood is
[p^(if d₁ then 1 else 0) (1−p)^(if d₁ then 0 else 1)] ×
[q^(if d₀ then 1 else 0) (1−q)^(if d₀ then 0 else 1)]
with all four exponents natural numbers (`bernoulliContribution`,
`twoReceiptLikelihood`). The prescribed fit (`twoReceiptFit`) and mass are:

| d | fitted (p,q) | mass | fitted likelihood | fitted p−q |
|---|---|---:|---:|---:|
| (false,false) | (0,0) | 3/16 | 1 | 0 |
| (false,true) | (1/2,1/2) | 1/16 | 1/4 | 0 |
| (true,false) | (1,0) | 9/16 | 1 | 1 |
| (true,true) | (1,1) | 3/16 | 1 | 0 |

For every d:Bool×Bool the fitted pair belongs to that triangle, and for every
real pair v belonging to the triangle its likelihood is ≤ that at the fitted
pair. This is global maximality, not a uniqueness assertion. The expectation
of fitted p−q is 9/16, unequal to the population compliance probability 1/2.

The second conjunct (`Defs/Part4.lean:212–219`) reiterates sample-law validity,
asserts ∀d, fitted p−q=1 exactly in the (true,false) case and 0 otherwise,
its expectation 9/16, the raw indicator-difference expectation
E[d̄₁−d̄₀]=1/2, and bias 9/16−1/2=1/16≠0. It also asserts the nested receipt
probability a(1−b)z̄+ab at a=3/4,b=1/3 equals 3/4 for z=true and 1/4 for
z=false (`nestedReceiptProbability`).

The third conjunct (`Defs/Part4.lean:193–196`) concerns independent count
variables k₁:Fin 6 and k₀:Fin 6. In general
`binomialCountMass n p k`=(n choose k.val) p^(k.val)(1−p)^(n−k.val), with
the binomial coefficient cast from ℕ to ℝ, and
`independentArmCountMass n₁ n₀ p₁ p₀` is the product of these two masses.
Here n₁=n₀=5, p₁=1/2,p₀=3/10. The score is
max((k₁.val:ℝ)/5−(k₀.val:ℝ)/5,0) (`empiricalPositiveScore`,
`positiveComplianceDifference`). Its expectation is 15659/64000, its excess
above 1/5 is 2859/64000, and P(k₁.val<k₀.val)=257079/1600000.
These are claims about that particular finite product-binomial law, not
universal claims about arbitrary counts or zero sample sizes.

The fourth conjunct (`Defs/Part6.lean:60–66`) universally quantifies p,q:ℝ
with no constraints and asserts four polynomial identities:

* 1−(1−p)(1−q)=p+(1−p)q;
* 1/4−(1−p)q=(p−1/2)²+(1−p)(p−q);
* 1−p(1−q)=(1−p)+pq;
* 1−pq=(1−p)+p(1−q).

The fifth (`Defs/Part6.lean:68–76`) asserts all four fitted pairs, fitted
likelihoods, and sample masses in the displayed table; its likelihood formula
is quantified over all d. These identities and inequalities certify an
actual nonzero bias for a valid finite population and independent arm law.

Junk-value audit: natural powers explicitly give 0^0=1, including at the
fitted boundary probabilities. This affects likelihood values and agrees
with dropping the Bernoulli factor for the unobserved outcome. The closed
triangle includes p,q=0 or 1; no logarithm of a boundary value is used.
All powers are natural powers, never rpow. In the binomial mass, natural
subtraction n−k.val is truncated in general but k:Fin(n+1) ensures k.val≤n,
so here it is ordinary subtraction; the cast of the binomial coefficient
does not truncate. The generic score allows n₁=0 or n₀=0, causing real
division by zero to return 0, but this theorem uses only n₁=n₀=5.
Population arm probabilities are 1/2, the covariate event has probability 1,
and the complier event has probability 1/2, so all conditional/compliance
denominators are positive. The latent equality definition would use a
zero-event default at an unsupported complier profile, but the only profile
here is () with positive complier mass. Relevance is a receipt difference of
1/2. All index types are nonempty, all lookup maps are total, and all
non-count subtraction is in ℝ. There are no Bochner integrals, `toReal`,
logs, square roots, infima/suprema, limits or partial functions in this target.

Remaining closure auxiliaries: `ClosedFitValues._proof_1/_proof_2` certify
numeral bases 16 and 9 are at least two; the six `FivePerArmBiasFacts`
proofs certify bases 10,15659,64000,2859,257079,1600000; the
`SaturatedBiasWitnessFacts` proof certifies base 9; the two
`complianceTypeMass` proofs certify bases 2 and 4. The SEM and specified-score
auxiliary proofs also included in this closure are the same elementary
numeral certificates already enumerated. All were individually printed and
read; none adds a premise, a placeholder, or a hidden statistical claim.
