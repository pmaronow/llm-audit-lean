# Blind reading (written before opening claims.json / record.json)

Common objects (SAP/P010/Defs/Part3.lean):

- `Population K d = (Fin K → ℝ) × (Fin K → Bool) × Fin K × (Fin d → ℝ)` (Part3:11) with the product /
  pi σ-algebras (Borel on ℝ, ⊤ on `Bool`, `Fin K`). A state ω = (Y(·), S(·), Z, X): potential responses
  Y(a), potential checks S(a), assigned arm Z, covariates X.
- `potentialOutcome a ω = Y(a)` (Part3:16), `potentialCheck a ω = S(a)` (Part3:17), `arm ω = Z` (Part3:18),
  `response ω = Y(Z)` (Part3:20), `check ω = S(Z)` (Part3:21).
- `allPass = {∀a, S(a)=true}` (Part3:22), `assigned a = {Z=a}` (Part3:24), `passed = {S(Z)=true}` (Part3:25),
  `wouldPass a = {S(a)=true}` (Part3:26).
- `meanOn μ f E = (∫_E f dμ) / (μ E).toReal` (Part3:28). Junk: if μE = 0 or μE = ∞ the value is 0
  (division by 0 / toReal ∞ = 0); if f is not integrable on E the Bochner integral is 0.
- `passRate μ a = μ(passed ∩ assigned a).toReal / μ(assigned a).toReal` (Part3:35). Junk: /0 = 0.
- `randomAssignment μ` (Part3:38): ∀a, (Y(a),S(a)) ⫫ Z under μ, and ∀a, μ(Z=a) > 0.
- `positivePassRates μ` (Part3:42): ∀a, passRate μ a > 0.
- `populationAssumptions μ` (Part3:45): μ probability ∧ randomAssignment ∧ positivePassRates.

Part5 objects:

- `conditionalLaw μ f E = (μ E)⁻¹ • (μ|_E).map f` (Part5:13). Junk: μE = 0 gives `0⁻¹ = ∞` times the zero
  measure = 0; if f is not (ae-)measurable `map` gives 0.
- `trimmingRatio μ a = (Σ_{b≠a} (1 − passRate μ b)) / passRate μ a` (Part5:17). Junk /0.
- `passerDistribution μ a = conditionalLaw μ response (passed ∩ assigned a)` (Part5:20): law of Y given S=1, Z=a.
- `leftQuantile ν u = sInf {x : EReal | u ≤ (ν{y : ℝ | ↑y ≤ x}).toReal}` (Part5:23). For a probability ν and
  u ∈ (0,1] it is the usual left quantile inf{x : F(x) ≥ u} (finite unless the tail forces ±∞, which cannot happen
  for u ∈ (0,1)); for u ≤ 0 it is ⊥ (x = ⊥ qualifies); for u > 1 the set is empty and the value is ⊤.
  If ν is not a probability measure (e.g. 0) the value is junk.
- `noAtoms ν = ∀x, ν{x} = 0` (Part5:28); `fullRealSupport μ f` (Part5:30): every open interval has positive
  μ-mass of f.
- `upperEndpoint μ a = meanOn μ response ((passed ∩ assigned a) ∩ {leftQuantile(passerDistribution μ a)
  (trimmingRatio μ a) ≤ ↑response})` (Part5:40): the mean of Y over arm-a passers whose response is at or above
  the trimmingRatio-quantile of the arm-a passer law (Lee-type upper trimmed mean).
- `otherArmsPass a = {∀b≠a, S(b)=true}` (Part5:61).
- `potentialTrimShare μ a = (Σ_{b≠a} μ{S(b)=false}.toReal) / μ(wouldPass a).toReal` (Part5:63).
- `tailCoupling F p γ` (Part5:67): γ is a probability measure on ℝ × Bool with first marginal F and
  γ{second = false}.toReal = p.
- `upperTailMean F p = meanOn F id {y | leftQuantile F p ≤ ↑y}` (Part5:70) = E_F[Y | Y ≥ F⁻¹(p)].
- `fairArmDistribution = ½δ₀ + ½δ₁` on Fin 2 (Part5:102).
- `commonOutcomePopulation s F = (F ⊗ fair).map (y,z) ↦ (![y,y], ![s,s], z, 0)` (Part5:122).
- `normalCommonPopulation = 4/5·commonOutcomePopulation true N(0,1) + 1/5·commonOutcomePopulation false N(0,1)`
  (Part5:138).

All `…._proof_n` entries in the closures (T11Statement._proof_1..8, cellPropensity._proof_1,
originalDistribution._proof_1/2, T3Statement._proof_1/2/4, T5Statement._proof_9, heavyTailDistribution._proof_1,
jointDependenceAtoms._proof_1, jointDependencePopulation._proof_1, laplaceDistribution._proof_1,
conditionalLaw._proof_1) were printed (scratch/Check.lean): they are `Nat.AtLeastTwo` / `NeZero` numeral
instances and `IsScalarTower ℝ≥0∞ ℝ≥0∞ ℝ≥0∞`; no semantic content.

---

## SAP.P010.T11 (Challenge/Part1.lean:58, statement `T11Statement`, Defs/Part4.lean:64)

Definitions (Defs/Part2.lean): `propensity π fR fO = π fR / (π fR + (1−π) fO)` (13); `odds p = p/(1−p)` (15);
`reverseOdds p = (1−p)/p` (17); `normalizeMass f w x = f x w x / Σ_u f u w u` on `Fin n` (19);
`originalDistribution = (3/4, 1/4)` (22); `replicationDistribution = (1/4, 3/4)` (24);
`cellPropensity x = propensity (1/2) (fR x) (fO x)` with fR = replication, fO = original (26), i.e.
P(replication | cell x) with equal study shares π = 1/2 (replication membership coded 1);
`sigmoid η = e^η/(1+e^η)` (29).

Plain statement: a closed numerical proposition (no quantified data except q₀, q₁), a conjunction of

(A) logistic fit:
1. sigmoid(log(1/3)) = 1/4 and sigmoid(log(1/3) + log 9) = 3/4 (intercept β₀ = log(1/3), slope β₁ = log 9 on the
   cell indicator);
2. for all q₀, q₁ ∈ (0,1): ℓ(q₀,q₁) := log q₀ + 3 log(1−q₀) + 3 log q₁ + log(1−q₁) ≤ ℓ(1/4, 3/4), with equality
   iff (q₀,q₁) = (1/4,3/4). This is the (binomial) log-likelihood of a saturated two-cell logistic model for
   replication membership when cell 0 holds replication:original = 1:3 and cell 1 holds 3:1 (the population
   proportions π fR : (1−π) fO with π = 1/2); its unique maximiser is the true cell propensity, which the logistic
   parameters in 1 attain.

(B) weighting:
1. for x ∈ {0,1}: fO x > 0, fR x > 0, 0 < cellPropensity x < 1;
2. cellPropensity 0 = 1/4, cellPropensity 1 = 3/4;
3. odds: 1/3 and 3;
4. fR(0)·odds = 1/12, fR(1)·odds = 9/4, total 7/3;
5. normalised odds-weighted replication share of cell 1 = (9/4)/(7/3) = 27/28, and 27/28 ≠ fO(1) = 1/4;
6. for both cells, normalizeMass fR (reverseOdds ∘ cellPropensity) x = fO x (weights 3 and 1/3; sum 1).

Junk values: `Real.log` only at positive arguments (q's ∈ (0,1), 1/3, 9, 1/4, 3/4) – none outside the domain.
Divisions: `odds`/`reverseOdds` at 1/4, 3/4 (denominators nonzero); `normalizeMass` denominators 7/3 and 1
(nonzero); `propensity` denominators 1/2. No `Fin`/`Nat` casts beyond numerals. No junk value can affect meaning.

## SAP.P010.T12 (Challenge/Part1.lean:72, statement `T12WholeStatement`, Defs/WholeW1.lean:38)

Definitions: `propensity`, `odds`, `reverseOdds` as above; `normalizeDensity ν f w x = f x w x / ∫ f w dν`
(Part2:31); `squareRatioMass ν fR fO = ∫⁻ ofReal(fR²/fO) dν` (WholeW1:16);
`printedWeightedMass ν π fR fO = ∫⁻ ofReal(fR · odds(propensity π fR fO)) dν` (WholeW1:22).

Plain statement: for every universe-u type Ω with σ-algebra, every measure ν on Ω (no σ-finiteness needed), every
real π and functions fR, fO : Ω → ℝ, assuming 0 < π < 1, fR > 0 ν-a.e., fO > 0 ν-a.e., fR and fO integrable with
∫ fR = ∫ fO = 1 (probability densities w.r.t. ν with common support = Ω mod ν), and writing
p(x) = π fR/(π fR + (1−π) fO) (true probability of replication membership given x, replication coded 1, π the
replication share) and Z = ∫⁻ ofReal(fR²/fO) ∈ [0,∞]:

1. a.e.: 0 < p < 1, p/(1−p) = (π/(1−π))(fR/fO), fO/fR = (π/(1−π))·(1−p)/p (Bayes odds identities);
2. a.e.: odds(1−p) = reverseOdds(p) (coding original membership 1 gives the reciprocal-odds weights);
3. fR·(1−p)/p is integrable and ∫ fR(1−p)/p dν = (1−π)/π;
4. normalizeDensity ν fR ((1−p)/p) = fO a.e. (reciprocal odds transport replication density to original);
5. for every c > 0 the same with weights c·(1−p)/p (scale cancels);
6. printedWeightedMass = ofReal(π/(1−π)) · Z (in [0,∞]);
7. if Z < ∞: fR²/fO integrable, Z > 0, Z.toReal > 0, 0 < printedWeightedMass < ∞, fR·odds(p) integrable with
   Bochner integral (π/(1−π)) Z.toReal > 0, normalizeDensity ν fR (odds ∘ p) = fR²/fO / Z.toReal a.e., and
   [that normalised density = fO a.e.] ⇔ fR = fO a.e.;
8. if Z = ∞: printedWeightedMass = ∞ and for every c ∈ ℝ≥0, ν.withDensity(c · ofReal(fR · odds p)) is not a
   probability measure.

Junk values: `propensity`, `odds`, `reverseOdds` divide by quantities that vanish only where fR or fO ≤ 0, a ν-null
set; every assertion is a.e. or an integral, so off-null-set junk is irrelevant. `normalizeDensity` divides by a
Bochner integral; in 4/5 that integral is (1−π)c/π > 0 and the integrand is proved integrable (3); in 7 the
integrand is integrable (Z < ∞) and the integral is positive. When Z = ∞ the Bochner integral of fR·odds would be
the junk value 0 and normalizeDensity would be identically 0; the statement avoids this by speaking only of the
extended mass and of `withDensity`, so no junk value enters. `ofReal` truncation of negatives only matters on the
null set where fO ≤ 0. `Z.toReal` used only under Z < ∞. c = 0 in clause 8 gives the zero measure, correctly not
a probability measure.

## SAP.P010.T13 (Challenge/Part1.lean:76, statement `T13Statement`, Defs/Part6.lean:162)

Witness: μ = normalCommonPopulation on Population 2 0: with probability 4/5 a unit passes the check under both
arms, with probability 1/5 fails under both; Y(0) = Y(1) = y ~ N(0,1) independent of the check stratum and of
Z ~ fair coin on {0,1}.

Plain statement: a conjunction of the facts
1. populationAssumptions μ (probability, (Y(a),S(a)) ⫫ Z, μ(Z=a)=1/2>0, pass rates >0); μ(allPass) = 4/5;
   μ∘response⁻¹ has no atoms; response has full real support;
2. for a ∈ {0,1}: passRate μ a = 4/5 and passerDistribution μ a = N(0,1);
3. potentialTrimShare μ 0 = 1/4 = trimmingRatio μ 0;
4. meanOn μ Y(0) allPass = 0, and meanOn μ Y(0) (otherArmsPass 0 ∩ wouldPass 0) = 0 (same set as allPass);
5. with q = Φ⁻¹(3/4) (toReal of `leftQuantile N(0,1) (3/4)`): meanOn μ Y(0) {Y(0) ≤ q} = −φ(q)/(3/4) < 0, and
   ¬(always-passer mean 0 ≤ that value) – i.e. a lower-tail mean E[Y(0) | Y(0) ≤ Φ⁻¹(3/4)] taken over the whole
   population (not restricted to passers or to arm 0) lies strictly below the always-passer mean;
6. upperEndpoint μ 0 = φ(Φ⁻¹(1/4))/(3/4) > 0 (the corrected Lee upper endpoint for arm 0 with trimming 1/4).

Junk values: `leftQuantile` at 3/4 and 1/4 of a probability measure – finite, so `toReal` is not junk.
`meanOn` denominators are μ(allPass)=4/5, μ{Y(0) ≤ q}=3/4, μ(passed∩assigned 0 ∩ {…}) = 3/10, all positive and
finite; integrands are Gaussian, integrable. passRate denominators 1/2. potentialTrimShare denominator
μ(wouldPass 0) = 4/5. No junk value can affect meaning. Note: item 5 uses the set {Y(0) ≤ q} over the whole
population; because Y(0) is independent of (S, Z) in this witness, its value equals the passer-arm-0 lower-tail
mean E[Y | Y ≤ q, S=1, Z=0]; whether item 5 is the "printed" bound must be checked against the claim.

## SAP.P010.T14 (Challenge/Part1.lean:80, statement `T14Statement`, Defs/Part6.lean:180)

Let F := conditionalLaw μ Y(a) (wouldPass a) = law of Y(a) given S(a)=1.

Plain statement: for all K, d, every measure μ on Population K d and arm a, assuming μ is a probability measure,
μ(allPass) > 0, F has no atoms, and Y(a) is integrable on {S(a)=1}:
1. for every p ∈ [0,1): (a) every probability coupling γ of F with a Bool "kept" indicator that discards mass
   exactly p satisfies E_γ[Y | kept] ≤ upperTailMean F p = E_F[Y | Y ≥ F⁻¹(p)]; (b) the coupling
   γ* = law of (Y, 1{F⁻¹(p) ≤ Y}) under F is such a coupling (discarded mass p) and attains equality;
2. p ↦ upperTailMean F p is monotone non-decreasing on [0,1);
3. μ({∃b≠a, S(b)=false} ∩ {S(a)=true}) / μ(S(a)=true) ≤ potentialTrimShare μ a = Σ_{b≠a} μ(S(b)=false)/μ(S(a)=true)
   (union bound);
4. if potentialTrimShare μ a < 1, then E[Y(a) | allPass] ≤ upperTailMean F (potentialTrimShare μ a).
No random-assignment or positive-pass-rate hypothesis is used (statement is about potential quantities only).

Junk values: μ(allPass) > 0 ⇒ μ(S(a)=true) > 0, so F is a probability measure (no 0⁻¹ junk) and
potentialTrimShare has a positive denominator. For p ∈ [0,1) and atomless F, F{Y ≥ F⁻¹(p)} = 1−p > 0, so the
meanOn in upperTailMean has a positive denominator; for p = 0, leftQuantile = ⊥ and the set is ℝ (mean of F).
Integrability of id under F follows from `hi`. In 1(a), γ{kept} = 1−p > 0 and fst is γ-integrable because its
γ-law is F. In 4, meanOn μ Y(a) allPass has a positive finite denominator and integrable integrand
(allPass ⊆ wouldPass a). Requiring p < 1 avoids the junk upperTailMean at p = 1. No junk value affects meaning.

## SAP.P010.T15 (Challenge/Part1.lean:84, statement `T15Statement`, Defs/Part6.lean:200)

Plain statement: for all K, d, every μ on Population K d and arm a, assuming populationAssumptions μ
(probability, (Y(b),S(b)) ⫫ Z ∀b, μ(Z=b) > 0, pass rates > 0), μ(allPass) > 0, the law of the response
Y(Z) has no atoms, and Y(Z) integrable on {S=1, Z=a}:
1. law(Y(a) | S(a)=1) = passerDistribution μ a = law(Y | S=1, Z=a);
2. ∀b, μ(S(b)=true) = passRate μ b;
3. potentialTrimShare μ a = trimmingRatio μ a;
4. if trimmingRatio μ a < 1: (a) upperTailMean(law(Y(a)|S(a)=1), trimmingRatio) = upperEndpoint μ a;
   (b) E[Y(a) | allPass] = E[Y(a) | otherArmsPass a ∩ wouldPass a] (these sets are equal); (c)
   E[Y(a) | allPass] ≤ upperEndpoint μ a (the corrected observable upper bound).

Junk values: passRate denominators μ(Z=b) > 0 (randomAssignment); passRate a > 0, so trimmingRatio has a positive
denominator; passerDistribution is a probability measure since μ(S=1,Z=a) = passRate·μ(Z=a) > 0; trimmingRatio ≥ 0
(pass rates ≤ 1) and < 1 in item 4, so leftQuantile is finite (or ⊥ at 0) and the upper set has passer mass
1 − trimmingRatio > 0 (no atoms of the response law ⇒ none of the passer law). meanOn μ Y(a) allPass: positive
denominator; integrability of Y(a) on allPass follows from `hi` plus independence (law of Y(a) on wouldPass a is
the passer law). No junk value affects the meaning.
