# Blind reading of SAP.P010.T1–T5 (written before opening claims.json / record.json)

Common objects (SAP/P010/Defs/Part3.lean, Part5.lean):

* `Population K d = (Fin K → ℝ) × (Fin K → Bool) × Fin K × (Fin d → ℝ)` (Part3:13): a unit is
  (potential outcomes Y(·), potential checks S(·), assigned arm Z, covariates X). σ-algebra: product of the
  Pi Borel σ-algebra, ⊤ on `Fin K → Bool`, ⊤ on `Fin K`, Pi Borel on `Fin d → ℝ`.
* `potentialOutcome a ω = Y(a)`, `potentialCheck a ω = S(a)`, `arm ω = Z`, `response ω = Y(Z)`,
  `check ω = S(Z)` (Part3:16–21). `allPass = {∀ a, S(a) = true}` (always-passers, Part3:22),
  `assigned a = {Z = a}`, `passed = {S(Z) = true}` (Part3:24–25).
* `meanOn μ f E = (∫_E f dμ) / (μ E).toReal` (Part3:31). Junk: = 0 if μ E = 0 or μ E = ∞ (toReal), and the
  numerator is 0 if f is not integrable on E. So `meanOn` is E[f | E] only when 0 < μ E < ∞ and f ∈ L¹(μ|E).
* `passRate μ a = μ(S(Z)=1, Z=a).toReal / μ(Z=a).toReal` = Pr(S=1 | Z=a) (Part3:35); junk 0 if μ(Z=a)=0.
* `randomAssignment μ` (Part3:38): for every arm a, the pair (Y(a), S(a)) is independent of Z under μ
  (**per-arm** independence, not joint independence of the whole vector (Y(·),S(·)) and Z), and μ(Z=a) > 0 for all a.
* `positivePassRates μ`: ∀ a, Pr(S=1|Z=a) > 0. `populationAssumptions μ` = μ is a probability measure ∧
  randomAssignment ∧ positivePassRates (Part3:45).
* `conditionalLaw μ f E = (μ E)⁻¹ • (μ|E).map f` (Part5:13) — the law of f given E (junk if μ E ∈ {0,∞}:
  `0⁻¹ = ∞` gives ∞•…, which is the zero measure only if the restricted map is 0).
* `trimmingRatio μ a = (Σ_{b≠a} (1 − p_b)) / p_a` with p_b = passRate (Part5:17); junk if p_a = 0.
* `passerDistribution μ a = conditionalLaw μ response (passed ∩ assigned a)` = law of Y given S=1, Z=a (Part5:20).
* `leftQuantile ν u = sInf {x : EReal | u ≤ (ν {y | (y:EReal) ≤ x}).toReal}` (Part5:23): EReal-valued left
  quantile F⁻¹(u) = inf{x | F(x) ≥ u}. Junk: = ⊥ for u ≤ 0, can be ⊤ for u = 1 (unbounded support) or u > 1;
  for a probability ν and u ∈ (0,1) it is a real number. `realQuantile = (leftQuantile ν u).toReal` (Part5:26),
  sending ⊥, ⊤ to 0 (only at u ∈ {0,1}, a null set in interval integrals).
* `noAtoms ν` (Part5:28): ν{x} = 0 for all x. `fullRealSupport μ f` (Part5:30): every open interval has positive
  μ-mass under f. `allMoments μ f` (Part5:33): |f|^n integrable for all n.
* `lowerEndpoint μ a = meanOn μ response (passed ∩ assigned a ∩ {Y ≤ F⁻¹_{pass,a}(1 − r_a)})`,
  `upperEndpoint μ a = meanOn μ response (passed ∩ assigned a ∩ {Y ≥ F⁻¹_{pass,a}(r_a)})` (Part5:36–42), with
  r_a = trimmingRatio and F_{pass,a} = passerDistribution: the Lee-type trimmed means of passers in arm a,
  **conditioning on passing**.
* `compatiblePopulations μ ν` (Part5:44): ν satisfies populationAssumptions, ν(allPass) > 0, and the joint law
  of the observables (Y, S, Z) = (response, check, arm) under ν equals that under μ (covariates are not observed
  for this purpose). `compatibleMeans μ a = {meanOn ν (Y(a)) allPass | ν compatible}` (Part5:49):
  the identified set of the always-passer mean E_ν[Y(a) | always-pass]. `extendedCompatibleMeans` (Part5:52) is
  its image in EReal.

## SAP.P010.T1 (Challenge/Part1.lean:12, T1Statement Defs/Part4.lean:11)

Docstring: "The printed claim is false: the unweighted preference interval for 90–90 is disjoint from each
other arm."

Data (Defs/Part1.lean:12–38), arms 0,1,2 = 90–90, 90–70, 90–45, all supplied constants:
n = sampleSize = (544, 538, 533); f = failures = (35, 182, 40); passers = n − f = (509, 356, 493) (ℕ
subtraction, no truncation since f ≤ n); preferCount = (61, 162, 327) (number of passers with Y = 1; this
reading is forced by `sampleBounds`, which uses passers − ones as the number of zeros among passers).
failureShare a = f_a / n_a ∈ ℚ; trimShare a = (Σ_{b≠a} f_b/n_b) / (1 − f_a/n_a) (sample trimming ratio
r̂_a). keptLower a = (⌈passers_a (1 − r̂_a)⌉ − 1).toNat (number of order statistics j with j/passers < 1 − r̂),
keptUpper a = passers_a − ⌊passers_a r̂_a⌋.toNat (number with j/passers > r̂).
sampleBounds ones a = ( (keptLower − (passers − ones))₊ / keptLower , min(keptUpper, ones) / keptUpper ):
the trimmed means of a 0/1 outcome after keeping the keptLower smallest / keptUpper largest passer values.
sampleInterval ones a = Icc of those (cast to ℝ).

Statement (closed proposition, no hypotheses): with I_a = sampleInterval preferCount a,
(i) I_0 ∩ I_1 = ∅; (ii) I_0 ∩ I_2 = ∅; (iii) ¬(∀ a b, I_a ∩ I_b ≠ ∅) (not every pair overlaps);
(iv) ¬(∃ x ∈ I_0 ∩ I_1 ∩ I_2).
Computed (scratch/Check1.lean): r̂ = (32239072/72978893, 10871635/51611456, 31403827/72143648),
keptLower = (284, 281, 278), keptUpper = (285, 282, 279),
I_0 = [0, 61/285] ≈ [0, 0.214], I_1 = [87/281, 27/47] ≈ [0.310, 0.574], I_2 = [56/139, 1] ≈ [0.403, 1].
So (i),(ii) hold, I_1 ∩ I_2 ≠ ∅; (iii),(iv) follow from (i).

Junk values: none reachable. All denominators (n_a, 1 − f_a/n_a, keptLower, keptUpper) are nonzero; the
truncated subtraction in `sampleBounds` numerator is the intended (·)₊ (zero when keptLower ≤ #zeros, as in arm
0); `Int.toNat` arguments are positive. Points to check against the claim: (a) the counts are inputs, not
derived from a data file; (b) the rounding rule is asymmetric: the lower bound keeps ⌈n(1−r̂)⌉ − 1 points, the
upper keeps n − ⌊n r̂⌋ (here 284 vs 285 for arm 0, since n(1 − r̂) = 284.14 is not an integer); a symmetric
rule would change the endpoints slightly but not the disjointness (margins ≈ 0.10 and 0.19); (c) the
computation is unweighted (docstring says "unweighted"); if the paper's claim concerns weighted estimates this
is a different object.

## SAP.P010.T2 (Challenge/Part1.lean:16, T2Statement Defs/Part4.lean:19–47)

Docstring: "Exact trimming counts and endpoints give approval overlap and positive preference separations
under both trimming rules."

Statement (closed proposition), a conjunction of three blocks:
1. Exact values: passers = (509,356,493); trimShare = (32239072/72978893, 10871635/51611456,
   31403827/72143648); keptLower = (284,281,278); keptUpper = (285,282,279);
   sampleBounds preferCount = ((0, 61/285), (87/281, 27/47), (56/139, 1));
   sampleBounds approveCount = ((0, 64/95), (113/281, 2/3), (109/278, 1)) with approveCount = (192,188,324).
2. Characterisation of the rounding: ∀ a, ∀ j ∈ [1, passers_a]:
   (j/passers_a < 1 − r̂_a ↔ j ≤ keptLower_a) ∧ (j/passers_a > r̂_a ↔ passers_a − keptUpper_a < j).
3. Conclusions: 1/2 ∈ sampleInterval approveCount a for every a; 1/2 ∈ I_1, 1/2 ∈ I_2 (preference);
   upper(I_0) < lower(I_1) and upper(I_0) < lower(I_2) with differences 7654/80085 and 7481/39615 (> 0);
   minAlwaysShare = 1 − Σ_a f_a/n_a = 40739821/77997088 > 0;
   fractionalPreference a = (max(0, (ŝ_a − Σ_{b≠a} f_b/n_b)/L̂), min(1, ŝ_a/L̂)) with ŝ_a = preferCount_a / n_a
   (share of *all* arm-a respondents who passed and prefer) and L̂ = minAlwaysShare — i.e. the population bound
   formula for a binary outcome with plug-in proportions and no integer rounding — equals
   ((0, 8745997/40739821), (12614477/40739821, 23486112/40739821), (16448045/40739821, 1));
   fractional separations (fP 1).1 − (fP 0).2 = 3868480/40739821 > 0 and (fP 2).1 − (fP 0).2 = 7702048/40739821 > 0.
All values verified by #eval in scratch/Check1.lean.

Junk values: none reachable (same as T1; minAlwaysShare > 0, so no division by zero; max/min clamps are the
intended [0,1] clamps for a binary outcome). Remarks: approval overlap is stated only for the integer rule
(no `fractionalPreference`-type object for approval exists); "under both trimming rules" in the docstring is
accurate only for the preference separations. The ⌈·⌉−1 vs n−⌊·⌋ asymmetry is pinned down by block 2 (strict
inequalities on both sides).

## SAP.P010.T3 (Challenge/Part1.lean:20, T3Statement Defs/Part6.lean:11)

Docstring: "The printed claim is false: both continuous witnesses have the same observables and violate the
printed bounds that omit passing from conditioning."

Witness `missingPassingPopulation upper` on Population 2 0 (Part5:109): mixture
1/4 · stratum(S=(1,1); Y(0) ~ Exp(1) if upper else −Exp(1); Y(1) ~ Laplace(1))
+ 1/4 · stratum(S=(1,0); Y(0) ~ −Exp(1) if upper else Exp(1); Y(1) ~ Laplace(1))
+ 1/2 · stratum(S=(0,1); Y(0) ~ Laplace(scale 1/2, density e^{−2|x|}); Y(1) ~ Laplace(1)),
where `stratumPopulation s₁ s₂ F₁ F₂` (Part5:105) = law of (Y(0),Y(1)) ~ F₁⊗F₂ independent of a fair arm
(Part5:102), checks fixed at (s₁,s₂). `unitExponential` density e^{−x}1{x>0} (Part5:96);
`laplaceDistribution r` density (r/2)e^{−r|x|} (Part5:99). Each stratum is product-with-fair-arm, so the
whole vector (Y(·),S(·)) is even jointly independent of Z.

Statement: for both values of `upper`, with μ the witness:
populationAssumptions μ; μ(allPass) = 1/4; response law atomless; response has full real support; all absolute
moments of response finite; Pr(S=1|Z=0) = 1/2, Pr(S=1|Z=1) = 3/4; trimming ratio for arm 0 = 1/2;
passer law in arm 0 = Laplace(1); its left 1/2-quantile = 0;
E[Y | Y ≤ 0, Z = 0] = −3/4 and E[Y | Y ≥ 0, Z = 0] = 3/4 (**not** conditioned on S = 1: the sets are
{response ≤ 0} ∩ assigned 0, so arm-0 failers, whose Y(0) ~ Laplace(1/2), are included);
always-passer mean E[Y(0) | AP] = 1 (upper) / −1 (lower); so E[Y(0)|AP] ∉ [−3/4, 3/4];
the corrected (passing-conditioned) endpoints are lowerEndpoint μ 0 = −1, upperEndpoint μ 0 = 1;
and the two witnesses have the same law of (Y, S, Z).
Hand check: arm-0 law of Y is ½Laplace(1)+½Laplace(1/2); E[Y;Y≤0 | Z=0] = −¼ − ⅛ = −3/8, divided by ½ → −3/4 ✓.

Reading of the "printed bounds": [E[Y | Y ≤ y_{1−r}, Z=a], E[Y | Y ≥ y_r, Z=a]] with S=1 dropped from the
conditioning, r the trimming ratio (=1/2), y_q the quantile. The statement plugs in y = 0 (proved to be the
passer-law 1/2-quantile); the arm-0 all-respondent law ½Laplace(1)+½Laplace(1/2) is symmetric, so its median is
0 as well (true but not stated). Junk values: none reachable — all meanOn sets have positive finite mass and
integrable integrands (allMoments; Exp has a finite mean), trimmingRatio/passRate denominators are positive.
Whether this refutes the *printed assertion* or only a typographical reading must be checked against the claim.

## SAP.P010.T4 (Challenge/Part1.lean:24, T4Statement Defs/Part6.lean:28)

Docstring: "The corrected finite-branch trimmed means bound all compatible always-passer means, attain both
endpoints, and have the stated quantile-integral forms."

Statement: ∀ K d, ∀ μ on Population K d, ∀ a : Fin K, assuming
(h) μ probability, per-arm independence (Y(b),S(b)) ⊥ Z for all b, μ(Z=b) > 0, Pr(S=1|Z=b) > 0 for all b;
(hA) μ(AP) > 0; (hc) the passer law of Y in arm a is atomless; (hi) Y ∈ L¹ on {S=1, Z=a};
(hr) r_a < 1, where r_a = Σ_{b≠a}(1 − p_b)/p_a;
conclude, with L = 1 − Σ_b (1 − p_b), m = E_μ[Y(a) | AP] (meanOn), lower/upper = lowerEndpoint/upperEndpoint:
lower ≤ m ≤ upper; lower and upper are both in compatibleMeans μ a (attained by some ν with the same observable
law, satisfying populationAssumptions and ν(AP) > 0); every compatible mean lies in [lower, upper];
p_a(1 − r_a) = L; (r_a < 1 ↔ L > 0); r_a = 0 → lower = upper = E[Y | S=1, Z=a];
lower = (p_a/L) ∫_0^{L/p_a} Q(u) du and upper = (p_a/L) ∫_{1−L/p_a}^1 Q(u) du, Q = realQuantile of the
arm-a passer law.

Junk values: meanOn ν (Y(a)) allPass could be a junk 0 if Y(a)·1_AP were not ν-integrable; it is not reachable
for compatible ν: by per-arm independence, the ν-law of Y(a) on {S(a)=1} is the observed passer law scaled by
1/ν(Z=a), which is integrable by (hi), and AP ⊆ {S(a)=1}; ν(AP) ∈ (0,1]. leftQuantile at u = 1 (r_a = 0) can be
⊤ and at u = 0 is ⊥: then {Y ≤ ⊤} / {⊥ ≤ Y} is everything, which is the intended untrimmed mean.
realQuantile maps ⊥/⊤ to 0 only at u ∈ {0,1} (null). Interval integrals are of an integrable quantile function
(Y ∈ L¹ on passers). hA is implied by hr (Fréchet bound μ(AP) ≥ L > 0), so it is not a restriction.
hc (continuity) and hr (finite branch) are the substantive hypotheses. Note the identified set uses per-arm
independence; if the paper's assumption were joint independence the attainment clause would be weaker and the
bound clause stronger than the paper's.

## SAP.P010.T5 (Challenge/Part1.lean:28, T5Statement Defs/Part6.lean:49)

Docstring: "The printed claim is false: the specified full-support observed law has finite sharp passer-mean
endpoints zero and one."

Witness `boundedPasserPopulation` on Population 2 0 (Part5:125) = 1/3 · commonOutcome(S=(1,1), Y(0)=Y(1) ~
Beta(3,3)) + 2/3 · commonOutcome(S=(0,0), Y(0)=Y(1) ~ H), arm fair and independent; Beta(3,3) density
30x²(1−x)² on (0,1) (Part5:116), H density 5/(2(1+|x|)^6) (Part5:119), symmetric, P(H > R) = 1/(2(1+R)^5),
finite moments of order < 5.

Statement: populationAssumptions; μ(AP) = 1/3; response law atomless; response full real support;
E[Y] = 1/6, E[Y²] = 13/63, E|Y|³ = 19/84 and |Y|³ integrable (hand-checked: Beta moments 1/2, 2/7, 5/28;
H moments 0, 1/6, 1/4); two-sided tails P(Y > R) = P(Y < −R) = 1/(3(1+R)^5) for R ≥ 1;
for each arm a: p_a = 1/3, r_a = 2 (so L = −1/3 < 0: the infinite/else branch);
every compatible always-passer mean m satisfies 0 < m < 1; in EReal, the identified set has GLB 0 and LUB 1
(so it is nonempty), and its GLB is not ⊥ and its LUB is not ⊤;
for every t ∈ (0,1): P_Beta(0,t) = 10t³ − 15t⁴ + 6t⁵; `betaEndpointPopulation t upper` (Part5:128) is compatible;
its always-passer mean is t(15/2 − 12t + 5t²)/(10 − 15t + 6t²) ∈ (0,t) (lower) and 1 − that (upper).

Junk values: as in T4, a compatible ν has Y(a) on {S(a)=1} with law the arm-a passer law (Beta(3,3)) up to
scaling, so meanOn ν (Y(a)) AP is a genuine conditional mean in (0,1); the strict bounds 0 < m < 1 are not
junk-driven (a junk 0 would violate 0 < m, and is impossible). IsGLB/IsLUB over EReal: nonemptiness is forced
(IsGLB ∅ 0 is false since ⊤ is a lower bound). betaEndpointPopulation weights q/3, (1−q)/3, (1−q)/3, (1+q)/3
are nonnegative and sum to 1 for q = Beta(E) ∈ (0,1); `conditionalLaw` there has 0 < mass < ∞.
The witness separates the overall support of Y (all of ℝ, from failers' heavy tails) from the passer support
(0,1): it refutes a claim that the else-branch bounds are infinite / the support of Y only under the reading
in which the support is that of the full outcome distribution — to be checked against the claim.
