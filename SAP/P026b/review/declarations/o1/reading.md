# Blind reading (step 1) — written before opening claims.json / record.json

Common objects (`SAP/P026b/Defs/Part1.lean`):

* `Design Ω I R` (l.11): a weight `p : Ω → R` and an assignment `T : Ω → I → Bool` (true = treated).
  No constraint is built in; `probabilityDesign` (l.20) = all weights ≥ 0 and sum 1.
* `expectation D f = Σ_ω p(ω) f(ω)` (l.18); `indicator D a ω i = 1{T(ω,i)=a}` (l.23);
  `marginal D a i = π_a(i) = E[1{T_i=a}]` (l.26); `joint D a b i j = π_{ai,bj} = E[1{T_i=a}1{T_j=b}]` (l.29);
  `positiveMarginals` (l.32): π_1(i)>0 and π_0(i)>0 for all i.
* `observed D y1 y0 ω i = y1 i` if treated else `y0 i` (l.35); `populationTotal y = Σ_i y_i` (l.38);
  `ate N y1 y0 = (Σy1 − Σy0)/N` with `N : ℕ` cast (l.40).
* `htTotal D a y ω = Σ_i 1{T_i=a} y_i / π_a(i)` (l.43); `ht D N y1 y0 = (htTotal true y1 − htTotal false y0)/N` (l.46).
* `generalizedTotal D a y f ω = Σ_i (1{T_i=a} y_i/π_a(i) − 1{T_i=a} f(ω)_i/π_a(i) + f(ω)_i)` (l.49);
  `generalized D N y1 y0 f = (genTotal true y1 f − genTotal false y0 f)/N` (l.54). Note: one prediction vector
  `f(ω)` is used for both arms.
* `covariance D f g = E[fg] − E[f]E[g]` (l.58), `variance D f = covariance D f f` (l.61) — population (design)
  moments with the raw weights.
* `disagreement D i j = P(T_i ≠ T_j)` (l.63); `offSum F = Σ_i Σ_{j≠i} F i j` (l.66);
  `zeroSum D a b F = Σ_{i≠j, π_{ai,bj}=0} F i j` (l.68); `epsilon p = 1{p=0}` (l.71).
* `estimatedPair D a b y1 y0 ω i j = 1{T_i=a}1{T_j=b}/(π_{ai,bj}+ε(π_{ai,bj})) · (π_{ai,bj} − π_a(i)π_b(j)) ·
  (Y_i/π_a(i)) · (Y_j/π_b(j))`, Y = observed outcome (l.73).
* `printedVariance D N y1 y0 ω` (l.80) =
  N^{-2} [ Σ_i (1{T_i=1}(Y_i/π_1i)² + 1{T_i=0}(Y_i/π_0i)²)
         + Σ_{i≠j} (pair_{11} + pair_{00} − 2 pair_{10})
         + Σ_{i≠j, π_{1i1j}=0} (1{T_i=1}Y_i²/(2π_1i) + 1{T_j=1}Y_j²/(2π_1j))
         + Σ_{i≠j, π_{0i0j}=0} (same with control) ].
  This is the Aronow–Middleton/Aronow–Samii conservative variance estimator with the ε trick; no
  zero-joint correction for the cross (1,0) term.
* `crossSupport D` (l.92): π_{1i,0j} > 0 for all i ≠ j.
* `UnitExperiment I` (l.129): weight on all allocations `I → Bool`, ≥ 0, sum 1, and π_1(i) > 0, π_0(i) > 0 for
  every i (positivity of marginals is built in). `E.design = ⟨E.weight, id⟩` (l.136).
* `residualContrast D N x z f ω = (Σ_i 1{T_i=1}(Y_i − f(ω)_i)/π_1i − Σ_i 1{T_i=0}(Y_i − f(ω)_i)/π_0i)/N` (l.159).

## T13 (`SAP/P026b/Challenge/Part1.lean:10`, statement `Defs/Part3.lean:38`)

For every finite nonempty type of units I, every UnitExperiment E (law on all allocations with positive
marginals), all potential outcomes y1, y0 : I → ℝ and every assignment-dependent prediction
f : (I → Bool) → I → ℝ:

1. for each arm a ∈ {1,0}: E[Ŷ^G_a] = Σ_i y_a(i) − Σ_i Cov(1{W_i=a}, f(W)_i / π_a(i));
2. E[δ̂^G] − δ = (Σ_i Cov(1{W_i=0}, f_i/π_0i) − Σ_i Cov(1{W_i=1}, f_i/π_1i)) / N, with N = |I|,
   δ = (Σy1 − Σy0)/N.

Quantifiers: ∀ I, E, y1, y0, f — fully universal, no extra hypotheses (only Nonempty I, which only avoids N = 0).
Junk values: division by π_a(i) — excluded by `UnitExperiment.positive`; division by N = card I — N ≥ 1 by
`Nonempty I`. None can affect meaning. The design ranges over every law on allocations, so the statement is
as general as a finite-population design can be; f is an arbitrary function of the assignment (which covers any
function of observed data given fixed potential outcomes).
Nonvacuity: a UnitExperiment exists (compiled `scratch/Check.lean`, `uniform1`).

## T14 (`Challenge/Part1.lean:15`, statement `Defs/Part4.lean:49`)

Population (Defs/Part2): 16 units, cluster map `tableCluster` (l.51) into 10 clusters
{0,1},{2,3},{4},{5},{6,7,8},{9,10},{11,12},{13},{14},{15}; outcome `tableY` (l.53), covariate `tableX` (l.55).
Design `tableDesign`/`realTableDesign` (l.46/86): uniform 1/90 on Fin 6 × Fin 15; clusters 0–3 (units 0–5,
"block 1") get exactly 2 of 4 treated (`twoOfFour`), clusters 4–9 (units 6–15, "block 2") exactly 2 of 6
(`twoOfSix`), independently. So π_1 = 1/2 (block 1 clusters), 1/3 (block 2 clusters); all joints positive.
Sharp null: the HT/variance estimators are applied with y1 = y0.

* `sigmoid z = 1 − 1/(1+e^z)` (l.90) (= logistic). `logitLikelihood b β` (l.92): Bernoulli log-likelihood of
  tableY on (1, tableX) over block b (b = true ↔ units ≥ 6, b = false ↔ units < 6). Arguments of `log` are in
  (0,1), no junk.
* `logitMaximizer b β` (l.97): β is a global maximizer. `logitCoefficients b` (l.100): a chosen maximizer, junk
  (0,0) if none exists — excluded because `logitCoreFacts` asserts ∃! maximizer for both blocks.
* `tableLogitPrediction i` (l.104) uses `logitCoefficients (decide (i < 6))`: a unit of block 1 (i < 6) gets
  the coefficients fitted on block 2 (b = true), and conversely — **cross-block (out-of-block) fitting**. The
  prediction is fixed (does not depend on the assignment; the outcomes are the sharp-null tableY).
* `tableLogitResidual` (l.108): cluster totals of (Y_i − prediction_i).
* `logitEstimate = ht realTableDesign 16 r r` (Part4 l.12): cluster-level HT with N = 16 units on residual
  totals (equal to the generalized estimator with these fixed predictions).
  `logitVarianceEstimate = printedVariance realTableDesign 16 r r` (l.15).
* `logitColumn` (l.19): [Δ = ate 16 Y Y = 0, μ = E est, μ−Δ, √Var est, √E(est−Δ)², Var est, E V̂, E V̂ − Var,
  √Var V̂, √E(V̂ − Var)²].
* `roundsTo x r` (l.29): r − 0.0005 ≤ x < r + 0.0005 (three-decimal rounding).

Statement: (i) `logitCoreFacts` (l.34): unique maximizer in each block; coefficients within 5e-7 of
block2 (−1.1201076, 0.5657586), block1 (1.0843223, 0.2280259); E est = 0 exactly; 0.247090 ≤ SD ≤ 0.247093;
0.0605 ≤ Var < 0.0615; E V̂ = Var exactly; 0.0125 ≤ SD(V̂) < 0.0135. (ii) the chosen coefficients are maximizers.
(iii) two pure linear-inequality facts about reals (non-separation certificates for the two blocks; true and
independent of the population objects). (iv) all ten logitColumn entries round to
[0,0,0,.247,.247,.061,.061,0,.013,.013]. (v) the entries 3,4,5,6,8,9 do not round to the printed
.170,.170,.029,.029,.007,.007.
Junk: `Real.sqrt` of variances (nonnegative here: a probability design), choice default excluded, joints
positive so ε and zeroSum are inert, marginals positive. None affect meaning.
My independent float computation (`scratch/table.py`) reproduces the cross-block numbers
(SD .2471, Var .0611, SD(V̂) .0126); within-block fitting would give .2478/.0614/.0155, a pooled fit
.2497/.0623/.0140 — none gives the printed .170/.029/.007.
Concern to check against the paper: whether the paper's "G (Logit)" uses cross-block fitting of a logit of Y on
(1, X) and the AM variance estimator on residual cluster totals.

## T15 (`Challenge/Part1.lean:22`, statement `Defs/Part3.lean:78`)

Design `oneOfThree` (Part2 l.16): Ω = Fin 3, I = Fin 3, weight 1/3, exactly unit w treated. Outcomes y1 ≡ 1,
y0 ≡ 0, so observed Y_i = 1{i = w}. `packageFit w i = c_w + d_w·i` with c = (5/6,1/3,−1/6), d = (−1/2,0,1/2)
(Part2 l.20). Concrete (quantifier-free) conjunction over ℚ (and ℝ for least squares):
probability design; positive marginals; π_1 = 1/3, π_0 = 2/3; the 3×3 table of fits; `packageLeastSquares`
(Part3 l.70): for each w, packageFit w (cast to ℝ) is a least-squares fitted vector of the observed outcome on
V = [1, x] with x_i = i (`designWithIntercept`, `IsLeastSquaresFitted`: in the column space and minimizes RSS)
and it is the unique such vector; generalized estimator values (1/4, 1, 1/4); Cov(1{W_i=1}, f_i) =
(1/6, 0, 1/6); E[gen] = 1/2; ATE = 1; bias = −1/2; the arithmetic identity −(1/3)(3+3/2)(1/6+0+1/6) = −1/2
(pure arithmetic, not linked to the definitions); HT ≡ 1; 1/2 ≠ 1.
Junk: none (marginals 1/3, 2/3; N = 3).
Docstring: refutes the reading that estate(HT=TRUE) with covariates X stays unbiased.

## T16 (`Challenge/Part1.lean:28`, statement `Defs/Part3.lean:96`)

Conjunction of:
(a) ∀ I, E, y1, y0, fixed g : I → ℝ: generalized(f ≡ g) = residualContrast(f ≡ g) at every allocation, and
    E[generalized] = ATE.
(b) ∀ I, E, K, X : I × K covariate matrix, y1, y0: with V = [1, X] and f(ω) = `olsFitted (K+1) V (Y(ω))`
    (orthogonal projection of the observed outcome onto col(V), Part3 l.26 — well defined for any rank):
    f(ω) is a least-squares fitted vector for every ω; generalized = residualContrast at every ω; and
    E[gen] − ATE = −(Σ_i Cov(1{W_i=1}, f_i)(1/π_1i + 1/π_0i))/N.
(c) ∀ I, E, y1, y0, any f: (∀ i, Cov(1{W_i=1}, f_i) = 0) → E[gen] = ATE.
(d) ∀ I, E, x, G : (I→ℝ) → I → ℝ: under the sharp null y1 = y0 = x, E[gen with f(ω) = G(Y(ω))] = ATE (= 0).
(e) T15Statement.
Junk: same as T13; `olsFitted` uses the orthogonal projection (`starProjection`), well defined for deficient rank,
and the LS property is asserted. Nothing else.

## T17 (`Challenge/Part1.lean:34`, statement `Defs/Part4.lean:60`)

(1) ¬ ∀ D : Design (Fin 3) (Fin 2) ℝ, probability design → positive marginals → (∀ i≠j, P(T_i≠T_j) > 0) →
    ∀ x z, (crossSupport D ∧ Var(HT) ≤ E[V̂]).  I.e. there is a 3-allocation, 2-unit design with positive
    marginals and positive disagreement and outcomes x, z with (cross support fails) OR (V̂ anticonservative).
    Because `crossSupport` does not depend on x, z, a design that merely lacks cross support witnesses (1);
    the conjunct alone does not show that conservativeness fails.
(2) The fixed design `realAsymmetricTwo` (Part2 l.111: allocations (0,0),(0,1),(1,1), weight 1/3) is a
    probability design with positive marginals, positive disagreement and positive same-arm joints π_11, π_00 for
    both ordered pairs, and with y1 = y0 ≡ 1 (sharp null), E[V̂] ≠ Var(generalized with f ≡ 0) (= Var HT).
    By hand: π_1 = (1/3, 2/3), π_{1,0}(0,1) = 0, HT ∈ {−2.25, 0, 2.25}, Var HT = 3.375, E V̂ = 2.875,
    so V̂ is biased (even anticonservative) here.
Junk: ε-convention in `estimatedPair` for π_{10}(0,1) = 0: the indicator product is 0 at every allocation in Ω,
so the term is 0 (inert). Division by marginals guarded by the hypotheses. N = 2.
