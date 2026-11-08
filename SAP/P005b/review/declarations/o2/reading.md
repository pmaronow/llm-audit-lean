# Blind reading (written before opening claims.json / record.json)

Line numbers are module-local (as in `closure.json`).

## Common objects (closure members shared by all five declarations)

* `Population n d` (Defs/Part1.lean:57–60): `x : Fin n → Fin d → ℝ` (covariate vectors x_i ∈ ℝ^d),
  `yT, yC : Fin n → ℝ` (potential outcomes). Finite population, design-based setting.
* `design n m` (Part1:16) = all m-subsets S of `Fin n` (treated set); `control S` (Part1:18) = complement.
* `mean S a` (Part1:20) = (Σ_{i∈S} a_i)/|S|  — **junk: 0 when S = ∅**.
* `popMean a` (Part1:23) = mean over all n units (junk 0 if n = 0).
* `expectation m f` (Part1:25) = (Σ_{S∈design n m} f S)/C(n,m), i.e. E under complete randomization
  with m treated. **Junk: 0 if m > n (empty design)**; every use below has 0 < m < n.
* `probability m E` (Part1:31) = #{S ∈ design : E S}/C(n,m).
* `sampleCov S a b` (Part1:36) = mean_S(ab) − mean_S(a)·mean_S(b) — covariance with divisor |S| (not |S|−1).
* `popCov a b` (Part1:39) = population covariance with divisor n.
* `centered a i` (Part1:41) = a_i − ā.
* `dot u v` (Part1:62) = Σ_k u_k v_k.
* `xMean P S` (Part1:64) = x̄_S ∈ ℝ^d.
* `gram P` (Part1:67) = (1/n) Σ_i x_i x_iᵀ.
* `standardized P` (Part1:70): x̄ = 0 and (1/n)Σ x_i x_iᵀ = I_d.
* `leverage P i` (Part1:73) = ‖x_i‖² (NOT divided by n; under standardization this is n·H_ii).
* `kappa P` (Part1:75) = sSup {‖x_i‖²/n} = max_i H_ii (finite nonempty range for n ≥ 1; junk sSup ∅ = 0 for n = 0).
* `ate P` (Part1:78) = ȳ_T − ȳ_C (population means).
* `pT n m` = m/n, `pC n m` = (n−m)/n (Part1:80,82) (junk only at n = 0).
* `populationSlope P y` (Part1:84) = (1/n)Σ_i y_i x_i; under standardization this is the population OLS slope β(y).
* `N P m` (Part1:87) = pT β(yT) + pC β(yC).
* `armL P S` (Part1:90) = mean_S(x xᵀ) − x̄_S x̄_Sᵀ (within-arm covariance, divisor |S|).
* `armN P S y` (Part1:93) = mean_S(y x) − ȳ_S x̄_S.
* `Lhat P m S` (Part1:97) = I − pT x̄_S x̄_Sᵀ − pC x̄_{S^c} x̄_{S^c}ᵀ (pooled within-group covariance, which equals
  this only when gram = I; the definition hard-codes I).
* `Nhat P m S` (Part1:102) = pT armN(S,yT) + pC armN(S^c,yC).
* `betaHat` (Part1:105) = Lhat⁻¹ Nhat; `armBetaHat P S y` (Part1:108) = armL(S)⁻¹ armN(S,y).
  **Junk: Mathlib `Matrix.inv` = 0 for singular matrices.** Guarded by
  `noninteractedRegular` (Part1:111: det Lhat ≠ 0 for all S in design) /
  `interactedRegular` (Part1:114: det armL(S) ≠ 0 and det armL(S^c) ≠ 0 for all S in design).
* Part2: `adjustedATE` (16) = ȳ_S(yT) − ȳ_{S^c}(yC) − (x̄_S − x̄_{S^c})ᵀ β̂ (coefficient of Z in Y ~ 1+Z+X).
  `interactedATE` (19) = ȳ_S − ȳ_{S^c} − (x̄_Sᵀ β̂_T − x̄_{S^c}ᵀ β̂_C) (Lin's interacted estimator with centered x).
  `armNu1 P S y` (24) = mean_S(e x) − popMean(e x), e = centered y.
  `armNu2 P S y` (28) = (armL(S)⁻¹ − I) armN(S,y).
  `armNu3 P S y` (31) = −x̄_S · ē_S.
  `nu1, nu2, nu3` (34,37,40): pooled versions, nu1 = pT armNu1_T + pC armNu1_C; nu2 = (Lhat⁻¹ − I) Nhat;
  nu3 = pT armNu3_T + pC armNu3_C.
  `biasEstimate` (43) = (sCov_{S^c}(h,yC) − sCov_S(h,yT))/(n−2) + (x̄_{S^c} − x̄_S)ᵀ nu2, h = leverage.
  `debiasedATE` (47) = adjustedATE − biasEstimate.
  `interactedBiasEstimate` (50) = m/((n−2)(n−m))·sCov_{S^c}(h,yC) + x̄_{S^c}ᵀ armNu2_C − (n−m)/((n−2)m)·sCov_S(h,yT) − x̄_Sᵀ armNu2_T.
  `interactedDebiasedATE` (56) = interactedATE − interactedBiasEstimate.
  `leverageCov P y` (59) = popCov(h, y) = (1/n)Σ (h_i − h̄) y_i.
  `NTTT n m` (61) = (n−m)(n−2m)/((n−1)(n−2)m²) (third-moment coefficient of SRSWOR mean);
  `NCCC n m` (64) = NTTT n (n−m) (ℕ subtraction, harmless for m < n);
  `NTTC n m` (66) = −(n−2m)/((n−1)(n−2)m). **Junk: (n−2) = 0 at n = 2** — all uses have 3 ≤ n.
  `armResidual P y i` (68) = e_i − x_iᵀ β(y); `armLeading P S` (77) = mean_S(r_T) − mean_{S^c}(r_C).
  `stochasticO m R r` (80): ∀ε>0 ∃M>0 ∃n₀ ∀n≥n₀, P_{m n}(|R n S| > M r_n) < ε (standard O_p).
  `standingAssumptions d m P` (88): for n ≥ 3: 1 ≤ d_n ≤ n, 0 < m_n < n; ∃K ≥ 0 bounding (for n ≥ 3)
  popMean(yT²), popMean(yC²), popMean(x_k²) for all k; eventually standardized; ∃ 0<lo<hi<1 with
  lo < m_n/n < hi for n ≥ 3. (Only **second** moments of outcomes are bounded; no fourth moment / max-norm condition,
  no κ → 0, no d/n → 0.)
  `armDebiased P S y` (98) = ȳ_S − x̄_Sᵀ armN(S,y) + (n−|S|)/((n−2)|S|)·sCov_S(h,y).
  `indicator S i` (103) = 1_{i∈S}.
* `biasEstimate._proof_1`, `T21Statement._proof_1` (line 0): auto-generated `(1+1).AtLeastTwo` instances for the
  numeral 2 (checked with `#print`); no content.

## T20 (Challenge/Part1.lean:38; `T20Statement`, Defs/Part5.lean:42)

`T20Statement = T24Statement ∧ ¬A ∧ ¬B` where

* `T24Statement` — see T24 below (exact decompositions and first-component expectations, n ≥ 2).
* `¬A`: it is NOT the case that for all n d m and all P with 3 ≤ n, 0 < m < n, P standardized, P interactedRegular,
  E[x̄_{S^c}ᵀ armNu3(S^c,yC)] − E[x̄_Sᵀ armNu3(S,yT)] = NCCC(n,m)·lcov(yC) − NTTT(n,m)·lcov(yT).
  My computation: E[x̄_Sᵀ armNu3_T] = −E[‖x̄_S‖² ē_S] = −NTTT·(1/n)Σ h_i e_i = −NTTT·lcov(yT), and similarly
  E[x̄_{S^c}ᵀ armNu3_C] = −NCCC·lcov(yC). So the true value of the left side is NTTT·lcov(yT) − NCCC·lcov(yC),
  the negative of the displayed right side; the displayed identity fails whenever the RHS ≠ 0 (n ≠ 2m and nonzero
  leverage covariance). So ¬A is a sign-error refutation of the displayed identity, with ν3 defined as
  −x̄ ē (the sign forced by β̂ = β + ν1 + ν2 + ν3).
* `¬B`: it is NOT the case that for all d m : ℕ → ℕ, P : (n) → Population n (d n):
  standingAssumptions d m P → (eventually interactedRegular (P n)(m n)) → κ_n·log(d_n) → 0 →
  interactedATE − ate − armLeading = O_p(√(κ_n d_n / n)).
  Notes: `Real.log (d n)` with d_n ≥ 1 is ≥ 0 and equals 0 exactly when d_n = 1; so with d_n ≡ 1 the logarithm
  condition holds for any κ_n. The refutation is presumably built on d_n = 1 with κ_n not → 0 (a "literal" reading of
  log d). Whether this refutes the paper depends on whether the paper's assumptions exclude this case (κ → 0, d → ∞,
  higher moments, ...); `standingAssumptions` only has second moments and no κ → 0.

Quantifier order: universal statements inside negations; so ¬A, ¬B are existence of counterexamples.

Junk values: Matrix inverse (guarded by interactedRegular for all S); (n−2) in NTTT/NCCC (3 ≤ n); mean of empty
arm (0 < m < n); `Real.log` of d_n ≥ 1 (genuine, but log 1 = 0 can trivialize the condition); kappa sSup (finite
range). In ¬B, interactedATE uses the inverse of armL, guarded only eventually — finitely many n irrelevant to O_p.

## T21 (Challenge/Part1.lean:47; `T21WholeStatement`, Defs/WholeW1.lean:91 → `T21Statement`, Defs/Part6.lean:24)

For all n d m, P with 3 ≤ n, 0 < m < n, P standardized, noninteractedRegular P m:
1. E[biasEstimate] = E[adjustedATE] − ate.
2. E[debiasedATE] = ate.
3. ∀ S ∈ design: debiasedATE(S) = ȳ_T − ȳ_C − (x̄_S − x̄_{S^c})ᵀ Nhat + sCov_S(h,yT)/(n−2) − sCov_{S^c}(h,yC)/(n−2)
   (inverse-free formula; algebraic since β̂ − nu2 = Nhat identically).
4. E[adjustedATE] − ate = E[(x̄_{S^c} − x̄_S)ᵀ(nu1 + nu2 + nu3)].
5. ∀ S: (x̄_{S^c} − x̄_S)ᵀ nu2 = (x̄_{S^c} − x̄_S)ᵀ((Lhat⁻¹ − I) Nhat) — definitional (rfl).
6. If 2 ≤ m and 2 ≤ n − m: E[biasPart11] = (lcov(yC) − lcov(yT))/(n−1);
   E[biasPart12] = (pT/pC)·NTTT·lcov(yT) − (pT/pC)·NTTC·lcov(yC)
   = (n−2m)/((n−1)(n−2)m)·lcov(yT) − (2m−n)/((n−1)(n−2)(n−m))·lcov(yC);
   ∀ S: biasPart11 + biasPart12 = sCov_{S^c}(h,yC)/(n−2) − sCov_S(h,yT)/(n−2).
   `biasPart11` (Part6:13) = (1/(n−1))[(n−m)(n−1)/((n−m−1)n)·sCov_{S^c}(h,yC) − m(n−1)/((m−1)n)·sCov_S(h,yT)]
   (expressions with (m−1), (n−m−1) denominators — junk division by zero at m = 1 or n − m = 1, excluded by 2 ≤ m,
   2 ≤ n−m); `biasPart12` (Part6:18) = NTTT m²(n−1)/((n−m)(m−1)n)·sCov_S(h,yT) − NTTC m(n−1)/((n−m−1)n)·sCov_{S^c}(h,yC).
   I verified by hand all coefficient identities (they are correct).
7. (WholeW1 part) Under the same hypotheses: ∀ S ∈ design, `wholeW1OLS P m S`: the triple
   (a*, t*, b*) = (ȳ_C − x̄_Cᵀβ̂, adjustedATE, β̂) minimises Σ_i (Y_i − a − t·1_{i∈S} − x_iᵀ b)² (Y_i observed outcome)
   and is the unique minimiser; E[(x̄_C − x̄_T)ᵀ nu1] = (lcov(yC) − lcov(yT))/(n−1);
   E[(x̄_C − x̄_T)ᵀ nu3] = (pT/pC)NTTT lcov(yT) − (pT/pC)NTTC lcov(yC) (I checked: = (pT/pC)NTTT lcov(yT) + (pT/pC)² NTTT lcov(yC)).
   `wholeW1Observed/Fit/Loss/Intercept/OLS` (WholeW1:62–81) are faithful renderings of the finite OLS problem.

Junk values: inverse of Lhat (guarded for all S in design); (n−2) (3 ≤ n); (m−1), (n−m−1) (guarded by 2 ≤ m,
2 ≤ n−m in clause 6 only); sampleCov uses divisor |S| (a convention, matters for the coefficients — must match the
paper's s_{h y} convention); pC = 0 impossible (m < n). `leverage` = ‖x_i‖² (not H_ii = ‖x_i‖²/n): matters for the
constants in the bias formulas and the estimator — must be checked against the paper's definition of leverage.

## T22 (Challenge/Part1.lean:52; `T22Statement`, Defs/Part6.lean:71, `T22Main` Part6:56)

`T22Statement = T22Main ∧ C1 ∧ C2`.
* T22Main: for all n d m, P with 3 ≤ n, 0 < m < n, standardized, interactedRegular:
  E[interactedBiasEstimate] = E[interactedATE] − ate; E[interactedDebiasedATE] = ate;
  E[armDebiased(S,yT)] = ȳ_T; E[armDebiased(S^c,yC)] = ȳ_C; ∀ S ∈ design:
  interactedDebiasedATE(S) = (ȳ_S − x̄_Sᵀ armN(S,yT) + (n−m)/((n−2)m)·sCov_S(h,yT))
                             − (ȳ_{S^c} − x̄_{S^c}ᵀ armN(S^c,yC) + m/((n−2)(n−m))·sCov_{S^c}(h,yC)).
  Hand check: E[x̄_Sᵀ(armNu1+armNu3)] = (n−m)n(m−1)/((n−1)(n−2)m²) lcov = E[(n−m)/((n−2)m) sCov_S(h,y)] ✓ (also at m=1).
* C1: for all n d m, P with 3 ≤ n, **2 ≤ m**, m < n, x̄ = 0 (no Gram condition, no regularity):
  E[armDebiased(S,yT)] = ȳ_T.
* C2: for all n d m, P with 3 ≤ n, 0 < m < n, **2 ≤ n − m**, x̄ = 0: E[armDebiased(S^c,yC)] = ȳ_C.
  (The identities in C1/C2 also hold at m = 1 / n − m = 1 by my computation: a singleton arm gives armN = 0 and
  sCov = 0; so 2 ≤ m, 2 ≤ n−m are restrictions, not needed for truth.)

Junk: (n−2) (3 ≤ n); armDebiased uses S.card (fine); mean of empty arm excluded; inverse of armL guarded by
interactedRegular in T22Main; C1/C2 involve no inverse.

## T23 (Challenge/Part1.lean:57; `T23Statement`, Defs/Part6.lean:79)

For all n d m, P with 3 ≤ n, 0 < m < n, standardized, noninteractedRegular:
1. ∀ S ∈ design: β̂ = N + nu1 + nu2 + nu3 (vector identity).
2. E[adjustedATE] − ate = E[(x̄_{S^c} − x̄_S)ᵀ(nu1+nu2+nu3)].
3. E[(x̄_{S^c} − x̄_S)ᵀ nu1] = (lcov(yC) − lcov(yT))/(n−1).
4. (lcov(yC) − lcov(yT))/(n−1) = −(1/(n−1))·popMean((h_i − h̄)(yT_i − yC_i)) (covariance interpretation).
5. E[(x̄_{S^c} − x̄_S)ᵀ nu3] = (n−2m)/((n−1)(n−2)m)·lcov(yT) − (2m−n)/((n−1)(n−2)(n−m))·lcov(yC).
6. If yT − yC is constant, then E[(x̄_C − x̄_T)ᵀ nu1] = 0.
7. If m = n − m (ℕ subtraction, fine as m < n), then E[(x̄_C − x̄_T)ᵀ nu3] = 0.
All checked by hand. Junk: Lhat inverse (guarded), (n−2) (3 ≤ n), (n−1), m, n−m nonzero.
Note the statement fixes the leverage as ‖x_i‖² and the covariance with divisor n.

## T24 (Challenge/Part1.lean:62; `T24Statement`, Defs/Part5.lean:21)

For all n d m, P with **2 ≤ n**, 0 < m < n, standardized, interactedRegular:
1. ∀ S ∈ design: β̂_T(S) = β(yT) + armNu1_T + armNu2_T + armNu3_T and β̂_C(S^c) = β(yC) + armNu1_C + armNu2_C + armNu3_C.
2. E[interactedATE − ate] = E[x̄_{S^c}ᵀ(ν1C+ν2C+ν3C)] − E[x̄_Sᵀ(ν1T+ν2T+ν3T)].
3. E[x̄_Sᵀ armNu1_T] = (n−m)/((n−1)m)·lcov(yT).
4. E[x̄_{S^c}ᵀ armNu1_C] = m/((n−1)(n−m))·lcov(yC).
5. The difference of 4 and 3.
Hand-checked (E[x̄_{S,k} mean_S(e x_k)] = (n−m)/(nm(n−1)) Σ_i e_i x_{ik}², summed over k).
No (n−2) denominators, so 2 ≤ n suffices. Junk: armL inverse (guarded by interactedRegular), empty arms excluded.
The third-component (ν3) expectations are NOT stated in T24 (they appear only negated in T20).
