# Blind reading of SAP.P033.T11–T15

This file was saved before opening either `claims.json` or `record.json`. It records only the Challenge declarations, their elaborated dependency closures, and the relevant Mathlib meanings. The theorem stubs themselves have no parameters or premises: each asserts the closed proposition described below. All implications listed below occur inside that proposition, rather than as global assumptions.

## Common Mathlib notation and closure inspection

Write ν for `ProbabilityTheory.gaussianReal 0 1`, the Borel probability measure on ℝ with mean zero and variance one. It has density exp(−x²/2)/√(2π) with respect to Lebesgue measure. For any measure μ, `μ.real A` means `(μ A).toReal`. Define Φ(x) = `(ν (Set.Iic x)).toReal`, Q(p) = `sInf {x : ℝ | p ≤ Φ(x)}`, and z = Q(39/40). Thus these symbols abbreviate explicit Mathlib measures, real coercions and infima; they are not additional assumptions or unexplained SAP notions.

Every one of the 83 distinct declarations in the five closures was inspected. In addition to the source definitions, `scratch/ClosurePrint.lean` prints every closure entry, including the generated proof declarations; its successful output is `scratch/closure-print.txt`. Every generated `_proof_…` entry is a proof of a specific natural numeral's `Nat.AtLeastTwo` instance, constructed with `Nat.instAtLeastTwoHAddOfNat`. They supply numeral elaboration, not mathematical assumptions or hidden axioms. In particular, a proof whose name belongs to another target does not import that target's mathematical statement.

The full per-target closure inventory is appended below. All quantities and subtractions in the displayed statistical formulas are real, unless explicitly declared natural. There are no unmentioned sample spaces, random functions or distributions in these statements.

## SAP.P033.T11

Location: `SAP/P033/Challenge/Part1.lean:74–76`. Its docstring says common scaling preserves the t ratio, the significance boundary has reciprocal slope, and a binary control sample has specified variance and standard-deviation bounds.

Its proposition is the conjunction of all the following, expanding `T11Statement` and `T11CoreStatement`:

1. For every β, se, s ∈ ℝ, in that order, if s ≠ 0 and se ≠ 0, then (β/s)/(se/s) = β/se.
2. For every x, y, ζ ∈ ℝ, if y ≠ 0 and ζ ≠ 0, then x/y = ζ if and only if y = x/ζ.
3. For every x, y, ζ ∈ ℝ, if y > 0 and ζ > 0, then both ζ ≤ x/y iff y ≤ x/ζ, and y ≤ x/ζ iff ζy ≤ x.
4. 1/(49/25) = 25/49, 25/49 < 1, and 1 < 49/25.
5. For every v ∈ ℝ, if v ≥ 0 then Mathlib's `Real.sqrt v` equals v iff v = 0 or v = 1.
6. For every n, k ∈ ℕ, if n ≥ 2 and k ≤ n, then
   `[k(1−k/n)² + (n−k)(k/n)²]/(n−1) = k(n−k)/[n(n−1)]`,
   with all n and k coerced to ℝ before arithmetic. The left side is the full expansion of `binarySampleVariance`.
7. For every n ∈ ℕ with n ≥ 2, every y : `Fin n → ℝ` whose values are all zero or one, and then every k ∈ ℕ with `∑ i, y i = (k : ℝ)`,
   `[∑ i : Fin n, (y i − (∑ j : Fin n, y j)/n)²]/((n : ℝ)−1) = k(n−k)/[n(n−1)]`.
   This expands `sampleVariance` and its `sampleMean`. No separate k ≤ n premise is given in this clause; it follows from binary values and their sum.
8. The real-valued binary formula at n = 568, k = 82 is 123/994.
9. With a = 351770457441169/10¹⁵ and ε = 1/10¹⁴, `(a−ε)² < 123/994 < (a+ε)²`. These are bounds on the variance using squared endpoints, not literally a displayed square-root bound. Both endpoints are positive, so they imply the intended standard-deviation enclosure.
10. z > 0 and 51021/10⁵ < 1/z < 51022/10⁵, where z is the normal infimum defined above.

The scaling result is an algebraic result for signed β, not a distributional assertion. The boundary result is also algebraic: an application to nonnegative funnel coordinates is a specialization. The statement contains no empirical assertion that a particular dataset really has these counts.

Junk-value audit: real division is total with a/0 = 0. Clauses 1–3 explicitly exclude their variable zero denominators. Clauses 6–7 require n ≥ 2, excluding empty `Fin n`, zero sample size and zero sample-variance denominator. In `sampleVariance` the subtraction is real subtraction, so no natural truncated subtraction occurs. The unconstrained real function `binarySampleVariance` would allow n = 0 or 1 and invalid counts, but those arguments never occur here. `Real.sqrt` returns zero on nonpositive inputs; its only quantified use is restricted to v ≥ 0, including the genuine boundary case v = 0. All fixed rational denominators are nonzero. The Q(39/40) defining z is an ordinary interior normal quantile: its defining set is nonempty and bounded below. The proposition also expressly states z > 0. The `toReal` in Φ is applied only to a probability measure, never to ∞. There are no integrals, logarithms, rpow, limits, partial functions or default indices in this closure.

## SAP.P033.T12

Location: `SAP/P033/Challenge/Part1.lean:78–80`. Its docstring asserts that exactly honest Gaussian intervals with bias bounds one and one half yield pseudo p-values that over-reject at level one fifth.

For this section introduce fully expanded notation:

- μ(θ,b) is `gaussianReal (θ+b) 1`, the law N(θ+b,1).
- C(b,H) = Φ(H−b)−Φ(−H−b).
- H(B) = `sInf {H : ℝ | 0 ≤ H ∧ 19/20 ≤ Φ(H−B)−Φ(−H−B)}`.
- p(t,h) = 2Φ(−z|t|/h).
- I(θ,b,h) = `(μ(θ,b) {t : ℝ | θ ∈ Set.Icc (t−h) (t+h)}).toReal`.
- V(B,P) means: for every b ∈ ℝ, if |b| ≤ B, then for every α ∈ ℝ with 0 < α < 1,
  `(μ(0,b) {t : ℝ | P(t) ≤ α}).toReal ≤ α`.

These expand, respectively, `biasModelLaw`, `biasCoverage`, `honestHalfLength`, `pseudoP`, `intervalCoverage` (with `id`) and `ValidBiasP`. In particular V is uniform super-uniformity under the null θ = 0 with bounded deterministic bias; it is not an assumption of the theorem.

The proposition conjoins:

1. There exists exactly one H ∈ ℝ such that H > 0 and C(1,H) = 19/20. H(1) > 0 and C(1,H(1)) = 19/20.
2. 264614554821530/10¹⁴ < H(1) < 264614554821540/10¹⁴.
3. For every θ, b ∈ ℝ, if |b| ≤ 1, then I(θ,b,H(1)) = C(b,H(1)), this coverage is at least 19/20, and it equals 19/20 iff |b| = 1.
4. 195996398454000/10¹⁴ < z < 195996398454010/10¹⁴.
5. 128155156554460/10¹⁴ < Q(9/10) < 128155156554470/10¹⁴.
6. Let c = H(1)Q(9/10)/z. Then
   173022157382648/10¹⁴ < c < 173022157382677/10¹⁴;
   `{t : ℝ | p(t,H(1)) ≤ 1/5} = {t : ℝ | c ≤ |t|}`;
   and `(μ(0,1) {t | p(t,H(1)) ≤ 1/5}).toReal = Φ(1−c)+Φ(−1−c)`.
7. The last probability lies strictly between 23579196727091/10¹⁴ and 23579196727101/10¹⁴ (approximately 0.235792).
8. There exists exactly one H > 0 with C(1/2,H) = 19/20; H(1/2) > 0; and C(1/2,H(1/2)) = 19/20.
9. 218147744232810/10¹⁴ < H(1/2) < 218147744232820/10¹⁴.
10. `(μ(0,1/2) {t | p(t,H(1/2)) ≤ 1/5}).toReal` lies strictly between 20414905632765/10¹⁴ and 20414905632774/10¹⁴ (approximately 0.204149).
11. V(1, t ↦ p(t,H(1))) is false, and V(1/2, t ↦ p(t,H(1/2))) is false.

For B = 1/2 this proposition gives exact coverage at the boundary bias, but does not itself state the uniform coverage inequality for every |b| ≤ 1/2. That inequality follows from monotonicity of the explicit Gaussian coverage expression. The two failures of V have concrete permitted boundary biases and α = 1/5; they are not failures caused by arbitrary unmeasurable tests.

Junk-value audit: Φ and every event probability use finite Gaussian measures, so `toReal ∞ = 0` is irrelevant. All displayed event sets are Borel, being inverse images under continuous real functions with fixed nonzero denominators. Q is a real infimum, whose empty or unbounded-below cases return zero in Mathlib's conditional complete order; only p = 39/40 and 9/10 are used here, both genuine quantiles with nonempty bounded-below defining sets. The infimum defining H(B) has the lower bound zero, and for each finite B its set is nonempty because C(B,H) tends to one as H tends to +∞. The theorem states positive actual roots for the two B's used. Thus no arbitrary infimum value is supplying a half-length. Every division by H(B) or z is nonzero; zero half-length would give a junk pseudo p-value, but is excluded by the asserted positivity. `intervalCoverage` generically accepts arbitrary measures and functions, yet here the measure is a probability and the function is the continuous identity. V is vacuous for negative B, but its two occurrences use B > 0. No expectation, nonintegrable integral, natural subtraction, square root, rpow, sequence limsup/liminf, empty index or partial function is used.

## SAP.P033.T13

Location: `SAP/P033/Challenge/Part1.lean:82–84`. Its docstring says the pseudo p-value preserves the interval decision at 5%, and a specified worst-case Gaussian tail is valid at every level.

Use the same explicit Φ, Q and z as above, and these expansions within this section: μ(θ,b) = `gaussianReal (θ+b) 1`; C(b,H) = Φ(H−b)−Φ(−H−b); H(B) = `sInf {h : ℝ | 0 ≤ h ∧ 19/20 ≤ Φ(h−B)−Φ(−h−B)}`; p(t,h) = 2Φ(−z|t|/h); and A(B,t) = Φ(B−|t|)+Φ(−B−|t|). The latter is the full definition of `biasAwareP`. V(B,P) expands to `∀ b : ℝ, |b| ≤ B → ∀ α : ℝ, 0 < α → α < 1 → (μ(0,b) {t | P(t) ≤ α}).toReal ≤ α`.

The statement conjoins:

1. For every t, h ∈ ℝ, if h > 0, then all of
   `|t|/(h/z) = z|t|/h`,
   `p(t,h) < 1/20 ↔ h < |t|`,
   `p(t,h) < 1/20 ↔ 0 ∉ Set.Icc (t−h) (t+h)`, and
   `p(t,h) ≤ 1/20 ↔ h ≤ |t|`.
   The strict and non-strict conventions are separately specified; a zero at a closed interval endpoint is not excluded.
2. For every real B ≥ 0: there exists exactly one positive H with C(B,H) = 19/20; H(B) > 0; C(B,H(B)) = 19/20; and then for every b ∈ ℝ with |b| ≤ B,
   `(μ(0,b) {t | p(t,H(B)) < 1/20}).toReal = 1−C(b,H(B)) ≤ 1/20`,
   with equality to 1/20 iff |b| = B.
3. H(0) = z.
4. For every t ∈ ℝ, p(t,H(0)) = 2Φ(−|t|).
5. For every real α with 0 < α < 1, `(μ(0,0) {t | p(t,H(0)) ≤ α}).toReal = α`.
6. `1/5 < (μ(0,1) {t | p(t,H(1)) ≤ 1/5}).toReal`.
7. For every real B ≥ 0, A(B,0) = 1; A(B,·) is continuous on ℝ, strictly decreasing on `Set.Ici 0` (for all 0 ≤ x < y, A(B,y) < A(B,x)), and tends to zero as t tends to +∞; V(B,A(B,·)) holds; and for every b, α ∈ ℝ, if |b| = B and 0 < α < 1, then `(μ(0,b) {t | A(B,t) ≤ α}).toReal = α`.
8. Within the preceding universal B ≥ 0 quantifier, for every t ∈ ℝ,
   `A(B,t) ≤ 1/20 ↔ H(B) ≤ |t|`, and
   `A(B,t) ≤ 1/20 ↔ p(t,H(B)) ≤ 1/20`.

Thus the all-level validity is for A, while the pseudo p-value is only shown valid at the original 5% decision (and at all levels in the B = 0 case). The statement does not claim the pseudo p-value is valid for arbitrary B at arbitrary α.

Junk-value audit: all distributions are genuine N(b,1) probability measures; event sets are Borel; their `toReal` values are finite probabilities. V has no internal measurability premise, but the only functions to which it is applied here are explicit continuous functions once H(B) > 0, so no nonmeasurable-event convention supplies validity. For B ≥ 0 the bias range is nonempty (b = 0 works), and b = ±B realizes its boundary. H(B)'s set is nonempty, lower bounded by zero and has the positive unique root asserted here. Q is only used at 39/40, a genuine positive quantile. The denominator h is protected by h > 0 and H(B) by its stated positivity; h/z is also nonzero. The hypotheses 0 < α < 1 exclude degenerate levels; B = 0 remains a valid, nonempty model. The `Tendsto` is a genuine real limit of an explicitly bounded tail function, not a conditional-order limsup or liminf. There is no integral, expectation, natural subtraction, out-of-domain root/log/rpow, empty finite index type or partial function in this closure.

## SAP.P033.T14

Location: `SAP/P033/Challenge/Part1.lean:86–88`. Its docstring compares two interval-imputation rules for recorded inputs and says the second statistic falls in adjacent histogram bins.

All variables here are real. Expanding the SAP definitions, let u(β,U,q) = (U−β)/q, w(L,U,q) = (U−L)/(2q), and a(β,se) = |β|/se. The full statement conjoins:

1. For every q ∈ ℝ with q > 0,
   `u(−3/20,−101/1000,q) = 49/(1000q)`,
   `w(−213/1000,−101/1000,q) = 7/(125q)`, and
   `w(−213/1000,−101/1000,q)/u(−3/20,−101/1000,q) = 8/7`.
2. `−101/1000−(−3/20) = 49/1000` and `−101/1000−(−213/1000) = 14/125`.
3. At q = 49/25,
   `u(−3/20,−101/1000,q) = 1/40`,
   `a(−3/20,u(−3/20,−101/1000,q)) = 6`,
   `w(−213/1000,−101/1000,q) = 1/35`, and
   `a(−3/20,w(−213/1000,−101/1000,q)) = 21/4`.
4. `((−213/1000)+(−101/1000))/2−(−3/20) = −7/1000`.
5. For every q ∈ ℝ with q > 0,
   `a(79/1000,w(27/1000,132/1000,q))/q = 158/105`, and
   `a(79/1000,u(79/1000,132/1000,q))/q = 79/53`.
6. `27/18 < 158/105 < 28/18` and `26/18 < 79/53 < 27/18`.

The last inequalities locate the normalized statistics (absolute t divided by q) in adjacent open intervals of width 1/18. The theorem does not independently define a histogram object. It does not assert that any of the input intervals were centered normal intervals: their lack of centering is part of the numerical comparison. The parameter q is any positive real, with 1.96 a particular recorded approximation.

Junk-value audit: the base definitions use total real division, including zero denominators and negative or zero putative standard errors off their intended domains. Here q > 0 or q = 49/25. Both widths U−L and both upper gaps U−β are strictly positive for the displayed data, so all standard errors and every further division by them are positive and nonzero. Every rational denominator is nonzero. Absolute value is taken only of the estimate; because all standard errors here are positive this is indeed an absolute t statistic. There are no normal quantile, measures, integrals, natural numbers or casts, truncated subtractions, roots, logarithms, rpow, infima, suprema, limits, finite index sets or partial functions. Generated numeral proofs add no substantive hypotheses.

## SAP.P033.T15

Location: `SAP/P033/Challenge/Part1.lean:90–92`. Its docstring describes width-imputation reconstruction formulas, recovery of a centered normal interval's standard error, and equality with the upper-endpoint rule exactly at midpoint estimates.

Expand u(β,U,q) = (U−β)/q, w(L,U,q) = (U−L)/(2q), a(β,se) = |β|/se, and r(β,L,U,q) = 2Φ(−|β|/[(U−L)/(2q)]). These are exactly `upperSE`, `widthSE`, `absoluteT`, and `reconstructedP`. The proposition is the conjunction of:

1. For every α, β, L, U ∈ ℝ, in that order, if L < U and Q(1−α/2) > 0, let q = Q(1−α/2). Then
   `w(L,U,q) = (U−L)/(2q)`,
   `a(β,w(L,U,q)) = |β|/w(L,U,q)`, and
   `r(β,L,U,q) = 2Φ(−a(β,w(L,U,q)))`.
   These three identities are literal expansions of definitions; they prescribe a reconstruction, not a validity theorem for arbitrary intervals.
2. Q(1−(1/10)/2) = Q(19/20) and Q(1−(1/20)/2) = z.
3. For every β, L, U, q ∈ ℝ, if L < U and q > 0, then all four statements hold:
   `2q(w(L,U,q)−u(β,U,q)) = 2β−(L+U)`,
   `w(L,U,q) = u(β,U,q) ↔ β = (L+U)/2`,
   `u(β,U,q) < w(L,U,q) ↔ (L+U)/2 < β`, and
   `w(L,U,q) < u(β,U,q) ↔ β < (L+U)/2`.
4. For every β, q, s ∈ ℝ, if q > 0 and s > 0, then
   `w(β−qs,β+qs,q) = s` and `u(β,β+qs,q) = s`.
5. For every q ∈ ℝ with q > 0,
   `w(−213/1000,−101/1000,q) = 7/(125q)` and
   `a(−3/20,w(−213/1000,−101/1000,q)) = 75q/28`.
6. At q = 49/25, the width-imputed standard error for those endpoints is 1/35 and the absolute t statistic for β = −3/20 is 21/4.

There is no claim that the reconstructed r is a valid p-value for every supplied interval. Clause 4 is deterministic recovery from endpoints of the centered form; it imposes no sampling distribution. Clause 3 permits arbitrary β, including β ≥ U, where u may not be a usable standard error; it only compares the real-valued reconstruction formulas.

Junk-value audit: the first clause assumes L < U and q = Q(1−α/2) > 0, ensuring a positive width standard error and all denominators nonzero. α is not explicitly assumed in (0,1). For a standard normal, Q(p) is the ordinary finite quantile on 0 < p < 1, returns zero when p ≤ 0 (unbounded-below defining set), and returns zero when p ≥ 1 (empty defining set). Thus the positive-q premise excludes those junk cases, as well as the nonpositive genuine quantiles; its intended normal-confidence range is nonempty. The two explicit confidence-level substitutions use p = 19/20 and 39/40. Clauses 3–6 have q > 0 or q = 49/25; clause 4 also has s > 0. In clause 3 u may be zero if β = U, but it is never used as a denominator there, so no junk t statistic is asserted for it. Every absolute t statistic appearing in this statement divides by a strictly positive w. Φ uses a probability measure, making `toReal ∞` irrelevant. The only infimum is Q, with the domain protection just explained. All subtraction is real. There is no integral, expectation, root/log/rpow, limsup/liminf, empty index type or partial function.

## Per-target closure inventory

All entries below were read before saving this blind-stage document. Line 0 marks generated declarations, whose printed bodies were inspected in the scratch output.

### SAP.P033.T11

- `SAP.P033.T11CoreStatement` — `SAP/P033/Defs/Part3.lean:214`.
- `SAP.P033.T11CoreStatement._proof_1` — `SAP/P033/Defs/Part3.lean:0`.
- `SAP.P033.T11CoreStatement._proof_2` — `SAP/P033/Defs/Part3.lean:0`.
- `SAP.P033.T11CoreStatement._proof_3` — `SAP/P033/Defs/Part3.lean:0`.
- `SAP.P033.T11CoreStatement._proof_4` — `SAP/P033/Defs/Part3.lean:0`.
- `SAP.P033.T11CoreStatement._proof_5` — `SAP/P033/Defs/Part3.lean:0`.
- `SAP.P033.T11Statement` — `SAP/P033/Defs/Part4.lean:188`.
- `SAP.P033.T11Statement._proof_1` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T11Statement._proof_2` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_4` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T5Statement._proof_3` — `SAP/P033/Defs/Part3.lean:0`.
- `SAP.P033.T5Statement._proof_8` — `SAP/P033/Defs/Part3.lean:0`.
- `SAP.P033.T7CoreStatement._proof_27` — `SAP/P033/Defs/Part3.lean:0`.
- `SAP.P033.binarySampleVariance` — `SAP/P033/Defs/Part1.lean:52`.
- `SAP.P033.normalCDF` — `SAP/P033/Defs/Part1.lean:17`.
- `SAP.P033.normalCritical` — `SAP/P033/Defs/Part1.lean:21`.
- `SAP.P033.normalCritical._proof_1` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalCritical._proof_2` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalQuantile` — `SAP/P033/Defs/Part1.lean:19`.
- `SAP.P033.sampleMean` — `SAP/P033/Defs/Part1.lean:34`.
- `SAP.P033.sampleVariance` — `SAP/P033/Defs/Part1.lean:36`.

### SAP.P033.T12

- `SAP.P033.T12Statement` — `SAP/P033/Defs/Part4.lean:15`.
- `SAP.P033.T12Statement._proof_1` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_10` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_11` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_12` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_13` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_14` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_15` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_16` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_17` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_18` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_19` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_2` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_20` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_3` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_4` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_5` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_6` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_7` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_8` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_9` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.ValidBiasP` — `SAP/P033/Defs/Part1.lean:240`.
- `SAP.P033.biasCoverage` — `SAP/P033/Defs/Part1.lean:236`.
- `SAP.P033.biasModelLaw` — `SAP/P033/Defs/Part1.lean:234`.
- `SAP.P033.honestHalfLength` — `SAP/P033/Defs/Part1.lean:238`.
- `SAP.P033.intervalCoverage` — `SAP/P033/Defs/Part1.lean:87`.
- `SAP.P033.m1Observed._proof_1` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.m2Perturbation._proof_1` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalCDF` — `SAP/P033/Defs/Part1.lean:17`.
- `SAP.P033.normalCritical` — `SAP/P033/Defs/Part1.lean:21`.
- `SAP.P033.normalCritical._proof_1` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalCritical._proof_2` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalQuantile` — `SAP/P033/Defs/Part1.lean:19`.
- `SAP.P033.pseudoP` — `SAP/P033/Defs/Part1.lean:231`.
- `SAP.P033.widthSE._proof_1` — `SAP/P033/Defs/Part1.lean:0`.

### SAP.P033.T13

- `SAP.P033.T12Statement._proof_1` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_13` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_16` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_2` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T13Statement` — `SAP/P033/Defs/Part4.lean:47`.
- `SAP.P033.ValidBiasP` — `SAP/P033/Defs/Part1.lean:240`.
- `SAP.P033.biasAwareP` — `SAP/P033/Defs/Part1.lean:244`.
- `SAP.P033.biasCoverage` — `SAP/P033/Defs/Part1.lean:236`.
- `SAP.P033.biasModelLaw` — `SAP/P033/Defs/Part1.lean:234`.
- `SAP.P033.honestHalfLength` — `SAP/P033/Defs/Part1.lean:238`.
- `SAP.P033.m1Observed._proof_1` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.m2Perturbation._proof_1` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalCDF` — `SAP/P033/Defs/Part1.lean:17`.
- `SAP.P033.normalCritical` — `SAP/P033/Defs/Part1.lean:21`.
- `SAP.P033.normalCritical._proof_1` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalCritical._proof_2` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalQuantile` — `SAP/P033/Defs/Part1.lean:19`.
- `SAP.P033.pseudoP` — `SAP/P033/Defs/Part1.lean:231`.
- `SAP.P033.widthSE._proof_1` — `SAP/P033/Defs/Part1.lean:0`.

### SAP.P033.T14

- `SAP.P033.T12Statement._proof_16` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_2` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement` — `SAP/P033/Defs/Part4.lean:75`.
- `SAP.P033.T14Statement._proof_1` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_10` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_11` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_12` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_13` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_14` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_15` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_16` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_17` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_18` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_19` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_2` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_20` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_21` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_22` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_23` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_24` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_3` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_4` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_5` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_6` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_7` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_8` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_9` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.absoluteT` — `SAP/P033/Defs/Part1.lean:47`.
- `SAP.P033.upperSE` — `SAP/P033/Defs/Part1.lean:43`.
- `SAP.P033.widthSE` — `SAP/P033/Defs/Part1.lean:45`.
- `SAP.P033.widthSE._proof_1` — `SAP/P033/Defs/Part1.lean:0`.

### SAP.P033.T15

- `SAP.P033.T12Statement._proof_1` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_16` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_2` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T12Statement._proof_4` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_1` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_10` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_13` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_14` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_15` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_2` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_23` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_3` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_4` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_5` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_6` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T14Statement._proof_7` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.T15Statement` — `SAP/P033/Defs/Part4.lean:95`.
- `SAP.P033.T15Statement._proof_1` — `SAP/P033/Defs/Part4.lean:0`.
- `SAP.P033.absoluteT` — `SAP/P033/Defs/Part1.lean:47`.
- `SAP.P033.normalCDF` — `SAP/P033/Defs/Part1.lean:17`.
- `SAP.P033.normalCritical` — `SAP/P033/Defs/Part1.lean:21`.
- `SAP.P033.normalCritical._proof_1` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalCritical._proof_2` — `SAP/P033/Defs/Part1.lean:0`.
- `SAP.P033.normalQuantile` — `SAP/P033/Defs/Part1.lean:19`.
- `SAP.P033.reconstructedP` — `SAP/P033/Defs/Part1.lean:49`.
- `SAP.P033.upperSE` — `SAP/P033/Defs/Part1.lean:43`.
- `SAP.P033.widthSE` — `SAP/P033/Defs/Part1.lean:45`.
- `SAP.P033.widthSE._proof_1` — `SAP/P033/Defs/Part1.lean:0`.
