# Blind reading

This file was written before opening `claims.json` or `record.json`. I read the two challenge docstrings and declarations, all three definition source files, both umbrella imports, and all 56 distinct closure declarations using `scratch/Inspect.lean`. The generated `_proof_...` declarations were printed with proofs: they supply numeral `AtLeastTwo`/`NeZero` instances and `CharZero ℝ`, not substantive mathematical assumptions. The challenge stubs themselves are taken as certified, as instructed.

## SAP.P036.T1

Location: `SAP/P036/Challenge/Part1.lean:6–12`; its proposition is `SAP/P036/Defs/Part3.lean:15–51`. The statement is a conjunction of the following independent universally quantified propositions and numerical assertions. Universes in the statement are `Type` (universe zero); the definition helpers are universe polymorphic.

1. For every measurable space Ω, probability measure μ on Ω, natural number k, set P ⊆ Ω, function X : Ω → (Fin k → ℝ), real coefficients β₀ and β₁, coefficient vector γ : Fin k → ℝ, and functions Y, ε : Ω → ℝ, in precisely that order: assume P is measurable, X is measurable for the usual product Borel structure, ε is integrable, the function C(ω) = Σ(j : Fin k) X(ω)(j)γ(j) is integrable, Y(ω) = β₀ + β₁1_P(ω) + C(ω) + ε(ω) μ-almost everywhere, and Eμ[ε | σ(1_P,X)] = 0 μ-almost everywhere. Then Eμ[Y | σ(1_P,X)](ω) = β₀ + β₁1_P(ω) + C(ω) μ-almost everywhere. Here 1_P is the real-valued set indicator with value 1 on P and 0 outside it. The sigma-algebra is the Mathlib measurable-space comap of ω ↦ (1_P(ω),X(ω)), with the Borel measurable spaces on ℝ and its finite product. The equations involving conditional expectations are almost-everywhere equations, not pointwise equations. No positivity of the probabilities of the two arms is assumed in this first conjunct.

2. For every measurable Ω, probability measure μ, set P, real β₀, β₁, and functions Y, ε, in that order: assume P is measurable, ε is integrable, Y = β₀ + β₁1_P + ε almost everywhere, Eμ[ε | σ(1_P)] = 0 almost everywhere, 0 < (μ P).toReal, and (μ P).toReal < 1. The sigma-algebra is the comap of the real indicator alone. Define m_A = (∫ ω in A, Y(ω) ∂μ)/(μ A).toReal, where the numerator is the Mathlib Bochner integral with respect to μ restricted to A. The conclusion is m_P − m_(Pᶜ) = β₁ and m_(Pᶜ) = β₀.

3. For every type I equipped with a finite enumeration and decidable equality, finite subset S, and arbitrary real function Y on I: assume 0 < |S| and 0 < |Sᶜ|, where the complement is within the full finite universe I. Put n_A = |A| and m_A(Y) = Σ(i ∈ A)Y(i)/n_A, with the cardinal cast into ℝ. For every i the indicator is 0 or 1, and Σ(i ∈ I)1_S(i) = n_S. There exists exactly one ordered pair b = (b₀,b₁) of real numbers such that, for every real pair c, R(b) ≤ R(c), where R(b₀,b₁) = Σ(i ∈ I)(Y(i) − b₀ − b₁1_S(i))². In addition, for every real pair b, this global-minimizer property holds if and only if b = (m_(Sᶜ)(Y), m_S(Y) − m_(Sᶜ)(Y)). Thus this is actual least squares with a proved minimizer characterization, not just a named pair of means.

4. For every finite decidable I, subset S, real function Y, and natural numbers k₁,k₀, in that order: if |S| = 94, |Sᶜ| = 95, every Y(i) is 0 or 1, Σ(i ∈ S)Y(i) = (k₁ : ℝ), and Σ(i ∈ Sᶜ)Y(i) = (k₀ : ℝ), then the pair (m_(Sᶜ)(Y), m_S(Y) − m_(Sᶜ)(Y)) equals ((k₀ : ℝ)/95, (k₁ : ℝ)/94 − (k₀ : ℝ)/95). The names `olsCoefficients` and `tableCoefficients` are exactly these two formulas.

5. The same count formula evaluated at (10,10) is (2/19,1/893), and at (10,7) is (7/95,146/4465). Its slope at (10,10) lies in [0.001−0.0005,0.001+0.0005), its intercept at (10,10) in [0.105−0.0005,0.105+0.0005), its slope at (10,7) in [0.033−0.0005,0.033+0.0005), and its intercept at (10,7) in [0.074−0.0005,0.074+0.0005). These interval predicates are exactly `roundsToThree x d := d−1/2000 ≤ x ∧ x < d+1/2000`.

The challenge docstring describes corrected symbol roles, zero-conditional-mean models, the unique unadjusted OLS minimizer, and two table count calculations. The proposition does not purport to prove the empirical response counts, adjusted numerical regressions, or independence/random assignment from data.

### Totalization and boundary conventions

- Real division is total, with x/0 = 0. An empty finite-set mean is therefore 0. The finite OLS hypotheses and the table sizes exclude empty arms at every use. Fixed table denominators 94 and 95 are positive.
- `μ.real A` is `(μ A).toReal`; ENNReal infinity maps to 0. Probability measures make every set finite in measure, and the two strict inequalities plus measurable complementation make both arm probabilities strictly positive in the arm-mean conjunct. Thus neither infinity conversion nor zero denominators affect that conclusion.
- The Bochner integral is 0 for a non-integrable function. The hypotheses make ε and C integrable; bounded indicator and constant terms are integrable on a probability space. The a.e. model equation then makes Y integrable. Its restrictions to the measurable arms are integrable. There is no non-integrable integral exploited here.
- Mathlib conditional expectation is defined to be 0 if the conditioning measurable space is not a sub-sigma-algebra, if the trimmed measure is not sigma-finite, or if the input is not integrable. Measurability of P and X makes the displayed comaps sub-sigma-algebras. A probability measure trims to a finite measure. Integrability of ε is explicit, and that of Y follows from the model as above. Consequently none of these zero defaults is used to discharge the zero-conditional-mean condition or the conclusion. The conditional-expectation representative is only relevant up to almost-everywhere equality.
- `Fin 0` is permitted: the covariate sum is then the empty sum 0. This legitimately includes the intercept/indicator model. Empty probability spaces cannot carry the required probability measure. The finite OLS branches cannot have empty ambient I because their arms are nonempty.
- Natural counts and cardinals embed exactly into ℝ. All subtraction in the displayed real formulas is real subtraction, not truncated natural subtraction. No integer division, floor, or modular arithmetic is involved.
- The rounding predicate has the half-open endpoints for nearest rounding with ties toward positive infinity when d lies on the thousandths grid. It does not itself require d to lie on that grid, but all four uses explicitly give such grid values. No tie ambiguity affects these numbers.
- There are no logarithms, real powers, square roots, infima/suprema, limits/limsup/liminf, partial-function defaults, or infinite sums in this closure.

The T1 closure's generated declarations are `T1Statement._proof_1` through `_proof_11`, `roundsToThree._proof_1`, and `tableCoefficients._proof_1` and `_proof_2`. They express numeral typeclass facts only and add no hypotheses.

## SAP.P036.T2

Location: `SAP/P036/Challenge/Part1.lean:14–21`; its proposition is `SAP/P036/Defs/Part3.lean:56–104`. This is an independent conjunction of finite-sample matrix identities, complete-randomization moment identities, a binary variance identity, and count calculations.

All helpers in this statement unfold as follows. For a finite subset S of a finite decidable type I, let Sᶜ be its complement in I, N = |I|, n₁ = |S|, n₀ = |Sᶜ|, p_i = 1 if i ∈ S and 0 otherwise, and m_A(Y) = Σ(i ∈ A)Y(i)/|A|. Set SS_A(Y) = Σ(i ∈ A)(Y(i)−m_A(Y))² and s_A²(Y) = SS_A(Y)/((|A| : ℝ)−1). These are `peers`, `armMean`, `armSS`, and `sampleVariance`; every denominator is real.

The design row d_i has two entries, indexed by `Fin 2`: d_i0 = 1 and d_i1 = p_i. The Gram entries are G_ab = Σ(i ∈ I)d_ia d_ib. The explicitly defined matrix H (`gramInverse`) has entries H₀₀ = 1/n₀, H₀₁ = H₁₀ = −1/n₀, and H₁₁ = 1/n₁+1/n₀. The regression coefficients are q_a = Σ(b ∈ {0,1}) H_ab Σ(i ∈ I)d_ibY(i). The pair called `olsCoefficients` is (m_(Sᶜ)(Y),m_S(Y)−m_(Sᶜ)(Y)); the residual is e_i = Y(i)−m_(Sᶜ)(Y)−(m_S(Y)−m_(Sᶜ)(Y))p_i. Leverage is h_i = Σ(a ∈ {0,1})Σ(b ∈ {0,1})d_ia H_ab d_ib. The covariance entry called `hc2Covariance` is Σ(i ∈ I)Σ(u ∈ {0,1})Σ(v ∈ {0,1}) H_au [e_i²/(1−h_i) · d_iu d_iv] H_vb. The scalar `hc2Variance` is its entry (1,1), i.e. the peer-slope variance. This is a genuine sandwich expression; equality to the Neyman expression is a conclusion.

For fixed natural n₁ and finite I, `assignments n₁` is the finite powerset consisting of all subsets S ⊆ I of cardinality n₁. `designExpectation n₁ F` is the Mathlib `Finset.expect`, namely Σ(S in that powerset)F(S) divided by the number of such subsets. `designVariance n₁ F` is that same uniform average applied to (F(S)−E F)², without a sample-variance correction. For fixed potential-outcome functions Y₁,Y₀ : I → ℝ, `observedOutcome S Y₁ Y₀ i` is Y₁(i) if i ∈ S and Y₀(i) otherwise. `unitEffect Y₁ Y₀ i` is τ_i = Y₁(i)−Y₀(i), and `estimatedEffect Y₁ Y₀ S` is the observed treated-arm mean minus the observed control-arm mean. `populationMean Y` is m_I(Y), and `populationVariance Y` is S_Y² = Σ(i ∈ I)(Y(i)−m_I(Y))²/((N : ℝ)−1). These potential outcomes are fixed functions throughout each assignment average.

The quantified assertions, in order, are:

1. For every finite decidable I, subset S, and arbitrary real Y, if 2 ≤ |S| and 2 ≤ |Sᶜ|, then:
   - For all a,b : Fin 2, G_ab is N if a=b=0 and is n₁ otherwise.
   - For all a,b, Σ_c H_ac G_cb = δ_ab and Σ_c G_ac H_cb = δ_ab.
   - (q₀,q₁) = (m_(Sᶜ)(Y),m_S(Y)−m_(Sᶜ)(Y)).
   - For every i, h_i = 1/n₁ on S and 1/n₀ on its complement.
   - The slope sandwich equals Σ(i ∈ S)e_i²/[n₁²(1−1/n₁)] + Σ(i ∈ Sᶜ)e_i²/[n₀²(1−1/n₀)].
   - The same sandwich equals s_S²(Y)/n₁+s_(Sᶜ)²(Y)/n₀.

2. For every finite decidable I, natural n₁,n₀, followed by hypotheses 2 ≤ n₁, 2 ≤ n₀, n₁+n₀ = |I|, and then for every Y₁,Y₀ : I → ℝ: let E be the uniform assignment expectation of the slope HC2 sandwich computed on the observed outcomes, and V the uniform assignment variance of the estimated effect. Then all nine assertions hold:
   - E_assignment[estimated effect] = m_I(Y₁)−m_I(Y₀).
   - V = S_(Y₁)²/n₁ + S_(Y₀)²/n₀ − S_τ²/N.
   - E_assignment[s_S²(observed outcomes)] = S_(Y₁)².
   - E_assignment[s_(Sᶜ)²(observed outcomes)] = S_(Y₀)².
   - E = S_(Y₁)²/n₁ + S_(Y₀)²/n₀.
   - E−V = S_τ²/N.
   - 0 ≤ S_τ²/N.
   - V ≤ E.
   - E=V if and only if there exists one real number c such that, for every i ∈ I, τ_i=c. The existential c is inside this last equivalence; it is not a prior restriction on the potential outcomes.

3. For every type I (not necessarily finite), finite subset S, and function Y : I → ℝ: if 2 ≤ |S|, then for every natural k, if every Y(i) on S equals 0 or 1 and Σ(i ∈ S)Y(i) = (k : ℝ), one has s_S²(Y) = (k : ℝ)((|S| : ℝ)−(k : ℝ))/[(|S| : ℝ)((|S| : ℝ)−1)]. No assumptions are made about Y outside S.

4. For every finite decidable I, subset S, real Y, natural k₁,k₀, in that order: if |S|=94, |Sᶜ|=95, all Y(i) are 0 or 1, and their two arm sums are k₁,k₀, then the slope HC2 sandwich equals B(94,k₁)+B(95,k₀), where B(n,k) = (k : ℝ)((n : ℝ)−(k : ℝ))/[(n : ℝ)²((n : ℝ)−1)]. These two definitions are `binaryHC2Arm` and `tableHC2`.

5. B(94,10)+B(95,10) = 50039/24720919, and B(94,10)+B(95,7) = 1080506/618022975. The nonnegative real square root of the first lies in [0.045−0.0005,0.045+0.0005); that of the second lies in [0.042−0.0005,0.042+0.0005). The rounding predicate is the two real inequalities defining those half-open intervals.

The docstring limits the randomization assertion to unadjusted regressions, complete randomization, fixed potential outcomes, and at least two units per arm. It describes nonnegative expectation bias and equality for constant effects, rather than an assignment-by-assignment upper bound on the true variance.

### Totalization and boundary conventions

- Real division by 0 is 0. Empty arm means are 0; single-unit sample variances also use zero division. The first and fourth conjuncts have sizes at least 2 or fixed sizes 94 and 95. The randomization conjunct has n₁,n₀ ≥ 2 and N=n₁+n₀ ≥ 4; every assignment included in the average has exactly these nondegenerate sizes. The binary single-arm conjunct has |S| ≥ 2. Hence all used arm means, sample variances, H entries, population variances, and the explicit denominators are well-defined in their usual mathematical domains.
- The explicit H would be an arbitrary total formula when an arm is empty; its inverse property is asserted only for nonempty arms (indeed at least two each). HC2 has a denominator 1−h_i, which would vanish for an arm of size 1. In its asserted domains h_i is the reciprocal of a size at least 2, so 1−h_i > 0. The covariance therefore does not rely on zero division.
- `Finset.expect` on an empty set is 0 (sum 0 and division by cardinal 0). The assignment collection is nonempty because 0 ≤ n₁ ≤ N, with N=n₁+n₀. It contains every fixed-size subset and gives each the same positive weight. The function F is real-valued on a finite domain, so no integrability convention is involved. `designVariance` is an actual probability variance on this nonempty collection.
- `tableHC2` has no explicit bounds k≤n at the definition level and can be negative for arbitrary impossible count inputs. Its generic application assumes binary outcomes and exact sums, which force those bounds; its two closed numerical applications use feasible counts. Both displayed fractions are strictly positive. `Real.sqrt x` is 0 for x≤0, but that default is not used for either standard error.
- Cardinal and count casts to ℝ are exact. Subtractions in `sampleVariance`, `populationVariance`, `binaryHC2Arm`, and all matrix formulas happen after casting, hence are real subtraction, not truncated natural subtraction.
- The matrix indices `Fin 2` have exactly the intended two elements; generated `NeZero 2` proofs make numeral indices legal. No empty matrix index is possible. Empty ambient finite populations are excluded by the hypotheses. The binary-arm proposition permits infinite ambient types but has a nonempty finite arm.
- The half-open rounding predicate requires no grid hypothesis internally, but both displayed values are explicit thousandths, and the evaluated roots are in its ordinary rounding cells.
- This closure has no Bochner integrals, conditional expectations, infinity-to-real conversions, logarithms, real powers, infima/suprema, limits/limsup/liminf, infinite sums, or partial-function defaults.

The T2 closure's generated declarations are `T1Statement._proof_8` (the numeral 1000), `T2Statement._proof_1` through `_proof_7`, `designExpectation._proof_1`, `designRow._proof_1`, and `roundsToThree._proof_1`. They give only numeric/typeclass facts; none changes the mathematical content.
