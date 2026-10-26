# Highlights

A declaration appears in full once; other sections link to the same entry. Helpers are supporting results and carry no independent target credit.

## The most helpful results

### H001

**Combinatorial central limit theorem for permutation arrays**

Uniform permutation sums of doubly centered arrays have a standard normal limit when normalized entries vanish.

Areas: Probability, Randomization inference.

**Statement.** Let $`N_q\to\infty`$ be natural row sizes, $`\beta_q\to0`$ a real sequence, and $`c_q`$ real $`N_q\times N_q`$ matrices. Eventually in $`q`$, assume $`N_q\ge2`$, every row and every column sums to zero, $`\sum_{i,j}c_q(i,j)^2=N_q-1`$, and $`\lvert c_q(i,j)\rvert\le\beta_q`$ for all $`i,j`$. Then for every bounded continuous real $`f`$,


```math
\frac1{N_q!}\sum_{\pi\in S_{N_q}}f\!\left(\sum_i c_q(i,\pi(i))\right)\longrightarrow\int f\,dN(0,1).
```


Equivalently, under uniform permutations the permutation sums converge weakly to the standard normal law.

**Use.** A common foundation for permutation tests, matching, and finite-population asymptotics, with no paper-specific objects in the signature.

**Relation to Mathlib.** Mathlib supplies weak-convergence tools. The permutation-array limit uses local exchangeable-transposition identities together with bundled StatLean permutation-marginal and Stein-method machinery.

**Declaration:** [`TailB_permutation_array_clt`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L1156)

```lean
import AronowAudit.Shared.MapTailB.PermutationArray

#check TailB_permutation_array_clt
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.MapTailB.PermutationArray.statistic`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L60): permutation-sum definition
- [`AronowAudit.MapTailB.PermutationArray.array_second_moments`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L478): finite-array second moments
- [`AronowAudit.MapTailB.PermutationArray.array_lipschitz_bound`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L1042): finite-stage bounded-Lipschitz error bound
- [`AronowAudit.MapTailB.PermutationArray.array_lipschitz_clt`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L1120): Lipschitz-test convergence form

**Scope.** Exact double centering and variance normalization are premises; the maximum entry must vanish. This is an asymptotic theorem, without an optimal finite-sample distribution-function error bound.

### H002

**Lindeberg CLT on changing probability spaces**

Independent centered triangular arrays converge to the standard normal law under variance normalization and the Lindeberg condition.

Areas: Probability, Asymptotic statistics.

**Statement.** For arbitrary finite row lengths $`m_n`$ and probability spaces $`(\Omega_n,P_n)`$, let measurable real $`X_{ni}`$, $`i\lt m_n`$, be jointly independent within each row, centered under $`P_n`$, and in $`L^2(P_n)`$. Assume $`\sum_{i\lt m_n}\mathrm{Var}_{P_n}(X_{ni})\to1`$ and, for every $`\epsilon\gt 0`$,


```math
\sum_{i\lt m_n}\int_{\{\lvert X_{ni}\rvert\gt \epsilon\}}X_{ni}^2\,dP_n\longrightarrow0.
```


Then $`\sum_{i\lt m_n}X_{ni}`$ converges in distribution to any random variable $`Z`$ with law $`N(0,1)`$ on any probability space $`(\Omega',P')`$. The formal conclusion uses Mathlib's weak convergence of laws.

**Use.** Supports independent clusters, triangular arrays, and conditional resampling arguments without forcing a common row space or identical distributions. No growth condition on $`m_n`$ or relationship between rows is assumed.

**Relation to Mathlib.** Mathlib v4.34.1 CentralLimitTheorem.lean supplies the scalar iid CLT, including ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub. This triangular-array extension allows changing row probability spaces and uses Mathlib independence, characteristic functions, Gaussian laws and Lévy convergence.

**Declaration:** [`AronowAudit.P037.LindebergCompletion.lindeberg_clt`](../AronowAudit/P037/P037_VaryingLindeberg.lean#L594)

```lean
import AronowAudit.P037.P037_VaryingLindeberg

#check AronowAudit.P037.LindebergCompletion.lindeberg_clt
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P037.LindebergCompletion.lindeberg_clt_of_bounded`](../AronowAudit/P037/P037_VaryingLindeberg.lean#L632): vanishing uniform-bound corollary

**Scope.** Measurability, within-row joint independence, square integrability, centering, variance normalization and the Lindeberg condition are inputs. The triangular-array argument adapts StatLean/Stat-Lean. A bounded-array version in the same module, `lindeberg_clt_of_bounded`, supplies block-level normal limits in `P037_FiniteDesign.lean`.

### H003

**Le Cam’s first lemma, four equivalent forms**

Contiguity is equivalent to transfer of negligible statistics and two subsequential likelihood-ratio criteria under mutual absolute continuity.

Areas: Asymptotic statistics, Probability.

**Statement.** Let $`P_n,Q_n`$ be probability measures on arbitrary measurable spaces $`\Omega_n`$, with $`P_n\ll Q_n`$ and $`Q_n\ll P_n`$ for every $`n`$. The following four statements are equivalent.

1. For every sequence of measurable $`A_n\subseteq\Omega_n`$, $`P_n(A_n)\to0`$ implies $`Q_n(A_n)\to0`$.
2. For every sequence of measurable real $`T_n`$, if $`P_n(\lvert T_n\rvert\ge\epsilon)\to0`$ for every $`\epsilon\gt 0`$, then $`Q_n(\lvert T_n\rvert\ge\epsilon)\to0`$ for every $`\epsilon\gt 0`$.
3. For every strictly increasing $`\phi:\mathbb N\to\mathbb N`$ and every probability measure $`U`$ on $`\mathbb R`$, if the $`Q_{\phi(k)}`$-laws of $`(dP_{\phi(k)}/dQ_{\phi(k)}).\mathrm{toReal}`$ converge weakly to $`U`$, then $`U((0,\infty))=1`$.
4. For every such $`\phi`$ and every probability measure $`V`$ on $`\mathbb R`$, if the $`P_{\phi(k)}`$-laws of $`(dQ_{\phi(k)}/dP_{\phi(k)}).\mathrm{toReal}`$ converge weakly to $`V`$, then $`\int x\,dV(x)=1`$.

Weak convergence means convergence of integrals of every bounded continuous real test function.

**Use.** Gives interchangeable event, statistic, and likelihood-ratio criteria for transferring negligible remainders between experiments. It applies to changing observation spaces and quantifies over all subsequential probability limits, without assuming convergence of the entire likelihood-ratio sequence.

**Relation to Mathlib.** Mathlib v4.34.1 supplies Radon–Nikodym derivatives, weak convergence and Portmanteau tools. The local asymptotic-statistics interface combines these ingredients into event, statistic and subsequential likelihood-ratio characterizations of contiguity.

**Declaration:** [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.Contiguity.leCam_first_tfae`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L3670)

```lean
import AronowAudit.P001.Wave1.Gap.GLP0011B3

#check AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.Contiguity.leCam_first_tfae
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.Contiguity.Contiguous`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L1457): directional contiguity definition
- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.WeakConverges`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L1365): bounded-continuous-test convergence
- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.Contiguity.contiguous_iff_tendsto_zero_statistics`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L2100): Event/statistic equivalence

**Scope.** The contiguity direction is vanishing under P implies vanishing under Q. Mutual absolute continuity is an explicit premise of this four-way theorem. Radon–Nikodym derivatives are converted from extended nonnegative values to real values.

### H004

**One-sided nondominated QMD gives score regularity and a local likelihood expansion**

One-sided quadratic-mean differentiability yields a centered square-integrable score and a local likelihood expansion without a common dominator.

Areas: Asymptotic statistics, Probability.

**Statement.** Let $`P`$ be a probability on an arbitrary measurable space $`\Omega`$, let $`P_t`$ be a probability for every real $`t\ge0`$, and assume $`P_0=P`$. Let $`g:\Omega\to\mathbb R`$ be measurable. For $`\nu_t=P+P_t`$, assume


```math
\frac{\left\|\sqrt{(dP_t/d\nu_t).\mathrm{toReal}}-\sqrt{(dP/d\nu_t).\mathrm{toReal}}-\frac t2g\sqrt{(dP/d\nu_t).\mathrm{toReal}}\right\|_{L^2(\nu_t)}}{t}\longrightarrow0\qquad(t\downarrow0).
```


The norm and quotient here take extended nonnegative values. For measurable iid $`X_i`$ of law $`P`$ on any probability space $`(\Omega',P')`$, the conclusions are $`E_Pg=0`$, integrability of $`g^2`$ under $`P`$, and


```math
\sum_{i\lt n}\log\!\left((dP_{1/\sqrt n}/dP)(X_i).\mathrm{toReal}\right)-\frac1{\sqrt n}\sum_{i\lt n}g(X_i)+\frac12\int g^2\,dP\longrightarrow0
```


in $`P'`$-measure.

**Use.** Supplies a LAN expansion for changing support and singular perturbations, deriving the score moments instead of assuming them. The path is scalar and may have no common dominating measure.

**Relation to Mathlib.** Mathlib supplies Radon–Nikodym, Lp and probability machinery. The local StatLean-based QMD machinery adds square-root transport, likelihood and product-Hellinger controls for the nondominated expansion.

**Declaration:** [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLAN.qmd_score_mean_integrable_and_lan_nondominated`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L7739)

```lean
import AronowAudit.P001.Wave1.Gap.GLP0011B3

#check AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLAN.qmd_score_mean_integrable_and_lan_nondominated
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic.IsRightQMD`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L854): exact right-sided QMD hypothesis
- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic.residualAgainst`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L846): square-root density residual
- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic.canonicalDominator`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L841): Pairwise dominating measure
- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.Core.NondominatedQMDPath.exists_nondominatedQMDPath_of_bare_qmd`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L1286): Package the derived square-integrable score

**Scope.** This is a scalar, right-sided path at local scale inverse square root of sample size; no common global dominator is assumed. The likelihood uses the Radon–Nikodym derivative of the absolutely continuous part. Lean uses log zero equal to zero, and the expansion does not assert everywhere-positive likelihoods. No Gaussian score limit is asserted by this declaration alone.

### H005

**Scalar outer Hadamard delta method**

Tangential Hadamard differentiability transfers outer weak convergence to a scalar limit and controls the actual linearization remainder.

Areas: Asymptotic statistics, Probability, Foundations.

**Statement.** Let $`E`$ be a real normed space with its Borel measurable structure, $`\mu`$ a probability on a measurable space $`\Omega`$, $`D,H\subseteq E`$, $`\theta\in D`$, and $`H`$ closed and separable. Suppose $`T:E\to\mathbb R`$ and a continuous linear map $`L:E\to\mathbb R`$ satisfy the following sequential tangential derivative condition: for every $`h\in H`$, every $`t_n\gt 0`$ with $`t_n\to0`$, and every $`h_n\to h`$ with $`\theta+t_nh_n\in D`$ for all $`n`$,


```math
\frac{T(\theta+t_nh_n)-T(\theta)}{t_n}\longrightarrow Lh.
```


Let $`r_n\to+\infty`$ and let arbitrary maps $`Z_n:\Omega\to E`$ satisfy the uniform eventual domain condition: there exists $`n_0\in\mathbb N`$ such that $`Z_n(\omega)\in D`$ for every $`n\ge n_0`$ and every $`\omega\in\Omega`$. Suppose $`r_n(Z_n-\theta)`$ converges outer weakly to a tight probability $`\nu`$ with $`\nu(H^c)=0`$: for every bounded continuous real test function, both its upper and lower expectations converge to its $`\nu`$-integral. Upper expectation is the infimum of integrals of measurable integrable pointwise majorants; lower expectation is minus the upper expectation of the negative function. Assume also that each $`T\circ Z_n`$ is measurable. Put $`R_n=r_n\{T(Z_n)-T(\theta)\}-L\{r_n(Z_n-\theta)\}`$. Then $`\mu^*(\lvert R_n\rvert\ge\epsilon)\to0`$ for every $`\epsilon\gt 0`$, and the CDF of $`r_n\{T(Z_n)-T(\theta)\}`$ converges to that of $`\nu\circ L^{-1}`$ at every continuity point. Here $`\mu^*`$ is the outer-measure value on an arbitrary event, so the remainder need not be measurable.

**Use.** Useful for empirical processes and functional estimators with potentially nonmeasurable paths and arbitrary diverging rates. Here outer weak convergence requires both upper and lower expectations of every bounded continuous test to converge; $`H`$ need not be a linear subspace.

**Relation to Mathlib.** Mathlib v4.34.1 supplies normed spaces, continuous linear maps, tightness and convergence tools. This theorem combines them with the local outer-expectation and sequential tangential derivative conventions and StatLean outer mapping and Slutsky tools.

**Declaration:** [`AronowAudit.P001.Wave1.TailA.outer_hadamard_delta_real`](../AronowAudit/P001/Wave1/Lib/TailA/OuterHadamardDelta.lean#L169)

```lean
import AronowAudit.P001.Wave1.Lib.TailA.OuterHadamardDelta

#check AronowAudit.P001.Wave1.TailA.outer_hadamard_delta_real
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P001.HadamardAt`](../AronowAudit/P001/P001_Foundations.lean#L418): sequential tangential derivative
- [`AronowAudit.P001.OuterWeakLimit`](../AronowAudit/P001/P001_Foundations.lean#L779): upper and lower expectation convergence
- [`AronowAudit.P001.Wave1.TailA.delta_hadamard_remainder_CP`](../AronowAudit/P001/Wave1/Lib/TailA/OuterHadamardDelta.lean#L99): outer-probability remainder theorem
- [`AronowAudit.P001.CP`](../AronowAudit/P001/P001_Foundations.lean#L60): probability remainder convention

**Scope.** Scalar output, a tight limit, a closed separable tangent set, eventual domain membership for every sample point, and measurable scalar readouts are explicit premises. Neither the original paths nor their linear readouts are required to be measurable.

### H006

**Attained Fréchet covariance bounds for square-integrable marginals**

Quantile couplings attain the largest and smallest covariances compatible with two square-integrable marginal laws.

Areas: Partial identification and bounds, Probability.

**Statement.** Let $`H`$ be a Borel probability on $`\mathbb R^2`$ whose two coordinate functions are in $`L^2(H)`$, with marginal laws $`\mu,\nu`$ and lower generalized-inverse quantiles $`Q_\mu,Q_\nu`$, where $`Q_\mu(u)=\inf\{x:u\le F_\mu(x)\}`$. Write $`X(x,y)=x`$ and $`Y(x,y)=y`$. Let $`\mathcal C(H)`$ be all Borel probability laws with the same two marginal CDFs as $`H`$. Put


```math
c_+=\int_{(0,1)}Q_\mu(u)Q_\nu(u)\,du-E_HX\,E_HY,\qquad c_-=\int_{(0,1)}Q_\mu(u)Q_\nu(1-u)\,du-E_HX\,E_HY.
```


Then $`\sup_{J\in\mathcal C(H)}\mathrm{Cov}_J(X,Y)=c_+`$ and $`\inf_{J\in\mathcal C(H)}\mathrm{Cov}_J(X,Y)=c_-`$. There exists a compatible law attaining $`c_+`$ and a compatible law attaining $`c_-`$. Covariance is the integral of the product of centered coordinates.

**Use.** Directly useful for sharp covariance and treatment-effect-variance identification, including atomic, mixed, and continuous distributions.

**Relation to Mathlib.** Mathlib v4.34.1 provides Measure.eq_of_cdf and covariance_eq_sub. This theorem adapts the bundled Causalean monotone/countermonotone product-loss optimality theorem to centered-coordinate covariance extrema. Its coupling and quantile foundations come from the Causalean library.

**Declaration:** [`TailB_frechet_covariance_L2`](../AronowAudit/Shared/MapTailB/QuantileBridge.lean#L226)

```lean
import AronowAudit.Shared.MapTailB.QuantileBridge

#check TailB_frechet_covariance_L2
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`TailB_compatibleLaws_iff_marginals`](../AronowAudit/Shared/MapTailB/QuantileBridge.lean#L29): equivalence of CDF and marginal-law compatibility
- [`AronowAudit.P022.lawCovariance`](../AronowAudit/P022/P022_Variance.lean#L535): centered-coordinate covariance definition
- [`Causalean.Stat.quantile`](../AronowAudit/External/Causalean/Stat/Quantile/Quantile.lean#L63): lower generalized-inverse quantile
- [`TailB_sharpCovariance_eq_quantile`](../AronowAudit/Shared/MapTailB/QuantileBridge.lean#L217): finite empirical sharp covariance formula

**Scope.** Both marginals must have finite second moments. The covariance extrema follow from the monotone and countermonotone product-loss coupling theorem in the bundled Causalean library.

### H007

**Order-two U-statistic CLT under only second moments**

Centered symmetric pairwise averages have a Gaussian limit under square integrability, including zero projection variance.

Areas: Probability, Asymptotic statistics, Interference and networks.

**Statement.** Let $`\mu`$ be a probability on any measurable space $`U`$, and let $`h:U\times U\to\mathbb R`$ be measurable, pointwise symmetric, in $`L^2(\mu\otimes\mu)`$, and centered under $`\mu\otimes\mu`$. Put $`g(u)=\int h(u,v)\,d\mu(v)`$ and $`D_N=N(N-1)/2`$. On the infinite iid product space with law $`\mu^{\mathbb N}`$ and coordinates $`U_i`$,


```math
\sqrt N\,D_N^{-1}\sum_{0\le i\lt j\lt N}h(U_i,U_j)\Rightarrow N\!\left(0,4\int g^2\,d\mu\right).
```


The formal conclusion is Mathlib convergence in distribution to the identity random variable under this Gaussian law. The nonnegative variance is represented using toNNReal. Division at $`N=0,1`$ is totalized in Lean and does not affect the limit.

**Use.** A general limit theorem for pairwise statistics, dyadic estimators and projection arguments; boundedness and a regression model are unnecessary.

**Relation to Mathlib.** Mathlib’s scalar iid CLT supplies the limit theorem for the first projection. This result adds the order-two projection decomposition and a negligible degenerate remainder, using local dyad and product-measure interfaces.

**Declaration:** [`AronowAudit.P018.Wave1.GP0182B2b_dyad_clt`](../AronowAudit/P018/Wave1/Gap/GP0182B2b.lean#L944)

```lean
import AronowAudit.P018.Wave1.Gap.GP0182B2b

#check AronowAudit.P018.Wave1.GP0182B2b_dyad_clt
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P018.Wave1.GP0182B2b_dyadAverage`](../AronowAudit/P018/Wave1/Gap/GP0182B2b.lean#L861): complete unordered-pair average
- [`AronowAudit.P018.Wave1.GP0182B2b_rowIntegral`](../AronowAudit/P018/Wave1/Gap/GP0182B2b.lean#L485): first projection
- [`AronowAudit.P018.Wave1.GP0182B2b_product`](../AronowAudit/P018/Wave1/Gap/GP0182B2b.lean#L773): infinite iid sample space
- [`AronowAudit.P018.Wave1.GP0182B2b_degenerate_null`](../AronowAudit/P018/Wave1/Gap/GP0182B2b.lean#L902): Negligible degenerate remainder

**Scope.** The kernel is scalar and the statistic averages all unordered pairs. Zero first-projection variance gives a degenerate Gaussian limit at this normalization; the theorem alone supplies neither studentization nor nondegenerate inference.

### H008

**Nearest positive-semidefinite matrix in Frobenius norm**

Clipping negative eigenvalues gives a Frobenius projection inequality that yields the unique nearest positive-semidefinite matrix.

Areas: Foundations, Optimization and computation, Regression and variance estimation.

**Statement.** For every natural $`n`$, every real symmetric $`n\times n`$ matrix $`M`$, and every real positive-semidefinite $`n\times n`$ matrix $`X`$, let $`M_+`$ replace each negative eigenvalue of $`M`$ by zero and let $`\lVert A\rVert_F^2=\sum_{i,j}A_{ij}^2`$. The declaration states


```math
\lVert M_+-M\rVert_F^2+\lVert X-M_+\rVert_F^2\le\lVert X-M\rVert_F^2.
```


The nearest-matrix and uniqueness conclusions are exposed by companion declarations; PSD membership of $`M_+`$ comes from the surrounding positive-part API.

**Use.** Useful for covariance repair, matrix optimization and numerical linear algebra, independently of a probability model or graph. The squared-distance remainder also quantifies the loss from a competing PSD matrix.

**Relation to Mathlib.** Mathlib v4.34.1 has matrix spectral theory, Matrix.PosSemidef and CFC positive parts, including CFC.posPart_nonneg and positive/negative-part identities. This development supplies the explicit Frobenius projection inequality and companion nearest-matrix and uniqueness results for the spectral positive part.

**Declaration:** [`AronowAudit.P011.SpectralConfidence.positive_part_frobenius_projection`](../AronowAudit/P011/P011_SpectralCompletion.lean#L203)

```lean
import AronowAudit.P011.P011_SpectralCompletion

#check AronowAudit.P011.SpectralConfidence.positive_part_frobenius_projection
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P011.positivePart`](../AronowAudit/P011/P011_Audit.lean#L255): spectral clipping definition
- [`AronowAudit.P011.SpectralConfidence.positive_part_frobenius_nearest`](../AronowAudit/P011/P011_SpectralCompletion.lean#L211): nearest-PSD inequality
- [`AronowAudit.P011.SpectralConfidence.positive_part_frobenius_unique`](../AronowAudit/P011/P011_SpectralCompletion.lean#L218): uniqueness at equal error
- [`AronowAudit.P011.positive_part_psd`](../AronowAudit/P011/P011_Audit.lean#L2505): PSD membership of the clipped matrix

**Scope.** The input matrix is real and symmetric. The headline declaration is the projection inequality; the nearest-matrix and uniqueness statements use companion results. No least-majorant assertion in Loewner order is made.

### H009

**Exponential tilting of possibly singular Gaussian laws**

A normalized linear exponential tilt shifts a finite-dimensional Gaussian mean by its covariance times the tilt vector.

Areas: Probability, Asymptotic statistics.

**Statement.** For any finite coordinate type with decidable equality, every real positive-semidefinite covariance matrix $`S`$, and every vector $`h`$ in the corresponding Euclidean space,


```math
\exp\!\left(\langle h,y\rangle-\frac12h^TSh\right)N(0,S)(dy)=N(Sh,S)(dy)
```


as an equality of measures. The left side is formally the centered Gaussian measure with nonnegative density $`\mathrm{ofReal}(\exp(\langle h,y\rangle-h^TSh/2))`$. The mean on the right is multiplication by $`S`$ viewed as a continuous linear map.

**Use.** A short measure-level change-of-law interface for Gaussian shifts, local alternatives and Le Cam calculations. Singular $`S`$, including $`S=0`$, is allowed.

**Relation to Mathlib.** The pinned Mathlib supplies multivariateGaussian, its characteristic function and covariance identities in Probability/Distributions/Gaussian/Multivariate.lean, together with standard Gaussian measure and scalar moment-generating tools. This theorem gives equality of the exponentially tilted Gaussian measure and the Gaussian measure with shifted mean.

**Declaration:** [`AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.multivariateGaussian_withDensity_exp_shift`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L8403)

```lean
import AronowAudit.P001.Wave1.Gap.GLP0011B3

#check AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.multivariateGaussian_withDensity_exp_shift
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.stdGaussian_withDensity_exp_shift`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L8339): standard-Gaussian density shift
- [`AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L8473): scalar Gaussian projection law
- [`AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.gaussianReal_withDensity_exp_shift`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L8260): Scalar standard-Gaussian tilt
- [`AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.pi_gaussianReal_withDensity_exp_shift`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L8299): coordinate product tilt

**Scope.** Finite-dimensional real Gaussian laws and linear exponential tilts only; this is not an infinite-dimensional Cameron–Martin theorem. Covariance invertibility is not assumed.

### H010

**Hellinger error tensorization for product experiments**

The square-root density error for independent repeated observations grows at most with the square root of sample size.

Areas: Probability, Asymptotic statistics.

**Statement.** Let probability measures $`\mu,\nu`$ on any measurable space $`\Omega`$ be absolutely continuous with respect to a common $`\sigma`$-finite measure $`\xi`$. Put $`p=(d\mu/d\xi).\mathrm{toReal}`$ and $`q=(d\nu/d\xi).\mathrm{toReal}`$. For every natural $`n`$,


```math
\left\|\sqrt{\prod_{j\lt n}p(x_j)}-\sqrt{\prod_{j\lt n}q(x_j)}\right\|_{L^2(\xi^{\otimes n})}\le\sqrt n\,\left\|\sqrt p-\sqrt q\right\|_{L^2(\xi)}.
```


The formal signature takes square roots of the real values of products of extended Radon–Nikodym derivatives and compares the real values of the extended $`L^2`$ norms. Companion integrability lemmas establish finiteness of the residual norms.

**Use.** Converts one-observation approximation into an experiment-level bound for testing, LAN and asymptotic equivalence on arbitrary observation spaces.

**Relation to Mathlib.** Mathlib supplies Radon–Nikodym derivatives, product integration and Lp inequalities. The local Hellinger product bound factors affinity over coordinates and applies a power inequality.

**Declaration:** [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ForMathlib.HellingerProduct.hellinger_product_eLpNorm_le_sqrt_n_per_sample`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L4417)

```lean
import AronowAudit.P001.Wave1.Gap.GLP0011B3

#check AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ForMathlib.HellingerProduct.hellinger_product_eLpNorm_le_sqrt_n_per_sample
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ForMathlib.HellingerProduct.hellinger_product_residual_sq_le_n_per_sample`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L4305): squared-integral version
- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ForMathlib.HellingerProduct.hellinger_per_sample_residual_memLp_two`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L4345): single-observation residual finiteness
- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ForMathlib.HellingerProduct.hellinger_product_residual_memLp_two_perCoord`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L4354): product residual finiteness

**Scope.** The convention is the unscaled square-root density difference. Both measures are probabilities, domination is common and sigma-finite, and the products have identical independent factors; arbitrary dependent laws are outside this statement.

### H011

**Multivariate iid CLT allowing singular covariance**

Sums of centered iid vectors with finite second moments converge after square-root normalization to a Gaussian law with the specified covariance, which may be singular.

Areas: Probability, Asymptotic statistics.

**Statement.** For any natural $`k`$, let measurable iid $`Y_i:\Omega\to\mathbb R^k`$ on a probability space with law $`P`$ satisfy $`Y_0\in L^2(P)`$ and $`E_P\langle u,Y_0\rangle=0`$ for every $`u`$. Let $`\Sigma`$ be a specified real positive-semidefinite matrix and assume, for every $`u,v\in\mathbb R^k`$,


```math
E_P[\langle u,Y_0\rangle\langle v,Y_0\rangle]=u^T\Sigma v.
```


Then the laws of $`n^{-1/2}\sum_{i\lt n}Y_i`$ converge weakly to $`N(0,\Sigma)`$: the integrals of every bounded continuous real test function converge to its Gaussian integral.

**Use.** A direct entry point for vector scores, estimators and joint limits in any finite dimension, without covariance invertibility.

**Relation to Mathlib.** The pinned Mathlib supplies a scalar iid CLT, multivariate Gaussian measures and Lévy characteristic-function convergence. This theorem combines those tools through a local bounded-continuous-test weak-convergence interface.

**Declaration:** [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ScoreCLT.clt_finDim`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L8046)

```lean
import AronowAudit.P001.Wave1.Gap.GLP0011B3

#check AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.ScoreCLT.clt_finDim
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P001.Wave1.GLP0011B3.AsymptoticStatistics.WeakConverges`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L1365): exact weak-convergence definition
- [`AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal`](../AronowAudit/P001/Wave1/Gap/GLP0011B3.lean#L8473): Gaussian projection law

**Scope.** Finite-dimensional iid observations and a finite second moment are required. The covariance matrix may be singular. This is separate from the changing-space, nonidentically distributed Lindeberg array theorem.

### H012

**Sharp bounded-weight means with explicit threshold optimizers**

Threshold weights attain the extreme bounded-weight means, and feasible weights attain every value between them.

Areas: Partial identification and bounds, Survey sampling, Optimization and computation.

**Statement.** Let $`n\gt 0`$, let $`y_0\le\cdots\le y_{n-1}`$ be real outcomes, let $`a_i\gt 0`$ be real masses, and assume $`0\lt \alpha\le\beta\le1`$. Put $`\gamma=\beta/\alpha`$ and $`R(w)=\sum_i a_iw_iy_i/\sum_i a_iw_i`$. For $`0\le k\lt n`$, define $`u^L_{k,i}=\gamma`$ for $`i\lt k`$ and $`1`$ otherwise, and $`u^H_{k,i}=1`$ for $`i\lt k`$ and $`\gamma`$ otherwise; write $`L_k=R(u^L_k)`$ and $`H_k=R(u^H_k)`$.

There exist least cuts $`k_L,k_H\in\{0,\ldots,n-1\}`$ satisfying $`L_{k_L}\le y_{k_L}`$ and $`H_{k_H}\le y_{k_H}`$, respectively. The weights $`w^L=u^L_{k_L}/\beta`$ and $`w^H=u^H_{k_H}/\beta`$ belong to $`[1/\beta,1/\alpha]^n`$ and have ratios $`L_{k_L}`$ and $`H_{k_H}`$. These ratios are, respectively, the least and greatest elements of the attainable set $`\{R(w):w\in[1/\beta,1/\alpha]^n\}`$. They equal its real infimum and supremum, and the entire attainable set is exactly $`[L_{k_L},H_{k_H}]`$.

**Use.** Gives explicit endpoint optimizers and the full interval for sensitivity analysis with bounded inverse-selection weights and arbitrary positive base masses. Unit masses and positive outcome-class masses are both covered.

**Relation to Mathlib.** Mathlib v4.34.1 supplies finite sums, ordered-field inequalities and intermediate-value tools used here. The threshold optimizers and attainable-interval result use local ratio and feasible-box definitions.

**Declaration:** [`AronowAudit.P025.corrected_weighted_bounds`](../AronowAudit/P025/P025_Interval.lean#L791)

```lean
import AronowAudit.P025.P025_Interval

#check AronowAudit.P025.corrected_weighted_bounds
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P025-T3](works/P025.md#p025-t3).

Related declarations:

- [`AronowAudit.P025.lowerCut`](../AronowAudit/P025/P025_Interval.lean#L81): corrected least-cut definition
- [`AronowAudit.P025.upperCut`](../AronowAudit/P025/P025_Interval.lean#L86): upper least-cut definition
- [`AronowAudit.P025.attainable`](../AronowAudit/P025/P025_Interval.lean#L96): set of ratios over the real weight box
- [`AronowAudit.P025.corrected_proposition_one`](../AronowAudit/P025/P025_Interval.lean#L846): Unit-mass specialization

**Scope.** Sorting and strictly positive masses are required; ties and $`\alpha=\beta`$ are allowed. Cuts are zero-based prefix lengths. Sharpness concerns the box of real weights; integer population-size or known-size compatibility constraints are not imposed.

### H013

**Causal IPW and double-robust identification**

Identifies the average treatment effect by inverse weighting and gives the two alternatives for double robustness.

Areas: Causal identification.

**Statement.** On any probability space with law $`\mu`$, let $`K`$ be a natural number, $`X:\Omega\to\mathbb R^K`$ measurable, and $`Y_0,Y_1,D`$ measurable real variables. Assume $`Y_0,Y_1\in L^1(\mu)`$, $`D\in\{0,1\}`$ almost surely, and $`P(D=0),P(D=1)\gt 0`$. Let $`p`$ be a conditional expectation function of $`D`$ given $`X`$ in the source's `IsCEF` sense, and assume that some $`\epsilon\gt 0`$ satisfies $`\epsilon\lt p(X)\lt 1-\epsilon`$ almost surely. Assume $`(Y_0,Y_1)\perp D\mid X`$ in the source's `CI` sense. Here `IsCEF` requires measurability of the function, integrability of the variable and fitted conditional mean, and equality of their integrals over every measurable covariate event; `CI` requires conditional-expectation factorization for every pair of measurable events.

Put $`Y=DY_1+(1-D)Y_0`$. Then


```math
E(Y_1-Y_0)=E\left[\frac{DY}{p(X)}-\frac{(1-D)Y}{1-p(X)}\right].
```


Moreover, for every measurable $`m_0,m_1,q:\mathbb R^K\to\mathbb R`$ with $`m_0(X),m_1(X)\in L^1(\mu)`$,


```math
E(Y_1-Y_0)=E\left[m_1(X)+\frac{D(Y-m_1(X))}{q(X)}-m_0(X)-\frac{(1-D)(Y-m_0(X))}{1-q(X)}\right]
```


provided either (a) $`m_a`$ is an `IsCEF` of $`Y`$ given $`X`$ under the unnormalized restricted measure $`\mu\vert_{\{D=a\}}`$ for each $`a\in\{0,1\}`$, and some $`\eta\gt 0`$ satisfies $`\eta\lt q(X)\lt 1-\eta`$ almost surely, or (b) $`q(X)=p(X)`$ almost surely.

**Use.** Provides population identification identities for causal IPW and augmented IPW, with the precise outcome-regression and propensity alternatives behind double robustness. The probability space is arbitrary; covariates have finitely many real coordinates.

**Relation to Mathlib.** Mathlib supplies conditional expectation and independence infrastructure. The causal IPW and double-robust identification identities use the local IsCEF and CI definitions.

**Declaration:** [`AronowAudit.P001.Wave1.causal_ipw_and_dr_paper_contract`](../AronowAudit/P001/Wave1/CausalIpwDr.lean#L23)

```lean
import AronowAudit.P001.Wave1.CausalIpwDr

#check AronowAudit.P001.Wave1.causal_ipw_and_dr_paper_contract
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P001-T117](works/P001.md#p001-t117).

Related declarations:

- [`AronowAudit.P001.IsCEF`](../AronowAudit/P001/P001_Foundations.lean#L97): integral-identity conditional expectation function
- [`AronowAudit.P001.CI`](../AronowAudit/P001/P001_Foundations.lean#L287): conditional-event independence
- [`AronowAudit.P001.observedOutcome`](../AronowAudit/P001/P001_Foundations.lean#L503): observed-outcome definition

**Scope.** Uniform overlap and integrable potential outcomes are assumed. These are population equalities, without a consistency or efficiency conclusion for estimated nuisance functions. The true-propensity branch does not require correct outcome regressions or a separate overlap assumption on q.

### H014

**MAR reweighting identifies the entire outcome law**

Shows that inverse-response weighting recovers the entire outcome distribution under missingness at random.

Areas: Causal identification, Probability.

**Statement.** Let $`\mu`$ be a probability measure on any measurable space, let $`X`$ be measurable into any measurable type, and let $`Y,R`$ be measurable real variables. Assume $`R(\omega)\in\{0,1\}`$ for every $`\omega`$. Let $`p`$ be an `IsCEF` of $`R`$ given $`X`$: $`p`$ is measurable, $`R`$ and $`p(X)`$ are integrable, and their integrals agree over every measurable covariate event. For a real $`\epsilon\gt 0`$, assume $`p(X(\omega))\gt \epsilon`$ for every $`\omega`$. Assume $`Y\perp R\mid X`$ in the `CI` sense of conditional-expectation factorization for every pair of measurable events.

Define $`\nu`$ by the nonnegative extended-real density $`d\nu/d\mu=\mathrm{ofReal}(R/p(X))`$. Then the pushforward outcome laws are equal: $`Y_\#\nu=Y_\#\mu`$.

**Use.** Identifies probabilities of all outcome events at once, providing a foundation for missing-data distributions, quantiles and bounded outcome functionals. No outcome moment assumption is required, and the covariate space need not be finite dimensional.

**Relation to Mathlib.** Mathlib v4.34.1 supplies pushforwards, withDensity, measure extensionality and conditional expectation. The statistical addition is the MAR event reweighting identity and its extension to equality of outcome laws through the CEF/CI interface.

**Declaration:** [`AronowAudit.P001.Wave1.mar_reweighting_map_eq`](../AronowAudit/P001/Wave1/Gap/GLP0014B4.lean#L84)

```lean
import AronowAudit.P001.Wave1.Gap.GLP0014B4

#check AronowAudit.P001.Wave1.mar_reweighting_map_eq
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P001.Wave1.mar_reweighting_indicator_eq`](../AronowAudit/P001/Wave1/Gap/GLP0014B4.lean#L18): outcome-event integral identity
- [`AronowAudit.P001.IsCEF`](../AronowAudit/P001/P001_Foundations.lean#L97): conditional expectation function
- [`AronowAudit.P001.CI`](../AronowAudit/P001/P001_Foundations.lean#L287): conditional-event independence
- [`AronowAudit.P001.Wave1.mar_reweighting_corrected_hypothesis_proof`](../AronowAudit/P001/Wave1/Gap/GLP0014B4.lean#L122): Integrable outcome mean consequence

**Scope.** Binary response and the strict positive lower bound are pointwise assumptions in this declaration. The result concerns the specified population response function and supplies no fitted-model guarantee.

### H015

**Quadratic-form sampling bound for doubly centered matrices**

Bounds the variance of a principal matrix sum under sampling without replacement when every row and column sums to zero.

Areas: Probability, Experimental design and estimation, Survey sampling.

**Statement.** Let $`n,s`$ be natural numbers with $`n\ge4`$ and $`s\le n`$, and let $`S`$ be uniform over all $`s`$-element subsets of $`\{0,\ldots,n-1\}`$. For any real $`n\times n`$ matrix $`Q`$ satisfying $`\sum_jQ_{ij}=0`$ for every row $`i`$ and $`\sum_iQ_{ij}=0`$ for every column $`j`$, put $`X_Q(S)=\sum_{i\in S}\sum_{j\in S}Q_{ij}`$. With variance defined as the uniform average of squared deviations over those subsets,


```math
\mathrm{Var}(X_Q)\le\frac{s(n-s)}{n(n-1)}\sum_i\sum_jQ_{ij}^2.
```



**Use.** A reusable finite-sample variance bound for sampled matrix statistics and regression adjustment in completely randomized experiments. It allows nonsymmetric matrices and includes the empty and full samples; no positive-semidefiniteness, rank or trace restriction is imposed.

**Relation to Mathlib.** The development uses finite uniform-subset expectations, inclusion moments, an exact symmetric variance calculation and symmetrization to bound principal matrix sums under fixed-size sampling.

**Declaration:** [`AronowAudit.P005.Wave1.qtc_principal_variance`](../AronowAudit/P005/Wave1/Lib/QuadraticSamplingTailC.lean#L404)

```lean
import AronowAudit.P005.Wave1.Lib.QuadraticSamplingTailC

#check AronowAudit.P005.Wave1.qtc_principal_variance
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P005.Wave1.qtc_principal_expectation`](../AronowAudit/P005/Wave1/Lib/QuadraticSamplingTailC.lean#L392): first moment for arbitrary matrices
- [`AronowAudit.Literature.leiDing2021QuadraticSampling_proof`](../AronowAudit/P005/Wave1/Lib/QuadraticSamplingTailC.lean#L433): complete published quadratic sampling proposition
- [`AronowAudit.Literature.principalSum`](../AronowAudit/Literature/CondP002P005P006.lean#L33): sampled matrix principal sum
- [`AronowAudit.P005.Wave1.principal_sum_variance_tailC`](../AronowAudit/P005/Wave1/Lib/QuadraticSamplingTailC.lean#L445): same bound in explicit finite-sum notation

**Scope.** Both zero row sums and zero column sums are required. The companion expectation formula and this bound assemble the full Lei–Ding quadratic sampling proposition without taking that published proposition as a hypothesis.

### H016

**Conservative HT contrast variance with zero joint exposure probabilities**

Bounds the design variance of an exposure contrast by the expectation of a zero-joint-corrected variance estimator.

Areas: Interference and networks, Regression and variance estimation, Experimental design and estimation.

**Statement.** Let a finite assignment support have strictly positive real design masses summing to one. Let $`N,K`$ be natural numbers, let each unit's exposure be an arbitrary function of the assignment into $`K`$ exposure labels, and let $`y_i(t)`$ be fixed real potential outcomes. Choose distinct labels $`d,e`$ with $`0\lt \pi_i(d)\lt 1`$ and $`0\lt \pi_i(e)\lt 1`$ for every unit, where $`\pi_i(t)=P(D_i=t)`$. Then


```math
\mathrm{Var}(\widehat\tau_{HT})\le E[\widehat V],\qquad
\widehat\tau_{HT}=\frac1N\sum_i\left[\frac{I_i(d)y_i(d)}{\pi_i(d)}-\frac{I_i(e)y_i(e)}{\pi_i(e)}\right],
```


where $`\widehat V`$ is the source's `effectVariance` estimator. Explicitly, when $`N\gt 0`$, index exposure cells by $`a=(i,t)`$, $`t\in\{d,e\}`$, set $`x_{i,d}=y_i(d)/N`$, $`x_{i,e}=-y_i(e)/N`$, $`I_a=\mathbf1\{D_i=t\}`$, $`\pi_a=E I_a`$, and $`\pi_{ab}=E(I_aI_b)`$. Then


```math
\widehat V=\sum_{a,b:\pi_{ab}\gt 0}I_aI_b\frac{\pi_{ab}-\pi_a\pi_b}{\pi_{ab}}\frac{x_a}{\pi_a}\frac{x_b}{\pi_b}
+\sum_{a,b:\pi_{ab}=0}\left(\frac{I_ax_a^2}{2\pi_a}+\frac{I_bx_b^2}{2\pi_b}\right).
```


Both sums run over ordered cell pairs. In the source this is the two same-exposure HT variance estimators plus their zero-joint Young corrections, minus twice the corrected cross-exposure covariance, all divided by $`N^2`$. The Lean declaration also allows $`N=0`$; empty sums and totalized real division make both sides zero.

**Use.** Handles finite interference designs with impossible joint exposures, where a usual unbiased pairwise variance estimator is unavailable. Potential outcomes may have either sign, and no positive-joint-probability assumption is required.

**Relation to Mathlib.** Mathlib supplies general covariance, variance and finite-sum tools. The finite-design, exposure-probability and zero-joint-corrected estimator interfaces are defined here.

**Declaration:** [`AronowAudit.P013.effectVariance_conservative`](../AronowAudit/P013/P013_Audit.lean#L643)

```lean
import AronowAudit.P013.P013_Audit

#check AronowAudit.P013.effectVariance_conservative
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P013-T15](works/P013.md#p013-t15).

Related declarations:

- [`AronowAudit.P013.effectVariance`](../AronowAudit/P013/P013_Audit.lean#L374): specified contrast variance estimator
- [`AronowAudit.P013.varianceHT_conservative`](../AronowAudit/P013/P013_Audit.lean#L493): same-exposure conservative variance
- [`AronowAudit.P013.covarianceA_conservative`](../AronowAudit/P013/P013_Audit.lean#L624): corrected cross-exposure covariance bound

**Scope.** Conservativeness is in design expectation. It is not a samplewise variance bound or a coverage guarantee. The exposure mapping and fixed potential outcomes are supplied as the finite Population object.

### H017

**Exact HC2 conservativeness gap and equality condition**

Gives the exact expected HC2 variance gap and characterizes equality by constant treatment effects.

Areas: Regression and variance estimation, Experimental design and estimation, Randomization inference.

**Statement.** Let the units be any finite type of size $`N=n_1+n_0`$, where $`n_1,n_0\ge2`$, with arbitrary fixed real potential outcomes $`Y_i(1),Y_i(0)`$. Randomize uniformly over all $`n_1`$-element treatment subsets. Let $`\widehat\tau`$ be the observed difference in means, let $`V=\mathrm{Var}(\widehat\tau)`$ under this design, and let $`E`$ be the design expectation of the HC2 sandwich slope variance from OLS with intercept and treatment indicator. The source defines HC2 from the inverse Gram matrix, OLS residuals and leverages, using $`e_i^2/(1-h_i)`$ in the sandwich.

Put $`\tau_i=Y_i(1)-Y_i(0)`$, $`\bar\tau=N^{-1}\sum_i\tau_i`$, and $`S_\tau^2=(N-1)^{-1}\sum_i(\tau_i-\bar\tau)^2`$. Then $`E-V=S_\tau^2/N`$, $`V\le E`$, and $`E=V`$ if and only if there exists $`c\in\mathbb R`$ with $`\tau_i=c`$ for every unit.

**Use.** Connects the actual HC2 matrix calculation to the finite-population treatment-effect heterogeneity gap. The companion identity equating HC2 to the Neyman estimate provides a useful check for an unadjusted regression implementation.

**Relation to Mathlib.** Mathlib v4.34.1 supplies matrix and variance algebra. This theorem uses explicit OLS, leverage and complete-randomization definitions to express the HC2–Neyman identity and the expected variance gap.

**Declaration:** [`AronowAudit.P036.corrected_hc2_conservativeness`](../AronowAudit/P036/P036_Unadjusted.lean#L1274)

```lean
import AronowAudit.P036.P036_Unadjusted

#check AronowAudit.P036.corrected_hc2_conservativeness
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P036-T2](works/P036.md#p036-t2).

Related declarations:

- [`AronowAudit.P036.hc2_eq_neyman`](../AronowAudit/P036/P036_Unadjusted.lean#L564): HC2 sandwich equals Neyman estimate
- [`AronowAudit.P036.hc2Variance`](../AronowAudit/P036/P036_Unadjusted.lean#L461): actual sandwich slope-variance definition
- [`AronowAudit.P036.populationVariance_zero_iff_constant`](../AronowAudit/P036/P036_Unadjusted.lean#L1245): equality-condition characterization
- [`AronowAudit.P036.randomization_variance_identity`](../AronowAudit/P036/P036_Unadjusted.lean#L1133): exact design variance

**Scope.** This is an unadjusted binary-treatment regression result under complete randomization, with at least two units in each arm. It concerns expected estimated variance, not expected standard error, and makes no claim for covariate-adjusted specifications.

### H018

**Exact prediction-covariance bias of regression-assisted contrasts**

Expresses regression-assisted contrast bias exactly through covariances of treatment indicators and fitted predictions.

Areas: Experimental design and estimation, Regression and variance estimation, Randomization inference.

**Statement.** Let $`\Omega,I`$ be finite types and let $`R`$ be any linearly ordered field. Let a finite design have nonnegative weights summing to one and binary assignments $`T_i:\Omega\to\{0,1\}`$. Assume $`\pi_{1i}=ET_i\gt 0`$ and $`\pi_{0i}=E(1-T_i)\gt 0`$ for every $`i`$. For arbitrary fixed $`y_1,y_0:I\to R`$, arbitrary assignment-dependent predictions $`f:\Omega\times I\to R`$, and any positive natural normalization $`N`$, define


```math
\widehat\Delta_G=\frac1N\sum_i\left[\frac{T_i(y_{1i}-f_i)}{\pi_{1i}}-\frac{(1-T_i)(y_{0i}-f_i)}{\pi_{0i}}\right],\qquad
\Delta=\frac1N\sum_i(y_{1i}-y_{0i}).
```


Expectation is the weighted finite design sum and $`\mathrm{Cov}(U,V)=E(UV)-EU\,EV`$. Then


```math
E\widehat\Delta_G-\Delta=-\frac1N\sum_i\mathrm{Cov}(T_i,f_i)\left(\frac1{\pi_{1i}}+\frac1{\pi_{0i}}\right).
```



**Use.** Expresses prediction-induced bias as a weighted sum of design covariances. Zero assignment–prediction covariance at every index is sufficient for unbiasedness. It allows arbitrary finite designs and assignment-dependent fitting, with no independence assumption. The normalization can represent original units even when the index set represents cluster totals.

**Relation to Mathlib.** Mathlib v4.34.1 provides covariance_eq_sub and covariance linearity lemmas in Probability/Moments/Covariance.lean. This module uses its own finite weighted expectation and covariance to state the fitted-prediction design-bias identity.

**Declaration:** [`AronowAudit.P026.generalized_bias_two_arm`](../AronowAudit/P026/P026_FiniteDesign.lean#L701)

```lean
import AronowAudit.P026.P026_FiniteDesign

#check AronowAudit.P026.generalized_bias_two_arm
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P026.generalized_bias`](../AronowAudit/P026/P026_FiniteDesign.lean#L655): unsimplified armwise covariance identity
- [`AronowAudit.P026.fixed_prediction_unbiased`](../AronowAudit/P026/P026_FiniteDesign.lean#L746): fixed-prediction unbiasedness corollary
- [`AronowAudit.P026.PaperScope.generalized_bias_two_arm_T13`](../AronowAudit/P026/P026_PaperScope.lean#L373): paper-scope specialization
- [`AronowAudit.P026.generalized_total_bias`](../AronowAudit/P026/P026_FiniteDesign.lean#L628): Arm-total covariance bias identity

**Scope.** The same prediction is used in both arms, so the augmentation terms cancel in the displayed contrast. N need not equal the number of indices. Independence from individual fitting inputs alone does not imply independence from their fitted joint function.

### H019

**Sharp ATE interval with unchanged observable law**

Constructs every bounded-outcome average treatment effect compatible with the same observed outcome and treatment law.

Areas: Partial identification and bounds, Causal identification.

**Statement.** On any probability space let $`Y_0,Y_1,D`$ be measurable real variables. For real $`a,b`$, assume $`Y_0,Y_1\in[a,b]`$ almost surely, $`D\in\{0,1\}`$ almost surely, and $`\pi_j=P(D=j)\gt 0`$ for both $`j=0,1`$. Put $`Y=DY_1+(1-D)Y_0`$ and $`m_j=\pi_j^{-1}\int_{\{D=j\}}Y\,d\mu`$. Define


```math
L=\pi_1m_1+a\pi_0-(\pi_0m_0+b\pi_1),\qquad
U=\pi_1m_1+b\pi_0-(\pi_0m_0+a\pi_1).
```


Then $`E(Y_1-Y_0)\in[L,U]`$ and $`U-L=b-a`$. For every real $`c\in[L,U]`$, there exist measurable $`Z_0,Z_1`$ on the same probability space, both in $`[a,b]`$ almost surely, such that the law of $`(DZ_1+(1-D)Z_0,D)`$ equals the law of $`(Y,D)`$ and $`E(Z_1-Z_0)=c`$.

**Use.** Gives both valid bounds and attainment of every value through observationally equivalent counterfactual completions, without ignorability. The interval width is exactly the outcome-support width, regardless of treatment imbalance.

**Relation to Mathlib.** Mathlib supplies measure pushforwards and integrals. The sharp ATE completion uses local observed-outcome and event-mean definitions.

**Declaration:** [`AronowAudit.P001.Wave1.ate_sharp_paper_bounds_same_observable_law`](../AronowAudit/P001/Wave1/AteSharpBounds.lean#L17)

```lean
import AronowAudit.P001.Wave1.AteSharpBounds

#check AronowAudit.P001.Wave1.ate_sharp_paper_bounds_same_observable_law
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P001-T114](works/P001.md#p001-t114).

Related declarations:

- [`AronowAudit.P001.conditionalMeanAt`](../AronowAudit/P001/P001_Foundations.lean#L687): arm mean as a normalized event integral
- [`AronowAudit.P001.observedOutcome`](../AronowAudit/P001/P001_Foundations.lean#L503): observed-outcome definition

**Scope.** Bounded potential outcomes and positive probabilities of both observed arms are required. The result does not impose covariate-specific or additional cross-world restrictions. The alternative outcomes use the original space and treatment variable.

### H020

**Exchangeable Monte Carlo p-values, with ties and floor bounds**

Establishes finite-sample validity of corrected exchangeable Monte Carlo tails and their doubled minimum.

Areas: Randomization inference, Resampling, Probability.

**Statement.** Let $`B\gt 0`$ be a natural number. Let $`(T_0,\ldots,T_B)`$ have any probability law on $`\mathbb R^{B+1}`$ invariant under every coordinate permutation. Define


```math
L=\frac{1+\#\{b=1,\ldots,B:T_b\le T_0\}}{B+1},\qquad
U=\frac{1+\#\{b=1,\ldots,B:T_0\le T_b\}}{B+1},\qquad
p_2=\min(1,2\min(L,U)).
```


For every real $`\alpha\in[0,1]`$,


```math
P(L\le\alpha)\le\frac{\lfloor\alpha(B+1)\rfloor}{B+1},\qquad
P(U\le\alpha)\le\frac{\lfloor\alpha(B+1)\rfloor}{B+1},\qquad
\frac{\lfloor\alpha(B+1)\rfloor}{B+1}\le\alpha,\qquad
P(p_2\le\alpha)\le\alpha.
```



**Use.** Provides finite-sample validity for simulation and permutation tests whenever the entire observed-and-reference statistic vector is exchangeable. The reference statistics may be dependent and may tie.

**Relation to Mathlib.** Mathlib v4.34.1 provides probability measures, finite counting and floor arithmetic. This theorem combines those tools with coordinate-permutation invariance to establish corrected p-value validity and the one-sided floor bounds.

**Declaration:** [`AronowAudit.P016.t14_corrected_valid`](../AronowAudit/P016/P016_Interference.lean#L2566)

```lean
import AronowAudit.P016.P016_Interference

#check AronowAudit.P016.t14_corrected_valid
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P016-T14](works/P016.md#p016-t14).

Related declarations:

- [`AronowAudit.P016.Exchangeable`](../AronowAudit/P016/P016_Interference.lean#L2104): permutation-invariance hypothesis
- [`AronowAudit.P016.correctedLower`](../AronowAudit/P016/P016_Interference.lean#L2504): inclusive lower-tail p-value
- [`AronowAudit.P016.correctedUpper`](../AronowAudit/P016/P016_Interference.lean#L2508): inclusive upper-tail p-value

**Scope.** The observed coordinate is included through the explicit plus-one correction, and both rank comparisons are weak. Exchangeability must hold for the actual simulation protocol; correct marginal laws alone do not establish it. Ties can make the bounds conservative.

### H021

**Dense quadratic variance bound under a genuine dependency graph**

Bounds the variance of dense quadratic forms of centered bounded variables with a dependency graph.

Areas: Probability, Interference and networks, Regression and variance estimation.

**Statement.** On any probability space with law $`\mu`$, let $`n`$ be a natural number and let $`Z_i`$, $`i\in\{0,\ldots,n-1\}`$, be measurable real variables with $`EZ_i=0`$. Let $`B\ge0`$ satisfy $`|Z_i|\le B`$ almost surely for every $`i`$. Suppose a reflexive symmetric relation $`G`$ is a dependency graph in the source's `DepGraph` sense: for any two finite index sets with no connecting edge, their variable tuples are independent. Let a real $`d\ge0`$ satisfy $`\sum_j\mathbf1\{G(i,j)\}\le d`$ for every row $`i`$, counting the self-edge.

For every deterministic symmetric real matrix $`A`$,


```math
\mathrm{Var}\left(\sum_i\sum_j A_{ij}Z_iZ_j\right)\le(144d^3+2d^2)B^4\lVert A\rVert_{op}^2n,
```


where $`\lVert A\rVert_{op}`$ is the Euclidean operator norm. The dependency-graph structure bundles measurability and the stated tuple-independence property.

**Use.** Gives an explicit finite-sample variance bound that can support consistency arguments for dense quadratic variance estimators in network or spatial models. The matrix need not be sparse, and the constant is explicit without an optimality claim.

**Relation to Mathlib.** Mathlib v4.34.1 supplies covariance and variance expansions and Euclidean operator norms. The DepGraph interface used here is vendored Causalean code in this repository. The local theorem gives an explicit variance bound for dense quadratic forms under that dependency-graph interface.

**Declaration:** [`AronowAudit.P011.DenseCenteredVariance.centered_variance_bound`](../AronowAudit/P011/P011_DenseCenteredVariance.lean#L17)

```lean
import AronowAudit.P011.P011_DenseCenteredVariance

#check AronowAudit.P011.DenseCenteredVariance.centered_variance_bound
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`Causalean.Mathlib.Probability.SteinMethod.DepGraph`](../AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/DepGraphCLT.lean#L55): dependency-graph structure
- [`AronowAudit.P011.operatorNorm`](../AronowAudit/P011/P011_Audit.lean#L250): Euclidean operator norm
- [`AronowAudit.P011.DenseCumulant.variance_expansion`](../AronowAudit/P011/P011_DenseCumulant.lean#L251): quadratic variance expansion

**Scope.** Centered bounded coordinates, a deterministic symmetric matrix and full tuple independence off the graph are required. Pairwise zero covariance is insufficient. The degree bound includes self; the declaration itself is a variance inequality, not an asymptotic consistency theorem.

### H022

**Exactly which means nonnegative reweighting can represent**

Characterizes attainable nonnegative weighted means by an atom at the target or positive probability on both sides.

Areas: Causal identification, Partial identification and bounds, Probability.

**Statement.** Let $`G`$ be any probability measure on a measurable space, let $`\tau`$ be a measurable integrable real function, and let $`t\in\mathbb R`$. There exists a measurable weight $`w`$ that is nonnegative at every point, satisfies $`w,w\tau\in L^1(G)`$ and $`E_Gw\gt 0`$, and has $`E_G(w\tau)/E_Gw=t`$, if and only if


```math
P_G(\tau=t)\gt 0\quad\text{or}\quad\bigl(P_G(\tau\lt t)\gt 0\ \text{and}\ P_G(\tau\gt t)\gt 0\bigr).
```



**Use.** Adds an exact converse to weighted-average support restrictions. It describes representable weighted causal effects and transport or selection targets, including the positive-atom requirement for attainable support extremes.

**Relation to Mathlib.** Mathlib supplies convex-integral and Jensen tools in Analysis/Convex/Integral and integral-positivity criteria in MeasureTheory/Integral/Bochner/Basic. The exact representability characterization and its weight constructions are defined here.

**Declaration:** [`AronowAudit.P017.weighted_mean_characterization`](../AronowAudit/P017/P017_Audit.lean#L515)

```lean
import AronowAudit.P017.P017_Audit

#check AronowAudit.P017.weighted_mean_characterization
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P017-T2](works/P017.md#p017-t2).

Related declarations:

- [`AronowAudit.P017.AdmissibleWeight`](../AronowAudit/P017/P017_Audit.lean#L65): weight measurability and integrability contract
- [`AronowAudit.P017.atom_weight_representation`](../AronowAudit/P017/P017_Audit.lean#L361): construction when the target has positive mass
- [`AronowAudit.P017.straddling_weight_representation`](../AronowAudit/P017/P017_Audit.lean#L433): construction from positive mass on both sides
- [`AronowAudit.P017.Representable`](../AronowAudit/P017/P017_Audit.lean#L76): exact representation predicate

**Scope.** The characterization uses an ordinary finite ratio. Weights may depend on the entire underlying state. They need not be bounded or positive everywhere, and the existence statement does not supply estimability from observed covariates.

### H023

**Fixed-size systematic sampling with prescribed inclusion probabilities**

Systematic sampling realizes any strictly positive admissible inclusion vector with an exactly fixed sample size.

Areas: Survey sampling, Experimental design and estimation.

**Statement.** Let $`N\ge2`$ and $`m`$ be natural numbers with $`0\lt m\lt N`$. Let real numbers $`\pi_k`$, $`0\le k\lt N`$, satisfy $`0\lt \pi_k\le1`$ for every $`k`$ and $`\sum_k\pi_k=m`$. Put $`L_k=\sum_{a\lt k}\pi_a`$ and select $`k`$ at start $`u`$ precisely when $`L_k\le u+j\lt L_k+\pi_k`$ for some integer $`0\le j\lt m`$. The spacing in `systematicSelected` is $`\sum_k\pi_k/m=1`$. For every real $`u`$ with $`0\le u\lt 1`$, the set of selected units has cardinality exactly $`m`$. Moreover, for every $`k`$,



```math
\int_{[0,1)}\mathbf1\{k\text{ is selected at }u\}\,du=\pi_k.
```



**Use.** Constructs an unequal-probability design for every strictly positive first-order inclusion vector satisfying the fixed-size feasibility constraints. The proof combines the cumulative-interval selection rule with exact cardinality and marginal-integral lemmas; it requires no outcome or superpopulation model.

**Relation to Mathlib.** Mathlib v4.34.1 supplies Lebesgue interval measures, finite sums and indicator integrals. The systematic-sampling construction combines them with cumulative intervals and a fixed-spacing selection rule.

**Declaration:** [`AronowAudit.P027.Wave1.systematic_probability_construction_proof`](../AronowAudit/P027/Wave1/Gap/GLP027P016P031B1.lean#L562)

```lean
import AronowAudit.P027.Wave1.Gap.GLP027P016P031B1

#check AronowAudit.P027.Wave1.systematic_probability_construction_proof
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P027-T13](works/P027.md#p027-t13).

Related declarations:

- [`AronowAudit.P027.systematicSelected`](../AronowAudit/P027/P027_Audit.lean#L730): Selection rule with general spacing
- [`AronowAudit.P027.Wave1.systematic_cardinality`](../AronowAudit/P027/Wave1/Gap/GLP027P016P031B1.lean#L405): Exact sample cardinality
- [`AronowAudit.P027.Wave1.systematic_marginal_integral`](../AronowAudit/P027/Wave1/Gap/GLP027P016P031B1.lean#L539): First-order inclusion probabilities
- [`AronowAudit.P027.cumulativeLeft`](../AronowAudit/P027/P027_Audit.lean#L725): cumulative interval endpoints

**Scope.** The unit ordering and half-open intervals are part of the construction. Zero target probabilities are outside this interface. It fixes sample size and first-order marginals, without prescribing second-order inclusion probabilities.

### H024

**Unknown-propensity impossibility for arbitrary randomized procedures**

With unrestricted measurable propensity and outcome-regression classes, no procedure, even a randomized one, estimates the average treatment effect uniformly or gives uniformly honest intervals that shrink.

Areas: Causal identification, Asymptotic statistics.

**Statement.** Let $`\mathcal L`$ consist of complete-unit probability laws $`L`$ for $`(W,A,Y(0),Y(1))`$ with $`W`$ uniform on $`(0,1]`$, binary treatment and almost-surely binary potential outcomes, joint conditional ignorability given $`W`$, and a measurable propensity $`e(W)\in[1/4,3/4]`$ almost surely. Ignorability is encoded by conditional-expectation factorization for every measurable integrable test of the potential-outcome pair. Write $`\tau_L=E_L[Y(1)-Y(0)]`$. For any measurable seed space $`R`$ and probability law $`Q`$ on it, let $`\mathbb P_{L,Q}=L^{\otimes\mathbb N}\otimes Q`$. The seed is independent of the iid complete-unit sample; procedures see only the first $`n`$ observed records $`(W,A,Y)`$ and the seed, and use the same functions under every law.

For every sequence of measurable real estimators $`E_n`$ on those inputs and every $`n\ge1`$,



```math
\sup_{L\in\mathcal L}\mathbb P_{L,Q}(|E_n-\tau_L|\ge1/12)\ge1/2.
```



There also exists $`\eta\gt 0`$ such that $`\limsup_{n\to\infty}\sup_{L\in\mathcal L}\mathbb P_{L,Q}(|E_n-\tau_L|\gt \eta)\gt 0`$.

For every pair of measurable extended-real endpoint sequences $`\ell_n,h_n`$ on those inputs and every $`0\lt \alpha\lt 1/2`$, if



```math
\liminf_{n\to\infty}\inf_{L\in\mathcal L}\mathbb P_{L,Q}(\ell_n\le\tau_L\le h_n)\ge1-\alpha,
```



then $`\liminf_{n\to\infty}\mathbb P_{S,Q}(\ell_n+1/6\lt h_n)\ge1-2\alpha\gt 0`$. Here $`S`$ is the single fixed baseline law with independent uniform $`W`$, fair binary $`A`$ and fair binary $`Y(1)`$, and $`Y(0)=0`$. The width event uses extended-real addition and ordering.

**Use.** Distinguishes causal identification and overlap from uniform estimability and honest shrinking inference. It covers all measurable procedures using observed data and an independent seed of any probability law, including deterministic procedures. The proof uses a two-family construction, agreement of observed laws on samples without cell collisions, and testing inequalities.

**Relation to Mathlib.** Mathlib v4.34.1 provides Bernoulli and product laws, conditional expectations and limit machinery. This declaration gives uniform-estimation and honest-interval impossibility results for observed-data procedures with an arbitrary independent seed.

**Declaration:** [`AronowAudit.P047.Wave1.unknown_propensity_impossibility_randomized`](../AronowAudit/P047/Wave1/Impossibility.lean#L38)

```lean
import AronowAudit.P047.Wave1.Impossibility

#check AronowAudit.P047.Wave1.unknown_propensity_impossibility_randomized
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P047-T3](works/P047.md#p047-t3).

Related declarations:

- [`AronowAudit.P047.UnknownModel`](../AronowAudit/P047/P047_Identification.lean#L785): Complete-unit model class
- [`AronowAudit.P047.Wave1.Impossibility.randCoverage`](../AronowAudit/P047/Wave1/ImpossibilityBlueprint.lean#L58): Worst-case coverage with a seed
- [`AronowAudit.P047.Wave1.Impossibility.widthProb`](../AronowAudit/P047/Wave1/ImpossibilityBlueprint.lean#L67): Width event under the fixed baseline
- [`AronowAudit.P047.Wave1.Impossibility.randRisk`](../AronowAudit/P047/Wave1/ImpossibilityBlueprint.lean#L43): worst-case randomized error probability

**Scope.** This is a binary-outcome subclass with unrestricted measurable nuisance functions. The conclusions concern worst-case estimation and interval width at one fixed baseline, without asserting pointwise estimation failure at every law. Endpoints may be infinite and need not be ordered.

### H025

**Exact dyadic sandwich decomposition with repeated dyads**

A finite-sum identity decomposes the dyadic sandwich exactly when dyads may repeat.

Areas: Regression and variance estimation, Interference and networks, Foundations.

**Statement.** Let the record, member and parameter types $`R,M,P`$ be finite, with decidable equality. Every record $`r`$ carries a dyad $`d_r`$, an unordered set of exactly two distinct members, and arbitrary real scores $`z_r\in\mathbb R^P`$. For a real record-pair pattern $`A`$, put $`\mathcal S(A)=\sum_{r,s\in R}A_{rs}z_rz_s^T`$, with ordered pair sums. Define $`D_{rs}=\mathbf1\{d_r\cap d_s\ne\varnothing\}`$, $`Q_{rs}=\mathbf1\{d_r=d_s\}`$, $`I_{rs}=\mathbf1\{r=s\}`$, and



```math
C_{i,rs}=\mathbf1\{i\in d_r\cap d_s\}+\mathbf1\{r=s,\ i\notin d_r\}\qquad(i\in M).
```



Then the matrix identity is



```math
\sum_{i\in M}\mathcal S(C_i)-\mathcal S(Q)-(|M|-2)\mathcal S(I)=\mathcal S(D).
```



Here $`|M|-2`$ is subtraction in the real numbers.

**Use.** Gives an implementation-ready exact identity for dyadic-cluster covariance calculations with repeated dyads and arbitrary finite labels. It is purely algebraic and permits arbitrary common scores. The proof reduces the matrix equality to a coefficient count for each ordered record pair.

**Relation to Mathlib.** Mathlib supplies finite-set intersections, finite sums and matrix algebra. The dyadic sandwich decomposition follows from a local coefficient identity for each ordered record pair.

**Declaration:** [`AronowAudit.P032.corrected_decomposition`](../AronowAudit/P032/P032_Dyadic.lean#L139)

```lean
import AronowAudit.P032.P032_Dyadic

#check AronowAudit.P032.corrected_decomposition
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P032-T4](works/P032.md#p032-t4).

Related declarations:

- [`AronowAudit.P032.Dyad`](../AronowAudit/P032/P032_Dyadic.lean#L31): Unordered two-distinct-member dyads
- [`AronowAudit.P032.scoreSandwich`](../AronowAudit/P032/P032_Dyadic.lean#L63): Ordered-pair score sandwich
- [`AronowAudit.P032.decomposition_coefficient`](../AronowAudit/P032/P032_Dyadic.lean#L104): Record-pair coefficient identity
- [`AronowAudit.P032.id_substitution_discrepancy`](../AronowAudit/P032/P032_Dyadic.lean#L167): Discrepancy from substituting an identifier-clustered component

**Scope.** Each member-specific clustering puts incident records together and treats each outsider record as a singleton. Bread factors and any common scaling must be absorbed consistently into the scores. The identity includes no small-sample multipliers, positive-semidefinite clipping or stochastic conservativeness conclusion.


## Reusable libraries

- [H001: Combinatorial central limit theorem for permutation arrays](#h001)
- [H002: Lindeberg CLT on changing probability spaces](#h002)
- [H003: Le Cam’s first lemma, four equivalent forms](#h003)
- [H004: One-sided nondominated QMD gives score regularity and a local likelihood expansion](#h004)
- [H005: Scalar outer Hadamard delta method](#h005)
- [H006: Attained Fréchet covariance bounds for square-integrable marginals](#h006)
- [H007: Order-two U-statistic CLT under only second moments](#h007)
- [H008: Nearest positive-semidefinite matrix in Frobenius norm](#h008)
- [H009: Exponential tilting of possibly singular Gaussian laws](#h009)
- [H010: Hellinger error tensorization for product experiments](#h010)
- [H011: Multivariate iid CLT allowing singular covariance](#h011)
- [H012: Sharp bounded-weight means with explicit threshold optimizers](#h012)
- [H013: Causal IPW and double-robust identification](#h013)
- [H014: MAR reweighting identifies the entire outcome law](#h014)
- [H015: Quadratic-form sampling bound for doubly centered matrices](#h015)
- [H016: Conservative HT contrast variance with zero joint exposure probabilities](#h016)
- [H017: Exact HC2 conservativeness gap and equality condition](#h017)
- [H018: Exact prediction-covariance bias of regression-assisted contrasts](#h018)
- [H019: Sharp ATE interval with unchanged observable law](#h019)
- [H021: Dense quadratic variance bound under a genuine dependency graph](#h021)
- [H022: Exactly which means nonnegative reweighting can represent](#h022)
- [H023: Fixed-size systematic sampling with prescribed inclusion probabilities](#h023)
- [H025: Exact dyadic sandwich decomposition with repeated dyads](#h025)
### H026

**Finite-sample bounded-Lipschitz bound for permutation arrays**

A finite-sample bound controls Gaussian approximation for bounded Lipschitz functions of permutation sums.

Areas: Probability, Randomization inference.

**Statement.** Let $`N\ge3`$ be natural and let $`c`$ be a real $`N\times N`$ matrix with every row and column sum zero and $`\sum_{i,j}c(i,j)^2=N-1`$. Let real $`\beta`$ satisfy $`|c(i,j)|\le\beta`$ for every $`i,j`$. Let $`h:\mathbb R\to\mathbb R`$ and real constants $`L,C`$ satisfy $`L\ge0`$, $`|h(x)-h(y)|\le L|x-y|`$ for every $`x,y`$, and $`|h(x)|\le C`$ for every $`x`$. For a uniform random permutation $`\pi`$ and $`S=\sum_i c(i,\pi(i))`$,



```math
\left|E_\pi h(S)-\int h\,dN(0,1)\right|\le32L\sqrt{\beta^2+1/N}+10L\beta.
```



The expectation on the left is the arithmetic average over all permutations.

**Use.** Gives an explicit finite-sample approximation guarantee for globally bounded Lipschitz readouts of a normalized permutation statistic. It also supplies the quantitative step for the max-entry permutation CLT. The proof combines local exchangeable-transposition moment bounds with bundled StatLean Stein-equation estimates.

**Relation to Mathlib.** Mathlib v4.34.1 supplies Gaussian laws, integration and finite probability infrastructure. This development combines permutation-array moment bounds with the bundled StatLean exchangeable-pair and Stein-equation machinery to obtain the explicit bounded-Lipschitz error estimate.

**Declaration:** [`AronowAudit.MapTailB.PermutationArray.array_lipschitz_bound`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L1042)

```lean
import AronowAudit.Shared.MapTailB.PermutationArray

#check AronowAudit.MapTailB.PermutationArray.array_lipschitz_bound
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.MapTailB.PermutationArray.statistic`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L60): Permutation sum
- [`AronowAudit.MapTailB.PermutationArray.array_second_moments`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L478): Exact variance normalization
- [`TailB_permutation_array_clt`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L1156): Weak-convergence consequence
- [`AronowAudit.MapTailB.PermutationArray.energy`](../AronowAudit/Shared/MapTailB/PermutationArray.lean#L73): array normalization

**Scope.** This controls bounded Lipschitz tests rather than distribution-function distance. The assumptions include exact double centering, energy normalization and a global bound on the test function.

### H027

**Density QMD score shift and contiguity**

Quadratic mean differentiability gives local product contiguity and a shifted Gaussian limit for centered readouts.

Areas: Probability, Asymptotic statistics.

**Statement.** Let $`E`$ be an arbitrary measurable space and $`\rho`$ an S-finite measure. For every real $`t`$, let $`p_t:E\to\mathbb R`$ be measurable, pointwise nonnegative, and normalized by $`\int p_t\,d\rho=1`$ (the signature uses the nonnegative extended integral). Write $`P_t=p_t\rho`$ and $`P=P_0`$. Let $`s,u:E\to\mathbb R`$ be measurable, in $`L^2(P)`$, and both centered under $`P`$. Assume that for every $`\varepsilon\gt 0`$ there is $`\delta\gt 0`$ such that, for every real $`t`$ with $`|t|\lt \delta`$,


```math
\int\left(\sqrt{p_t}-\sqrt{p_0}-\frac{t}{2}s\sqrt{p_0}\right)^2d\rho\le\varepsilon t^2.
```


Set $`Q_n=P_{1/\sqrt n}`$. Then $`Q_n^{\otimes n}`$ is contiguous with respect to $`P^{\otimes n}`$: for every sequence of measurable events $`A_n`$, $`P^{\otimes n}(A_n)\to0`$ implies $`Q_n^{\otimes n}(A_n)\to0`$. Under $`Q_n^{\otimes n}`$,


```math
n^{-1/2}\sum_{i\lt n}u(X_i)\ \Rightarrow\ N\!\left(E_P[us],E_P[u^2]\right).
```


Here convergence means that, for every bounded continuous $`f:\mathbb R\to\mathbb R`$, the expectation of $`f(n^{-1/2}\sum_{i\lt n}u(X_i))`$ under $`Q_n^{\otimes n}`$ converges to $`\int f\,dN(E_P[us],E_P[u^2])`$.

**Use.** Provides a density-based entry point for local asymptotic experiments and influence-function limits. The readout can be any centered square-integrable real function; changing support and zero limiting variance are allowed. The adapter uses the bundled StatLean QMD and local-experiment infrastructure.

**Relation to Mathlib.** Mathlib v4.34.1 provides densities, product measures, Gaussian laws and weak-convergence ingredients. The density adapter connects these ingredients to the bundled StatLean QMD and local-experiment infrastructure.

**Declaration:** [`TailB_density_qmd_score_shift`](../AronowAudit/Shared/MapTailB/DensityQMD.lean#L102)

```lean
import AronowAudit.Shared.MapTailB.DensityQMD

#check TailB_density_qmd_score_shift
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`TailB_density_isRightQMD`](../AronowAudit/Shared/MapTailB/DensityQMD.lean#L69): density-to-pairwise QMD bridge
- [`TailB_density_residual_memLp`](../AronowAudit/Shared/MapTailB/DensityQMD.lean#L31): square-integrability of the QMD residual
- [`TailB_density_pairwise_residual_norm`](../AronowAudit/Shared/MapTailB/DensityQMD.lean#L54): change-of-dominator residual identity

**Scope.** Scalar path and readout, at the specific local scale one over the square root of sample size. The QMD hypothesis is two-sided near zero and assumes both score centering and square integrability. The conclusion states contiguity of the alternative products with respect to the baseline products. The adapter depends on the bundled StatLean QMD and local-experiment infrastructure.

### H028

**Poisson limits for moving rare-category counts**

Counts in finitely many disjoint moving rare categories converge jointly to independent Poisson laws.

Areas: Probability, Asymptotic statistics.

**Statement.** Fix a natural number $`k`$. Let $`m_n\in\mathbb N`$ tend to infinity, let $`P_n`$ be probability measures on an arbitrary measurable space $`E`$, and let $`A_{n1},\ldots,A_{nk}`$ be measurable and pairwise disjoint within each row. For nonnegative rates $`\lambda_i`$, assume


```math
m_nP_n(A_{ni})\longrightarrow\lambda_i\qquad(i=1,\ldots,k).
```


Under $`P_n^{\otimes m_n}`$, form the count vector $`C_{ni}=\sum_{j\lt m_n}\mathbf1\{X_j\in A_{ni}\}`$. Then $`C_n`$ converges weakly to $`\bigotimes_{i=1}^k\mathrm{Poisson}(\lambda_i)`$ as a law on $`\mathbb N^k`$. The formal conclusion is convergence of expectations of every bounded continuous real function on this finite product of discrete count spaces; the product sample space may change with $`n`$.

**Use.** A joint law-of-small-numbers interface for shrinking windows and categorical rare events, including triangular arrays with changing distributions and sample sizes. The interval-category corollary supplies local-density rates for windows shrinking around a fixed point.

**Relation to Mathlib.** Mathlib supplies scalar binomial-to-Poisson probability limits. This theorem gives joint weak convergence for finitely many disjoint measurable categories, moving laws and arbitrary diverging sample sizes.

**Declaration:** [`AronowAudit.P001.TailA.rare_partition_counts`](../AronowAudit/P001/Wave1/Lib/TailA/RareCounts.lean#L446)

```lean
import AronowAudit.P001.Wave1.Lib.TailA.RareCounts

#check AronowAudit.P001.TailA.rare_partition_counts
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P001.TailA.finite_window_interval_category_counts`](../AronowAudit/P001/Wave1/Lib/TailA/RareCounts.lean#L507): shrinking-interval corollary
- [`AronowAudit.P001.TailA.rare_counts_singleton`](../AronowAudit/P001/Wave1/Lib/TailA/RareCounts.lean#L74): exact finite multinomial count probability
- [`AronowAudit.P001.TailA.rareCounts`](../AronowAudit/P001/Wave1/Lib/TailA/RareCounts.lean#L22): finite categorical count vector

**Scope.** The number of categories is fixed and observations are independent with the same law within each row. Disjointness is required in every row. Rates may be zero; no separate convergence of count moments is asserted.

### H029

**Exact ordinary-bootstrap variance of the sample mean**

The ideal ordinary-bootstrap variance of a fixed sample mean equals its empirical variance divided by sample size.

Areas: Resampling, Asymptotic statistics.

**Statement.** For every natural number $`n\gt 0`$ and every fixed real sample $`x_1,\ldots,x_n`$, let $`\bar x=n^{-1}\sum_i x_i`$. For each resampling map $`a:\{1,\ldots,n\}\to\{1,\ldots,n\}`$, let $`\bar x_a=n^{-1}\sum_i x_{a(i)}`$. The definition of the ideal ordinary-bootstrap variance averages $`(\bar x_a-\bar x_*)^2`$ over all $`n^n`$ maps with equal weights, where $`\bar x_*`$ is their average. Then


```math
n\mathrm{Var}_*(\bar x_a)=\frac1n\sum_i x_i^2-\bar x^2.
```


There is no population law, independence assumption on the supplied sample, or asymptotic hypothesis in this declaration.

**Use.** An exact finite-sample identity for checking bootstrap mean implementations and reducing ideal-bootstrap variance consistency to consistency of the empirical second moment. It is valid for every nonempty fixed sample, including a singleton.

**Relation to Mathlib.** The proof uses Mathlib v4.34.1 variance_sum_pi, variance_const_mul and variance_eq_sub, together with finite uniform-measure integral identities. The theorem expresses ordinary-bootstrap sample-mean variance through this variance algebra.

**Declaration:** [`AronowAudit.P001.bootstrap_sample_mean_exact_variance`](../AronowAudit/P001/P001_Foundations.lean#L5811)

```lean
import AronowAudit.P001.P001_Foundations

#check AronowAudit.P001.bootstrap_sample_mean_exact_variance
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P001-T62](works/P001.md#p001-t62).

Related declarations:

- [`AronowAudit.P001.bootVar`](../AronowAudit/P001/P001_Foundations.lean#L226): ideal finite-resample variance definition
- [`AronowAudit.P001.bootstrap_sample_mean_consistency`](../AronowAudit/P001/P001_Foundations.lean#L5857): bootstrap variance and standard-error consistency under iid finite-second-moment and positive-variance assumptions
- [`AronowAudit.P001.uniform_resampling_integral`](../AronowAudit/P001/P001_Foundations.lean#L5767): finite-resample sum as a product-law integral

**Scope.** The empirical variance on the right uses divisor n. The bootstrap variance is the exact average over all resamples; the theorem makes no claim about a variance estimated from finitely many simulated bootstrap replicates. Asymptotic consistency requires additional hypotheses in the companion theorem.

### H030

**Squared quantile error from tails and CDF distance**

Squared quantile distance is bounded by marginal square tails and an integrated CDF difference on a compact interval.

Areas: Probability, Asymptotic statistics.

**Statement.** Let $`\mu,\nu`$ be Borel probability measures on $`\mathbb R`$ whose lower generalized-inverse quantiles $`Q_\mu,Q_\nu`$ belong to $`L^2((0,1),du)`$. For every real $`C\ge0`$,


```math
\int_0^1[Q_\mu(u)-Q_\nu(u)]^2\,du
\le4\int x^2\mathbf1\{x^2\ge C^2\}\,d\mu(x)
+4\int x^2\mathbf1\{x^2\ge C^2\}\,d\nu(x)
+2C\int_{-C}^{C}|F_\mu(x)-F_\nu(x)|\,dx.
```


The unit-level measure in the signature is Lebesgue measure restricted to $`(0,1)`$; $`F_\mu,F_\nu`$ are the Mathlib CDFs.

**Use.** Separates quantile approximation into tail control and CDF approximation on a bounded interval. It applies to empirical, atomic, mixed and continuous laws, and is useful when a uniform CDF bound is unavailable.

**Relation to Mathlib.** Mathlib v4.34.1 supplies CDFs, integrals and L2/Vitali tools. This declaration gives a quantile/CDF truncation inequality. The quantile definition and indicator-to-CDF transport identity come from the bundled Causalean library.

**Declaration:** [`TailB_quantile_square_error_le`](../AronowAudit/Shared/MapTailB/QuantileL2.lean#L287)

```lean
import AronowAudit.Shared.MapTailB.QuantileL2

#check TailB_quantile_square_error_le
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`TailB_quantileSquareError`](../AronowAudit/Shared/MapTailB/QuantileL2.lean#L334): squared error between finite empirical quantiles
- [`TailB_sample_quantile_square_error_bound`](../AronowAudit/Shared/MapTailB/QuantileL2.lean#L354): expected finite-population sampling bound
- [`TailB_sample_quantile_L2_mean`](../AronowAudit/Shared/MapTailB/QuantileL2.lean#L436): mean convergence under uniform square tails
- [`TailB_integral_quantile`](../AronowAudit/Shared/MapTailB/QuantileL2.lean#L170): integration through the quantile map

**Scope.** Both quantiles must be square integrable. The tail cutoffs include equality. The conclusion is a deterministic inequality for two real laws and does not itself assert a sampling or convergence result.

### H031

**Empirical ceiling-rank quantile equals the generalized inverse**

For a nonempty finite sample, the ceiling-rank empirical quantile equals the generalized inverse at every interior probability level.

Areas: Probability, Foundations.

**Statement.** For every natural number $`N\gt 0`$, every real sample $`y:\{1,\ldots,N\}\to\mathbb R`$, and every $`u`$ with $`0\lt u\lt 1`$, let $`\widehat\mu_y=N^{-1}\sum_i\delta_{y_i}`$. Then


```math
y_{(\lceil Nu\rceil)}=Q_{\widehat\mu_y}(u),
```


where the left side is the audit’s empirical quantile, using increasing order statistics with multiplicities, and $`Q_\mu(u)=\inf\{x:u\le F_\mu(x)\}`$ is the Causalean lower generalized inverse of the Mathlib CDF. The equality is pointwise for each such $`u`$.

**Use.** Makes finite order-statistic formulas interoperable with general quantile transport and coupling theorems. Ties and atoms are allowed, and the almost-everywhere companion supports integrals of arbitrary functions of the quantile.

**Relation to Mathlib.** Mathlib supplies CDFs and finite probability measures. This result identifies the local ceiling-rank empirical quantile with the lower generalized inverse defined in bundled Causalean code.

**Declaration:** [`TailB_empiricalQuantile_eq_quantile`](../AronowAudit/Shared/MapTailB/QuantileBridge.lean#L147)

```lean
import AronowAudit.Shared.MapTailB.QuantileBridge

#check TailB_empiricalQuantile_eq_quantile
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`TailB_empiricalLaw`](../AronowAudit/Shared/MapTailB/QuantileBridge.lean#L96): uniform empirical probability measure
- [`TailB_empiricalQuantile_eq_quantile_ae`](../AronowAudit/Shared/MapTailB/QuantileBridge.lean#L178): almost-everywhere equality on uniform levels
- [`TailB_empiricalQuantile_integral_eq`](../AronowAudit/Shared/MapTailB/QuantileBridge.lean#L184): equality inside single-quantile integrals

**Scope.** Only strictly interior levels are covered by this declaration. It makes no endpoint equality claim and uses the ceiling-rank convention rather than an interpolated sample quantile. This is an interface identity, not an additional statistical limit theorem.

### H032

**Mean squared quantile approximation without replacement**

Growing samples without replacement approximate population quantiles in mean squared distance under uniform square-tail control.

Areas: Survey sampling, Asymptotic statistics, Probability.

**Statement.** For each $`n`$, let $`d_n`$ be a P022 finite design. Its built-in conditions are $`N_n\ge4`$ and auxiliary arm sizes $`a_n,b_n\ge2`$ with $`a_n+b_n\le N_n`$. Let $`s_n\ge1`$, let $`e_n:\{1,\ldots,s_n\}\to\{1,\ldots,N_n\}`$ be injective, let $`y_n`$ be an arbitrary real population array, and suppose $`s_n\to\infty`$. Assume uniform square-tail control: for every $`\varepsilon\gt 0`$ there is a real $`\beta\gt 1`$ such that for every $`n`$,


```math
\frac1{N_n}\sum_i y_{ni}^2\mathbf1\{y_{ni}^2\ge\beta\}\le\varepsilon.
```


Let $`\pi`$ be uniform over all permutations of the $`N_n`$ labels. Write $`\widehat\mu_{n,\pi}`$ for the empirical law of $`y_{n,\pi(e_n(j))}`$ over $`j\le s_n`$, and $`\mu_n`$ for the full-population empirical law. Then


```math
E_\pi\left[\int_0^1[Q_{\widehat\mu_{n,\pi}}(u)-Q_{\mu_n}(u)]^2\,du\right]\longrightarrow0.
```


The expectation is the exact finite average over the row-specific permutation design.

**Use.** Provides mean convergence of empirical quantiles to finite-population quantiles for sampling without replacement, without a common probability space for assignments or an assumed limiting population law. The probability-convergence companion follows by a finite-design Markov bound.

**Relation to Mathlib.** Mathlib v4.34.1 supplies integration and uniform-integrability tools. This finite-population mean quantile-approximation theorem uses the P022 sampling bounds and the bundled Causalean quantile base.

**Declaration:** [`TailB_sample_quantile_L2_mean`](../AronowAudit/Shared/MapTailB/QuantileL2.lean#L436)

```lean
import AronowAudit.Shared.MapTailB.QuantileL2

#check TailB_sample_quantile_L2_mean
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`TailB_sample_quantile_L2_probability`](../AronowAudit/Shared/MapTailB/QuantileL2.lean#L475): convergence in row-specific design probability
- [`TailB_sample_quantile_square_error_bound`](../AronowAudit/Shared/MapTailB/QuantileL2.lean#L354): finite mean bound before passage to the limit
- [`TailB_sample_integratedCDFError_tendsto`](../AronowAudit/Shared/MapTailB/QuantileL2.lean#L391): integrated CDF approximation in mean

**Scope.** The injection enforces sampling without replacement; no lower bound on the sampling fraction is assumed. Uniform square-tail control is stronger than separate finite second moments in every row. The P022 design type carries auxiliary treatment/control size restrictions even though the sampled block here is any injection.

### H033

**Horvitz–Thompson unbiasedness with positive exposure marginals**

A Horvitz–Thompson exposure mean is unbiased whenever every target exposure probability is positive.

Areas: Experimental design and estimation, Interference and networks, Survey sampling.

**Statement.** Let $`\Omega`$ be a finite assignment type with strictly positive real weights summing to one, and let $`N,K`$ be natural numbers. A population supplies an exposure map $`D:\Omega\to\{0,\ldots,N-1\}\to\{0,\ldots,K-1\}`$ and fixed real potential outcomes $`y_i(d)`$. Choose a target exposure $`d`$ and assume $`\pi_i(d)=E[\mathbf1\{D_i=d\}]\gt 0`$ for every unit $`i`$. Define


```math
\widehat\mu_{HT}(d)=\frac1N\sum_{i\lt N}\frac{\mathbf1\{D_i=d\}y_i(d)}{\pi_i(d)},\qquad \mu(d)=\frac1N\sum_{i\lt N}y_i(d).
```


Then $`E[\widehat\mu_{HT}(d)]=\mu(d)`$. The statement has no strict upper bound on $`\pi_i(d)`$ and no hypothesis $`N\gt 0`$; when $`N=0`$, both means are zero under Lean's total division convention.

**Use.** Provides the basic design-unbiased exposure-mean interface under arbitrary finite assignment and exposure mappings, including interference. Exposure probability one is allowed. The observed_exposure_sum companion connects the masked potential-outcome formula to observed outcomes; recorded_unbiased applies it to fixed recording indicators.

**Relation to Mathlib.** Mathlib v4.34.1 supplies finite-sum and integral linearity. Exposure-mean unbiasedness here follows from an elementary finite weighted-sum identity.

**Declaration:** [`AronowAudit.P013.ht_positive_unbiased`](../AronowAudit/P013/P013_Audit.lean#L3881)

```lean
import AronowAudit.P013.P013_Audit

#check AronowAudit.P013.ht_positive_unbiased
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P013-T24](works/P013.md#p013-t24).

Related declarations:

- [`AronowAudit.P013.htMean`](../AronowAudit/P013/P013_Audit.lean#L88): Exposure-mean estimator definition
- [`AronowAudit.P013.observed_exposure_sum`](../AronowAudit/P013/P013_Audit.lean#L3873): Observed-outcome masking identity
- [`AronowAudit.P013.recorded_unbiased`](../AronowAudit/P013/P013_Audit.lean#L3897): Unbiasedness for recorded outcomes

**Scope.** Probabilities are the exact known design probabilities. The theorem assumes fixed exposure-specific potential outcomes; it does not address estimated propensities, consistency, or loss of reports unless that loss is encoded in the population outcomes. It also includes the empty-unit case through total division.

### H034

**Unadjusted HC2 equals the Neyman variance estimator**

The treatment-slope HC2 variance equals the Neyman variance formula for every assignment with at least two observations per arm.

Areas: Regression and variance estimation, Experimental design and estimation.

**Statement.** Let $`\iota`$ be any finite type, $`s\subseteq\iota`$ a treatment arm, and $`Y:\iota\to\mathbb R`$ arbitrary outcomes. Suppose $`n_1=\#s\ge2`$ and $`n_0=\#s^c\ge2`$. In OLS of $`Y`$ on an intercept and $`\mathbf1\{i\in s\}`$, let $`e_i`$ be the fitted residual, $`h_i`$ the leverage, and $`x_i=(1,\mathbf1\{i\in s\})^T`$. The slope diagonal of the HC2 sandwich


```math
(X^TX)^{-1}\left(\sum_i\frac{e_i^2}{1-h_i}x_ix_i^T\right)(X^TX)^{-1}
```


equals $`s_1^2/n_1+s_0^2/n_0`$, where $`s_a^2`$ is the within-arm sample variance with divisor $`n_a-1`$. This is an equality for every fixed $`s,Y`$.

**Use.** Connects the matrix HC2 calculation to the familiar design-based variance estimator. It is useful for checking implementations of unadjusted binary-treatment regression on arbitrary finite samples, without a stochastic model for the outcomes.

**Relation to Mathlib.** Mathlib supplies finite matrix and sum algebra. The binary-treatment Gram inverse, OLS residuals, leverage and HC2 sandwich are defined here, together with the equality to the Neyman variance expression.

**Declaration:** [`AronowAudit.P036.hc2_eq_neyman`](../AronowAudit/P036/P036_Unadjusted.lean#L564)

```lean
import AronowAudit.P036.P036_Unadjusted

#check AronowAudit.P036.hc2_eq_neyman
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P036-T2](works/P036.md#p036-t2).

Related declarations:

- [`AronowAudit.P036.hc2Variance`](../AronowAudit/P036/P036_Unadjusted.lean#L461): Treatment diagonal of the HC2 sandwich
- [`AronowAudit.P036.hc2_arm_formula`](../AronowAudit/P036/P036_Unadjusted.lean#L540): Residual-square formula by arm
- [`AronowAudit.P036.neymanEstimate`](../AronowAudit/P036/P036_Unadjusted.lean#L467): Neyman sample-variance expression

**Scope.** Applies to an intercept and a single binary treatment indicator, with at least two observations in each arm. It states neither randomization-expectation conservativeness nor a standard-error identity, and it does not cover covariate-adjusted specifications.

### H035

**Bounded vector pair-kernel CLT and overlap-meat consistency**

Bounded symmetric vector pair scores have a Gaussian limit and a consistent overlap-based covariance matrix.

Areas: Probability, Asymptotic statistics, Regression and variance estimation.

**Statement.** Let $`\mu`$ be a probability measure on any measurable type $`U`$ and $`k`$ any finite dimension. Let $`h:U\times U\to\mathbb R^k`$ be measurable and pointwise symmetric, with $`\|h(u,v)\|\le B`$ for some real $`B`$ and all $`u,v`$, and with $`\int h_j\,d(\mu\otimes\mu)=0`$ for every coordinate $`j`$. Define $`g_j(u)=\int h_j(u,v)\,d\mu(v)`$ and $`\Gamma_{j\ell}=\int g_j(u)g_\ell(u)\,d\mu(u)`$. For each $`N`$, use the iid row law $`P_N=\mu^{\{0,\ldots,N-1\}}`$, put $`D_N=N(N-1)/2`$, and for each unordered two-element dyad $`d`$ let $`H_d=h(U_i,U_j)`$ for its two endpoints. Define the ordered overlap meat


```math
M_N=\sum_{d,f:\ d\cap f\ne\varnothing}H_dH_f^T.
```


Then $`NM_N/D_N^2\to4\Gamma`$ in probability: for every $`\varepsilon\gt 0`$, the $`P_N`$-probability that the norm of the error is at least $`\varepsilon`$ tends to zero. Also there exists a probability law $`G`$ on $`\mathbb R^k`$ with positive-semidefinite covariance $`4\Gamma`$, whose every real linear contrast is mean-zero Gaussian with the corresponding quadratic-form variance, such that


```math
\frac{\sqrt N}{D_N}\sum_d H_d\ \Rightarrow\ G.
```


The row statistics are almost everywhere measurable, and the latter convergence uses all bounded continuous real test functions on these changing finite product spaces.

**Use.** Pairs a multivariate pair-average CLT with consistency of the overlap-based covariance matrix. This supports vector dyadic scores and sandwich calculations, allowing singular projection covariance. It adds vector and covariance-estimation conclusions to the scalar second-moment CLT, at the cost of boundedness.

**Relation to Mathlib.** Mathlib v4.34.1 provides scalar iid CLTs, multivariate Gaussian laws, characteristic functions and product measures. This theorem combines these ingredients with local pair and overlap calculations to obtain a vector pair-score CLT and overlap-meat consistency.

**Declaration:** [`AronowAudit.Shared.MapTailB.TailB_bounded_pair_score_limit`](../AronowAudit/Shared/MapTailB/BoundedPairScore.lean#L446)

```lean
import AronowAudit.Shared.MapTailB.BoundedPairScore

#check AronowAudit.Shared.MapTailB.TailB_bounded_pair_score_limit
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P018.meat`](../AronowAudit/P018/P018_Audit.lean#L78): Ordered overlap-meat definition
- [`AronowAudit.P018.Wave1.GP0182B2b_dyad_clt`](../AronowAudit/P018/Wave1/Gap/GP0182B2b.lean#L944): Scalar CLT under a second moment
- [`AronowAudit.Shared.MapTailB.tb09_pair_lln`](../AronowAudit/Shared/MapTailB/BoundedPairScore.lean#L30): Bounded pair-average law of large numbers

**Scope.** Fixed finite dimension, uniformly bounded kernel, pointwise symmetry and coordinatewise centering. The complete unordered-pair set is used, while the meat sums ordered overlapping pairs including equal dyads. Singular covariance is allowed; no inverse-covariance or studentized limit is asserted.

### H036

**Bernoulli coupling with prescribed all-success mass**

Every feasible common success probability is attained by a finite joint distribution with the prescribed Bernoulli marginals.

Areas: Probability, Partial identification and bounds.

**Statement.** For any natural number $`K`$, numbers $`p_i\in[0,1]`$ for $`i\in\{0,\ldots,K-1\}`$, and real $`\alpha`$ satisfying


```math
0\le\alpha\le1,\qquad \alpha\le p_i\ \text{for every }i,\qquad
1-\sum_i(1-p_i)\le\alpha,
```


there exist real weights $`w(s)`$ on all Boolean vectors $`s\in\{\mathrm{false},\mathrm{true}\}^K`$ such that


```math
w(s)\ge0,\qquad \sum_s w(s)=1,\qquad
\sum_{s:s_i=\mathrm{true}}w(s)=p_i\ \text{for every }i,\qquad
w(\mathrm{true},\ldots,\mathrm{true})=\alpha.
```


The quantifier includes $`K=0`$, where the hypotheses force $`\alpha=1`$.

**Use.** A small finite coupling construction for attaining intersection-probability bounds, joint-status models and sharp identification arguments. It gives a joint mass function without requiring strictly positive probabilities for every status vector; its splitting argument uses only finite sums and real arithmetic.

**Relation to Mathlib.** Mathlib v4.34.1 has Bernoulli laws and finite product measures. This prescribed-intersection construction uses elementary finite real weights rather than a measure-valued interface.

**Declaration:** [`AronowAudit.P010.Wave1.bernoulli_status_coupling`](../AronowAudit/P010/Wave1/Lib/StatusCouplingTailC.lean#L75)

```lean
import AronowAudit.P010.Wave1.Lib.StatusCouplingTailC

#check AronowAudit.P010.Wave1.bernoulli_status_coupling
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P010.Wave1.tcStatus_split`](../AronowAudit/P010/Wave1/Lib/StatusCouplingTailC.lean#L14): split a distinguished atom and its complement

**Scope.** The declaration proves sufficiency of the displayed feasibility inequalities. It does not separately state their necessity or impose any independence between the coordinates.

### H037

**Positive semidefinite graph matrices and unions of cliques**

Identity plus adjacency is positive semidefinite exactly for unions of cliques and then yields a cluster sum-of-squares formula.

Areas: Foundations, Regression and variance estimation.

**Statement.** For any natural number $`n`$ and any simple undirected graph $`A`$ on $`\{0,\ldots,n-1\}`$, write $`S=I+\mathrm{adj}(A)`$. Then $`S`$ is positive semidefinite if and only if equality-or-adjacency is transitive, that is, $`A`$ is a disjoint union of cliques. Moreover, for every labeling $`C:\{0,\ldots,n-1\}\to\mathbb N`$ satisfying


```math
A(i,j)=\mathrm{true}\ \Longleftrightarrow\ i\ne j\ \text{and}\ C_i=C_j,
```


and every real vector $`x`$, let $`\bar x=n^{-1}\sum_i x_i`$ and $`e_i=x_i-\bar x`$. The declaration also asserts


```math
V_1(A,x)=\frac{\sum_i e_i^2+\sum_{i,j}\mathrm{adj}(A)_{ij}e_ie_j}{n^2}
=\frac{1}{n^2}\sum_{c\in\mathrm{image}(C)}\left(\sum_{i:C_i=c}e_i\right)^2.
```


There is no positive-size hypothesis; at $`n=0`$ the source uses Lean's totalized division convention.

**Use.** Characterizes precisely when the identity-plus-adjacency quadratic estimator is PSD before spectral repair, and turns clique dependence into a familiar cluster sum-of-squares formula. A companion theorem constructs suitable cluster labels; the result is purely finite algebra and imposes no stochastic model.

**Relation to Mathlib.** Mathlib supplies finite equivalence classes and matrix PSD criteria, including the zero-quadratic-form kernel property. The graph characterization uses local Boolean-graph and PSD definitions and expresses clique quadratic forms as cluster sums of squares.

**Declaration:** [`AronowAudit.P011.clique_characterization`](../AronowAudit/P011/P011_FiniteCompletion.lean#L160)

```lean
import AronowAudit.P011.P011_FiniteCompletion

#check AronowAudit.P011.clique_characterization
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P011-T3](works/P011.md#p011-t3).

Related declarations:

- [`AronowAudit.P011.CliqueUnion`](../AronowAudit/P011/P011_Audit.lean#L462): transitivity definition for a union of cliques
- [`AronowAudit.P011.CliqueCompletion.labels_exist`](../AronowAudit/P011/P011_FiniteCompletion.lean#L52): construct cluster labels
- [`AronowAudit.P011.CliqueCompletion.quadratic_labels`](../AronowAudit/P011/P011_FiniteCompletion.lean#L86): unscaled cluster quadratic identity

**Scope.** Singleton cliques and empty graphs are allowed. The formula concerns centered scores and ordered matrix-pair sums; it does not assert stochastic conservativeness.


## Counterexamples and corrections

### H038

**Weak bootstrap validity need not give variance consistency**

A heavy-tailed median has valid sampling and bootstrap weak limits while its scaled bootstrap variance remains inconsistent.

Areas: Resampling, Asymptotic statistics.

**Statement.** Let $`\mu`$ be any probability measure and let $`(X_i)_{i\ge0}`$ be measurable iid real variables under $`\mu`$, with common law


```math
\tfrac12\,\mathrm{Uniform}[-1,1]+\tfrac14\,\mathcal L(2^{1/U^2})+\tfrac14\,\mathcal L(-2^{1/U^2}),\qquad U\sim\mathrm{Uniform}[0,1].
```


Let $`M_n`$ be the sample median, and let $`M_n^*`$ recompute it on an ordinary size-$`n`$ sample drawn with replacement from the first $`n`$ observations. Write $`V_n^*=\mathrm{Var}^*(M_n^*)`$, the exact finite conditional variance over all $`n^n`$ resampling maps. Along $`n=2k+1`$, the declaration asserts CDF convergence $`\sqrt n M_n\Rightarrow N(0,4)`$ and conditional bootstrap weak convergence in probability: for every bounded continuous real $`f`$,


```math
E^*f\!\left(\sqrt n(M_n^*-M_n)\right)\ \longrightarrow_p\ \int f\,dN(0,4).
```


It also asserts, for every odd $`n\ge5`$,


```math
\mu(nV_n^*\gt 5)\ge\frac{3}{16},
```


and $`nV_n^*`$ does not converge in probability to $`4`$ along $`n=2k+1`$.

**Use.** Separates weak bootstrap validity from convergence of bootstrap moments using the actual sample median. The population is regular near its median, but remote tails make rare resamples influential for conditional variance. It is a concrete warning when bootstrap standard errors are justified only by a weak limit.

**Relation to Mathlib.** Mathlib v4.34.1 supplies Gaussian laws, CDFs and convergence-in-measure infrastructure. This bootstrap-median variance counterexample uses the P001 iid, CDF-limit and conditional-bootstrap-test interfaces.

**Declaration:** [`AronowAudit.P001.Wave1.TailA.heavy_median_bootstrap_variance_counterexample_final`](../AronowAudit/P001/Wave1/Gap/TailA/HeavyMedian.lean#L287)

```lean
import AronowAudit.P001.Wave1.Gap.TailA.HeavyMedian

#check AronowAudit.P001.Wave1.TailA.heavy_median_bootstrap_variance_counterexample_final
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P001-T61](works/P001.md#p001-t61).

Related declarations:

- [`AronowAudit.P001.heavyBootstrapLaw`](../AronowAudit/P001/P001_Foundations.lean#L587): explicit heavy-tailed population
- [`AronowAudit.P001.BootstrapWeakCP`](../AronowAudit/P001/P001_Foundations.lean#L741): bounded-continuous conditional weak-limit definition
- [`AronowAudit.P001.TailA.local_median_weak`](../AronowAudit/P001/Wave1/Lib/TailA/MedianWeak.lean#L736): general moment-free median weak limits

**Scope.** The selected declaration concerns odd sample sizes and exact ordinary-bootstrap variance, not a finite Monte Carlo estimate of that variance. The population has local density one quarter at median zero; local regularity alone does not control bootstrap second moments.

### H039

**Nearest-neighbor matching can defeat the ordinary bootstrap variance**

An exactly unbiased nearest-neighbor matching estimator has an inconsistent ordinary bootstrap variance with a smaller expectation limit.

Areas: Resampling, Causal identification, Asymptotic statistics.

**Statement.** On any probability space let $`(P_i,A_i,E_i)_{i\ge0}`$ be measurable iid observations from `matchingUnitLaw`: $`P_i\sim\mathrm{Uniform}[1/4,3/4]`$, $`A_i\mid P_i\sim\mathrm{Bernoulli}(P_i)`$, and $`E_i`$ is an independent fair sign. For each treated unit match to the untreated unit with nearest $`P`$; the source fixes a tie choice and assigns a zero contribution when no untreated donor exists. The statistic `causalMatch` is


```math
T_n=-\frac1n\left(\sum_{i:A_i=0}E_i+\sum_{i:A_i=1}E_{j(i)}\right),
```


with the stated no-donor convention. Let $`V_n^*=\mathrm{Var}^*(T_n^*)`$ be its exact ordinary-bootstrap variance, recomputing matches on every resample. Then $`E_\mu T_n=0`$ for every $`n\gt 0`$,


```math
n\mathrm{Var}_\mu(T_n)\to V,\qquad E_\mu[nV_n^*]\to V_B,\qquad 0\lt V_B\lt V,
```


and $`nV_n^*`$ does not converge in probability to $`V`$. The constants are $`V=3\log3-1/4`$ and


```math
s=1-e^{-1},\quad a=2/s-s/(2-s),\quad b=3/(2s)-(4-s)/(2(2-s)),\quad
V_B=1/2+a/2+b(2\log3-3/2).
```



**Use.** Shows that bootstrap variance failure for nearest-neighbor matching need not be caused by estimator bias: unbiasedness holds at every positive sample size. The same development has a hot-deck counterpart and extensions to the source’s estimated-score statistic. The result is for a specified continuous-score design, rather than arbitrary matching procedures.

**Relation to Mathlib.** Mathlib v4.34.1 provides product laws, finite sums, moments and probability convergence tools. The matching and exact-resampling definitions are local to P001.

**Declaration:** [`AronowAudit.P001.Wave1.TailA.matching_bootstrap_counterexample_supporting_final`](../AronowAudit/P001/Wave1/Gap/TailA/MatchingFinals.lean#L43)

```lean
import AronowAudit.P001.Wave1.Gap.TailA.MatchingFinals

#check AronowAudit.P001.Wave1.TailA.matching_bootstrap_counterexample_supporting_final
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P001-T15](works/P001.md#p001-t15).

Related declarations:

- [`AronowAudit.P001.MatchingFailure`](../AronowAudit/P001/P001_Foundations.lean#L247): complete bias, variance and inconsistency contract
- [`AronowAudit.P001.causalMatch`](../AronowAudit/P001/P001_Foundations.lean#L214): exact nearest-neighbor statistic
- [`AronowAudit.P001.matchingUnitLaw`](../AronowAudit/P001/P001_Foundations.lean#L229): uniform-score and sign-noise joint law

**Scope.** The bootstrap conclusion is convergence of its variance expectation to the smaller constant, plus failure of convergence in probability to the sampling constant. It does not claim convergence in probability to the smaller constant.

### H040

**A smooth positive density can have an infinite exceptional marginal slice**

A smooth strictly positive joint density can have an infinite marginal slice at one point despite finite total mass.

Areas: Probability, Foundations.

**Statement.** Define, for all real $`x,y`$,


```math
f(x,y)=\frac{(e^x/(1+e^x))^2}{\pi(1+y^2e^{2x})}.
```


The declaration asserts jointly that $`f`$ is infinitely differentiable on $`\mathbb R^2`$, $`f(x,y)\gt 0`$ everywhere, $`f`$ is Lebesgue integrable on $`\mathbb R^2`$, and $`\int_{\mathbb R^2}f=1`$. Nevertheless,


```math
\int_{\mathbb R}^{-}\mathrm{ofReal}(f(x,0))\,dx=+\infty,
```


where this is the nonnegative extended Lebesgue integral. For every real $`y\ne0`$, the function $`x\mapsto f(x,y)`$ is Lebesgue integrable.

**Use.** A concrete distinction between pointwise claims about marginal-density formulas and the almost-everywhere conclusions supplied by Fubini and Tonelli. The proof normalizes Cauchy conditional densities using a logistic mixing density; the failure is confined to the exceptional slice at zero.

**Relation to Mathlib.** Mathlib supplies Cauchy densities, improper integrals, Fubini–Tonelli tools and almost-everywhere integrability of slices through MeasureTheory.Integrable.prod_left_ae. The explicit smooth positive density has an exceptional slice consistent with that almost-everywhere theorem.

**Declaration:** [`AronowAudit.P001.Wave1.infinite_marginal_slice_counterexample_proof`](../AronowAudit/P001/Wave1/Gap/GLP0013B1.lean#L246)

```lean
import AronowAudit.P001.Wave1.Gap.GLP0013B1

#check AronowAudit.P001.Wave1.infinite_marginal_slice_counterexample_proof
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P001-T36](works/P001.md#p001-t36).

Related declarations:

- [`AronowAudit.P001.smoothSlicePDF`](../AronowAudit/P001/P001_Foundations.lean#L355): explicit joint density
- [`AronowAudit.P001.Wave1.t36B1r2_conditional_cauchy`](../AronowAudit/P001/Wave1/Gap/GLP0013B1.lean#L122): integrability in the second coordinate and logistic marginal identity

**Scope.** The exceptional slice has infinite nonnegative extended integral. This infinite value is not represented by Lean’s totalized real Bochner integral.

### H041

**Absolute sandwich consistency does not validate a degenerate contrast**

A bounded dyadic model has an absolutely consistent sandwich matrix, a negative estimated slope variance with positive limiting probability, and a totalized slope pivot without a standard normal limit.

Areas: Regression and variance estimation, Interference and networks, Asymptotic statistics.

**Statement.** Take iid units $`(Z_i,W_i)`$ consisting of two independent fair signs, observe all unordered distinct dyads, and set $`X_{ij}=(1,1+Z_iZ_j)`$ and $`Y_{ij}=W_i+W_j`$. Let $`Q=E[X_{12}X_{12}^{\mathsf T}]`$, $`\beta=Q^{-1}E[X_{12}Y_{12}]`$, $`h_{ij}=X_{ij}(Y_{ij}-X_{ij}^{\mathsf T}\beta)`$, and $`\Gamma=E[g(U)g(U)^{\mathsf T}]`$ for $`g(u)=E[h(u,U')]`$. Let $`\widehat V_N`$ be the OLS residual sandwich with all ordered pairs of dyads sharing at least one unit in its meat, including identical dyads, and let $`D_N=N(N-1)/2`$. The declaration asserts the source's standing conditions: a probability unit law, measurable symmetric bounded dyad data, an intercept and nonsingular $`Q`$. It also asserts `Proposition1Extra`: uniformly bounded fitted residuals at every size; nonzero entries of $`Q`$ and of $`E[X_{12}X_{13}^{\mathsf T}]`$; and eventually in $`N`$, nonzero expected fitted-residual squares and nonzero expected fitted-residual products for every pair of distinct overlapping dyads.

Its population identities are


```math
Q=\begin{pmatrix}1&1\\1&2\end{pmatrix},\qquad \beta=0,\qquad
\Gamma=\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
4Q^{-1}\Gamma Q^{-1}=\mathrm{diag}(4,0).
```


For every $`N\ge3`$, the source's unconditional covariance target is


```math
V_N=\frac{N}{D_N^2}Q^{-1}\mathrm{Var}\!\left(\sum_{i\lt j}h_{ij}\right)Q^{-1}
=\begin{pmatrix}4N/(N-1)&-4/(N-1)\\-4/(N-1)&4/(N-1)\end{pmatrix}.
```


Finally,


```math
P((\widehat V_N)_{22}\lt 0)\to1-e^{-1/2},\qquad
N\widehat V_N\longrightarrow_p\mathrm{diag}(4,0),
```


while $`(\widehat\beta_{N,2}-\beta_2)/\sqrt{(\widehat V_N)_{22}}`$ does not converge weakly to $`N(0,1)`$ under the source's bounded-continuous-test definition.

**Use.** Demonstrates that absolute consistency of a covariance estimator does not justify studentization of a contrast whose limiting variance is zero, even with bounded iid unit characteristics and the source’s additional moment conditions. The same development supplies an explicit eight-unit negative-variance certificate.

**Relation to Mathlib.** Mathlib v4.34.1 provides finite probability laws, covariance, Gaussian laws and convergence infrastructure. The counterexample uses P018 definitions of OLS, overlap meat and bounded-continuous-test weak limits.

**Declaration:** [`AronowAudit.P018.Wave1.TailB_degenerate_inference_counterexample`](../AronowAudit/P018/Wave1/Gap/TailBSignDegeneracy.lean#L14)

```lean
import AronowAudit.P018.Wave1.Gap.TailBSignDegeneracy

#check AronowAudit.P018.Wave1.TailB_degenerate_inference_counterexample
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P018-T7](works/P018.md#p018-t7).

Related declarations:

- [`AronowAudit.P018.signPairKernel`](../AronowAudit/P018/P018_Audit.lean#L1578): exact iid-sign dyadic model
- [`AronowAudit.P018.Wave1.TailBSign.tb05_negative_variance_probability`](../AronowAudit/P018/Wave1/Gap/TailBSignInference.lean#L141): limiting probability of negative slope variance
- [`AronowAudit.P018.Wave1.TailBSign.tb05_pivot_not_normal`](../AronowAudit/P018/Wave1/Gap/TailBSignInference.lean#L161): failure of the normal pivot limit

**Scope.** Matrix coordinates in the statement use statistical numbering; Lean’s slope coordinate is 1. The pivot is totalized: Real.sqrt of a negative estimate is zero and division by zero is zero. The claim concerns that specified pivot and an absolute matrix error scale.

### H042

**Inverse continuity does not imply inverse-moment control**

A bounded full-rank dyadic design has a probability limit for its inverse Gram matrix but infinite inverse-norm expectation at every relevant size.

Areas: Regression and variance estimation, Probability.

**Statement.** Let iid real unit characteristics $`T_i`$ have density $`t^{-2}\mathbf1\{t\ge1\}`$. On all unordered distinct dyads take $`X_{ij}=(1,e^{-T_i}+e^{-T_j})`$ and $`Y_{ij}=0`$. Put $`D_N=N(N-1)/2`$, $`Q=E[X_{12}X_{12}^{\mathsf T}]`$, and $`Q_N=D_N^{-1}\sum_{i\lt j}X_{ij}X_{ij}^{\mathsf T}`$. The declaration asserts `Standing`: the unit law is a probability, the dyad functions are measurable and symmetric, are bounded almost surely under the two-unit product law, an intercept is present, and $`Q`$ is nonsingular. It also asserts `SampleRank`: some deterministic $`N_0`$ gives almost-sure nonsingularity of the sample Gram matrix for each $`N\ge N_0`$. Under the finite iid product law at size $`N`$,


```math
Q_N^{-1}-Q^{-1}\longrightarrow_p0.
```


For every integer $`N\ge3`$ and integer $`m\ge1`$ it additionally gives the quantitative lower bound


```math
\mathrm{ofReal}\!\left(\frac{e^{2m}}{4m^N}\right)
\le\int^{-}\mathrm{ofReal}\!\left(\|Q_N^{-1}\|_{\mathrm{op}}\right)\,dP_N,
```


and for every integer $`N\ge3`$ this nonnegative extended integral equals $`+\infty`$. The displayed operator norm is the Euclidean induced norm.

**Use.** A concrete obstruction to replacing probability convergence of inverse sample matrices with inverse-moment bounds. It isolates a design-matrix problem in bounded regressors and shows exactly how a small-probability nearly singular design can dominate expectation.

**Relation to Mathlib.** Mathlib v4.34.1 provides Pareto distributions, matrix inversion, finite products and convergence-in-measure tools. The dyadic inverse-Gram infinite-moment witness uses these ingredients within the P018 kernel model.

**Declaration:** [`AronowAudit.P018.Wave1.inverse_gram_counterexample_proof`](../AronowAudit/P018/Wave1/Gap/GLP0182B1.lean#L443)

```lean
import AronowAudit.P018.Wave1.Gap.GLP0182B1

#check AronowAudit.P018.Wave1.inverse_gram_counterexample_proof
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P018-T3](works/P018.md#p018-t3).

Related declarations:

- [`AronowAudit.P018.inverseKernel`](../AronowAudit/P018/P018_Audit.lean#L1898): bounded dyadic design with zero outcomes
- [`AronowAudit.P018.SampleRank`](../AronowAudit/P018/P018_Audit.lean#L731): eventual almost-sure rank contract
- [`AronowAudit.P018.Wave1.inverse_gram_integral_lower`](../AronowAudit/P018/Wave1/Gap/GLP0182B1.lean#L394): quantitative inverse-moment lower bound

**Scope.** The divergence is a nonnegative extended expectation of the inverse Euclidean operator norm, not a finite real expectation. Outcomes are identically zero, so this does not exhibit infinite moments of fitted OLS coefficients. Probability convergence uses varying finite product sample spaces.

### H043

**A deterministic-matrix expansion can fail after data selection**

A rank-one matrix selected from iid signs breaks the deterministic quadratic expansion despite having bounded operator norm.

Areas: Regression and variance estimation, Probability.

**Statement.** For every integer $`n\gt 0`$ and every sign vector $`x\in\{-1,1\}^n`$, define $`\bar x=n^{-1}\sum_i x_i`$, $`M(x)=xx^{\mathsf T}/n`$, and


```math
\mathrm{varianceForm}(M,x)=\frac{(x-\bar x\mathbf1)^{\mathsf T}M(x-\bar x\mathbf1)}{n^2}.
```


The declaration asserts the exact identities


```math
\|M(x)\|_{\mathrm{op}}=1,\qquad\mathrm{tr}\,M(x)=1,\qquad
n\,\mathrm{varianceForm}(M(x),x)=(1-\bar x^2)^2.
```


For $`n=k+1`$ and a vector $`X`$ of $`n`$ independent fair signs, under its size-specific joint law it further asserts


```math
n\,\mathrm{varianceForm}(M(X),X)-1\longrightarrow_p0,\qquad
\frac{\mathrm{tr}(M(X)-I_n)}{n}\longrightarrow_p-1.
```



**Use.** An exact counterexample to extending a deterministic-matrix quadratic expansion to a matrix selected from the same observations using only an operator-norm bound. The finite identity makes the mismatch visible before taking limits; the probability limit follows from the iid-sign sample mean tending to zero.

**Relation to Mathlib.** Mathlib supplies rank-one operators, their norm formula, finite-sum variance and convergence tools. The counterexample combines these ingredients with the local centering and variance-form definitions.

**Declaration:** [`AronowAudit.P011.data_dependent_expansion_failure`](../AronowAudit/P011/P011_DataMatrixCompletion.lean#L203)

```lean
import AronowAudit.P011.P011_DataMatrixCompletion

#check AronowAudit.P011.data_dependent_expansion_failure
```

**Status:** `counterexample_proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P011-T4](works/P011.md#p011-t4).

Related declarations:

- [`AronowAudit.P011.dataMatrix`](../AronowAudit/P011/P011_Audit.lean#L477): rank-one data-selected matrix
- [`AronowAudit.P011.varianceForm`](../AronowAudit/P011/P011_Audit.lean#L65): centered quadratic variance estimator
- [`AronowAudit.P011.deterministic_quadratic_expansion`](../AronowAudit/P011/P011_DenseVarianceCompletion.lean#L240): deterministic-matrix theorem whose substitution fails

**Scope.** This is a fixed iid-sign witness with a matrix selected from the same data. It does not refute the deterministic-matrix theorem. The limits use size n equal to k plus one and its corresponding finite sample law.

### H044

**Equal completion rates do not identify a complete-case treatment effect**

Equal response rates across randomized treatment arms can coexist with a biased complete-case regression coefficient.

Areas: Causal identification, Regression and variance estimation.

**Statement.** The declaration has no hypotheses and establishes the concrete proposition `EqualCompletionFailure`. On the 32 configurations $`(u,r_0,r_1,x,t)\in\{0,1\}^5`$, give each configuration weight


```math
\frac18\,p_0(u)^{r_0}(1-p_0(u))^{1-r_0}p_1(u)^{r_1}(1-p_1(u))^{1-r_1},
```


where $`p_b(u)=37/50`$ if $`b=u`$ and $`13/50`$ otherwise. Set $`T=t`$, $`Y(0)=Y(1)=u`$, $`R(b)=r_b`$, and $`X=x`$, with realized completion $`R=R(T)`$. The conclusion is that $`T`$ is independent of the entire potential-outcome, potential-completion and covariate bundle; $`P(R=1\mid T=b)=1/2`$ for both arms; $`R(0)`$ is independent of neither $`u`$ nor $`(u,u,x)`$; and the population treatment effect is zero. For respondent design vector $`z=(1,T,X)`$, the vector $`\beta=(13/50,12/25,0)`$ solves $`E[zz^\top\mid R=1]\beta=E[zY\mid R=1]`$, while its treatment coefficient $`12/25`$ differs from the zero population effect.

**Use.** A finite diagnostic example for attrition assumptions: equal arm response rates do not supply independence of potential response from outcomes and covariates. It concerns complete-case population normal equations with one binary covariate.

**Relation to Mathlib.** This is an application-specific finite rational construction using finite sums and independence factorizations. Mathlib supplies the finite algebraic and counting tools used to establish the explicit attrition example.

**Declaration:** [`AronowAudit.P034.equal_completion_does_not_identify`](../AronowAudit/P034/P034_Attrition.lean#L925)

```lean
import AronowAudit.P034.P034_Attrition

#check AronowAudit.P034.equal_completion_does_not_identify
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P034.EqualCompletionFailure`](../AronowAudit/P034/P034_Attrition.lean#L914): exact conjunction established by the theorem
- [`AronowAudit.P034.worldAModel`](../AronowAudit/P034/P034_Attrition.lean#L96): potential outcomes, completions and covariate
- [`AronowAudit.P034.corrected_complete_case_identification`](../AronowAudit/P034/P034_Attrition.lean#L936): general identification under independent potential completion

**Scope.** A fixed 32-point population example, with coefficients specified as a normal-equation solution. The general identification theorem states additional assumptions.

### H045

**Pairwise independence does not protect a fit of the whole fitting vector**

Pairwise treatment independence can leave a prediction fitted from the other outcomes correlated with the target treatment.

Areas: Randomization inference, Experimental design and estimation.

**Statement.** The declaration has no hypotheses. Let $`D`$ put weight $`1/4`$ on each treatment vector $`(0,0,0)`$, $`(0,1,1)`$, $`(1,0,1)`$ and $`(1,1,0)`$ for three units indexed $`0,1,2`$. Let the fitting set be $`J=\{1,2\}`$, take treated potential outcomes identically one and control potential outcomes identically zero, and define the prediction $`g(y_1,y_2)=y_1+y_2-2y_1y_2`$. The conclusion is that $`D`$ is a probability design with positive treatment and control marginals; $`T_0`$ is independent of $`T_j`$ for every $`j\in J`$; yet $`\mathrm{Cov}_D(\mathbf1\{T_0=1\},g(Y_1,Y_2))\ne0`$, where the fitting inputs are the observed outcomes under $`D`$. Independence here means factorization of expectations of every pair of functions of the two variables.

**Use.** A compact example for checking assumptions about fitted predictions. Independence of the target assignment from the entire fitting vector is preserved by fitting; separate independence from its coordinates is insufficient.

**Relation to Mathlib.** The construction specializes finite expectation, covariance and independence algebra to a counterexample involving a nonlinear prediction from a fitting vector.

**Declaration:** [`AronowAudit.P026.Refutations.printed_pairwise_fitting_refuted`](../AronowAudit/P026/P026_Refutations.lean#L123)

```lean
import AronowAudit.P026.P026_Refutations

#check AronowAudit.P026.Refutations.printed_pairwise_fitting_refuted
```

**Status:** `counterexample_proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P026-T18](works/P026.md#p026-t18).

Related declarations:

- [`AronowAudit.P026.Refutations.realXorThree`](../AronowAudit/P026/P026_Refutations.lean#L102): four-point parity assignment design
- [`AronowAudit.P026.Refutations.xorFit`](../AronowAudit/P026/P026_Refutations.lean#L108): prediction from the fitting outcomes
- [`AronowAudit.P026.independent_comp`](../AronowAudit/P026/P026_FiniteDesign.lean#L764): whole-vector independence survives a deterministic fit

**Scope.** The example concerns a nonlinear XOR prediction under this three-unit assignment design. It does not assert failure under independence from the whole fitting vector.

### H046

**Regression residuals do not create fresh Student degrees of freedom**

A six-observation Gaussian residual regression has a scaled Student law that differs from its conventional reference law.

Areas: Regression and variance estimation, Probability.

**Statement.** For every positive noise scale $`\sigma\in\mathbb R_{\ge0}`$ and every $`\gamma\in\mathbb R^2`$, let $`u=(1,-1,0,0,0,0)`$, $`v=(0,0,1,-1,0,0)`$, $`Z=[\mathbf1,u]`$, and $`y=Z\gamma+\varepsilon`$, where the six coordinates of $`\varepsilon`$ are independent $`N(0,\sigma^2)`$. Regress $`y`$ on $`Z`$, then regress the first-stage residual on $`[\mathbf1,v]`$. Let $`S`$ be the conventional second-stage slope t statistic, using its residual sum of squares divided by $`6-2=4`$. Put


```math
U=\frac{v^\top\varepsilon}{\sigma\sqrt2},\qquad V=\frac{\mathrm{SSE}([Z,v],y)}{\sigma^2}.
```


The conclusion is that the joint law of $`(U,V)`$ is $`N(0,1)\otimes\chi^2_3`$, that $`S=U/\sqrt{V/4}`$ for every noise vector, and that the law of $`S`$ is the image of $`t_3`$ under multiplication by $`\sqrt{4/3}`$. Moreover $`E[S^2]=4`$, $`E[t_3^2]=3`$, $`E[t_4^2]=2`$, and the law of $`S`$ differs from $`t_4`$. The Student and chi-square laws are defined from independent standard-normal coordinates.

**Use.** An exact distributional check on conventional inference after residualizing outcomes. It separates the full model residual degrees of freedom from the second-stage divisor and holds for every positive Gaussian noise scale and every first-stage coefficient vector. The proof uses Gaussian projection and Gaussian-ratio moments from bundled Causalean and StatLean libraries.

**Relation to Mathlib.** Mathlib supplies Gaussian measures and linear algebra. The exact reference-law calculation also uses bundled Causalean chi-square projection and StatLean Gaussian-ratio moment results.

**Declaration:** [`AronowAudit.P039.residual_gaussian_reference_counterexample`](../AronowAudit/P039/P039_GaussianCompletion.lean#L463)

```lean
import AronowAudit.P039.P039_GaussianCompletion

#check AronowAudit.P039.residual_gaussian_reference_counterexample
```

**Status:** `counterexample_proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P039-T3](works/P039.md#p039-t3).

Related declarations:

- [`AronowAudit.P039.olsT`](../AronowAudit/P039/P039_Regression.lean#L56): conventional coefficient statistic
- [`AronowAudit.P039.witnessZ`](../AronowAudit/P039/P039_Regression.lean#L150): explicit first-stage design
- [`AronowAudit.P039.GaussianCompletion.actual_stat_law`](../AronowAudit/P039/P039_GaussianCompletion.lean#L395): scaled Student distribution identity

**Scope.** An explicit linear OLS Gaussian model with six observations. It does not address arbitrary nonlinear first-stage fits. The pointwise ratio uses Lean’s totalized division and square root conventions.

### H047

**Sparsity and absolute variance conservativeness do not ensure coverage**

A sparse randomized sequence satisfies absolute variance conservativeness while its nominal confidence intervals cover only half the time.

Areas: Experimental design and estimation, Asymptotic statistics, Interference and networks.

**Statement.** The declaration has no hypotheses. For every $`t\ge0`$, set $`n=t+1`$ and use independent fair binary assignments $`Z_i`$, with outcome $`Y_0(z)=z_0`$ and $`Y_i(z)=0`$ for $`i\ne0`$. It establishes `RegularSequence sparseStudy 2 4 1`: treatment propensities equal $`1/2`$, each observed fourth absolute moment is at most $`2^4`$, and each potential-outcome first absolute moment is at most $`2`$. Every experiment is Bernoulli and has no interference; the source’s average, maximum and root-mean-square dependence degrees and largest dependence eigenvalue all equal one. It satisfies `Restricted`, meaning the average degree divided by $`n`$ tends to zero.

For every $`t`$, the expected average treatment effect, average contrast of conditional expected outcomes between treatment arms (`adse`) and average squared expected direct effect all equal $`1/n`$. For every assignment the HT estimator and Bernoulli variance estimator obey


```math
\widehat\tau=2Z_0/n,\qquad \widehat V=4Z_0/n^2.
```


All three degree-inflated estimators `vAVG`, `vMAX` and `vSR` equal $`\widehat V`$. Also $`\mathrm{Var}(\widehat\tau)=1/n^2`$, $`E\widehat V=2/n^2\gt \mathrm{Var}(\widehat\tau)`$, and the squared standard deviation across unit HT-contribution variances is $`(n-1)/n^2`$.

All four variance estimators satisfy the source’s `Conservative` condition: there exists $`L:\mathbb R\to\mathbb R`$ such that, for every $`\epsilon\gt 0`$, $`P(n(\widehat V-\mathrm{Var}(\widehat\tau))\le-\epsilon)\to L(\epsilon)`$, and $`L(\epsilon)\to0`$ as $`\epsilon\downarrow0`$. In addition, $`n(\widehat V-\mathrm{Var}(\widehat\tau))-1/n\to0`$ in probability on the changing assignment spaces. Nevertheless, for every $`t`$,


```math
P\left(\lvert\widehat\tau-1/n\rvert\le\sqrt{\widehat V/(1/20)}\right)=1/2\lt 1-1/20.
```



**Use.** Shows why sparsity, bounded moments and absolute conservativeness on the stated scale do not alone justify asymptotic coverage. A variance nondegeneracy or relative-error condition is needed for a general coverage theorem.

**Relation to Mathlib.** The counterexample uses finite randomization laws and convergence definitions on changing assignment spaces to compare absolute variance conservativeness with interval coverage.

**Declaration:** [`AronowAudit.P009.Wave1.sparse_coverage_counterexample_proof`](../AronowAudit/P009/Wave1/Gap/GLP0091B1.lean#L242)

```lean
import AronowAudit.P009.Wave1.Gap.GLP0091B1

#check AronowAudit.P009.Wave1.sparse_coverage_counterexample_proof
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P009-T1](works/P009.md#p009-t1).

Related declarations:

- [`AronowAudit.P009.sparseStudy`](../AronowAudit/P009/P009_Audit.lean#L635): explicit sequence of finite experiments
- [`AronowAudit.P009.Conservative`](../AronowAudit/P009/P009_Audit.lean#L543): iterated-limit conservativeness definition
- [`AronowAudit.P009.Wave1.sparseCoverage_coverage`](../AronowAudit/P009/Wave1/Gap/GLP0091B1.lean#L231): exact coverage at every sample size

**Scope.** Conservativeness uses an absolute variance-error scale and an iterated limit. The variance shrinks as the inverse square of population size.


## Candidates for Mathlib

- [H001: Combinatorial central limit theorem for permutation arrays](#h001)
- [H002: Lindeberg CLT on changing probability spaces](#h002)
- [H003: Le Cam’s first lemma, four equivalent forms](#h003)
- [H004: One-sided nondominated QMD gives score regularity and a local likelihood expansion](#h004)
- [H005: Scalar outer Hadamard delta method](#h005)
- [H006: Attained Fréchet covariance bounds for square-integrable marginals](#h006)
- [H007: Order-two U-statistic CLT under only second moments](#h007)
- [H008: Nearest positive-semidefinite matrix in Frobenius norm](#h008)
- [H009: Exponential tilting of possibly singular Gaussian laws](#h009)
- [H010: Hellinger error tensorization for product experiments](#h010)
- [H011: Multivariate iid CLT allowing singular covariance](#h011)
- [H012: Sharp bounded-weight means with explicit threshold optimizers](#h012)
- [H013: Causal IPW and double-robust identification](#h013)
- [H014: MAR reweighting identifies the entire outcome law](#h014)
- [H015: Quadratic-form sampling bound for doubly centered matrices](#h015)
- [H016: Conservative HT contrast variance with zero joint exposure probabilities](#h016)
- [H017: Exact HC2 conservativeness gap and equality condition](#h017)
- [H018: Exact prediction-covariance bias of regression-assisted contrasts](#h018)
- [H019: Sharp ATE interval with unchanged observable law](#h019)
- [H020: Exchangeable Monte Carlo p-values, with ties and floor bounds](#h020)
- [H022: Exactly which means nonnegative reweighting can represent](#h022)
- [H023: Fixed-size systematic sampling with prescribed inclusion probabilities](#h023)
- [H024: Unknown-propensity impossibility for arbitrary randomized procedures](#h024)
- [H025: Exact dyadic sandwich decomposition with repeated dyads](#h025)
- [H026: Finite-sample bounded-Lipschitz bound for permutation arrays](#h026)
- [H030: Squared quantile error from tails and CDF distance](#h030)
- [H036: Bernoulli coupling with prescribed all-success mass](#h036)

## Further useful results

### H048

**Population-mean identification from sampling probabilities known up to scale**

Within-degree mean ignorability identifies the population mean by inverse sampling weights known only up to scale.

Areas: Survey sampling, Causal identification.

**Statement.** Let $`F`$ be any probability law of $`(Y,D,S)`$ on $`[-B,B]\times\{1,\ldots,K\}\times\{0,1\}`$, where $`B\in\mathbb R`$ and $`K\in\mathbb N`$. For every degree $`k`$ with $`p_k=P(D=k)\gt 0`$, assume


```math
E[Y\mid S=1,D=k]=E[Y\mid D=k],\qquad P(S=1\mid D=k)\gt 0,\qquad P(S=1\mid D=k)=c f_k,
```


for real $`c`$ and real profile $`f`$. No separate sign restrictions on $`c`$ or $`f`$ are assumed. Put $`\rho=P(S=1)`$, $`q_k=P(D=k\mid S=1)`$, $`m_k=E[Y\mid S=1,D=k]`$, and $`J=\{k:p_k\gt 0\}`$. Then $`\rho\gt 0`$, $`J=\{k:q_k\gt 0\}`$, and $`c\ne0`$. For every $`k\in J`$,


```math
c f_k\gt 0,\qquad f_k\ne0,\qquad p_k=\frac\rho c\frac{q_k}{f_k}.
```


Also,


```math
\sum_{k\in J}\frac{q_k}{f_k}=\frac c\rho\ne0,\qquad E_FY=\frac{\sum_{k\in J}m_k(q_k/f_k)}{\sum_{k\in J}q_k/f_k}.
```


All conditional means and probabilities are event-integral ratios, evaluated on the positive-mass cells used above.

**Use.** Gives inverse-inclusion identification when inclusion probabilities are known only up to an unknown common scale. Equality of within-degree means suffices; no full outcome–selection independence, network model or random-walk assumption is needed.

**Relation to Mathlib.** Mathlib v4.34.1 provides integration, finite sums and conditional-probability tools. This known-to-scale mean-identification theorem uses explicit event-integral ratios.

**Declaration:** [`AronowAudit.P021.proposition_one`](../AronowAudit/P021/P021_RDS.lean#L370)

```lean
import AronowAudit.P021.P021_RDS

#check AronowAudit.P021.proposition_one
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P021-T1](works/P021.md#p021-t1).

Related declarations:

- [`AronowAudit.P021.KnownSampling`](../AronowAudit/P021/P021_RDS.lean#L126): known-to-scale sampling assumption
- [`AronowAudit.P021.proposition_one_observed`](../AronowAudit/P021/P021_RDS.lean#L415): formula using the observed support
- [`AronowAudit.P021.population_mean_identified`](../AronowAudit/P021/P021_RDS.lean#L426): agreement across observationally equivalent laws

**Scope.** Bounded outcomes and finitely many positive integer degrees are part of the state space. Every sum uses the positive population degree support, which the theorem shows equals the observed support. The theorem does not require c and f separately to be positive and is an identification result rather than a finite-sample estimator guarantee.

### H049

**Finite-population central limit theorem without a sampling-fraction limit**

A maximum-deviation condition gives asymptotic normality of a sample mean under uniform fixed-size sampling.

Areas: Survey sampling, Asymptotic statistics, Randomization inference.

**Statement.** Let $`N_j`$ be strictly increasing natural population sizes. For each $`j`$, let $`D_j`$ be a population object with sample size $`m_j=(D_j).n1`$, assume $`N_j\ge2`$ and $`0\lt m_j\lt N_j`$, and let $`q_j:\mathrm{Fin}(N_j)\to\mathbb R`$ be any fixed array. Write


```math
\bar q_j=\frac1{N_j}\sum_iq_{ji},\qquad s_j^2=\frac1{N_j-1}\sum_i(q_{ji}-\bar q_j)^2,
```


and assume $`s_j^2\gt 0`$ for every $`j`$. If


```math
\frac{\max_i(q_{ji}-\bar q_j)^2}{\min(m_j,N_j-m_j)s_j^2}\longrightarrow0,
```


then for every real $`t`$,


```math
P_j\!\left(\frac{\bar q_{j,S}-\bar q_j}{\sqrt{(1/m_j-1/N_j)s_j^2}}\le t\right)\longrightarrow\Phi(t).
```


Here $`P_j`$ is uniform over all $`m_j`$-element subsets $`S`$ of the $`N_j`$ units, $`\bar q_{j,S}=m_j^{-1}\sum_{i\in S}q_{ji}`$, and $`\Phi`$ is the standard normal CDF. Both limits are as $`j\to\infty`$.

**Use.** Provides a Hájek finite-population CLT interface for sampling without replacement and design-based inference. It applies to arbitrary real triangular arrays and valid sampling fractions, including fractions approaching zero or one; no limiting sampling fraction is assumed.

**Relation to Mathlib.** Mathlib supplies probability and convergence infrastructure. This result transports the bundled StatLean combinatorial CLT from uniform permutations to uniform subsets; the local interface supplies centering, standardization and the maximum-deviation argument.

**Declaration:** [`AronowAudit.P002.Wave1.finitePopulationCLT`](../AronowAudit/P002/Wave1/Lib/FinitePopulationCLT.lean#L266)

```lean
import AronowAudit.P002.Wave1.Lib.FinitePopulationCLT

#check AronowAudit.P002.Wave1.finitePopulationCLT
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P002.Wave1.FPCLT_uniform`](../AronowAudit/P002/Wave1/Lib/FinitePopulationCLT.lean#L85): uniform permutation-to-subset law
- [`AronowAudit.P002.Wave1.FPCLT_standardize`](../AronowAudit/P002/Wave1/Lib/FinitePopulationCLT.lean#L222): standardization identity
- [`AronowAudit.P002.popVar`](../AronowAudit/P002/P002_Audit.lean#L56): finite-population variance convention

**Scope.** The conclusion is convergence of the standardized CDF at every real threshold. Strictly increasing population sizes, positive variance at every stage and nonempty sample and complement are explicit hypotheses. Only the sample-size field of the population object matters; no potential-outcome, compliance or covariate assumption is used.

### H050

**Central limit theorem for bounded-degree dependency graphs**

Uniformly bounded centered rows with bounded dependency degree and linearly growing sum variance have a normal limit.

Areas: Probability, Asymptotic statistics.

**Statement.** For each row size $`N`$, let $`\mu_N`$ be a probability measure on a measurable space $`\Omega_N`$ and $`V_{Ni}`$, $`0\le i\lt N`$, measurable real random variables with $`E_{\mu_N}V_{Ni}=0`$. Assume a common finite bound $`M`$ gives $`|V_{Ni}|\le M`$ almost surely for every $`N,i`$. Let $`B_{Ni}`$ be neighborhoods containing $`i`$, symmetric in $`i,j`$, with a common cardinality bound $`D`$. For any finite index sets $`I,J`$ with no cross edge, the whole vectors $`(V_{Ni})_{i\in I}`$ and $`(V_{Nj})_{j\in J}`$ must be independent.

Put $`S_N=\sum_iV_{Ni}`$ and $`s_N^2=E_{\mu_N}S_N^2`$. If some $`v\gt 0`$ satisfies $`s_N^2\ge vN`$ for all sufficiently large $`N`$, then for every real $`x`$,


```math
\mu_N\{S_N/\sqrt{s_N^2}\le x\}\longrightarrow\Phi(x)
```


as $`N\to\infty`$, where $`\Phi`$ is the standard normal distribution function. The conclusion is pointwise convergence of distribution functions.

**Use.** A normal approximation for graph-dependent sums on probability spaces that may vary by row. Identical distributions within rows are unnecessary.

**Relation to Mathlib.** Mathlib v4.34.1 supplies a scalar iid CLT in Probability/CentralLimitTheorem.lean, including ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum. This dependency-graph CLT uses the separately vendored Causalean Stein-method library.

**Declaration:** [`AronowAudit.P004.corrected_dependency_clt`](../AronowAudit/P004/P004_DependencyCompletion.lean#L18)

```lean
import AronowAudit.P004.P004_DependencyCompletion

#check AronowAudit.P004.corrected_dependency_clt
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P004-T20](works/P004.md#p004-t20).

Related declarations:

- [`AronowAudit.P004.DependencyGraph`](../AronowAudit/P004/P004_Spatial.lean#L1465): Whole-vector dependency condition
- [`AronowAudit.P004.Wave1.dependency_clt_counterexample_proof`](../AronowAudit/P004/Wave1/Gap/GP0041B3.lean#L582): Failure without adequate variance growth

**Scope.** The sum variance has an eventual linear lower bound. Summand bounds and closed-neighborhood cardinalities are uniform in row size. Pairwise independence alone does not satisfy the graph condition.

### H051

**External validity bound under changes in assignment law**

A transport bound controls how the expected average direct effect changes when the assignment law changes.

Areas: Interference and networks, Experimental design and estimation, Probability.

**Statement.** Fix $`n\gt 0`$ units and an experiment $`E`$ specifying an assignment law $`P`$ and real outcome functions $`y_i(z)`$ on the entire binary assignment cube. Keep these functions fixed and replace $`P`$ by any assignment law $`Q`$. Write $`\tau_i(z)=y_i(1,z_{-i})-y_i(0,z_{-i})`$ and $`\bar\tau(z)=n^{-1}\sum_i\tau_i(z)`$. Assume $`|\tau_i(z)|\le K`$ for every unit and assignment, and let $`r`$ be any real number with $`r\ge1`$.

Let $`c_i`$ count outcomes potentially affected by coordinate $`i`$, including the declared self-interference edge. Define $`C_q=(n^{-1}\sum_i c_i^q)^{1/q}`$ for $`q\gt 0`$, $`C_\infty=\max_i c_i`$, and interpret $`C_{r/(r-1)}`$ as $`C_\infty`$ when $`r=1`$. Let $`W_r(P,Q)`$ be the infimum, over couplings of $`P,Q`$, of expected ground distance $`\|z-z'\|_r`$. Then


```math
|E_P\bar\tau-E_Q\bar\tau|\le2K n^{-1/r}C_{r/(r-1)}W_r(P,Q).
```



**Use.** Quantifies sensitivity of an interference estimand to a change in assignment distribution, with the same full potential-outcome schedule. Both assignment laws may be arbitrary finite probability laws.

**Relation to Mathlib.** This development defines finite couplings and first-order transport with an assignment ground metric, and gives a finite Lipschitz transport bound with an interference-specific Lipschitz constant.

**Declaration:** [`AronowAudit.P009.external_validity_wasserstein`](../AronowAudit/P009/P009_TransportCompletion.lean#L171)

```lean
import AronowAudit.P009.P009_TransportCompletion

#check AronowAudit.P009.external_validity_wasserstein
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P009-T39](works/P009.md#p009-t39).

Related declarations:

- [`AronowAudit.P009.assignment_ATE_lipschitz`](../AronowAudit/P009/P009_TransportCompletion.lean#L163): Pointwise Lipschitz inequality
- [`AronowAudit.P009.wasserstein`](../AronowAudit/P009/P009_Audit.lean#L495): First-order transport with assignment ground metric
- [`AronowAudit.P009.ValidityCompletion.finite_transport_bound`](../AronowAudit/P009/P009_TransportCompletion.lean#L112): General finite Lipschitz transport bound

**Scope.** The Wasserstein order is one: the subscript specifies the ground metric, not an rth moment cost. The direct-effect bound covers the full assignment cube, including assignments of zero probability.

### H052

**Sharp always-passer mean bounds**

Trimmed observed passer means give attained bounds for outcomes among units who would pass in every arm.

Areas: Partial identification and bounds, Causal identification.

**Statement.** Let $`\mu`$ be a probability law of real potential outcomes, binary potential passing indicators, assignment to one of $`K`$ arms, and $`d`$ real covariates. Observed outcome and passing status are the assigned-arm coordinates. For each arm $`b`$, assume $`(Y(b),S(b))`$ is independent of assignment, the assignment arm has positive probability, and $`p_b=P(S=1\mid Z=b)\gt 0`$. Fix an arm $`a`$. Assume positive probability of the always-pass event $`A=\{S(b)=1\text{ for every }b\}`$, atomlessness of the conditional outcome law $`F_a`$ given $`S=1,Z=a`$, and integrability of observed $`Y`$ on that passing event. Define


```math
r_a=\frac{\sum_{b\ne a}(1-p_b)}{p_a},\qquad L=1-\sum_b(1-p_b),
```


and assume $`r_a\lt 1`$.

Let $`\ell_a`$ be the observed passer mean in arm $`a`$ at or below the $`1-r_a`$ quantile of $`F_a`$, and $`u_a`$ its mean at or above the $`r_a`$ quantile. Then $`\ell_a\le E[Y(a)\mid A]\le u_a`$. Both endpoints are attained by population laws satisfying the same per-arm assumptions, positive always-pass probability, and exactly the same joint observed law of $`(Y,S,Z)`$; every always-passer mean attainable under such laws lies between these endpoints.

The theorem also states $`p_a(1-r_a)=L`$, the equivalence $`r_a\lt 1\iff L\gt 0`$, and equality of both bounds to $`E[Y\mid S=1,Z=a]`$ when $`r_a=0`$. For the real quantile function $`Q_a`$ of $`F_a`$, it gives


```math
\ell_a=\frac{p_a}{L}\int_0^{L/p_a}Q_a(t)\,dt,\qquad u_a=\frac{p_a}{L}\int_{1-L/p_a}^{1}Q_a(t)\,dt.
```



**Use.** Provides validity, endpoint attainment, and quantile-integral formulas for selection bounds with finitely many arms. The compatible-law construction preserves the full observed outcome law, including failer outcomes.

**Relation to Mathlib.** Mathlib supplies CDF and integration infrastructure. The trimming and compatible-law constructions are local, and the quantile transport layer uses the bundled Causalean coupling library.

**Declaration:** [`AronowAudit.P010.Wave1.proposition_one_finite_proof`](../AronowAudit/P010/Wave1/PropositionOneFiniteTailC.lean#L336)

```lean
import AronowAudit.P010.Wave1.PropositionOneFiniteTailC

#check AronowAudit.P010.Wave1.proposition_one_finite_proof
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P010-T4](works/P010.md#p010-t4).

Related declarations:

- [`AronowAudit.P010.lowerBound`](../AronowAudit/P010/P010_Population.lean#L130): Lower trimmed passer mean
- [`AronowAudit.P010.upperBound`](../AronowAudit/P010/P010_Population.lean#L135): Upper trimmed passer mean
- [`AronowAudit.P010.identifiedMeans`](../AronowAudit/P010/P010_Population.lean#L149): Attainable means preserving the observed law

**Scope.** The finite-bound branch uses tail means conditional on passers. The assumption is per-arm pair ignorability, without joint-vector ignorability. The conclusion gives endpoint attainment and containment, without explicitly asserting attainment of every interior mean.

### H053

**OLS limit as a residual-weighted treatment effect**

Under explicit regularity conditions, the OLS treatment coefficient converges to an average effect weighted by squared treatment residuals.

Areas: Regression and variance estimation, Causal identification, Asymptotic statistics.

**Statement.** On a standard Borel probability space, let measurable tuples $`(D_i,Y_{0i},\tau_i,X_i)`$ be independent and identically distributed, with real $`D_i,Y_{0i},\tau_i`$ and $`X_i\in\mathbb R^K`$ for fixed $`K`$. Assume $`(Y_{00},\tau_0)`$ and $`D_0`$ are conditionally independent given $`X_0`$, and for some $`\omega\in\mathbb R^{K+1}`$,


```math
E[D_0\mid X_0]=(1,X_0)'\omega\quad\text{almost surely}.
```


Write $`V_i=(1,X_i)`$ and $`w=(D_0-E[D_0\mid X_0])^2`$. OLSRegularity requires integrability at every observation index and convergence in probability of sample averages to the observation-zero expectations for each of the eight moment families


```math
V_{ij}V_{ik},\quad V_{ij}D_i,\quad D_i^2,\quad D_iY_{0i},\quad V_{ij}Y_{0i},\quad D_i^2\tau_i,\quad V_{ij}D_i\tau_i,\quad V_{ij}V_{ik}\tau_i
```


for every control-coordinate pair $`j,k`$. It also requires $`\det E[V_0V_0']\ne0`$, integrability of $`w`$, and $`E[w]\gt 0`$.

For outcomes $`Y_i=Y_{0i}+\tau_iD_i`$, let $`\widehat\beta_n`$ be the treatment coordinate of matrix OLS with regressors $`(1,D_i,X_i)`$ and the first $`n`$ observations. Then


```math
\widehat\beta_n\xrightarrow{P}\frac{E[w\tau_0]}{E[w]}.
```


Lean states convergence in measure under the common probability law to this constant.

**Use.** Identifies the OLS limit under heterogeneous affine treatment effects. Treatment can be real-valued and the fixed finite-dimensional covariates need not have finite support.

**Relation to Mathlib.** Mathlib v4.34.1 supplies conditional expectations, conditional independence, matrix inverses and convergence in measure. This theorem combines them with explicit causal assumptions, moment laws of large numbers and OLS definitions.

**Declaration:** [`AronowAudit.P015.ols_weighted_effect_limit`](../AronowAudit/P015/P015_Regression.lean#L4974)

```lean
import AronowAudit.P015.P015_Regression

#check AronowAudit.P015.ols_weighted_effect_limit
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P015-T15](works/P015.md#p015-t15), [P015-T22](works/P015.md#p015-t22).

Related declarations:

- [`AronowAudit.P015.OLSRegularity`](../AronowAudit/P015/P015_Regression.lean#L1359): Exact moment and nonsingularity hypotheses
- [`AronowAudit.P015.populationWeight`](../AronowAudit/P015/P015_Regression.lean#L1312): Squared conditional treatment residual
- [`AronowAudit.P015.betaHat`](../AronowAudit/P015/P015_Regression.lean#L1306): Sample OLS treatment coefficient

**Scope.** The moment laws of large numbers are explicit assumptions of this declaration. The number of controls is fixed and outcomes follow the affine treatment model.

### H054

**Exact cluster-randomization Horvitz–Thompson variance**

The Horvitz–Thompson estimator has an exact design variance under complete randomization of clusters.

Areas: Experimental design and estimation, Survey sampling.

**Statement.** Consider $`M`$ clusters, positive fixed integer sizes $`n_j`$, arbitrary real potential totals $`T_{0j},T_{1j}`$, and a fixed treated count $`m_t`$ with $`0\lt m_t\lt M`$. Set $`m_c=M-m_t`$ and $`N=\sum_jn_j`$. Under uniform assignment to all $`m_t`$-subsets $`S`$ of clusters, define


```math
\widehat\tau_{HT}=\frac1N\left(\frac{M}{m_t}\sum_{j\in S}T_{1j}-\frac{M}{m_c}\sum_{j\notin S}T_{0j}\right).
```


Let $`\sigma_a^2=M^{-1}\sum_j(T_{aj}-\overline T_a)^2`$ and $`\sigma_{01}=M^{-1}\sum_j(T_{0j}-\overline T_0)(T_{1j}-\overline T_1)`$, using divisor $`M`$. The variance under this assignment law equals


```math
\mathrm{Var}(\widehat\tau_{HT})=\frac{M^2}{N^2}\left[\frac{M}{M-1}\left(\frac{\sigma_0^2}{m_c}+\frac{\sigma_1^2}{m_t}\right)+\frac{2\sigma_{01}-\sigma_0^2-\sigma_1^2}{M-1}\right].
```



**Use.** An exact finite-population identity for cluster experiments allowing unequal sizes and unrestricted real potential totals, useful for assessing conservative variance formulas.

**Relation to Mathlib.** Mathlib v4.34.1 supplies finite sums and basic measure and algebra tools. The fixed-size cluster design, Horvitz–Thompson estimator and exact design-variance calculation are defined and proved in this module.

**Declaration:** [`AronowAudit.P020.ht_design_variance_formula`](../AronowAudit/P020/P020_Design.lean#L1246)

```lean
import AronowAudit.P020.P020_Design

#check AronowAudit.P020.ht_design_variance_formula
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P020-T15](works/P020.md#p020-t15).

Related declarations:

- [`AronowAudit.P020.htVarianceFormula`](../AronowAudit/P020/P020_Design.lean#L880): Closed-form variance expression
- [`AronowAudit.P020.ht_unbiased`](../AronowAudit/P020/P020_Design.lean#L657): Exact design unbiasedness
- [`AronowAudit.P020.ht_variance_identity_bound`](../AronowAudit/P020/P020_Design.lean#L1478): Variance identity and conservative upper bound

**Scope.** The design is complete cluster randomization with fixed arm counts. The theorem concerns true design variance, not an estimated variance; an arm may contain only one cluster.

### H055

**Sharp bounded-outcome IV complier means**

Every feasible treated complier mean is attained by a randomized bounded-outcome IV model on four states.

Areas: Partial identification and bounds, Causal identification.

**Statement.** For real $`p,e_0,e_1`$ with $`0\lt p\le1`$, $`e_0,e_1\in[0,1]`$, and $`|e_1-e_0|\le p`$, put $`\delta=(e_1-e_0)/p`$ and


```math
\ell_1=\max\{0,\delta,1-(1-e_1)/p\},\qquad u_1=\min\{1,1+\delta,e_1/p\}.
```


For every $`x_1\in[\ell_1,u_1]`$, there exists a CausalModel on $`\mathrm{Bool}\times\mathrm{Bool}`$, a four-state space, with both potential outcomes in $`[0,1]`$ at every state, complier probability $`p`$, observed assignment-arm means $`E[Y\mid Z=0]=e_0`$, $`E[Y\mid Z=1]=e_1`$, and


```math
E[Y(1)\mid C]=x_1,\qquad E[Y(0)\mid C]=x_1-\delta.
```


The constructed model includes measurable integrable potential outcomes, a binary instrument with both arms positive, joint instrument independence from latent treatment stratum and both potential outcomes, monotone binary receipt, exclusion, consistency, and a nonzero first stage.

**Use.** Shows that bounds based only on the two assignment-arm outcome means and complier share cannot be tightened: every treated-mean value in the interval has a genuine causal probability model.

**Relation to Mathlib.** Mathlib supplies independence and Bernoulli infrastructure. The complier-mean sharpness theorem uses a local causal-model interface and an explicit four-state probability construction.

**Declaration:** [`AronowAudit.P028.proposition1_sharp`](../AronowAudit/P028/P028_Results.lean#L1108)

```lean
import AronowAudit.P028.P028_Results

#check AronowAudit.P028.proposition1_sharp
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P028-T8](works/P028.md#p028-t8).

Related declarations:

- [`AronowAudit.P028.proposition1_valid`](../AronowAudit/P028/P028_Results.lean#L1088): Universal validity and translated control interval
- [`AronowAudit.P028.lowerTreated`](../AronowAudit/P028/P028_Results.lean#L24): Treated complier lower endpoint
- [`AronowAudit.P028.upperTreated`](../AronowAudit/P028/P028_Results.lean#L28): Treated complier upper endpoint

**Scope.** Sharpness is relative to the summaries p, e0, and e1; it does not preserve a full observed distribution. Universal validity is the separate proposition1_valid theorem.

### H056

**LATE identity on general probability spaces**

Random assignment, exclusion, monotonicity, and a nonzero first stage identify the complier effect by the Wald ratio.

Areas: Causal identification.

**Statement.** Let $`\mu`$ be a probability law on an arbitrary measurable space, with covariates in any measurable space $`X`$. Each unit has covariates, binary potential receipts $`D(0),D(1)`$, and real potential outcomes $`Y(0),Y(1)`$; observed receipt is $`D=D(Z)`$ and observed outcome is $`Y=Y(D(Z))`$. Assume all covariate, receipt, outcome, and binary instrument coordinates are measurable, both potential outcomes are integrable, and $`Z`$ is independent of the joint vector of covariates and all potential receipts and outcomes. Also assume $`0\lt P(Z=1)\lt 1`$, zero probability of defiers $`D(0)=1,D(1)=0`$, and a nonzero observed first-stage difference $`\Delta_D=E[D\mid Z=1]-E[D\mid Z=0]`$.

For $`C=\{D(0)=0,D(1)=1\}`$, $`\tau=Y(1)-Y(0)`$, and $`\Delta_Y=E[Y\mid Z=1]-E[Y\mid Z=0]`$, the theorem gives all four identities


```math
\Delta_D=P(C),\qquad \Delta_Y=E[\mathbf1_C\tau],\qquad E[\mathbf1_C\tau]=P(C)E[\tau\mid C],\qquad E[\tau\mid C]=\frac{\Delta_Y}{\Delta_D}.
```


The last ratio is the population weighted-Wald definition evaluated at constant weight one.

**Use.** A measure-theoretic binary-instrument LATE identity with arbitrary measurable covariates and integrable outcomes, exposing the first-stage and reduced-form decompositions as well as the ratio.

**Relation to Mathlib.** Mathlib v4.34.1 supplies integration and independence on general probability spaces. This LATE identity uses the potential-response and population Wald interfaces defined in P029.

**Declaration:** [`AronowAudit.P029.Wave1.late_identity_paper_scope`](../AronowAudit/P029/Wave1/LateIdentity.lean#L18)

```lean
import AronowAudit.P029.Wave1.LateIdentity

#check AronowAudit.P029.Wave1.late_identity_paper_scope
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P029-T25](works/P029.md#p029-t25).

Related declarations:

- [`AronowAudit.P029.IVAssumptions`](../AronowAudit/P029/P029_Audit.lean#L414): Full measurable IV assumptions
- [`AronowAudit.P029.PotentialUnit`](../AronowAudit/P029/P029_Audit.lean#L27): Potential receipt and outcome representation
- [`AronowAudit.P029.mWald`](../AronowAudit/P029/P029_Audit.lean#L456): Population weighted Wald ratio

**Scope.** Exclusion and consistency are encoded in the potential-response definitions. Assignment is unconditionally independent of covariates and potentials. This is a population identification identity, not a sampling limit or an instrument theorem based only on conditional random assignment.

### H057

**Exact homoskedastic HC0 covariance shortfall**

Under zero-mean homoskedastic errors, expected HC0 falls below true OLS covariance by an explicit positive semidefinite matrix.

Areas: Regression and variance estimation.

**Statement.** Let $`X`$ be a fixed real $`n\times k`$ matrix with injective column map, $`\beta\in\mathbb R^k`$, and $`\sigma^2\ge0`$. On a probability space let each error coordinate $`u_i`$ and every product $`u_iu_j`$ be integrable, with $`E[u]=0`$ and $`E[u_iu_j]=\sigma^2\mathbf1\{i=j\}`$. Set $`y=X\beta+u`$, $`A=(X'X)^{-1}X'`$, $`H=XA`$, $`e=y-XAy`$, $`V=\mathrm{Cov}(Ay)`$, and $`\overline V=E[A\mathrm{diag}(e_i^2)A']`$ entrywise. The theorem states


```math
e=(I-H)u\quad\text{at every sample point},\qquad E[e_i^2]=\sigma^2(1-H_{ii})\quad\text{for every }i,
```




```math
V=\sigma^2AA'=\sigma^2(X'X)^{-1},\qquad \overline V=\sigma^2A\mathrm{diag}(1-H_{ii})A',
```




```math
V-\overline V=\sigma^2A\mathrm{diag}(H_{ii})A',\qquad t'(V-\overline V)t\ge0\quad\text{for every }t\in\mathbb R^k.
```



**Use.** Gives the exact finite-sample downward bias of uncorrected HC0 under a fixed-design homoskedastic benchmark, and its direction for every linear combination of coefficients.

**Relation to Mathlib.** Mathlib v4.34.1 supplies matrix rank, nonsingular inverses, and covariance infrastructure. This development supplies the OLS and sandwich identities used in the exact HC0 covariance shortfall.

**Declaration:** [`AronowAudit.P037.hc0_homoskedastic_shortfall`](../AronowAudit/P037/P037_Inference.lean#L418)

```lean
import AronowAudit.P037.P037_Inference

#check AronowAudit.P037.hc0_homoskedastic_shortfall
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P037-T18](works/P037.md#p037-t18).

Related declarations:

- [`AronowAudit.P037.schoolHC0`](../AronowAudit/P037/P037_Inference.lean#L42): Uncorrected HC0 matrix
- [`AronowAudit.P037.school_leverage_facts`](../AronowAudit/P037/P037_Inference.lean#L405): Projection and leverage properties
- [`AronowAudit.P037.hc0_row_bias_factor`](../AronowAudit/P037/P037_Inference.lean#L442): Scalar leverage-weighted expectation ratio

**Scope.** A fixed-design model-error benchmark, separate from the paper’s randomization interpretation. Independence and Gaussian errors are unnecessary: the specified moments suffice. Positive semidefiniteness does not assert a strictly positive shortfall.

### H058

**Residual-multiplier bootstrap covariance equals HC0**

Residual multipliers with zero means and identity second moments reproduce the HC0 covariance exactly.

Areas: Resampling, Regression and variance estimation.

**Statement.** Fix a real $`n\times k`$ design matrix $`X`$ with injective column map and an outcome vector $`y\in\mathbb R^n`$. Set $`A=(X'X)^{-1}X'`$, $`b=Ay`$, and $`e=y-Xb`$. Let $`v`$ be a random vector on any probability space, with each $`v_i`$ and every product $`v_iv_j`$ integrable, $`E[v]=0`$, and $`E[v_iv_j]=\mathbf1\{i=j\}`$. Define the bootstrap OLS coefficient by $`b^*=A(Xb+e\odot v)`$. Then at every sample point


```math
b^*=b+A(e\odot v),
```


and its mean and covariance under the multiplier law satisfy


```math
E[b^*]=b,\qquad \mathrm{Cov}(b^*)=A\mathrm{diag}(e_i^2)A'=\mathrm{HC0}(X,y).
```



**Use.** Connects the residual-multiplier bootstrap to uncorrected robust covariance for any fixed full-column-rank design. The multiplier coordinates need not be independent or identically distributed.

**Relation to Mathlib.** Mathlib supplies integration and linear algebra. The residual-multiplier coefficients, HC0 matrix and exact covariance identity are defined here.

**Declaration:** [`AronowAudit.P037.wild_bootstrap_is_hc0`](../AronowAudit/P037/P037_Inference.lean#L387)

```lean
import AronowAudit.P037.P037_Inference

#check AronowAudit.P037.wild_bootstrap_is_hc0
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P037-T18](works/P037.md#p037-t18).

Related declarations:

- [`AronowAudit.P037.schoolOLSMap`](../AronowAudit/P037/P037_Inference.lean#L27): Fixed-design OLS coefficient map
- [`AronowAudit.P037.schoolHC0`](../AronowAudit/P037/P037_Inference.lean#L42): HC0 covariance definition
- [`AronowAudit.P037.hc0_homoskedastic_shortfall`](../AronowAudit/P037/P037_Inference.lean#L418): Related finite-sample HC0 shortfall

**Scope.** X and y are fixed and expectation is over the multiplier law. The theorem identifies covariance; it supplies no bootstrap calibration, coverage, or exact test-size guarantee.

### H059

**Multilevel IV margin decomposition**

With monotone bounded integer treatment, the IV ratio is a convex average of effects at crossed treatment margins.

Areas: Causal identification.

**Statement.** Let $`P`$ be a probability mass function on a finite type space, $`0\lt p\lt 1`$ an independent Bernoulli assignment probability, and an IVModel specify natural-number potential doses $`K_i(0),K_i(1)\in\mathbb N`$ and real responses $`Y_i(k)`$ for $`k\in\mathbb N`$. Fix $`J\in\mathbb N`$. Observed dose and outcome are $`K_i(Z)`$ and $`Y_i(K_i(Z))`$, encoding consistency and exclusion. Assume for every type $`i`$ that both doses are at most $`J`$ and $`K_i(0)\le K_i(1)`$, and assume $`E_P[K(1)-K(0)]\gt 0`$.

Let $`\Delta_K,\Delta_Y`$ be the observed dose and outcome assignment-arm mean differences under the product assignment/type law. For each integer margin $`j\ge0`$, set $`q_j=P(K(0)\lt j\le K(1))`$ and $`w_j=q_j/\Delta_K`$. Then $`w_j\ge0`$ for every $`j`$, $`\sum_{j=1}^Jw_j=1`$, and


```math
\frac{\Delta_Y}{\Delta_K}=\sum_{\substack{1\le j\le J\\q_j\gt 0}}w_jE_P[Y(j)-Y(j-1)\mid K(0)\lt j\le K(1)].
```



**Use.** A finite-population IV interpretation for bounded integer doses, separating margin-crossing probabilities from average causal increments among units crossing each margin.

**Relation to Mathlib.** The margin decomposition uses finite weighted sums and telescoping identities over Mathlib algebra, with explicit definitions of the population law, potential doses and responses, assignment-arm contrasts and margin effects.

**Declaration:** [`AronowAudit.P043.corrected_multilevel_iv`](../AronowAudit/P043/P043_Formalization.lean#L1127)

```lean
import AronowAudit.P043.P043_Formalization

#check AronowAudit.P043.corrected_multilevel_iv
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P043.IVMarginAverageClaims`](../AronowAudit/P043/P043_Formalization.lean#L1120): Nonnegative weights and margin-average formula
- [`AronowAudit.P043.marginEffect`](../AronowAudit/P043/P043_Formalization.lean#L906): Conditional causal increment at a margin
- [`AronowAudit.P043.iv_repair`](../AronowAudit/P043/P043_Formalization.lean#L1152): population contrasts, covariance equivalence, monotone margins and signed formulas

**Scope.** Population support is finite, doses are bounded natural numbers, and dose monotonicity is pointwise; response increments may have either sign. Companion results give signed representations without monotonicity.

### H060

**Known-propensity finite-sample IPW guarantees**

Known propensity scores and fixed boundedness and overlap constants give unbiased IPW estimates and finite-sample concentration intervals.

Areas: Causal identification, Asymptotic statistics.

**Statement.** Let a CausalLaw be a probability law of a real covariate $`W`$, binary treatment $`A`$, and real potential outcomes $`Y(0),Y(1)`$, with a supplied measurable propensity $`e(W)`$. Its ignorability condition states, for each arm $`a`$ and every measurable integrable test function $`f(Y(a))`$, that $`E[\mathbf1\{A=a\}f(Y(a))\mid W]=p_a(W)E[f(Y(a))\mid W]`$, where $`p_1=e`$ and $`p_0=1-e`$. Assume $`B\gt 0`$, $`0\lt \varepsilon\le1/2`$, $`|Y(a)|\le B`$ for both arms almost surely, and $`\varepsilon\le e(W)\le1-\varepsilon`$ almost surely. With observed $`Y=Y(A)`$ define


```math
S=\frac{AY}{e(W)}-\frac{(1-A)Y}{1-e(W)},\qquad\tau=E[Y(1)-Y(0)].
```


The theorem gives $`E[S\mid W]=E[Y(1)-Y(0)\mid W]`$ almost surely, $`E[S]=\tau`$, and $`|S|\le B/\varepsilon`$ almost surely. For every integer $`n\ge1`$, under iid product sampling the mean $`T_n=n^{-1}\sum_{i=1}^nS_i`$ is unbiased, and for every $`t\ge0`$,


```math
P\{|T_n-\tau|\ge t\}\le2\exp\left(-\frac{nt^2\varepsilon^2}{2B^2}\right).
```


For every $`0\lt \alpha\lt 1`$, set $`h_n=(B/\varepsilon)\sqrt{2\log(2/\alpha)/n}`$. The interval $`[T_n-h_n,T_n+h_n]`$ has coverage at least $`1-\alpha`$, with exact width identity


```math
\sqrt n\,(2h_n)=\frac{2B}{\varepsilon}\sqrt{2\log(2/\alpha)}.
```



**Use.** Provides identification, finite-sample unbiasedness, a uniform tail bound, and an explicit concentration interval for every law sharing the known constants. No smoothness restriction on the covariate distribution or response functions is imposed.

**Relation to Mathlib.** Mathlib v4.34.1 supplies Hoeffding’s lemma and independent sub-Gaussian sum bounds in Probability/Moments/SubGaussian.lean, plus conditional expectation and infinite-product sampling infrastructure. This declaration adds the causal IPW score identity and assembles those tools into estimator and interval guarantees.

**Declaration:** [`AronowAudit.P047.known_propensity_finite_sample`](../AronowAudit/P047/P047_Identification.lean#L544)

```lean
import AronowAudit.P047.P047_Identification

#check AronowAudit.P047.known_propensity_finite_sample
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P047-T1](works/P047.md#p047-t1).

Related declarations:

- [`AronowAudit.P047.BoundedOverlap`](../AronowAudit/P047/P047_Identification.lean#L80): Known boundedness and overlap contract
- [`AronowAudit.P047.confidenceInterval`](../AronowAudit/P047/P047_Identification.lean#L126): Explicit concentration interval
- [`AronowAudit.P047.treated_mean_finite_sample`](../AronowAudit/P047/P047_Identification.lean#L577): One-potential-outcome mean variant

**Scope.** The propensity and common positive boundedness and overlap constants are supplied. The result uses iid sampling and one real covariate, without estimated propensity scores or vanishing overlap.

### H061

**Mean square remainder bound for a finite-law ratio estimator**

A conditional sample mean has a controlled linearization remainder even when empty samples receive a fixed completion.

Areas: Asymptotic statistics, Probability.

**Statement.** Let $`P`$ be any probability mass function on a finite type, $`f`$ any real function, and $`D`$ an event with $`p=P(D)\gt 0`$. Fix any real completion $`c`$. For $`n`$ independent draws from $`P`$, let $`R_n`$ be the average of $`f`$ among draws in $`D`$, with $`R_n=c`$ when none falls in $`D`$. Put $`m=E_P[f\mathbf{1}_D]/p`$ and $`u=(f-m)\mathbf{1}_D`$, and let $`\bar u_n`$ be its sample average. There exist nonnegative finite constants $`C_2,C_4`$ such that, for every integer $`n\gt 0`$,


```math
E[(R_n-m-\bar u_n/p)^2]\le C_2/n^2,\qquad E[(R_n-m)^4]\le C_4/n^2.
```


Expectations use the finite product law $`P^{\otimes n}`$; the constants may depend on $`P,f,D,c`$ but are uniform in $`n`$.

**Use.** Provides moment control for linearizing cell means and ratio estimators, including their behavior on empty cells. It applies to every real outcome function on a finite probability space without additional moment assumptions.

**Relation to Mathlib.** Mathlib supplies finite sums and real-moment inequalities. The ratio estimator and its product-law moment bounds use local finite-law definitions.

**Declaration:** [`AronowAudit.P019.Wave1.GP019B2b_t18_ratio_L2`](../AronowAudit/P019/Wave1/Gap/GP019B2b.lean#L358)

```lean
import AronowAudit.P019.Wave1.Gap.GP019B2b

#check AronowAudit.P019.Wave1.GP019B2b_t18_ratio_L2
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P019.Wave1.GP019B2b_t18_ratio`](../AronowAudit/P019/Wave1/Gap/GP019B2b.lean#L297): ratio estimator and empty-cell completion
- [`AronowAudit.P019.Wave1.GP019B2b_t18_MomentBound`](../AronowAudit/P019/Wave1/Gap/GP019B2b.lean#L161): uniform moment-rate predicate
- [`AronowAudit.P019.Wave1.proposition_one_variance_limit_proof`](../AronowAudit/P019/Wave1/Gap/GP019B2b.lean#L671): application to asymptotic variance

**Scope.** Finite probability spaces only. The positive cell probability and the completion are fixed as sample size grows; the constants are not uniform over shrinking cells or changing completions.

### H062

**Uniform score error bounds decision regret**

Uniform score approximation controls the welfare regret of any score maximizer.

Areas: Optimization and computation.

**Statement.** For any type of choices $`P`$, feasible set $`\Pi\subseteq P`$, real-valued scores $`S,V`$, choices $`b,s`$, and real $`\gamma`$, suppose $`b\in\Pi`$ maximizes $`S`$ over $`\Pi`$, $`s\in\Pi`$ maximizes $`V`$ over $`\Pi`$, and $`\lvert S(\pi)-V(\pi)\rvert\le\gamma`$ for every $`\pi\in\Pi`$. Then


```math
\mathrm{regret}(\Pi,V,b)=\sup_{\pi\in\Pi}V(\pi)-V(b)\le2\gamma.
```


Both maximizing choices are hypotheses; ties are allowed. The theorem has no separate nonnegativity assumption on $`\gamma`$.

**Use.** Turns a uniform approximation guarantee into a decision-quality guarantee. It is a deterministic inequality on arbitrary feasible sets, so it can be used for policy selection or any score-based optimization once maximizers and the error bound are available.

**Relation to Mathlib.** This is an elementary consequence of maximizer inequalities and real order. Mathlib v4.34.1 supplies the order and supremum tools used to express the attained optimum and regret.

**Declaration:** [`AronowAudit.P006.uniform_error_regret`](../AronowAudit/P006/P006_CounterfactualMetrics.lean#L777)

```lean
import AronowAudit.P006.P006_CounterfactualMetrics

#check AronowAudit.P006.uniform_error_regret
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P006-T8](works/P006.md#p006-t8).

Related declarations:

- [`AronowAudit.P006.IsBest`](../AronowAudit/P006/P006_CounterfactualMetrics.lean#L58): maximizer predicate
- [`AronowAudit.P006.regret`](../AronowAudit/P006/P006_CounterfactualMetrics.lean#L69): regret definition
- [`AronowAudit.P006.bestValue_eq`](../AronowAudit/P006/P006_CounterfactualMetrics.lean#L391): supremum equals an attained best value

**Scope.** The theorem assumes an attained welfare maximum as well as an attained score maximum. It does not establish a uniform statistical error bound or existence of optimizers.

### H063

**Outcome-share sharpness and integer-population attainment**

Outcome shares give sharp mean bounds whose finite-population attainment is characterized by rational proportions.

Areas: Partial identification and bounds, Survey sampling.

**Statement.** Let $`J\gt 0`$, let the real outcomes $`y_j`$ be strictly increasing on $`\mathrm{Fin}(J)`$, and let $`q_j\gt 0`$ with $`\sum_jq_j=1`$. Assume $`0\lt \alpha\le\beta\le1`$ and at least one compatible vector of integer class sizes exists. Here compatibility means $`m_j\in\mathbb N`$, $`m_j\gt 0`$, and there is $`T\gt 0`$ such that $`\alpha m_j\le Tq_j\le\beta m_j`$ for every $`j`$.

Let $`\mathcal M`$ be the set of means $`\sum_jm_jy_j/\sum_jm_j`$ of these compatible populations. Let $`L,U`$ be the infimum and supremum of $`\sum_jq_jW_jy_j/\sum_jq_jW_j`$ over $`1/\beta\le W_j\le1/\alpha`$. Define $`\gamma=\beta/\alpha`$ and


```math
\mathcal C_\gamma(q)=\{r:r_j\ge0,\ \sum_jr_j=1,\ r_jq_k\le\gamma r_kq_j\text{ for all }j,k\}.
```


The theorem states all of the following: $`L`$ is the greatest lower bound of $`\mathcal M`$ and $`U`$ its least upper bound; the image of the weight box under $`r_j=W_jq_j/\sum_kW_kq_k`$ equals $`\mathcal C_\gamma(q)`$; a vector $`r`$ equals the class proportions $`m_j/\sum_km_k`$ of some compatible integer population if and only if $`r\in\mathcal C_\gamma(q)`$ and every coordinate of $`r`$ is rational; and each endpoint $`E\in\{L,U\}`$ belongs to $`\mathcal M`$ if and only if some rational-coordinate $`r\in\mathcal C_\gamma(q)`$ satisfies $`\sum_jr_jy_j=E`$.

**Use.** Separates sharp bounds based on normalized outcome shares from exact endpoint attainment by a finite population. It characterizes when continuous weight optimization gives an infimum or supremum that no compatible integer population attains.

**Relation to Mathlib.** Mathlib v4.34.1 provides rational density (Rat.isDenseEmbedding_coe_real) and order-theoretic extrema. This result gives the statistical compatibility and rational-attainment characterization for weighted-mean endpoints.

**Declaration:** [`AronowAudit.P025.shares_sharpness_and_attainment`](../AronowAudit/P025/P025_Interval.lean#L3296)

```lean
import AronowAudit.P025.P025_Interval

#check AronowAudit.P025.shares_sharpness_and_attainment
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P025-T15](works/P025.md#p025-t15).

Related declarations:

- [`AronowAudit.P025.sharesCompatible`](../AronowAudit/P025/P025_Interval.lean#L1746): integer population compatibility
- [`AronowAudit.P025.compatible_proportions_iff_rational_region`](../AronowAudit/P025/P025_Interval.lean#L3079): rational-proportion characterization
- [`AronowAudit.P025.shares_sharp_endpoints`](../AronowAudit/P025/P025_Interval.lean#L3269): sharp infimum and supremum

**Scope.** Only normalized shares are retained; the absolute scale and population size are unrestricted. Endpoint attainment is conditional on the rational-coordinate criterion, and compatibility nonemptiness is an explicit hypothesis, including when alpha equals beta.

### H064

**Sharp enclosing interval for network homophily**

Compatible network completions have explicit sharp homophily endpoints attained by private-leaf constructions.

Areas: Interference and networks, Partial identification and bounds.

**Statement.** Let $`D`$ be finite recruitment data whose seeds are sampled, whose sampled entry times are distinct, whose every nonseed has a sampled earlier recruiter, and whose observed degrees dominate recruitment degrees. Assume the sum of observed degrees among sampled vertices is strictly positive separately for each binary trait. Compatibility requires a finite simple undirected augmented graph preserving sampled vertices and traits, recruitment edges and exact sampled degrees; every unobserved vertex has a sampled neighbor, and every edge touches a sampled vertex.

Write $`a,b,c_R`$ for the recruitment graph’s trait-one, trait-zero and mixed edge counts; $`s_1,s_0`$ for spare observed degrees in the two trait groups; and $`s=s_0+s_1`$. Define $`\phi(x,y,c)=1-c/(2x+c)-c/(2y+c)`$, $`L=\phi(a,b,c_R+s)`$ and $`U=\phi(a+s_1,b+s_0,c_R)`$. For every compatible graph $`H`$, with counts $`x=e_{11}(H),y=e_{00}(H),c=e_{01}(H)`$, the theorem gives


```math
\mathrm{hDenominator}(H)=\frac{(2x+c)(2y+c)}{2(x+y+c)}\gt 0,\qquad h(H)=\phi(x,y,c),
```




```math
a\le x\le a+s_1,\quad b\le y\le b+s_0,\quad c_R\le c\le c_R+s,\quad L\le h(H)\le U.
```


Attaching one private leaf for each spare degree, with the opposite trait, gives a compatible graph with homophily $`L`$; attaching leaves of the same trait gives one with homophily $`U`$. Finally, homophily is defined on every compatible graph, and $`L,U`$ are respectively the least and greatest compatible values. Thus $`[L,U]`$ is the smallest closed interval containing them.

**Use.** Computes sharp enclosing homophily bounds from recruitment links, traits and observed degrees without knowing the unsampled network. Explicit leaf completions certify both endpoints under the development’s augmented-graph model.

**Relation to Mathlib.** Mathlib supplies finite graph, finite-set and real-algebra tools. The recruitment observation model, compatibility predicate and endpoint constructions are defined here.

**Declaration:** [`AronowAudit.P012.exact_h_region`](../AronowAudit/P012/P012_Identification.lean#L2774)

```lean
import AronowAudit.P012.P012_Identification

#check AronowAudit.P012.exact_h_region
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P012-T6](works/P012.md#p012-t6).

Related declarations:

- [`AronowAudit.P012.Compatible`](../AronowAudit/P012/P012_Identification.lean#L119): allowed network completions
- [`AronowAudit.P012.FullHomophilyRegion`](../AronowAudit/P012/P012_Identification.lean#L243): definedness and least/greatest values
- [`AronowAudit.P012.leafCompletion`](../AronowAudit/P012/P012_Identification.lean#L264): endpoint-attaining construction

**Scope.** Homophily uses the formula stated above. The region is defined as the smallest enclosing interval; the theorem does not assert that every value between the endpoints is attained.

### H065

**Student quantiles converge to normal quantiles**

Every fixed interior Student quantile converges to its standard normal counterpart as real degrees of freedom increase.

Areas: Probability, Asymptotic statistics.

**Statement.** For every real $`a`$ with $`0\lt a\lt 1`$,


```math
\lim_{\nu\to+\infty,\ \nu\in\mathbb R}q_\nu(a)=q_N(a).
```


Here $`q_\nu(a)=\inf\{x:a\le F_\nu(x)\}`$, where $`F_\nu(x)=\int_{-\infty}^x f_\nu(t)\,dt`$ and, for positive degrees of freedom, $`f_\nu(t)=\Gamma((\nu+1)/2)[\sqrt{\nu\pi}\Gamma(\nu/2)]^{-1}(1+t^2/\nu)^{-(\nu+1)/2}`$ is the Student density. The normal quantile $`q_N(a)`$ is the same generalized-inverse construction for the actual standard Gaussian CDF. The conclusion is ordinary real convergence along the filter of real degrees of freedom tending to infinity.

**Use.** Justifies replacing fixed Student critical values by Gaussian ones when degrees of freedom diverge, including noninteger degrees of freedom. It supplies a quantile step after convergence of the integral Student CDF.

**Relation to Mathlib.** Mathlib v4.34.1 provides the Gaussian measure, CDF and Gamma-function tools. This theorem uses a locally defined Student density, its integral CDF and its generalized inverse.

**Declaration:** [`AronowAudit.P004.Wave1.t7_student_quantile_normal`](../AronowAudit/P004/Wave1/Gap/GLP0042B5.lean#L1793)

```lean
import AronowAudit.P004.Wave1.Gap.GLP0042B5

#check AronowAudit.P004.Wave1.t7_student_quantile_normal
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P004.studentQuantile`](../AronowAudit/P004/P004_Spatial.lean#L1884): integral-CDF quantile definition
- [`AronowAudit.P004.normalQuantile`](../AronowAudit/P004/P004_Spatial.lean#L204): standard Gaussian quantile definition
- [`AronowAudit.P004.Wave1.t7_student_cdf_tendsto`](../AronowAudit/P004/Wave1/Gap/GLP0042B5.lean#L1751): pointwise Student CDF convergence

**Scope.** The quantile level is fixed and strictly between zero and one. This is not a uniform-in-level assertion or a rate of convergence.

### H066

**Pointwise consistency of a rectangular density estimator**

The rectangular kernel density estimator is pointwise consistent under continuous density and standard bandwidth conditions.

Areas: Asymptotic statistics, Probability.

**Statement.** On any probability space $`(\Omega,\mu)`$, let $`(X_i)_{i\ge0}`$ be measurable, mutually independent and identically distributed real random variables. Suppose their common law has a density $`f`$ in the development’s `HasPDF` sense: $`f`$ is Lebesgue almost-everywhere measurable, everywhere nonnegative and integrable, and the law equals Lebesgue measure weighted by $`f`$. Assume $`f`$ is continuous on all of $`\mathbb R`$. Let $`h_n\gt 0`$ for every natural $`n`$, $`h_n\to0`$ and $`nh_n\to+\infty`$.

For every fixed $`x\in\mathbb R`$, the rectangular estimator


```math
\widehat f_n(x)=\frac1{2nh_n}\sum_{i=0}^{n-1}\mathbf{1}\{\lvert x-X_i\rvert\le h_n\}
```


converges in probability to $`f(x)`$: for every $`\varepsilon\gt 0`$, $`\mu\{\lvert\widehat f_n(x)-f(x)\rvert\ge\varepsilon\}\to0`$ as $`n\to\infty`$.

**Use.** A complete pointwise density-consistency interface for the rectangular kernel, requiring neither bounded outcomes nor moments of the observations. Its proof combines finite-sample indicator moments with local CDF differentiation and vanishing variance.

**Relation to Mathlib.** Mathlib v4.34.1 supplies independence, variance identities and Chebyshev’s inequality, including ProbabilityTheory.meas_ge_le_variance_div_sq. This declaration assembles those tools for the rectangular density estimator and the local convergence-in-probability predicate.

**Declaration:** [`AronowAudit.P001.rectangular_kernel_consistency`](../AronowAudit/P001/P001_Foundations.lean#L4312)

```lean
import AronowAudit.P001.P001_Foundations

#check AronowAudit.P001.rectangular_kernel_consistency
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P001-T127](works/P001.md#p001-t127).

Related declarations:

- [`AronowAudit.P001.rectangular_kernel_moments_core`](../AronowAudit/P001/P001_Foundations.lean#L4176): exact expectation and variance
- [`AronowAudit.P001.kernelDensity`](../AronowAudit/P001/P001_Foundations.lean#L405): kernel estimator definition
- [`AronowAudit.P001.CP`](../AronowAudit/P001/P001_Foundations.lean#L60): convergence-in-probability predicate

**Scope.** The signature assumes global continuity of the density, although the conclusion is pointwise at each fixed location. It gives neither uniform consistency nor almost-sure convergence; the kernel is specifically rectangular.

### H067

**Exact unbiasedness of debiased noninteracted regression adjustment**

The specified bias correction makes noninteracted regression adjustment exactly unbiased under complete randomization.

Areas: Experimental design and estimation, Regression and variance estimation.

**Statement.** Fix a population of $`n\ge3`$ units, $`d`$ real covariates and two arbitrary real potential-outcome arrays. Choose $`0\lt m\lt n`$ treated units uniformly among all size-$`m`$ subsets. Suppose covariates are standardized: their population mean is zero and their Gram matrix $`n^{-1}\sum_i x_ix_i^\mathsf T`$ is the identity. For every possible assignment $`S`$, assume the pooled within-arm matrix


```math
\widehat L_S=I-p_T\bar x_S\bar x_S^\mathsf T-p_C\bar x_{S^c}\bar x_{S^c}^\mathsf T
```


has nonzero determinant, where $`p_T=m/n`$ and $`p_C=(n-m)/n`$. Let $`\widehat N_S=p_T\widehat{\mathrm{Cov}}_S(x,y_T)+p_C\widehat{\mathrm{Cov}}_{S^c}(x,y_C)`$, using covariances divided by arm size, and $`\widehat\beta_S=\widehat L_S^{-1}\widehat N_S`$. Define $`\widehat\tau_S=\bar y_{T,S}-\bar y_{C,S^c}-(\bar x_S-\bar x_{S^c})^\mathsf T\widehat\beta_S`$ and the source’s correction


```math
\widehat B_S=\frac{\widehat{\mathrm{Cov}}_{S^c}(h,y_C)-\widehat{\mathrm{Cov}}_S(h,y_T)}{n-2}+(\bar x_{S^c}-\bar x_S)^\mathsf T(\widehat L_S^{-1}-I)\widehat N_S,
\qquad h_i=x_i^\mathsf T x_i.
```


Writing $`\tau=\bar y_T-\bar y_C`$, the two conclusions are $`E[\widehat B]=E[\widehat\tau]-\tau`$ and $`E[\widehat\tau-\widehat B]=\tau`$, with expectations over the uniform fixed-size design.

**Use.** Gives exact design-based bias estimation and unbiasedness for the specified noninteracted regression correction. It is finite-sample and allows arbitrary fixed potential outcomes, subject to standardization and invertibility under every assignment.

**Relation to Mathlib.** Mathlib supplies finite sums and nonsingular matrix inverses. The estimator, uniform randomization expectation and algebraic bias correction are local definitions.

**Declaration:** [`AronowAudit.P005.Wave1.noninteracted_exact_unbiasedness_proof`](../AronowAudit/P005/Wave1/Gap/GP005B3b.lean#L151)

```lean
import AronowAudit.P005.Wave1.Gap.GP005B3b

#check AronowAudit.P005.Wave1.noninteracted_exact_unbiasedness_proof
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P005-T21](works/P005.md#p005-t21).

Related declarations:

- [`AronowAudit.P005.biasEstimate`](../AronowAudit/P005/P005_Formalization.lean#L256): specified finite-sample correction
- [`AronowAudit.P005.noninteractedRegular`](../AronowAudit/P005/P005_Formalization.lean#L213): assignmentwise invertibility condition
- [`AronowAudit.P005.Wave1.GP005B3b_T21_inverse_free_identity`](../AronowAudit/P005/Wave1/Gap/GP005B3b.lean#L113): pointwise cancellation identity

**Scope.** Invertibility must hold for every size-m assignment, not merely with high probability. This result concerns the noninteracted estimator; the interacted estimator has a separate exact-unbiasedness theorem.

### H068

**Conditional remainder rate for interacted regression adjustment**

An explicit row-sampling theorem hypothesis yields a remainder rate for interacted regression adjustment with growing covariate dimension.

Areas: Asymptotic statistics, Experimental design and estimation, Regression and variance estimation.

**Statement.** Assume the published row-sampling proposition `AronowAudit.Literature.Tropp2011RowSampling`. Let $`d_n,m_n`$ be natural-valued sequences and $`P_n`$ fixed populations of size $`n`$ with $`d_n`$ covariates and two real potential-outcome arrays. For every $`n\ge3`$, assume $`1\le d_n\le n`$ and $`0\lt m_n\lt n`$. Assume one constant $`K\ge0`$ bounds the population second moments of both outcome arrays and of each covariate coordinate for all $`n\ge3`$. Covariates are eventually standardized to mean zero and Gram matrix identity. Assume constants $`0\lt \ell\lt u\lt 1`$ satisfy $`\ell\lt m_n/n\lt u`$ for all $`n\ge3`$. Eventually, both centered within-arm Gram matrices have nonzero determinant under every size-$`m_n`$ assignment. Finally, with $`\kappa_n=\max_i\|x_{ni}\|_2^2/n`$, assume


```math
\kappa_n\log(\max\{d_n,2\})\longrightarrow0.
```


Let $`\widehat\tau_{I,n}`$ be the interacted estimator using separate within-arm slopes, and $`\tau_n`$ the population average effect. For each arm $`t`$, form the population residual $`e_{ni}(t)=y_{ni}(t)-\bar y_n(t)-x_{ni}^\mathsf T\beta_n(t)`$ with $`\beta_n(t)=n^{-1}\sum_i y_{ni}(t)x_{ni}`$; let $`A_n`$ be the treated mean of $`e_n(1)`$ minus the control mean of $`e_n(0)`$. Then


```math
\widehat\tau_{I,n}-\tau_n-A_n=O_p\!\left(\sqrt{\kappa_n d_n/n}\right).
```


Precisely, for every $`\varepsilon\gt 0`$ there exist $`M\gt 0`$ and $`n_0`$ such that, for all $`n\ge n_0`$, uniform size-$`m_n`$ randomization assigns probability less than $`\varepsilon`$ to the event that the absolute remainder exceeds $`M\sqrt{\kappa_n d_n/n}`$.

**Use.** Supplies the interacted-regression expansion in a growing-dimensional finite-population design. It isolates the published concentration input needed to control the random arm Gram matrices.

**Relation to Mathlib.** Mathlib v4.34.1 supplies finite-dimensional matrix and probability tools. This interacted-regression expansion takes the full Tropp row-sampling singular-value tail proposition as an explicit hypothesis.

**Declaration:** [`AronowAudit.P005.Wave1.corrected_interacted_expansion_max_conditional`](../AronowAudit/P005/Wave1/Cond/CondP005T8T9Proofs.lean#L709)

```lean
import AronowAudit.P005.Wave1.Cond.CondP005T8T9Proofs

#check AronowAudit.P005.Wave1.corrected_interacted_expansion_max_conditional
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P005-T8](works/P005.md#p005-t8).

Related declarations:

- [`AronowAudit.Literature.Tropp2011RowSampling`](../AronowAudit/Literature/CondP002P005P006.lean#L78): published concentration premise
- [`AronowAudit.P005.standingAssumptions`](../AronowAudit/P005/P005_Formalization.lean#L320): sequence regularity conditions
- [`AronowAudit.P005.Wave1.corrected_interacted_expansion_two_conditional`](../AronowAudit/P005/Wave1/Cond/CondP005T8T9Proofs.lean#L797): companion logarithmic condition

**Conditional on:** AronowAudit.Literature.Tropp2011RowSampling Source: J. A. Tropp, “Improved Analysis of the Subsampled Randomized Hadamard Transform,” Advances in Adaptive Data Analysis 3(1–2) (2011), 115–126, Lemma 3.4. The full row-sampling singular-value tail proposition is defined in AronowAudit/Literature/CondP002P005P006.lean.

**Scope.** The expansion is conditional on the Tropp row-sampling singular-value tail proposition. Its conclusion is stochastic boundedness at the stated scale, not a central limit theorem.

### H069

**Conditional exponential representation of Bayesian bootstrap weights**

Normalized independent exponential weights have the Bayesian bootstrap law conditional on a general gamma–Dirichlet theorem.

Areas: Resampling, Probability.

**Statement.** Assume `AronowAudit.Literature.DevroyeGammaDirichlet` at universe zero, the development’s general gamma–Dirichlet proposition. For every natural $`n`$, let $`W_0,\ldots,W_{n+1}`$ be independent exponential variables of rate one. Then the joint law of $`P_i=W_i/\sum_jW_j`$, for all $`n+2`$ coordinates, equals `bayesianBootstrapLaw (n+1)`.

The latter law is defined by taking $`(n+1)!`$ times Lebesgue measure on the open simplex $`\{p\in\mathbb R^{n+1}:p_i\gt 0,\ \sum_i p_i\lt 1\}`$ and appending the final coordinate $`1-\sum_i p_i`$. Thus the conclusion is equality of measures on all $`n+2`$ weights, namely the Dirichlet law with every parameter equal to one.

**Use.** Gives a precise distributional justification for generating Bayesian-bootstrap weights by normalizing independent exponentials. The application is finite-dimensional and holds for every number of weights at least two.

**Relation to Mathlib.** Mathlib v4.34.1 provides ProbabilityTheory.expMeasure, gammaMeasure and product-measure independence. This declaration assumes the general gamma–Dirichlet theorem and gives its specialization to the project’s simplex measure.

**Declaration:** [`AronowAudit.P037.Wave1.exponentials_give_bayesian_bootstrap_conditional`](../AronowAudit/P037/Wave1/Cond/CondP037P041Proofs.lean#L57)

```lean
import AronowAudit.P037.Wave1.Cond.CondP037P041Proofs

#check AronowAudit.P037.Wave1.exponentials_give_bayesian_bootstrap_conditional
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P037-T5](works/P037.md#p037-t5).

Related declarations:

- [`AronowAudit.Literature.DevroyeGammaDirichlet`](../AronowAudit/Literature/CondP037P041.lean#L56): published distributional premise
- [`AronowAudit.P037.normalizedExponentialLaw`](../AronowAudit/P037/P037_Bootstrap.lean#L52): law of normalized exponential weights
- [`AronowAudit.P037.bayesianBootstrapLaw`](../AronowAudit/P037/P037_Bootstrap.lean#L40): uniform simplex measure with completed coordinate

**Conditional on:** AronowAudit.Literature.DevroyeGammaDirichlet.{0} Source: L. Devroye, Non-Uniform Random Variate Generation, Springer-Verlag (1986), Chapter XI, Theorem 4.1, p. 594; Dirichlet definition on p. 593. The full forward-and-converse proposition is defined in AronowAudit/Literature/CondP037P041.lean.

**Scope.** The general gamma–Dirichlet theorem is an explicit premise. The conclusion concerns normalized exponential weights and does not assert that normalized uniform weights have this law.

### H070

**Validity of bounded-outcome IV complier-mean bounds**

Random assignment and monotone treatment identify valid bounds on both complier potential-outcome means.

Areas: Causal identification, Partial identification and bounds.

**Statement.** On any measurable probability space, let the measurable principal stratum $`S`$ be always-taker, never-taker or complier, with binary potential treatment defined accordingly; this encodes monotonicity. Let measurable integrable potential outcomes $`Y(0),Y(1)`$ obey $`0\le Y(d)(\omega)\le1`$ for every $`d,\omega`$. Binary assignment $`Z`$ is measurable, each arm has positive probability, and $`Z`$ is independent of the full vector $`(S,Y(0),Y(1))`$. Exclusion is built into the observation rule $`Y=Y(D(Z))`$. Assume the population first stage $`E[D(1)-D(0)]`$ is nonzero.

Put $`p=P(S=\mathrm{complier})`$, $`e_z=E[Y\mid Z=z]`$, $`\mu_d=E[Y(d)\mid S=\mathrm{complier}]`$ and $`\Delta=(e_1-e_0)/p`$. The theorem concludes


```math
\max\{0,-\Delta,1-(1-e_0)/p\}\le\mu_0\le\min\{1,1-\Delta,e_0/p\},
```




```math
\max\{0,\Delta,1-(1-e_1)/p\}\le\mu_1\le\min\{1,1+\Delta,e_1/p\},\qquad \mu_1=\mu_0+\Delta.
```


The model assumptions imply $`p\gt 0`$, so these ordinary event-conditional means are defined.

**Use.** Bounds the levels of both complier potential-outcome means from assignment-arm outcome means and the complier share. It is measure-theoretic and imposes no finite-support or sampling model.

**Relation to Mathlib.** Mathlib supplies probability measures, integrals and independence. The principal-stratum causal model and explicit complier-mean interval formulas are defined here.

**Declaration:** [`AronowAudit.P028.proposition1_valid`](../AronowAudit/P028/P028_Results.lean#L1088)

```lean
import AronowAudit.P028.P028_Results

#check AronowAudit.P028.proposition1_valid
```

**Status:** `proved`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Targets: [P028-T8](works/P028.md#p028-t8).

Related declarations:

- [`AronowAudit.P028.CausalModel`](../AronowAudit/P028/P028_Results.lean#L224): full causal assumptions
- [`AronowAudit.P028.proposition1_sharp`](../AronowAudit/P028/P028_Results.lean#L1108): separate endpoint-attainment result
- [`AronowAudit.P028.boundedOutcomes`](../AronowAudit/P028/P028_Results.lean#L281): pointwise potential-outcome bounds

**Scope.** Both potential outcomes are bounded pointwise, and randomization is joint independence from the complete latent vector. This declaration establishes validity and the translated-mean identity; sharpness is a separate theorem.

### H071

**Exact rectangular density-estimator moments**

The rectangular kernel density estimator has exact finite-sample expectation and variance determined by interval probability.

Areas: Probability, Asymptotic statistics.

**Statement.** On a probability space $`(\Omega,\mu)`$, let $`(X_i)_{i\ge0}`$ be measurable, mutually independent and identically distributed real variables. Suppose their common law has a density $`f`$: $`f`$ is Lebesgue almost-everywhere measurable, everywhere nonnegative and integrable, and the law equals Lebesgue measure weighted by $`f`$. For every natural $`n\gt 0`$, bandwidth $`h\gt 0`$ and real $`x`$, set $`F(t)=P(X_0\le t)`$ and $`p=F(x+h)-F(x-h)`$. For the closed-window rectangular estimator


```math
\widehat f_{n,h}(x)=\frac1{2nh}\sum_{i=0}^{n-1}\mathbf{1}\{\lvert x-X_i\rvert\le h\},
```


the conclusions are exactly


```math
E[\widehat f_{n,h}(x)]=\frac p{2h},\qquad \mathrm{Var}(\widehat f_{n,h}(x))=\frac{p(1-p)}{4h^2n}.
```


No continuity assumption on $`f`$ or asymptotic bandwidth condition appears in this declaration.

**Use.** Provides finite-sample moments for rectangular density estimation and a direct input to consistency arguments. Absolute continuity makes endpoint atoms irrelevant, while bounded indicator summands supply the required moments without moment assumptions on the observations.

**Relation to Mathlib.** Mathlib v4.34.1 provides variance scaling and independent-sum identities, including ProbabilityTheory.variance_mul_const and IndepFun.variance_sum. This helper specializes those tools to a closed rectangular window and the local CDF and estimator definitions.

**Declaration:** [`AronowAudit.P001.rectangular_kernel_moments_core`](../AronowAudit/P001/P001_Foundations.lean#L4176)

```lean
import AronowAudit.P001.P001_Foundations

#check AronowAudit.P001.rectangular_kernel_moments_core
```

**Status:** `helper`; axioms: `Classical.choice`, `Quot.sound`, `propext`.

Related declarations:

- [`AronowAudit.P001.rectangular_kernel_consistency`](../AronowAudit/P001/P001_Foundations.lean#L4312): asymptotic consequence
- [`AronowAudit.P001.kernelDensity`](../AronowAudit/P001/P001_Foundations.lean#L405): kernel estimator definition
- [`AronowAudit.P001.rectangleKernel`](../AronowAudit/P001/P001_Foundations.lean#L413): closed rectangular kernel

**Scope.** The result concerns a fixed positive bandwidth and positive sample size; continuity of the density is unnecessary.

