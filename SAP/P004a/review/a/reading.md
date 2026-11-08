# Blind reading of the Challenge

Saved before opening `claims.json` or `record.json`. This is a reading of the propositions, not a judgment of their correspondence with the paper. All theorems below are in `SAP.P004a`. Their proofs are `sorry`; those placeholders provide no evidence of truth in this review.

## Shared objects and exact conventions

Write (I_N=\{0,\ldots,N-1\}) and (Z_N=\{0,1\}^{I_N}). These are `Fin N` and `Fin N → Bool`. The empty sample size is allowed unless a positive-size hypothesis is stated. `bit` identifies the two Boolean values with real 0 and 1. All sums over assignments or indices are finite sums, including sums over every one of the (2^N) assignments.

For a real vector (p=(p_i)), define

\[
w_p(z)=\prod_i p_i^{z_i}(1-p_i)^{1-z_i},\quad
E_p X=\sum_{z\in Z_N}w_p(z)X(z),\quad
P_p(A)=E_p1_A.
\]

The powers here abbreviate the two branches of `coin`, not any extra positivity convention. These are product Bernoulli probabilities when (0\le p_i\le1); the definitions themselves also accept arbitrary real (p_i). `cov p X Y` is (E_p(XY)-E_pX E_pY); `variance` is covariance with itself.

For an arbitrary real table (R_i(z)), write

\[
\mu_i(a)=\frac{E_p[1_{\{z_i=a\}}R_i(z)]}{p_i\ \text{if }a=1,\quad1-p_i\ \text{if }a=0},
\quad\Delta_i=\mu_i(1)-\mu_i(0),\quad\tau=\frac1N\sum_i\Delta_i.
\]

These are `marginal`, `nodeEffect`, and `ame`. They are conditional means and their differences when the denominators are positive. The table can have arbitrary interference. For a nonrandom fit (g_i(a)), put

\[
\delta_i^g=\Delta_i-g_i(1)+g_i(0),\quad
C_i^g(z)=\frac{z_i(R_i(z)-g_i(1))}{p_i}
-\frac{(1-z_i)(R_i(z)-g_i(0))}{1-p_i},
\quad Q_B(g)=\frac1N\sum_i\sum_{j\in B_i}\delta_i^g\delta_j^g.
\]

These are `residualEffect`, `residualContrast`, and `homophilyQ`. The estimators are

\[
H_p(R,z)=\frac1N\sum_i\left(\frac{z_iR_i(z)}{p_i}-\frac{(1-z_i)R_i(z)}{1-p_i}\right),
\quad A_p(R,g,z)=\frac1N\sum_i[g_i(1)-g_i(0)+C_i^g(z)].
\]

`printedObsHT` instead divides the control term by (p_i). `fittedIPW` is (H_{\hat p(z)}(R,z)), where (\hat p_i(z)=\ell(O_i\cdot\hat\theta(z))) and (\ell(t)=e^t/(1+e^t)). These are finite real expressions, not integrals over an implicit probability space.

Here (O_i\in\mathbb R^k), `dot` is the ordinary coordinate sum, and

\[
I=\frac1N\sum_i p_i(1-p_i)O_iO_i^T,\qquad
\beta_a=I^{-1}\frac1N\sum_i\mu_i(a)p_i(1-p_i)O_i,
\quad f_i(a)=O_i^T\beta_a,
\]
\[
\gamma=I^{-1}\frac1N\sum_i[(1-p_i)\mu_i(1)+p_i\mu_i(0)]O_i,
\quad L_i=O_i^T\gamma,\quad D_i=f_i(1)-f_i(0).
\]

`information`, `beta`, `printedFits`, `scoreGamma` are respectively (I,\beta,f,\gamma). `scoreFits` is the pair

\[
s_i(1)=p_iD_i+p_i(1-p_i)L_i,\qquad
s_i(0)=-(1-p_i)D_i+p_i(1-p_i)L_i.
\]

`fittedBeta` replaces its right-hand vector by (N^{-1}\sum_i1_{z_i=a}R_i(z)\operatorname{coin}(\hat p_i,1-a)O_i) and uses (I(\hat p,O)^{-1}). `fittedGamma` replaces its right-hand vector by

\[
N^{-1}\sum_i\left[z_iR_i(z)\frac{1-\hat p_i}{\hat p_i}
+(1-z_i)R_i(z)\frac{\hat p_i}{1-\hat p_i}\right]O_i.
\]

`fittedScoreFits` uses these two fitted coefficient formulas in the formula for (s), with (p=\hat p).

`LogisticConditions O θ₀ Θ θhat` means all of the following, in this order: 

1. (\Theta\subseteq\mathbb R^k) is compact and (\theta_0\in\Theta).
2. There exists one real (U) such that ( |O_{Ni,j}|\le U) for every sample size (N), every node (i\in I_N), and every coordinate (j\in I_k).
3. There exist (c>0) and an eventual range of (N) such that, for every vector (v\in\mathbb R^k), (c\sum_jv_j^2\le N^{-1}\sum_i(O_{Ni}\cdot v)^2).
4. For every (N,z), (\hat\theta_N(z)\in\Theta), and for every (\theta\in\Theta),
   \(\sum_i[z_iO_{Ni}\cdot\theta-\log(1+e^{O_{Ni}\cdot\theta})]\le\sum_i[z_iO_{Ni}\cdot\hat\theta_N(z)-\log(1+e^{O_{Ni}\cdot\hat\theta_N(z)})]\).

No convexity, uniqueness, interior membership, or measurability condition on the selector is part of this definition. Each assignment space is finite. `Overlap p` means there exists (0<\epsilon<1/2) such that (\epsilon<p_{Ni}<1-\epsilon) for every (N,i). `logisticScore` is (S_N(z)=N^{-1}\sum_i(z_i-p_i)O_i).

A `SpatialPopulation N X` consists of nonempty node sets (C_i\subseteq X) in a metric space with a separately specified measurable space, a measure (\zeta), real outcomes (Y(x,z)), and an arbitrary band map (d\mapsto D_d\subseteq\mathbb R). No Borel compatibility, node disjointness, or positivity/finite measure is built into the structure. Define

\[
\rho_i(x)=\inf_{y\in C_i}\operatorname{dist}(x,y),\quad
A_i(d)=\{x:\rho_i(x)\in D_d\},\quad
R_i(d,z)=\frac{\int_{A_i(d)}Y(x,z)\,d\zeta}{\zeta(A_i(d)).\mathrm{toReal}},
\quad d_{ij}=\inf_{x\in C_i,y\in C_j}\operatorname{dist}(x,y).
\]

These are `nodeDistance`, `region`, `circleAverage`, and `nodeSeparation`. Nonempty node sets make both distance infima nonempty and bounded below. `WellDefined P d` requires, for every (i), that (A_i(d)) is measurable, (0<\zeta(A_i(d))<\infty), and (Y(\cdot,z)) is integrable on it for every assignment (z).

`interferes R i j` means (i=j), or there exist two assignments differing at most at (j) at which (R_i) differs. `sharesSource R i j` means some index interferes with both (i) and (j). Thus a node is always its own source, even if its outcome is constant. `LocalAt R dist h` says that (h<\mathrm{dist}_{ij}) implies no shared source. `ball dist i r` is the set of all (j) with (\mathrm{dist}_{ij}\le r).

`SpatialLocalConditions P` is the conjunction of: (i) some (b>0) bounds ( |Y_N(x,z)|<b) for every (x,z) eventually in (N); (ii) there exists a function (h(d)\ge0) for nonnegative (d), such that, for each (d\ge0), `LocalAt` for the circle table and node separation at range (h(d)) holds eventually in (N); (iii) there exists a real function (c(r)) such that, for each (r\ge0), every node's radius-(r) ball has cardinality at most (c(r)) eventually in (N). The eventual thresholds may depend on (d) and (r). `circleSequence` and `spatialNeighborhoods P h N` select (R_N(d)) and (B_{Ni}=\{j:d_{ij}\le h\}).

The variance expressions are

\[
V_{\rm raw}(p,R,B,g,z)=N^{-2}\sum_i|B_i|\left[\frac{z_i(R_i-g_i(1))^2}{p_i^2}+\frac{(1-z_i)(R_i-g_i(0))^2}{(1-p_i)^2}\right],
\]
\[
V_{\rm HAC}(p,R,B,g,z)=N^{-2}\sum_i\sum_{j\in B_i}C_i^g(z)C_j^g(z),
\quad V_{\rm lim}(p,R,B,g)=N^{-2}\sum_i|B_i|\left[\frac{E_p[(R_i-g_i(1))^2\mid z_i=1]}{p_i}+\frac{E_p[(R_i-g_i(0))^2\mid z_i=0]}{1-p_i}\right].
\]

The names are `rawSAH`, `oracleHAC`, and `sahLimit`. Define

\[
e_i^w(z)=\frac{n_1}{N}\frac{z_i}{p_i}(R_i-g_i(1))+
\frac{n_0}{N}\frac{1-z_i}{1-p_i}(R_i-g_i(0)),\qquad n_a=\sum_i1_{z_i=a}.
\]

`weightedEpsilon` is this (e^w); `printedSAH` substitutes its square in both residual squares of (V_{\rm raw}). `secondMomentBound` is (N^{-2}) times the sum of (i) the diagonal terms (\sum_i[E((R_i-g_i(1))^2\mid z_i=1)/p_i+E((R_i-g_i(0))^2\mid z_i=0)/(1-p_i)]), and (ii) for every (i,j\in B_i\setminus\{i\}), the sum over (a,b\in\{0,1\}) of (\sigma_a\sigma_b E[(R_i-g_i(a))(R_j-g_j(b))\mid z_i=a,z_j=b]), where (\sigma_1=1,\sigma_0=-1). `pairMarginal` implements this last conditional expectation by dividing the finite restricted expectation by the product of the two arm probabilities.

The sample arm mean is (\bar R_a(z)=\sum_i1_{z_i=a}R_i(z)/n_a); `hajek` is (\bar R_1-\bar R_0). Let (\bar\mu_a=N^{-1}\sum_i\mu_i(a)). `linearHajek` is (A_p(R,g,\cdot)) for (g_i(a)=\bar\mu_a). `residual` is (e_i=R_i(z)-\bar R_{z_i}(z)), and `lambda` is (\lambda_i=z_i/n_1-(1-z_i)/n_0). `kernelVariance z e Q` is \(\sum_{ij}\lambda_i\lambda_j e_ie_jQ_{ij}\).

Let (X) have rows ((1,z_i)), (M=I-X(X^TX)^{-1}X^T), and

\[
\mathcal A_Q=(n_1n_0/N)M\operatorname{diag}(\lambda)Q\operatorname{diag}(\lambda)M,
\quad\mu_Q=\operatorname{tr}\mathcal A_Q,\quad\nu_Q=2\operatorname{tr}(\mathcal A_Q^2).
\]

These are `designMatrix`, `residualMaker`, `adjustmentMatrix`, `adjustmentMu`, `adjustmentNu`. `uniformDistanceKernel D h` has entry (1_{D_{ij}\le h}). For supplied eigenvalues (l_k) and columns (v_k), `spectralKernel false` has entries (\sum_kl_kv_{ik}v_{jk}), and `spectralKernel true` replaces (l_k) by \(\max(l_k,0)\). `cappedVariance V μ` is (V/\min(\mu,1)) if (\mu>0), and (V) otherwise.

`InProb p U` means: for every real (\epsilon>0), (P_{p_N}(|U_N|>\epsilon)\to0) as natural (N\to\infty). `LittleOp p U r` applies that definition to (U_N/r_N). `BigOp p U r` means: for every (\epsilon>0), there exists (C>0) such that eventually (P_{p_N}(|U_N|>C|r_N|)<\epsilon). `Nondegenerate V` means there exists (v>0) such that eventually (v\le NV_N). `NormalLimit` means convergence of the distribution function at every real argument to that of `gaussianReal 0 1`, the Gaussian measure with mean zero and variance one. Denote that CDF by (\Phi), and its quantile `normalQuantile a` by (q_a=\inf\{x:a\le\Phi(x)\}\).

`LiminfAtLeast u a` means: for each (\epsilon>0), eventually (a-\epsilon\le u_N). `Conservative coverage α` means this with (a=1-\alpha). No conditionally complete lattice `liminf`/`limsup` is used. `studentCDF ν x` is the real Bochner integral over (( -\infty,x]) of

\[
\frac{\Gamma((\nu+1)/2)}{\sqrt{\nu\pi}\,\Gamma(\nu/2)}(1+t^2/\nu)^{-(\nu+1)/2}.
\]

`studentQuantile ν a` is the infimum of its CDF superlevel set. For (\nu>0) this is the usual Student distribution formula.

Mathlib endpoints followed: ordinary finite sums/products; `Metric.infDist` in `Topology/MetricSpace/HausdorffDistance.lean`; the real infimum; `IntegrableOn` as integrability for the restricted measure and the Bochner integral in `MeasureTheory/Integral`; matrix nonsingular inverse in `LinearAlgebra/Matrix/NonsingularInverse.lean`; `gaussianReal` in `Probability/Distributions/Gaussian/Real.lean`; and the finite product norm in `Analysis/Normed/Group/Constructions.lean`. In particular the norm on `Fin k → ℝ` in T10 is the maximum coordinate norm, not the Euclidean norm (equivalent for fixed finite (k)). `EuclideanSpace ℝ (Fin 2)` uses the Euclidean norm and its volume. Real division by zero is zero; a singular matrix inverse is the zero matrix; the nonintegrable real Bochner integral is zero; `ENNReal.toReal` takes infinity to zero; `ENNReal.ofReal` clips negative reals to zero; real square root clips negative inputs to zero. The mathematical readings above are ordinary averages/inverses only where hypotheses guard them. The quantile infima are ordinary quantiles when their probability/degree parameters are in the ranges explicitly used in the statements.

## T1

Fix the following objects for every (N): (O_{Ni}=(1,(i\bmod3)-1)), (\theta_0=(0,\log2)), (\Theta=[-2,2]^2), and (R_{Ni}(z)=21/20) if (i\bmod3=1), otherwise 1. The spatial population has singleton nodes ((10i,0)), measure the sum of Dirac masses at those points, outcome (\sum_i1_{x=(10i,0)}R_{Ni}(z)), and bands ([0,d]). Thus radius zero samples the table at its nodes. This is `threeTypePopulation` via `linePopulation`; (p_{Ni}=\ell(O_{Ni}\cdot\theta_0)).

There exists one family of selectors (\hat\theta_N:Z_N\to\mathbb R^2) such that all these hold simultaneously: `LogisticConditions` for these fixed (O,\theta_0,\Theta); (\theta_0\in\operatorname{int}\Theta); the spatial local conditions; overlap; well-defined radius-zero averages for every positive (N); (Q_B(f)=0) for every (N) with (B_i=\{i\}) and the radius-zero circle table; nondegeneracy of (\operatorname{Var}_{p_N}(A_{p_N}(R_N,f_N))); and failure of (A_{p_N}(R_N,f_N)-H_{\hat p_N}(R_N)) to be (o_p(N^{-1/2})).

Independently, for the entered triples (w=(2/9,1/4,2/9)), (a=(27/250,-24/125,27/250)), (b=(-81/1000,16/125,-81/1000)), the weighted-square averages are respectively (\sum_tw_ta_t^2/3=3/625), (\sum_tw_tb_t^2/3=1753/750000), and (\sum_tw_t(a_t-b_t)^2/3=10369/750000>0). These numerical arrays are not equated to any estimator variance in the proposition.

## T2

This is the conjunction of the following asymptotic and finite propositions. The theorem is universally parameterized by any family of metric/measurable spaces (\mathrm{Space}_N).

Asymptotic part: universally, in order, fix a finite dimension (k), population sequence (P), covariates (O), truth (\theta_0), parameter set (\Theta), selector family (\hat\theta), and real (d,h). Assume (d,h\ge0), spatial local conditions, eventually well-defined radius-(d) circle averages, eventual locality at this particular range (h), the logistic conditions, interior truth, and overlap. Define (p_N=\ell(O_N\theta_0)), (R_N=R_N(d)), (B_{Ni}=\{j:d_{ij}\le h\}), and (V_N=\operatorname{Var}_{p_N}(A_{p_N}(R_N,s_N))). Then

* (H_{\hat p_N}(R_N)-[H_{p_N}(R_N)-N^{-1}\sum_i(z_i-p_{Ni})O_{Ni}^T\gamma_N]=O_p(N^{-1})).
* (A_{p_N}(R_N,s_N)-H_{\hat p_N}(R_N)=o_p(N^{-1/2})).
* If (V) is nondegenerate, then \((H_{\hat p_N}(R_N)-\tau_N)/\sqrt{V_N}\) has the standard normal limit. For every real (0<\alpha<1), the interval inequality using radius (q_{1-\alpha/2}\sqrt{V_{\rm raw}(\hat p,R_N,B_N,\hat s,z)}) has lower limiting coverage at least (1-\alpha). Under the additional hypothesis (Q_{B_N}(f_N)\ge0) for every (N), the same is true with variance \(\max(V_{\rm HAC}(\hat p,R_N,B_N,\hat s,z),0)\). Here (\hat p) and (\hat s) depend on the realized assignment exactly as defined above.

Finite part: universally fix (N,k,p,R,O,B). Assume (N>0), all (0<p_i<1), (\det I(p,O)\ne0), (i\in B_i), (j\in B_i\iff i\in B_j), and no shared source whenever (j\notin B_i). Then all of the following hold:

* For every (i), (s_i(1)-s_i(0)=f_i(1)-f_i(0)) and (s_i(1)/p_i+s_i(0)/(1-p_i)=O_i^T\gamma).
* For every assignment (z), (A_p(R,s,z)=H_p(R,z)-N^{-1}\sum_i(z_i-p_i)O_i^T\gamma).
* For every (i), (E_pC_i^s=\delta_i^f), and (E_pA_p(R,s)=\tau).
* \(\operatorname{Var}_p A_p(R,s)=\mathrm{secondMomentBound}(p,R,B,s)-Q_B(s)/N\).
* \(E_pV_{\rm HAC}(p,R,B,s)=\operatorname{Var}_p A_p(R,s)+Q_B(f)/N\).
* \(\operatorname{Var}_p A_p(R,s)\le E_pV_{\rm raw}(p,R,B,s)\).

## T3

For every (N), nodes (i\bmod8<2) form the active group. Set (O_i=(1,0)) in that group and ((0,1)) outside it; (\theta_0=(0,-\log9)); (\Theta=[-\log19,\log19]^2). Put (R_i(z)=z_i) at (i\bmod8=0), (-z_i) at (i\bmod8=1), and zero otherwise. `activePopulation` is the same singleton-node/counting-measure line realization as in T1. Thus the true probabilities are (1/2) in the active group and (1/10) outside it.

There exists a single family of actual likelihood-maximizing selectors satisfying the logistic conditions, interior truth, spatial local conditions, (Q_{\{i\}}(f)\ge0) at every (N), overlap, well-defined radius-zero averages at every positive (N), and nondegeneracy of the variance of the printed-fit augmented estimator. The actual variance of (H_{\hat p}(R)) is eventually strictly positive. Under the true product design,

\[
\frac{V_{\rm printed}(\hat p,R,\{i\},\hat f,z)}{\operatorname{Var}_{p_N}(H_{\hat p_N}(R_N))}\ \longrightarrow\ 8/25
\quad\text{in probability},
\]

where (\hat f_i(a)=O_i^T\widehat\beta_a(\hat p,R,O,z)). The denominator is the finite-design variance of the actual fitted estimator, not of a leading approximation.

## T4

The conjunction of two universal propositions:

First fix (N,\hat p,R,B,g,z); assume (N>0,n_1>0,n_0>0) and (0<\hat p_i<1). Then

\[
V_{\rm raw}=\frac{\sum_i z_i|B_i|(e_i^w)^2}{n_1^2}
+\frac{\sum_i(1-z_i)|B_i|(e_i^w)^2}{n_0^2},
\]
\[
V_{\rm printed}=N^{-2}\sum_i|B_i|\left[(n_1/N)^2\frac{z_i(R_i-g_i(1))^2}{\hat p_i^4}
+(n_0/N)^2\frac{(1-z_i)(R_i-g_i(0))^2}{(1-\hat p_i)^4}\right].
\]

Second fix (N,p,R,B,g); assume (N>0), (0<p_i<1), self-membership and symmetry of (B), and zero covariance between (C_i^g) and (C_j^g) whenever (j\notin B_i). Then

\[
\operatorname{Var}_p\left(N^{-1}\sum_i C_i^g\right)\le V_{\rm lim}(p,R,B,g)=E_pV_{\rm raw}(p,R,B,g).
\]

No fitted-estimator asymptotic assertion is present.

## T5

All objects are fixed; there are no hypotheses. Two nodes are the closed unit disks centered at ((0,0)) and ((100,0)); the measure is Euclidean area. For points within distance six of a center, the outcome is the indicator that the normalized polar angle about that center is below a share depending on that node's treatment. The treated share is (1/50) inside radius one and (273/2500) outside; the control share is (1/10) everywhere in that disk of radius six. Away from both disks the outcome is zero. Normalized angle is the complex principal argument, shifted by (2\pi) when negative, then divided by (2\pi). The bands in node-set distance are \(D_0=\{0\}\), \(D_6=[0,5]\), and \(D_d=(d-1,d]\) otherwise.

For (j\in\{0,\ldots,5\}), define a three-point mass vector ((2j+1)(1/50,2/25,9/10)) for (j=0), and ((2j+1)(1/10,23/2500,2227/2500)) otherwise. For (j=0), the treated outcome is one on point 0 only, and the control outcome on points 0 and 1; for (j>0), swap these roles. `areaWitnessTable j i z` is the mass-normalized average of this vector under arm (z_i).

For the observed assignment ((1,0)), both arm counts equal one. For every (j), the entire spatial circle table at (d=j), for every node and assignment, equals this finite table. For each node, the six regions are pairwise disjoint and their union is its (d=6) region. All point outcomes are binary. All six regions and the union are well-defined; bin (j) has area (\pi(2j+1)). The sum of the six observed Hájek contrasts is (-17/500), as is the sum of the six AMEs under (p_i=1/2). The whole-region AME is (121/18000>0), different from that sum.

## T6

First, universally fix a measurable space (A), natural (N,m), measure (\zeta), sets (B_{ik}\subseteq A), outcomes (Y(x,z)), and probabilities (p_i). Assume (N,m>0); every (B_{ik}) is measurable; for each node the (m) sets are pairwise disjoint; every set has finite positive measure; every outcome is integrable on each set; and all (0<p_i<1). Let (a_{ik}=\zeta(B_{ik})\), (R_{ki}(z)=a_{ik}^{-1}\int_{B_{ik}}Y(x,z)d\zeta\), and (W_i(z)) be the area-normalized integral over the union. Then, for every (i,z), (W_i(z)=\sum_ka_{ik}R_{ki}(z)/\sum_ka_{ik}). The same weighted averaging formula holds for every node's marginal mean in each arm and every node's effect. The whole AME equals (N^{-1}\sum_i\sum_ka_{ik}\Delta_{ki}/\sum_ka_{ik}). For every node and every real pair \(\mathrm{lo},\mathrm{hi}\), if all bin node effects lie between those bounds, so does its whole effect. For every node and real (c), if all of its bin masses equal (c), its whole node effect is the arithmetic mean of the bin node effects.

Second, for every real (c,s,t) with (c>0), ( |cs|\ge|ct|\iff |s|\ge|t|\). Third, for every (N), arbitrary real assignment weights (w), statistic (T), observed assignment, and (c>0), the exact weighted sum of absolute-statistic exceedances is invariant under multiplying (T) by (c). The latter clause does not require (w\ge0) or normalization; it is an algebraic identity and becomes a p-value identity for probability weights.

## T7

The base five-node outcome vector is (y=(0,1,1,-1,-1)), independent of assignment. `starBlockTable m` repeats it (m) times. Let (K_{ij}=1) if (i=j), (i=0), or (j=0), and zero otherwise; let (v=(2,-1,-1,-1,-1)), and (Q=K+vv^T/8). `starBlockKernel m false/true` consists of (m) diagonal blocks (K/Q) with off-block zeros.

The fixed assignment on twenty nodes is ((1,1,0,1,0,\ 0,1,0,1,0,\ 1,1,0,1,0,\ 0,1,0,1,0)). Both counts are ten and both arm means of the repeated table are zero. Its two raw kernel variances both equal (4/25). The trace parameters are (41/50) for (K), (101/100) for (Q). The adjusted variances equal (8/41) and (16/101), respectively, with (16/101<8/41).

The spatial sequence has five singleton points per block: a center at ((10b,0)) and leaves one unit east, north, west, south, with truncated final blocks for general (N). Its measure is counting measure at those points, outcomes are the corresponding (y) at each point and zero elsewhere, and bands are ([0,d]). This sequence satisfies spatial local conditions and well-defined radius-zero averages for all positive (N). At (p=1/2), its homophily quantity with neighborhood range (6/5) and the constant arm-marginal-mean fits is zero for all (N). Its linear Hájek variance is nondegenerate. At (N=5m) the uniform distance kernel with range (6/5) is the block kernel (K). Locality at this range holds for every (N), and (5m\operatorname{Var}(\mathrm{linearHajek})=16/5) for every (m>0).

Finally, put (L=2\Phi(q_{39/40}\sqrt{15/16})-1). For every real (\epsilon>0), eventually in (m), the product-(1/2) probability of the conjunction

\[
n_1>0,\ n_0>0,\ \mu_Q>0,\ \nu_Q>0,\quad
|\mathrm{hajek}|\le t_{2\mu_Q^2/\nu_Q,39/40}\sqrt{V_Q/\mu_Q}
\]

is strictly less than (L+\epsilon). Also (L<19/20). This is an upper limiting bound on a joint event with validity conditions, not an exact limiting equality and not a conditional probability given those conditions.

## T8

The theorem, for any family of metric/measurable spaces, conjoins a finite and an asymptotic universal statement.

Finite: fix (N), real arrays of eigenvalues and square eigenvector matrix (U), with (U^TU=I); an assignment (z) and arbitrary real vector (e); assume both arm counts positive. Fix real \(\mathrm{critical},c,\mathrm{err}\), with (0\le\mathrm{critical}\le c). Let (K=U\operatorname{diag}(l)U^T), (Q=U\operatorname{diag}(l^+)U^T), and (V^*=\mathrm{cappedVariance}(V_Q,\mu_Q)). Then (V_Q\le V^*), (\max(V_K,0)\le V_Q), and, if (V_K\ge0) and ( |\mathrm{err}|\le\mathrm{critical}\sqrt{V_K}\), then ( |\mathrm{err}|\le c\sqrt{V^*}\).

Asymptotic: fix (P,p,d,h,\alpha), with (0<p<1,d,h\ge0,0<\alpha<1); assume spatial local conditions, eventual well-defined radius-(d) averages and locality at (h), and nondegenerate linear Hájek variance under the constant probability (p). Supply eigenvalues and orthonormal eigenvector matrices for every (N), exactly representing the uniform node-distance kernel at (h). Assume eventual nonnegative homophily for that neighborhood and the arm-mean fits. Finally supply arbitrary assignment-dependent real critical values (c_N(z)\ge q_{1-\alpha/2}) for every (N,z). Then the lower limiting probability is at least (1-\alpha) of the event

\[
n_1>0\ \Longrightarrow\ n_0>0\ \Longrightarrow\
|\mathrm{hajek}(R_N,z)-\tau_N|\le c_N(z)\sqrt{\mathrm{cappedVariance}(V_{Q_N},\mu_{Q_N})}.
\]

An assignment with either empty arm satisfies this implication. There is no assertion about all Student degrees of freedom, and no probability conditional on nonempty arms.

## T9

For each (N,z), put (q=n_1/N), and define (\hat\theta=0) when (q\le1/2), (\hat\theta=1) when (q\ge\ell(1)), and otherwise (\hat\theta=\log(q/(1-q))\). At (N=0) the first branch is taken under real zero division. In dimension one with all covariates equal to one, truth zero, and parameter set \([0,1]\), these selectors satisfy `LogisticConditions`. For every positive (N), under independent fair treatment,

\[
P\bigl(\sqrt N\,|\hat\theta-4(n_1/N-1/2)|>1\bigr)\ge3/32.
\]

In addition the remainder (\hat\theta-4(n_1/N-1/2)) is not (o_p(N^{-1/2})). This does not deny consistency or the (O_p(N^{-1/2})) rate.

## T10

Universally, in order, fix (k,O,\theta_0,\Theta,\hat\theta), assume the logistic conditions and overlap, and let (p_N=\ell(O_N\theta_0)). Then (\|\hat\theta_N-\theta_0\|_\infty\to0) in probability and is (O_p(N^{-1/2})). If in addition (\theta_0\in\operatorname{int}\Theta), then

\[
\|\hat\theta_N-\theta_0-I(p_N,O_N)^{-1}S_N\|_\infty=O_p(N^{-1})=o_p(N^{-1/2}),
\]

where the two order assertions are separately conjoined. No spatial assumptions or nondegeneracy of an outcome variance occur.

## T11

For every (N,p,R) with (N>0) and all (0<p_i<1),

\[
E_pH_p=\tau,\qquad E_p\mathrm{printedObsHT}=N^{-1}\sum_i\left[\mu_i(1)-\frac{1-p_i}{p_i}\mu_i(0)\right].
\]

Equality of the latter expectation with (\tau) holds if and only if (N^{-1}\sum_i(1-2p_i)\mu_i(0)/p_i=0). Independently, for every positive (N), constant (p_i=1/4) and constant outcome table 1 have AME zero, printed expectation (-2), and corrected expectation zero.

## T12

Eight singleton nodes are at ((3(i+1),0)). Their measure is the sum of Dirac masses, their assignment-independent point outcomes are (2^i/128), and bands are ([0,d]). `SharpNull` means that every point outcome at every assignment equals its all-control outcome; this population satisfies it and has well-defined radius-zero averages. Under (p_i=1/2), the observed all-control assignment has HT statistic (-255/512). The assignment treating nodes 0 through 6 has statistic (-1/512).

For (P+1) draws, indexed (0,\ldots,P), let (B\) be the number of indices (r\ne0) with ( |T(z_0)|\le|T(z_r)|\); `mcPlusPvalue` is ((1+B)/(P+1)). Draw 0 is counted only through the added one. The draw-array probability `mcDrawWeight` is the product of its assignment probabilities, including draw 0.

For the fixed array of 101 draws consisting of the observed assignment followed by 100 copies of the resampled assignment, that probability is (256^{-101}>0). The proportion comparing the *signed* observed statistic to the absolute resampled statistic is one, whereas (B=0) and the plus-one p-value is (1/101).

For the same sharp-null population, the exact joint probability over 101 independent draws that (B/100\le1/20) equals

\[
s=128^{-101}\sum_{m=0}^{127}\sum_{b=0}^5\binom{100}{b}(m+1)^b(128-(m+1))^{100-b},
\]

and (s>1/20). Both subtractions inside this natural-number formula are nonnegative on their stated ranges. This is the size of an absolute-statistic comparison under the null, with the observed draw random as well.

## T13

Universally fix (N,P,w,T), assume (w_z\ge0) and (\sum_zw_z=1), (P>0), and (0<\alpha<1). On (P+1) independent draws with common assignment weights (w), the rejection probabilities satisfy

\[
P((1+B)/(P+1)\le\alpha)\le\alpha,\qquad
P(B/P\le\alpha)\le\frac{\lfloor\alpha P\rfloor+1}{P+1}
\le\alpha+\frac{1-\alpha}{P+1}.
\]

The sum defining these probabilities is over all draw arrays with weight \(\prod_rw(z_r)\), and (B) uses absolute values and weak exceedance as above. Independently, for every (N,P,T\) and every draw array with (P>0), the difference between the corrected and raw p-values equals \((1-B/P)/(P+1)\), lies between zero and (1/(P+1)), and at (P=100,\alpha=1/20) the displayed raw upper bound is strictly greater than (1/20). No assertion that this upper bound is always attained is present.

## T14

There are two singleton nodes at ((0,0)) and ((3,0)), and three measure atoms of unit mass at ((0,4),(3,4),(3,-4)). At atom (x\in\{0,1,2\}) the outcome is (1+\sum_i z_i\delta_{ix}), with rows (\delta_0=(0,1,1)), (\delta_1=(-1,0,0)). Away from those atoms the outcome is one. For a distance set (D), `shellSpatialPopulation D` uses the constant band map (d\mapsto D), so the argument zero below is just a label.

All four populations with (D=\{4\},\{5\},[4,5],[0,5]) have well-defined averages. Every point outcome has absolute value less than three. At (p_i=1/2), the AMEs for the first two sets are zero, and for the last two are (1/6). For every pair of real weights (w_4,w_5), the weighted sum of the two singleton-shell AMEs differs from the ([4,5]) AME. These are concrete atomic-measure spatial effects, not area integrals on zero-area circles.

## T15

Three universally quantified components, with independent universe levels for the first two:

1. For every metric/measurable space (A), (N,P,p,d), assume (N>0), (0<p_i<1), and `WellDefined P d`. Define the point effect (\delta_i(x)=E[Y(x,Z)\mid Z_i=1]-E[Y(x,Z)\mid Z_i=0]) using the same finite Bernoulli marginal operation. For every node, its averaged node effect equals \(\int_{A_i(d)}\delta_i(x)d\zeta/\zeta(A_i(d))\). The AME is the arithmetic mean over nodes of these normalized integrals.
2. For every finite type (A), natural (m,N), masses (a_i(x)\ge0), shell-label map (s_i:A\to I_m), and real effects (\delta_i(x)), assume (N>0) and \(\sum_xa_i(x)>0\) for every node. Let (A_{ik}=\sum_{x:s_i(x)=k}a_i(x)). For every node its mass-weighted mean equals \(\sum_{k:A_{ik}>0}\frac{A_{ik}}{\sum_xa_i(x)}\frac{\sum_{x:s_i(x)=k}a_i(x)\delta_i(x)}{A_{ik}}\). The corresponding arithmetic average over nodes equals the double sum divided by (N). Finally, for every vector (w\in\mathbb R^m), if all (w_k>0) and (A_{ik}/\sum_xa_i(x)=w_k) for every (i,k), then that node-average effect equals \(\sum_kw_k[N^{-1}\sum_i\sum_{x:s_i(x)=k}a_i(x)\delta_i(x)/A_{ik}]\). Only supported positive shell masses are divided by in the decomposition; the common-weight clause requires every enumerated label to have positive mass at every node.
3. For every center (c\in\mathbb R^2), real (0\le a<b), the pushforward under (x\mapsto\|x-c\|\) of area restricted to \(\{x:a\le\|x-c\|\le b\}\), normalized by (1/[\pi(b^2-a^2)]\), equals the measure on the real line with density \(1_{[a,b]}(r)\,2r/(b^2-a^2)\) relative to real Lebesgue measure. The displayed Lean density uses `ENNReal.ofReal`; this expression is nonnegative, and the normalization is positive under the hypotheses.
