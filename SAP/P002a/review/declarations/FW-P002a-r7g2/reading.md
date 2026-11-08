# Blind reading of T6–T10

Written before opening `claims.json` or `record.json`. I read all five Challenge docstrings and statements and every entry in their `closure.json` closures. Source definitions were read in Part1, Part2, Part3, Part6, Part8, WholeW1, WholeW3 and WholeW4. All 33 distinct line-zero generated declarations were printed and read in `scratch/ClosureGenerated.log`: they are numeral/`Fin` instance proofs and `Option` eliminators, with no additional mathematical hypotheses. Constructors and projections of the two population structures have their ordinary record meanings.

The following common notation is an explicit expansion into finite sums, real arithmetic, matrices and measures. References to this notation below do not introduce additional assumptions.

* A population of size `n : ℕ` is arbitrary data `y : Fin n → Bool → ℝ`, `d : Fin n → Bool → Bool`, `n1 : ℕ`. Here `y(i,b)` is a potential response indexed by receipt, and `d(i,a)` is receipt under assignment `a`. A covariate population additionally has `x : Fin n → Fin k → ℝ`. Write `N={0,…,n−1}`, `n0=n−n1` in **real** arithmetic, `π=n1/n`, and `I(b)=1` for true and 0 for false.
* The complier set is `C={i : d(i,false)=false ∧ d(i,true)=true}`. Monotonicity is `d(i,false)=true ⇒ d(i,true)=true` for every i. The LATE is `β=(Σ_{i∈C}(y(i,true)−y(i,false)))/|C|`.
* For a real vector f on N, `M(f)=Σ_i f_i/n`; for a subset S, `M_S(f)=Σ_{i∈S}f_i/|S|`. Its population sample variance is `V(f)=Σ_i(f_i−M(f))²/(n−1)`. Population covariance is the analogous product sum over `n−1`. Subset covariance uses the centered product sum over `|S|−1` when `|S|≥2`, and is explicitly 0 otherwise; subset variance is covariance with itself. `L4(f)=sqrt(sqrt(M(f⁴)))`.
* `W_a(i)=y(i,d(i,a))−β I(d(i,a))`. Its centered version is `v_a=W_a−M(W_a)`. Under an observed treatment set S, `q_S(i)=y(i,d(i,1_{i∈S}))−β I(d(i,1_{i∈S}))`.
* The design set is `D={S⊆N : |S|=n1}`. For any real function f on subsets, `E_D f=(Σ_{S∈D} f(S))/|D|`, `Var_D f=E_D[(f−E_D f)²]` and `Pr_D(E)=|{S∈D:E(S)}|/|D|`. These are uniform complete-randomization quantities, not Bochner integrals. Complements are relative to N.
* Append an intercept: `z_i(none)=1`, `z_i(some j)=x_ij`. The squared vector norm is `||b||²=Σ_j b_j²`; dot products and matrix products are ordinary finite coordinate sums. For subset S, `G_S=|S|⁻¹Σ_{i∈S}z_i z_iᵀ` and `h_S(q)=|S|⁻¹Σ_{i∈S}z_i q_i`. Define `RSS_S(q,c)=Σ_{i∈S}(q_i−z_iᵀc)²`.
* `c_S(q)` is `G_S⁻¹ h_S(q)` when `det G_S≠0`; otherwise it is the `Classical.choose` of a coefficient vector minimizing RSS over all vectors, if such a minimizer exists, and is the zero vector if none exists. Thus it is a fixed least-squares choice. In finite-dimensional real least squares a minimizer always exists. The population coefficient is `ψ_a=c_N(W_a)` and population residuals are `u_a(i)=W_a(i)−z_iᵀψ_a`.
* For arbitrary coefficients c1,c0, the adjusted difference is `M_S(q−Σ_j x_ij c1(some j))−M_{Sᶜ}(q−Σ_j x_ij c0(some j))`. Let `F(q,S)` use c1=`c_S(q)` and c0=`c_{Sᶜ}(q)`. Let `O(q,S)` use the common pooled coefficient `c_N(q)` in both arms. The feasible variance estimator is `H(q,S)=RSS_S(q,c_S(q))/n1²+RSS_{Sᶜ}(q,c_{Sᶜ}(q))/n0²`. No degrees-of-freedom correction or factor `π²(1−π)²` occurs in this adjusted estimator/statistic.
* Expanded membership in the covariate class, with real constants δ,e,A,B,r, is the conjunction of: `n≥2`, `0<n1<n`; monotone receipt; `C≠∅`; `rn≤n1≤(1−r)n`; `Cov(u_true,u_false)≥−δ sqrt(V(u_true))sqrt(V(u_false))`; `L4(u_a)≤B sqrt(V(u_a))` for each Boolean arm; `Σ_i x_ij=0` and `M(x_j⁴)≤A` for each coordinate j; and `e||b||²≤M((x_iᵀb)²)` for every covariate vector `b : Fin k → ℝ`. Constants' admissibility restrictions are separately quantified in the particular theorem.
* A random assignment sequence on a measurable probability space `(Ω,μ)` means that for every size index j and **every** predicate E on subsets of `Fin(sizes j)`, the set `{ω:E(Z_j(ω))}` is measurable and has measure `ENNReal.ofReal(Pr_{D_j}(E))`. This forces exact uniform marginals, including design support almost surely; it does not impose independence across sizes.
* Write `λ(x)=inf{M((x_iᵀb)²):||b||²=1}` and `λ⁺(x)=inf{M((z_iᵀb)²):||b||²=1}` as real `sInf`s. The covariate Gram C has entries `M(x_s x_t)`.

## SAP.P002a.T6

The theorem asserts a conjunction about explicit models; it has no external hypotheses and does not universally assert (E.58)–(E.60). Its docstring calls (E.61), with **feasible** reassignment variance in the denominator, false.

For each natural m≥4, take n=2m and define

`t_j=(2j−m+1)/(m−1)` for j∈Fin m,
`V_m=(m+1)/(3(m−1))`, `η_m=2^{−(2m)²}`,
`t_i=t_{i mod m}`, `x_i=(1 if i<m else −1)+η_m t_i`,
`y_i=t_i+(t_i²−V_m)/10`, `d(i,a)=a`, `y(i,a)=y_i`, `n1=m`.

Let `γ_m=η_m V_m/(1+η_m² V_m)` and `e_i=y_i−γ_m x_i`; the coefficient vector `(a,b)` has intercept a and sole slope b. Let Bm be the subset `i<m`. The following **all** hold for every m≥4:

1. The single-block grid has mean 0, second moment V_m, third moment 0, absolute entries ≤1, and `1/3≤V_m≤1`.
2. The model satisfies the entire expanded covariate class above at `(δ,e,A,B,r)=(0,1/4,16,5,1/3)`. LATE is 0; all units are compliers; treatment and control sizes are m; π=1/2; all receipt and potential-response/covariate formulas agree with those displayed; every original assignment S, including arbitrary subsets in this last equality, yields `q_S=y`.
3. `Σx_i=0`, `M(x)=M(y)=0`, `|x_i|≤5/4`, `|y_i|≤11/10`, `M(x⁴)≤16`, `M(x²)=1+η_m²V_m≥1/4`, `M(xy)=η_mV_m`.
4. Both population OLS coefficients at β=0 equal `(0,γ_m)` and both residual vectors equal e. `M(e)=0`, `|e_i|≤27/20`, `M(e²)≥1/6`, `Cov(e,e)≥0`, `L4(e)≤5sqrt(V(e))`. The map `i↦x_i` is injective. For every design assignment T, both arm augmented Grams have nonzero determinant.
5. Bm and its complement are design assignments; both fitted slopes at Bm are `1/η_m`; `F(y,Bm)=−2/η_m`, `F(y,Bmᶜ)=2/η_m`. For **every** subset T, `F(y,Tᶜ)=−F(y,T)`. Its uniform design expectation is 0.
6. Put `V_F=Var_D(F(y,·))`. Then `V_F>0`, `V_F≥8/(choose(2m,m)η_m²)`, and `8·2^{2(2m)²}/2^{2m}≤8/(choose(2m,m)η_m²)`.
7. Every design T has `0≤H(y,T)≤Σ_i y_i²/m²`; this last bound is at most `121/(25(2m))<5/(2m)`.
8. Put `R_m=5·2^{2m}/(8(2m)2^{2(2m)²})`. Then `R_m<1/2`. For every original design S and every reassignment T∈D, `0≤H(q_S,T)/Var_D(F(q_S,·))≤R_m`, and `Pr_D(|H(q_S,T)/Var_D(F(q_S,·))−1|≥1/2)=1`.

For every odd n≥9, the odd extension has `x_i=2i/(n−1)−1`, `y(i,a)=(x_i²−M(x²))/10`, `d(i,a)=a`, `n1=floor(n/2)`. It satisfies the same covariate class constants, has LATE 0 and all compliers, has `|x_i|≤1`, injective x, and pair differences `x_j−x_i=2(j−i)/(n−1)`.

The size-indexed family chooses the even model with m=floor(n/2) when `2 floor(n/2)=n`, transporting its type across that equality; otherwise it chooses the odd extension. It belongs to the displayed class for every n≥8. Its even specialization equals the even model for **all** m, and its odd specialization equals the odd extension for **all** odd n. Finally the error probability at the even sizes `2(j+4)` tends to 1 and does not tend to 0 as j→∞.

Junk conventions: real division at zero is 0. The grid's m−1 denominator and modulo m could be problematic at m≤1 (natural modulo 0 returns its argument), but all numerical/moment/regression/refutation assertions use m≥4. η and `1+η²V_m` are positive there, as are arm sizes, assignment counts, n−1 and the expressly positive feasible variance. Odd models use n≥9. Parity-specialization equalities also cover small n/m, but merely identify the very same totalized data, without claiming validity at those sizes. `floor(n/2)` is natural division, and powers have natural nonnegative exponents; `n−n1` and `m−1` denominators here are real subtraction. Square roots in the class and fourth norm have nonnegative arguments on the stated data. Matrix inverse is used only under nonzero determinant; all admissible even arm fits are expressly full rank. The complement identity over arbitrary subsets can include empty arms, so zero empty-subset means and fixed least-squares completion are part of that ancillary identity; the counterexample probabilities range only over genuine nonempty balanced arms. No logarithm, rpow, integral, infinite `toReal`, infimum or limsup occurs.

## SAP.P002a.T7

Universally and in this order: choose a type Ω (in an arbitrary universe), its measurable space, a measure μ and its probability-measure instance; a deterministic size sequence `sizes : ℕ→ℕ` and proof it is strictly increasing; natural k; deterministic populations P_j with covariate dimension k and sample sizes sizes j; maps `Z_j : Ω→subsets(Fin(sizes j))`; real δ,e,A,B,r; assume `k>0`, `δ<1`, `e,A,B>0`, `0<r≤1/2`; assume every P_j satisfies every clause of the expanded covariate class; assume `V(u_{j,a})>0` for every j and each Boolean arm a; assume the exact measurable uniform-marginal assignment property above; choose a deterministic strictly increasing subsequence `sub : ℕ→ℕ`.

Then for μ-almost every **single** ω the following conjunction holds. For each j put N=sub j, observed assignment `Z_N(ω)`, hold the resulting observed q fixed during reassignment, and put `σ_j²=Var_{D_N}(O(q,·))`.

* For **every** real κ>0, `Pr_{D_N}(|F(q,S)−O(q,S)|≥κsqrt(σ_j²))→0`.
* For **every** real x>0, `|Pr_{D_N}(|O(q,S)|≥xsqrt(σ_j²))−Pr(|G|≥x)|→0`, where G has the Mathlib real Gaussian probability law with mean 0 and variance 1.
* For **every** real x>0, the same absolute-tail assertion holds for F in place of O, using the **same oracle** variance σ_j².
* For **every** real κ>0, `Pr_{D_N}(|H(q,S)/σ_j²−1|≥κ)→0`.

All limits are ordinary real limits along j→∞ (`Filter.atTop` and real neighborhood filters). The probability-one event is inside the universal choice of subsequence and outside all thresholds, so thresholds share an event, but the theorem does not assert one event uniform over all subsequences or populations. Independence of Z_j is not assumed. The arm coefficients for F are fitted afresh for each S; O uses the common pooled fit to the observed q. The positive variances in the hypotheses are population **residual** variances, not unprojected W variances and not conditional oracle variances.

Junk conventions: n≥2, positive treatment and control sizes, nonempty compliers and nonempty assignment sets follow from class membership, so their means and variance divisors are genuine. Population covariate and augmented Grams are positive definite from centering and e>0. Sample arms can be singular; the fixed least-squares choice described above completes them, and the nonexistent-minimizer fallback is mathematically unreachable in finite-dimensional least squares. Conditional oracle variance is nonnegative but not assumed positive at each size. Its square root is 0 if it vanishes; the non-strict tail/merging events then use a zero threshold. The estimator/oracle-variance quotient is 0 at denominator 0 in Lean, making its error from 1 equal to 1. Those conventions can affect finite terms; the asymptotic assertion is that they do not destroy the four limits under the positive-residual hypotheses. `normalTail` is `(gaussianReal 0 1 {z:x≤|z|}).toReal`; this Gaussian is a probability measure so no ∞ is converted to 0. There are no Bochner integrals or unbounded limsup/liminf values. All operations on vectors have finite indices; k>0 excludes an empty covariate type. The almost-everywhere quantifier and the exact measurable marginal property supply the relevant measure conditions rather than assuming pointwise paths are always design assignments.

## SAP.P002a.T8

No external hypotheses. For every natural m>0, n=2m, k=1 and `x_i=2(−1)^{i+1}` at zero-based Lean index i (paper indices start at 1), all of the following hold:

* For the sole coordinate, `Σ_i x_i=0` and `M(x⁴)=16≤16`.
* The 1×1 covariate Gram is [4], its infimum unit-vector Rayleigh value λ is 4, and `2≤λ`.
* For every `b : Fin 1→ℝ`, `2||b||²≤M((x_iᵀb)²)`.
* The full augmented Gram is `diag(1,4)`, and its unit-vector Rayleigh infimum λ⁺ is 1.
* For the specifically chosen vector with intercept 1 and sole covariate coordinate 0, `||b||²=1`, `bᵀG_Nb=1`, and `bᵀG_Nb<2||b||²`.

Thus the proposition is a family of counterexamples to passing the bound e=2 unchanged from the covariate Gram to the augmented Gram. It asserts no potential-outcome, randomization or OLS conditions.

Junk conventions: m>0 ensures n>0; mean/group-mean denominators n are nonzero. k=1 and the augmented dimension 2 give nonempty unit spheres. Both real infimum sets are nonempty and bounded below by 0, indeed are Rayleigh values of explicit finite real matrices, so the conditional completeness totalization of real `sInf` is not involved. Natural exponent i+1 is used at base −1, with no fractional power convention. Zero-based indexing accounts for the sign relative to the prose formula; it is not a different family. There is no partial inverse, integral, probability division, square root, empty-index issue or limit.

## SAP.P002a.T9

This is the conjunction of two independently universal assertions.

Finite assertion: for all natural n,k, real covariates x, hypotheses n>0 and k>0, real e>0, centered coordinate sums, and `e≤λ(x)`, the full augmented Gram has intercept entry 1, both intercept/covariate cross blocks 0, and covariate block exactly C. Also `λ⁺(x)=min(1,λ(x))`, `min(1,e)≤λ⁺(x)`, and for **every** augmented vector b,

`min(1,e)||b||²≤bᵀG_Nb`.

Sequence assertion: universally choose Ω, measurable space, probability μ, strictly increasing deterministic sizes, k, deterministic covariate populations P_j, assignment maps Z_j, real δ,e,A,B,r, admissibility `k>0`, `δ<1`, `e,A,B>0`, `0<r≤1/2`, class membership at every size (every clause expanded above), exact measurable uniform assignment marginals, and a deterministic strictly increasing sub. Then for μ-almost every ω there **exists** a real sequence err_j tending to 0 such that for all sufficiently large j, simultaneously for both Boolean arms a,

`(min(1,e)+err_j)||b_{j,a}||²≤b_{j,a}ᵀG_{arm(j,a)}b_{j,a}`,

where N=sub j, S=Z_N(ω), `q=q_S` at its LATE, `b_{j,a}=c_{arm(a)}(q)−c_N(q)`, and `arm(true)=S`, `arm(false)=Sᶜ`. The error may depend on ω, the subsequence and all preceding data, and may have either sign. One error works for both arms; only eventual validity is required. No independence or positive response/residual variance is a hypothesis.

Junk conventions: the finite statement guards n>0 and k>0. Thus both real Rayleigh infimum sets have unit vectors and are bounded below by 0; no empty/unbounded `sInf` convention affects the spectral claim. In the sequence, class membership guarantees n≥2, nonempty arms/compliers/design and all nonzero size divisors. Population OLS is nonsingular by centering and positive e. Sample OLS uses the genuine least-squares singular-arm completion. Empty arms only occur off the probability-one design-support event, since the marginal assignment property forces support almost surely at every index. Square roots are of finite nonnegative variance/fourth-moment values. The measurable marginal property plus countable sequences is meaningful without independence. `err` is an arbitrary real null sequence, not a limsup or infimum-based default. No logarithm, rpow, infinite `toReal`, Bochner integral or variance quotient occurs.

## SAP.P002a.T10

There are no external hypotheses; the theorem asserts two conjunctions of numerical facts about the explicit population n=4, n1=2, all-complier receipt `d(i,a)=a`, and `y(i,a)=s_i+2I(a)`, where `s=(-1,−1,1,1)`.

The population satisfies the following unadjusted class at `(δ,r,A)=(0,1/2,1)`: n≥2 and 0<n1<n, monotone receipt, nonempty compliers, balance `rn≤n1≤(1−r)n`, complier covariance of the two W vectors at their LATE at least `−δ` times the product of their subset standard deviations (the subset covariance convention is as above), and `L4(v_a)≤A sqrt(V(W_a))` for both arms. Its LATE is 2.

Let S={0,1}; it is an admissible complete-randomization treatment set. At β=2, observed q and both W vectors are s. The following printed-form computations hold:

* `M_S((q−M_S(q))²)=0`.
* `M_S(v_true²)−[M_S(W_true)−M(y(i,d(i,true)))−2M(I(d(i,true)))]²=−24`.
* The uniform-design expectation of the last **minus-sign bracket squared** is 49/3, whereas `n0/(n1·n·(n−1)) Σ_i v_true(i)²=1/3`.

The additional corrected evaluations are: the scaled variance `S_1²=π²(1−π)²V(W_true)` is positive and exactly 1/12; the treated-potential response population mean is 2; the treated receipt mean is 1; `M_S(W_true)=−1`; `M_S(v_true²)=1`; the minus-sign bracket is −5; the bracket with **plus** `2M(I(d(i,true)))` is −1; the corrected within-arm variance difference is 0; and the uniform-design expectation of the corrected bracket squared is 1/3. Thus the first two unequal pairs contradict the two centering equalities indicated by the docstring, and the plus-sign replacements have the asserted finite values. The statement does not universally prove corrected identities for arbitrary populations.

Junk conventions: n=4, both arms have size 2, all four are compliers, and all six size-2 subsets are the design. Thus n, n−1, subset sizes, subset-variance denominators and assignment counts are nonzero. Scaled variance is expressly 1/12>0. `Real.sqrt` is used only for nonnegative variances and fourth moments in class membership. `groupCov`'s default 0 for singleton/empty subsets is not exercised by the complier set. The literals in `2*4*(4−1)` are real through the expression's type; no truncated natural subtraction produces this value. All casts from natural cardinalities are standard nonnegative real casts. There is no matrix inversion, real infimum, conditional expectation, undefined integral, rpow, log, infinite conversion or limit.
