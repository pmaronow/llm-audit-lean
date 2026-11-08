# Blind reading

This file was written before opening `claims.json` or `record.json`. It describes the elaborated statements and their dependency closures only. All five declarations and every entry of their `closure.json` lists have been read. The auxiliary declarations at source line 0 were also inspected with Lean in `scratch/Inspect.lean`.

Throughout, a real-valued expectation means Mathlib's Bochner integral. For a probability measure and an L2 real random variable, variance means the integral of the squared deviation from its expectation; literally Mathlib defines it as the `toReal` of the corresponding nonnegative extended integral. A real probability means `(measure of the event).toReal`. Finite real vectors `Fin d → ℝ` have the usual product measurable structure and the sup metric, not the Euclidean norm; these give the same finite-dimensional topology. All limits in sample size are along the natural-number filter `atTop`.

## SAP.P001a.T11

Source: `SAP/P001a/Challenge/Part1.lean:85–88`; main proposition: `Defs/Part4.lean:18–33`.

Put

\[
 K=[0,1]\times[0,1]\times[1/4,3/4],\qquad
 q_{(p,a,b)}=(p(1-a),pa,(1-p)(1-b),(1-p)b),
\]

where parameters are real three-vectors and observations are in the four-element set `Fin 4`. For an ordered sample `y : Fin n → Fin 4`, let

\[
 L_y(t)=\prod_{i<n}q_t(y_i),\qquad
 P_t^n(A)=\sum_{y\in(\mathrm{Fin}\,4)^n}1_A(y)L_y(t).
\]

For a single estimator sequence `T : (n : ℕ) → (Fin n → Fin 4) → (Fin 3 → ℝ)`, consistency at `t` means: for every coordinate `k : Fin 3`, then every real `ε>0`, `P_t^n(|T_n(k)-t_k|<ε) → 1`.

The statement is a conjunction of the following assertions, with no externally supplied hypotheses:

1. `K` is compact; `t0=(1,1/3,1/4)` and `t1=(1,1/3,3/4)` belong to it; `q_t0=q_t1=(2/3,1/3,0,0)`.
2. For every natural `n` and every ordered sample `y`, there exists a parameter `t∈K` such that, for every `u∈K`, `L_y(u)≤L_y(t)`.
3. For every `n`, then every sample-to-vector estimator `S` at this size, the sample masses at `t0` sum to one, every such mass is nonnegative, and each individual mass equals its counterpart at `t1`. In addition,
   `P_t0^n(|S(y)_2-1/4|<1/8) + P_t1^n(|S(y)_2-3/4|<1/8) ≤ 1`.
4. For every estimator sequence `T`, it is impossible for `T` to be consistent at both `t0` and `t1`.
5. There exists one sequence `T` whose value is in `K` and maximizes `L_y` for **every** `n,y`; this sequence is inconsistent at `t0` or inconsistent at `t1`.
6. Independently repeated in the last conjunct: `K` is compact, both targets are in it, and for every `n,y`, the function `t↦L_y(t)` is continuous on the whole real parameter space and attains a maximum on `K`.

The two-target impossibility concerns the entire vector including the unused coordinate `b`. It does not require the two targets to be identified, interior points, or to have nonsingular information. No regular-efficiency assertion is present. The docstring explicitly limits what reading the example contradicts and lists two omitted finite identities.

Junk-value audit: `n=0` is included. The empty likelihood product is one, there is exactly one empty sample, and the finite sample mass is still one. There is no division by `n` here. All denominators are fixed nonzero rational constants, and all Fin indices are in bounds. Sums, products, and coordinatewise intervals have their ordinary meanings; no integral, real logarithm, square root, real power, supremum, infimum, limsup, truncated subtraction or partial-function default occurs. No estimator measurability assumption is needed on a finite sample space. The two parameters are genuinely distinct and define normalized finite laws, not junk probability weights.

Closure coverage: `FiniteMixtureConsistent`, `UnusedMixtureWitness`, `disjointMixture`, `disjointMixtureLikelihood`, `disjointMixtureParameterSet`, `finiteMixtureSampleProb`, and `T11Statement` are unfolded above. The closure's additional rational/index implementation proofs are described at the end of this file.

## SAP.P001a.T12

Source: `SAP/P001a/Challenge/Part1.lean:90–105`; proposition: `Defs/WholeW2.lean:491–493`. This theorem uses **T12WholeStatement**, not the older `T12Statement` in `Defs/Part4.lean`. It is the conjunction of four independently quantified principles, as follows.

### 1. Unused-component nonidentification

First quantify natural dimensions `M,K,d`, a measure `νX` on real `K`-vectors, a measure `κ` on the real line, weights `p : ℝ^d → ℝ^M`, component real functions `g_m(y,x,t)`, and two real `d`-vectors `θ,θ'`. Assume `θ≠θ'`. Then quantify an index `j : Fin M` and assume:

- `p(θ)=p(θ')` as vectors;
- `p_j(θ)=0`;
- for every `k≠j`, every real `y`, and every real `K`-vector `x`, `g_k(y,x,θ)=g_k(y,x,θ')`.

Write `G_t(y,x)=Σ_m p_m(t)g_m(y,x,t)` and

\[
 Q_t=(\nu_X\otimes\kappa)\text{.withDensity}(\operatorname{ofReal}(G_t)).
\]

Assume `Q_θ` is a probability measure and `log(G_θ)` is integrable under it. No separate component normalization, weight positivity, finiteness of the reference measures, or truth-distribution hypothesis is imposed in this principle. Its conclusion is:

- `G_θ=G_θ'` pointwise on all `(y,x)`;
- `Q_θ=Q_θ'`;
- for every `n`, the products `⊗_{i:Fin n}Q_θ` and `⊗_{i:Fin n}Q_θ'` agree;
- the expectations of their own log density functions under `Q_θ,Q_θ'` agree;
- for every estimator sequence `T_n : ((ℝ^K×ℝ)^n) → ℝ^d`, if every `T_n` is measurable, it cannot be consistent at both `θ` and `θ'`. Here consistency means: for every `ε>0`, the product-law probability of `ε≤dist(T_n, target)` tends to zero.

These are implications about a variable family, not an existential assertion that every mixture has an unused free coordinate.

### 2. Consistency of a measurable log-criterion maximizer

Quantify any measurable space `Ω`, probability `μ`, dimensions `K,d`, sequences `X_i : Ω → ℝ^K`, `Y_i : Ω → ℝ`, a real function `g(y,x,t)`, and a parameter `θ : ℝ^d`. There is no iid premise in this consistency principle. Quantify data `B` comprising exactly:

- a compact parameter set `Θ⊆ℝ^d` containing `θ`;
- for every `t∈Θ`, integrability of `log(g(Y_0,X_0,t))` and positivity of `g(Y_0,X_0,t)` almost surely (separately for each `t`);
- continuity on `Θ` of `L(t)=∫log(g(Y_0,X_0,t))dμ`;
- for every `t∈Θ`, `L(t)≤L(θ)` and `L(t)=L(θ) ⇒ t=θ`;
- an estimator `B_n : Ω → ℝ^d`, measurable for every `n`, and lying in `Θ` almost surely for every `n>0`;
- for every `n>0`, almost surely on the event that **all** `g(Y_i,X_i,t)>0` for `t∈Θ,i<n`, `B_n` maximizes
  `F_n(t)=n⁻¹Σ_{i<n}log(g(Y_i,X_i,t))` over `Θ`;
- for every `ε>0`, `μ{ω : ∃t∈Θ, ε≤|F_n(ω,t)-L(t)|} → 0`, with probabilities converted to reals;
- the probability that some fitted log in the finite sample fails its strict positivity condition tends to zero.

Conclusion: for every `ε>0`, `μ{ω: ε≤dist(B_n(ω),θ)}→0`. Normalization of `g` as a density is not required in this abstract criterion theorem. Substituting a genuine mixture criterion gives a specialization. A unique population maximizer is a substantive identification premise, distinct from the estimator consistency conclusion.

### 3. Normality of those maximizers

Quantify `Ω,μ,K,d,X,Y` as above, now assume the pairs `(X_i,Y_i)` are iid: each is measurable, the family is jointly independent, and every pair has the same distribution as pair 0. Then quantify `g,θ` and all of `B` from part 2. In addition quantify regularity data with the following fields:

- a real radius `r>0`, with the open sup-metric ball `U=B(θ,r)` contained in `Θ`;
- a measurable subset `S⊆ℝ^K×ℝ` with probability one under the distribution of `(X_0,Y_0)`;
- positivity `g(y,x,t)>0` for every `(x,y)∈S` and every `t∈Θ`;
- measurability of `(x,y)↦g(y,x,t)` for every `t∈Θ`;
- for every `(x,y)∈S`, the map `t↦log(g(y,x,t))` is `C²` on `U`;
- put `s_j(y,x,t)=D_t log(g(y,x,t))[e_j]` and `H_jk(y,x,t)=D_t(s_j(y,x,t))[e_k]`, with `e_j` the coordinate unit vector;
- every `s_j(Y_0,X_0,θ)` is L2 and has expectation zero;
- `I_jk=∫s_j(Y_0,X_0,θ)s_k(Y_0,X_0,θ)dμ` is a positive definite matrix;
- the expected Hessian `A(t)=∫H(Y_0,X_0,t)dμ` satisfies `A(θ)=-I` and is continuous at `θ`;
- every entry of the Hessian is integrable for every `t∈U`;
- for every `ε>0`, the probability of the event
  `∃t∈U, ∃j,k, ε≤|n⁻¹Σ_{i<n}H_jk(Y_i,X_i,t)-A_jk(t)|`
  tends to zero.

Conclusion: `sqrt(n)(B_n-θ)` converges weakly to the centered multivariate Gaussian with covariance `I⁻¹`. Literally weak convergence is quantified over every real continuous bounded function `f` on `ℝ^d`, whose expectations converge to the Gaussian expectation. The Gaussian is Mathlib's multivariate Gaussian pushed forward by the coordinate identity from EuclideanSpace to real-valued coordinate vectors. No QMD hypothesis is used here.

### 4. Information bound for regular asymptotically linear estimators

Quantify any measurable observation space `E`, dimension `d`, dominating measure `ρ`, real functions `f_t(z)`, vector function `s(z)`, a vector `θ`, and `δ>0`. For every `t∈B(θ,δ)`, assume `f_t` is measurable, nonnegative at every `z`, and `Q_t=ρ.withDensity(ofReal(f_t))` is a probability. Also supply the probability instance at `θ`. Every coordinate of `s` is L2 under `Q_θ` and has mean zero.

QMD means, writing

\[
 R_t(z)=\sqrt{f_t(z)}-\sqrt{f_\theta(z)}-
 \tfrac12\bigl(\sum_j(t_j-\theta_j)s_j(z)\bigr)\sqrt{f_\theta(z)},
\]

that there exists `r>0` on which every `R_t²` is integrable under `ρ`, and for every `ε>0` there is another `r>0` such that for all `dist(t,θ)<r`, `∫R_t²dρ ≤ ε dist(t,θ)²`.

Next quantify a real matrix `I` equal entrywise to `∫s_js_kdQ_θ` and assume it positive definite. Next quantify a finite-sample estimator sequence `T_n : E^n → ℝ^d` and an influence function `ψ : E → ℝ^d`, with all of these `RegularAL` premises:

- every `T_n` and `ψ` are measurable;
- every coordinate `ψ_j` is L2 under `Q_θ` and has mean zero;
- for every `ε>0`, under `Q_θ^n`, the probability that the distance between `sqrt(n)(T_n-θ)` and `n^(-1/2)Σ_iψ(z_i)` is at least `ε` tends to zero;
- for **every** fixed local vector `h∈ℝ^d`, under iid observations from `Q_(θ+h/sqrt(n))`, `sqrt(n)(T_n-(θ+h/sqrt(n)))` converges weakly to the **same** centered Gaussian with covariance `C_jk=∫(ψ_j-∫ψ_j)(ψ_k-∫ψ_k)dQ_θ`.

Conclusion: for every real vector `a`, `Σ_jΣ_k a_j(C_jk-(I⁻¹)_jk)a_k≥0`. Regularity includes local-alternative stability, not merely pointwise asymptotic linearity. The conclusion is not one of its premises.

Junk-value audit for all four principles:

- Real Bochner integrals are zero by convention when their integrability requirements fail. The finite expected logs, scores, Hessians, QMD residuals and influence functions used here have explicit integrability or L2 guards. The bounded continuous test functions are integrable under measurable probability experiments.
- `Real.log 0=0`, and `Real.log x=log|x|` for negative `x`. The consistency principle explicitly controls the probability of **any** nonpositive sampled fitted value, so the artificial logs on exceptional samples cannot supply its asymptotic premise. The normality principle has a common positive full-law set. For genuine nonnegative densities their own zero sets have probability zero; the nonidentification equality is also an algebraic equality before any logs are taken. The abstract consistency/normality criteria need not be normalized densities.
- `ENNReal.ofReal` truncates nonpositive input to zero. Genuine mixtures specialize to nonnegative densities; QMD's information-bound branch assumes local nonnegativity and normalization. The raw nonidentification implication admits other weights/functions as well but concludes equality after the same transformation.
- `fderiv` is zero where there is no Fréchet derivative. C² on an open ball makes this fallback irrelevant at the truth and in the Hessian neighborhood. No differentiability at the boundary of `Θ` is used.
- Matrix inverse defaults on singular matrices; positive definiteness ensures a genuine inverse where used. A multivariateGaussian with a non-positive-semidefinite matrix would collapse to a Dirac law; the information matrices are positive definite and the influence covariance is a genuine finite covariance, so that fallback is not used.
- `Real.sqrt x=0` for `x≤0`; all sample-size square roots are of nonnegative natural casts, and density square roots are locally guarded by nonnegativity. At sample size zero, means over `range 0`, `sqrt(0)⁻¹`, and scaled sums use the field convention `0⁻¹=0`. All limiting premises and conclusions ignore this initial term; maximization and set membership in `B` are required only for positive sizes. Empty finite products in observation laws are the unit probability law.
- `prob` uses `toReal`, which sends infinity to zero. All relevant measures are probabilities, including the product experiments, so no infinite mass is turned into a false zero. Uniform error events are measured by the measure's value on arbitrary sets (outer measure); measurability of a random supremum is not required.
- The dimensions are natural numbers and may be zero. In the nonidentification branch `θ≠θ'` rules out `d=0`, and the index `j` rules out `M=0`. Zero-dimensional normality and information principles are harmless degenerate cases; positive-dimensional cases remain in scope. There is no `sInf`, `sSup`, limsup/liminf or truncated subtraction in the target closure. There are no real powers besides ordinary square roots.

Closure coverage: `CP`, `IID`, `RegularAL`, `SampleCP`, `SampleWeakLimit`, `T12WholeStatement`, `W2HessianCP`, `W2InformationBound`, `W2LogGood`, `W2MLConsistency`, `W2MLNormality`, `W2MLProblem` (including its constructor and `estimate`/`parameterSet` projections), `W2MLRegularity` (including its constructor), `W2MixtureNonidentification`, `W2QMD`, `W2UniformCP`, `W2UniformLogCP`, `WeakLimit`, `conditionalModelLaw`, `covarianceMatrix`, `expectedLogLikelihood`, `iidObservationLaw`, `informationMatrix`, `mean`, `mixtureFamily`, `modelHessian`, `modelScore`, `normalVectorLaw`, `populationHessian`, `prob`, `sampleHessian`, `sampleLogLikelihood` and `sampleMean` are unfolded above. The two auxiliary proofs are covered below.

## SAP.P001a.T13

Source: `SAP/P001a/Challenge/Part1.lean:107–110`; proposition: `Defs/Part4.lean:166–181`.

The observation space is `E=ℝ×Bool×Bool`, written `(P,R,B)`. Its measure has density

\[
 1_{[1/4,3/4]}(p)\begin{cases}p&r=\mathrm{true},\\1-p&r=\mathrm{false}\end{cases}
\]

relative to Lebesgue measure in `p` times counting measure in the two Bool coordinates. Equivalently, `P` is uniform on `[1/4,3/4]`, `R|P=p` is Bernoulli `p`, and `B` is an independent fair bit. The outcome attached to a donor is `50+e(B)`, where `e(true)=1,e(false)=-1`.

For a finite sample `s_i=(p_i,r_i,b_i)`, the selected donor for recipient `i` is `some j`, where `j` is chosen by `Classical.choose` from
`{j : r_j=true and for every k with r_k=true, |p_j-p_i|≤|p_k-p_i|}`; if this set has no member, the selector is `none`. This is one nearest donor with arbitrary deterministic tie choice. Define the hot-deck statistic `H_n(s)` as follows. If there is at least one donor, average over all `i`: use `50+e(b_i)` for a donor, use `50+e(b_j)` for a recipient with selected donor `j`, and use `50` if its selector were `none`. If there is no donor, return `50`.

For **any** statistic `T : E^n→ℝ` and sample `s`, the bootstrap enumerates every map `a : Fin n→Fin n`, each with weight `1/n^n`. The resample is `(s_(a(i)))_i`; its bootstrap mean is `m_T(s)=n^(-n)Σ_a T(s∘a)`, and its bootstrap variance is `V_T^*(s)=n^(-n)Σ_a(T(s∘a)-m_T(s))²`. Thus it is the exact conditional variance over independent, uniform with-replacement draws, not a variance over repeated copies of one assignment.

Define the literal constants

\[
 v=3\log 3-1/4,\quad q=1-\exp(-1),\quad
 A=2/q-q/(2-q),\quad B=3/(2q)-(4-q)/(2(2-q)),
\]
\[
 v_b=1/2+A/2+B(2\log3-3/2).
\]

The first conjunct quantifies, in order, a measurable space `Ω`, a probability measure `μ`, and an infinite sequence `Z_i : Ω→E`. Assume each coordinate is measurable, the sequence is jointly independent, all coordinates are identically distributed, and the law of `Z_0` is the density above. Assume for **every** `n`, both `ω↦H_n((Z_i(ω))_(i<n))` and its bootstrap variance are L2 under `μ`. Then:

- for every `n>0`, the expectation of `H_n` is `50`;
- `n Var_μ(H_n)→v`;
- `E_μ[n V_H^*]→v_b`;
- `0<v_b<v`;
- `n V_H^*` does **not** converge in probability to `v`: the negated convergence means the failure of “for every `ε>0`, `μ{ε≤|n V_H^*-v|}→0`.”

The second conjunct **independently** quantifies another measurable probability experiment with the same iid, law, and two L2 assumptions. It concludes that there is a real `C≥0` such that for **every** `n`, `E_μ[(n V_H^*)²]≤C`.

The third conjunct is unconditional: `0<q<1`, `A<3`, `B<3/2`, and `v_b<v`. There is no standard-error, confidence-interval, MAR/MCAR, root-n tightness, or empirical-number assertion in this statement. The docstring describes these as omissions from its selected scope.

Junk-value audit: `n=0` gives an empty hot-deck sample, returning `50`; there is one empty resampling map and the denominator `0^0` is one, so the bootstrap variance is zero. For `n>0` all sample denominators are positive. Returning `50` for no donors is an explicit finite-sample completion on an event of positive probability, not an undefined expectation. Its probability decays with sample size. With a donor present, finiteness guarantees a nearest donor exists, so the internal `none→50` branch is unreachable. Ties are resolved deterministically; for iid continuous scores, distinct nonidentical original observations tie only on a null event; duplicates in bootstrap samples have the same outcome. Expectations and variances are protected by L2 hypotheses (the statistics are also bounded at each size). The measure is finite and normalized, so `toReal ∞=0` cannot affect probabilities. The constant logarithm has positive argument, and `q` and `2-q` are nonzero; their inverses are ordinary inverses. No negative-domain log or sqrt, truncated subtraction, infinite-series default, empty supremum or limsup/liminf occurs. Choice is a donor selection, not a missing value filled from an arbitrary inhabited type.

Closure coverage: `CP`, `IID`, `MatchingFailure`, `T13Statement`, `bootMean`, `bootVar`, `firstSample`, `hotDeck`, `nearestDonor`, `noise`, `resample`, `matchingUnitLaw`, `matchV`, `matchS`, `matchA`, `matchB`, `matchVB`, `mean`, `var` and `prob` are unfolded above. `MatchingFailure` also syntactically mentions the other branch's statistic `causalMatch`; it is the negative of the average of control noise for controls and nearest-control noise for treated units, using zero for a treated unit with no control. In this theorem its Boolean switch is literally false, so only `H_n` and target `50` are selected. All remaining generated closure entries are covered below.

## SAP.P001a.T14

Source: `SAP/P001a/Challenge/Part1.lean:112–115`; proposition: `Defs/Part4.lean:184–198`.

The first conjunct universally quantifies a measurable probability experiment, then an infinite iid sequence `Z_i : Ω→ℝ×Bool×Bool`. Its law and its exact hot-deck and exhaustive with-replacement bootstrap algorithms are **the same explicit density and algorithms unfolded in the T13 section**: `P` uniform on `[1/4,3/4]`, `R|P=p` Bernoulli `p`, independent fair noise bit, one nearest respondent in absolute score distance, fallback `50` for no respondent, average of donor-imputed `50±1` outcomes, and exact average squared deviations over all `n^n` resampling maps. It assumes all the sample hot-deck statistics and bootstrap variances are L2. Its conclusion, fully unpacking the Boolean-false branch, is: expectation `50` for every `n>0`; `n Var(H_n)→3log3-1/4`; `E[n V_H^*]→1/2+A/2+B(2log3-3/2)` for `q=1-exp(-1)`, `A=2/q-q/(2-q)`, `B=3/(2q)-(4-q)/(2(2-q))`; the latter limit is strictly positive and smaller than the former; and `n V_H^*` fails convergence in probability to the former.

The second conjunct is independent of that experiment. Quantify a natural `n`, assume `n>0`, then quantify an arbitrary score vector `p : Fin n→ℝ` and donor indicator vector `r : Fin n→Bool`. Let

\[
 w_j=\begin{cases}
 1+\#\{i:r_i=\mathrm{false},\;j\text{ is the chosen nearest donor for }i\}, & r_j=\mathrm{true},\\
 0,&r_j=\mathrm{false}.
 \end{cases}
\]

Then all of the following hold:

- for every bit vector `e : Fin n→Bool`, `H_n((p_j,r_j,e_j)_j)-50 = n⁻¹Σ_j w_j noise(e_j)`;
- the product over `Fin n` of the half-Dirac-true plus half-Dirac-false measures is a probability;
- under precisely that product measure on noise bits, the mean of `H_n` is `50` and its variance is `Σ_j w_j²/n²`.

The word “conditional” in the docstring refers to holding `p,r` fixed and varying independent fair signs. No regular conditional distribution is directly constructed in this conjunct, but the one-observation law in the first conjunct has those independent signs. If all `r_j` are false, every weight is zero and these assertions give the completed statistic's correct zero variance. There is no confidence-interval or reported-standard-error conclusion.

Junk-value audit: the first conjunct has the same initial-size, fallback, moment, finite-measure and rational/log protections just enumerated for T13. In particular, the explicit expectation and variance limits are not quantities assigned zero for nonintegrability. The second conjunct excludes `n=0`, so `n²` is nonzero; its finite sign space makes every function measurable and integrable. The donor count is a cardinality cast to a real, with no division or truncated subtraction. The product is a genuine probability; variance's infinite-to-zero convention cannot apply. An absent donor set gives weights zero and statistic `50` by definition. An existing donor set has an actual finite minimum. No extra partial function, real-power, log-domain, supremum or unbounded-limit convention is used. The `causalMatch` branch is again in the closure but is not selected.

Closure coverage: the first conjunct's names are exactly those unfolded for T13, now with `T14Statement`; the additional `donorReuseWeight` and `signProductLaw` are unfolded in the second conjunct. The generated entries are covered below.

## SAP.P001a.T15

Source: `SAP/P001a/Challenge/Part1.lean:117–120`; proposition: `Defs/Part4.lean:201–211`.

Write a sample observation `(p_i,d_i,b_i)`, again using the density `1_[1/4,3/4](p)·(p if d=true else 1-p)` against Lebesgue times two counting measures. Thus `P` is uniform on `[1/4,3/4]`, treatment `D|P=p` is Bernoulli `p`, and the noise bit is independent and fair. Put `e_i=1` for a true noise bit and `-1` for a false bit.

For every treated unit choose one control minimizing the absolute score distance, by the same finite `Classical.choose` nearest-donor rule used above, now with eligibility `d_j=false`. Define

\[
 C_n(s)=-\frac1n\sum_{i<n}
 \begin{cases}
 e_j,&d_i=\mathrm{true}\text{ and nearest control }j\text{ exists},\\
 0,&d_i=\mathrm{true}\text{ and no control exists},\\
 e_i,&d_i=\mathrm{false}.
 \end{cases}
\]

The bootstrap mean and variance are the exact mean and squared centered mean over **all** maps `a : Fin n→Fin n`, using `C_n(s∘a)` and denominator `n^n`.

The first conjunct quantifies `Ω`, its measurable structure, a probability `μ`, and an infinite sequence `Z_i` of these observations, in that order. Assume each `Z_i` measurable, joint independence, identical distribution, and distribution of `Z_0` equal to the displayed law. Assume for every `n` that `C_n((Z_i)_(i<n))` and its exact bootstrap variance are L2. The conclusion is:

- for every `n>0`, `E[C_n]=0`;
- `n Var(C_n)→v=3log3-1/4`;
- `E[n V_C^*]→v_b=1/2+A/2+B(2log3-3/2)`, with `q=1-exp(-1)`, `A=2/q-q/(2-q)` and `B=3/(2q)-(4-q)/(2(2-q))`;
- `0<v_b<v`;
- it is false that, for every `ε>0`, `μ{ε≤|n V_C^*-v|}→0`.

The second conjunct independently quantifies a measurable probability experiment and iid `Z_i` with the same law. **No two L2 premises occur in this conjunct.** Define

\[
 \widehat\alpha_n(s)=\max\left(1/8,\min\left(3/8,
 \frac1n\sum_{i<n}\left(1_{\{d_i=\mathrm{true}\}}-(p_i-1/4)\right)\right)\right).
\]

Conclusion: for every `ε>0`, `μ{ε≤|αhat_n-1/4|}→0`. This is just consistency of an additive score intercept. The theorem does not define or analyze a statistic matched on the estimated scores, and it asserts no equality of true-score and estimated-score matches, first-step variance adjustment, standard-error inconsistency or confidence-interval failure.

Junk-value audit: the empty sample has `C_0=-(0/0)=0`, the empty bootstrap has denominator `0^0=1` and variance zero, and `αhat_0=max(1/8,min(3/8,0/0))=1/8`. None of these initial values affects a limit at infinity. For `n>0` all sample-size divisions are defined in the ordinary sense. With no controls the whole matching statistic is zero; with controls the finite minimum exists. Ties are deterministic and depend only on scores and eligibility, not noise. Bootstrap duplicate controls have the same outcome. The `clip` function is literally `max a (min b x)`; its endpoints `1/8<3/8` are correctly ordered, so there is no reversed-interval behavior. The intercept summands and both statistics are bounded at each size under the stated law; the explicit first-conjunct L2 assumptions prevent undefined moments, and boundedness and iid measurability supply the intercept's usual probabilistic meaning. Variance and probabilities cannot use `toReal ∞=0` under these premises. Constant logarithms and `q,2-q` have valid arguments and nonzero denominators. No square root, real power, truncated subtraction, supremum, infimum or limsup/liminf occurs. The unselected hot-deck branch is in `MatchingFailure`'s syntactic closure and has the finite-sample definitions described above.

Closure coverage: `CP`, `IID`, `MatchingFailure`, `T15Statement`, `bootMean`, `bootVar`, `causalMatch`, `clip`, `estimatedMatchIntercept`, `firstSample`, `hotDeck`, `nearestDonor`, `noise`, `resample`, `matchingUnitLaw`, `matchV`, `matchS`, `matchA`, `matchB`, `matchVB`, `mean`, `var` and `prob` are unfolded above, with the generated entries inspected below.

## Generated declarations in the closures

`scratch/Inspect.lean` prints every source-line-zero closure entry. The proofs named `T11Statement._proof_1`, `T11Statement._proof_2`, `T12Statement._proof_1`, `T14Statement._proof_1`, `W2MatchingMarginals._proof_2`, `estimatedMatchIntercept._proof_1/_proof_2/_proof_3`, `geoMass._proof_1`, `hotDeck._proof_1`, `matchingUnitLaw._proof_1/_proof_2` and `signProductLaw._proof_2` are only natural-number `AtLeastTwo` instances used for numeric literals such as rational denominators. `disjointMixtureLikelihood._proof_1` is a `NeZero (2+1)` index instance. `signProductLaw._proof_1` is the usual `ENNReal` scalar-tower instance. `hotDeck.match_1` is the ordinary Option eliminator, applying the `some` branch to its index and the `none` branch to unit. None adds a mathematical assumption, arbitrary real value, or different statistic. These facts also explain why some entries bear names of definitions not otherwise used by the corresponding target.

## Post-blind precision note

Added after the claim and record comparison; the blind text above is preserved. In T12's information branch, the local normalization hypothesis at `Defs/WholeW2.lean:433–437` applies only inside a ball. For each fixed local vector h, `θ+h/sqrt(n)` is in that ball for all sufficiently large n. The finitely many preceding local-alternative measures in `RegularAL` (`Defs/Part2.lean:167–169`) need not be probabilities; a bounded-function Bochner integral could take its nonintegrable default there. The blanket statement above that all product experiments are probabilities should thus be read as “all truth experiments and all sufficiently large local-alternative experiments.” This does not affect any limiting premise or conclusion, and changes none of the claim-stage assessments. The common finite-probability statements about CP and truth laws are unchanged.
