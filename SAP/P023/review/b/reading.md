# Blind reading of P023

This document was written and saved before opening either `claims.json` or `record.json`. The source of this reading is `SAP/P023/Defs{,/Part1,…,/Part6}.lean` and `SAP/P023/Challenge{,/Part1}.lean`. All twelve Challenge declarations are closed propositions, with no additional theorem parameters. Quantifiers inside their definitions are detailed below. The docstrings are descriptions, not hypotheses.

## Mathematical dictionary, including totalization conventions

All finite sums below run over the indicated finite type, without a normalization by sample size. A finite type is not implicitly nonempty. `Fin n` is the set of integers from 0 through n−1. Real division uses 1/0 = 0. Natural-number subtraction is truncated at zero; the subtraction in the polynomial column index occurs only after indices 0 and 1 have been excluded, so its active values are 1,…,J. Natural ceiling is the least nonnegative integer at least the given real, and thus is zero for negative inputs. All other arithmetic displayed below is real arithmetic unless explicitly integral.

For a finite design matrix X, fitted values are Xc, meaning `(Xc)_i = Σ_j X_ij c_j`. `IsOLS X y c` means the normal equations `Σ_i X_ij(y_i−(Xc)_i)=0` for every column j. It does not separately assert a minimization problem. `FullRank X` means `Xc=0 ⇒ c=0` for every coefficient vector. The chosen OLS coefficient vector is Hilbert choice of a vector satisfying the normal equations. If solutions exist it chooses one; it does not supply existence or rank as a hypothesis. Polynomial regression of degree J uses columns `(1,d,x,x²,…,x^J)` and the estimator `b_J(x,d,y)` is the coefficient of d. With J=0 the columns are just `(1,d)`.

The data condition `TwoParty x d` says, for every observation i: `−1≤x_i≤1`, `d_i∈{0,1}`, `x_i>0 ⇒ d_i=1`, and `x_i<0 ⇒ d_i=0`. At x_i=0 it allows either binary value. Write `D(x)=1_{x≥0}`; this is `party` and fixes ties as 1 when it is used instead of a supplied d.

The close set is `C_k={i:−k<x_i≤k}`. Let `n_1=Σ_{C_k}d_i` and `n_0=Σ_{C_k}(1−d_i)`. The finite RD statistic is `R_k(y)=Σ_{C_k}d_i y_i/n_1−Σ_{C_k}(1−d_i)y_i/n_0`. `Condition1 k x` means `(∃i,0<x_i<k) ∧ (∃i,−k<x_i<0)`, with separate witnesses. Localization of an estimator E means `∀y ∀y', (∀i∈C_k,y_i=y'_i) ⇒ E(y)=E(y')` with unrestricted real outcome vectors.

For bins put `q=ceil_nat((1−k)/(2k))` and `M=2q`. Bin 0 is `−M−1≤x/k≤−M+1`; bin j>0 is `2j−M−1<x/k≤2j−M+1`. The printed coarsened regression has columns `(1,d,1_bin1,…,1_binM)`, omitting bin 0. A second representation labels a point by `B_k(x)=min(M,ceil_nat((x/k+M−1)/2))`, a member of `{0,…,M}`. The central label is q. For any finite label set, `IsBinOLS B d y a b` means both `Σ_{B_i=j}(y_i−a_{B_i}−b d_i)=0` for each label j and `Σ_i d_i(y_i−a_{B_i}−b d_i)=0`. `CoarsenedOLS k x d y b` means that such an a exists with B_i=B_k(x_i). It is a relation on coefficients, not another Hilbert-choice estimator.

For a bin j its mean is `Σ_{B_i=j}z_i / #{i:B_i=j}`; this is zero for an empty bin. Demeaning is `z_i−mean_{B_i}(z)`, so every mean actually subtracted at an observed i has a nonempty bin. The coarsened weight is zero off C_k and `d_i/n_1−(1−d_i)/n_0` on C_k. Let r^fin be the residual from regressing d on `(1,x,…,x^J)`, using the chosen normal-equation solution, and let `w_i=r_i^fin/Σ_l(r_l^fin)²`.

Measures are Mathlib measures on the Borel measurable spaces on real Euclidean spaces, or on the explicitly quantified measurable space Ω. A probability law means total measure 1. `MarginSupport μ` means `μ([-1,1]^c)=0`, with no density assertion. For a joint law ν on real pairs (X,Y), μ is its pushforward by first coordinate. `ConditionalMean ν m` means Y and m(X) are integrable and, for every globally bounded measurable real function t, `∫t(X)Y dν=∫t(X)m(X)dν`. No separate global measurability of m is included in that definition. Integrability includes almost-everywhere strong measurability.

Expectation is the real Bochner integral. Mathlib defines that integral to be zero if its integrand is not integrable (`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`, integral and integral_undef). Restricted integrals use the restricted measure. Measure evaluation on arbitrary sets is the measure's outer-measure extension. Pushforwards of measurable maps are the usual distributions; Mathlib's totalized `Measure.map` uses an arbitrary Dirac mass on a nonzero measure when the map is not almost-everywhere measurable (`Measure/Map.lean`). The maps used explicitly in the witness families are continuous or Borel piecewise continuous.

The chosen degree-J projection p_J is Hilbert choice among real polynomials p with natural degree at most J and `E_μ[(D−p)x^j]=0` for every natural j≤J. Zero polynomial has natural degree 0. Write `r_J=D−p_J`, `v_J=E_μ[r_J²]`, `A_J=E_μ[|r_J|]/v_J`, and `L_J(h)=E_μ[r_J h]/v_J`. Moment positive definiteness means `E_μ[(a_0+a_1D+Σ_{j=1}^J a_{j+1}x^j)²]>0` for every nonzero coefficient vector a. The population d coefficient b_J(μ,m) is the d entry of Hilbert choice among vectors solving all population normal equations for regressing m on `(1,D,x,…,x^J)`. Choice alone supplies no existence or uniqueness assertion. The population RD is the mean of m over `(0,k]` minus its mean over `(−k,0)`, each computed as the restricted integral divided by the corresponding measure converted to a real. It excludes x=0 on both sides. ENNReal.toReal sends infinity to zero, although a probability law has finite masses.

Let U be uniform probability on [-1,1], namely one half of Lebesgue measure restricted there. The uniform polynomials displayed in the definitions are
`P_1(x)=1/2+3x/4` and `P_7(x)=1/2+(11025x−40425x³+63063x⁵−32175x⁷)/4096`.
Let `c_n=binom(2n,n)/4^n`. Supremum approximation error is `sSup{|h(x)−p(x)|:x∈[-1,1]}` and RMS error is `sqrt(E_μ[(h−p)²])`. Real sSup/sInf are conditionally complete order operations, not extended-real extrema; they represent actual extrema only for nonempty sets bounded in the relevant direction. All infima below are the literal real sInf of the indicated sets. Prediction risk is `Q_ν(f)=∫(Y−f(X))²dν`, and fitted risk `Q_{ν,J}` is the infimum over all coefficient vectors in the polynomial-plus-D model.

The noise law is the equal mixture of point masses at ±1/10. `W(μ,h)` is the law of `(X,1/2+h(X)+e)` for independent X∼μ and e with that noise law. Let `s_{a,η}(x)=a max(−1,min(1,x/η))`.

For the clustered family, `T_{c,w}(x)=max(w−|x−c|,0)/w²`, and
`ρ_d(x)=d⁴/2+(1−d⁴)(T_{1/2,d/2}(x)+T_{−1/2,d/2}(x))/2`.
The margin law μ_d has density max(ρ_d,0) on [-1,1], zero outside. To define h_d, for x≥0 put it equal to 0 before 1/2−d; to `1/2−d−x` on `[1/2−d,1/2−d/2]`; to `x−1/2` on `(1/2−d/2,1/2+d/2]`; to `1/2+d−x` on `(1/2+d/2,1/2+d]`; and to zero afterward. For x<0 put h_d(x)=−h_d(−x), using that positive-side formula. These formulas specify endpoint choices as in the Lean conditionals.

`Z_N→_P z` means `∀ε>0, P{ω:ε<|Z_N(ω)−z|}→0`, with probabilities in [0,∞] and its topology. The definition does not demand measurability of Z_N. `IIDSample P ν sample` means P has mass 1, every sample_i is measurable, every sample_i pushes P to ν, and the family of generated sigma algebras is mutually independent (Mathlib iIndepFun). The N-sample estimators use the first N draws, x_i=X_i, d_i=D(X_i), y_i=Y_i. Write them `bhat_{N,J}` and `Rhat_{N,k_N}`. `OLSAdmissible` for degrees J_N means `P{the N by (J_N+2) design is not full rank}→0`. `RDAdmissible` means `P{n_1≤0 or n_0≤0}→0`. These predicates assert probabilities of bad designs, not consistency of the estimators.

`UsualRDRegularity ν m k` means μ{0}=0, `N μ((0,k_N])→∞`, `N μ((−k_N,0))→∞`, and there exist δ>0 and σ²≥0 such that for every measurable A⊆[-δ,δ], `∫_{X∈A}(Y−m(X))²dν≤σ² μ(A)`.

`RepairedRegularity ν α β h c δ L σ²` means: ν is a probability law; μ is supported on [-1,1]; μ{0}=0; Y² is integrable; c>0; 0<δ≤1; L≥0; σ²≥0; every measurable A⊆[-δ,δ] has `c Leb(A)≤μ(A)`; h(0)=0; h is L-Lipschitz on [-1,1]; m(x)=α+βD(x)+h(x) is the conditional mean in the test-function sense above; and the preceding integrated conditional-noise bound holds for every such A with this δ and σ². No global density or upper density bound is required. Put `K=3(1+π⁴)/(4π)`. The smallest moment eigenvalue λ_J is the infimum of `E_μ[(a_0+a_1D+Σa_{j+1}x^j)²]` over coefficient vectors with `Σa_j²=1`.

## T1 — SAP.P023.T1

This is a conjunction about a specified data set, with no antecedent. Its six observations have

|i|x_i|d_i|y_i|y'_i|w_i|
|--|--|--|--|--|--|
|0|−3/4|0|37/80|37/80|20299/139202|
|1|−1/4|0|39/80|39/80|−59901/139202|
|2|−1/400|0|3999/8000|3999/8000|−49800/69601|
|3|1/400|1|4801/8000|4801/8000|49800/69601|
|4|1/4|1|49/80|49/80|59901/139202|
|5|3/4|1|51/80|259/400|−20299/139202|

With k=1/200 and J=1 it asserts: TwoParty and Condition1 hold; the design is full rank; y is exactly the fitted value at coefficients (1/2,1/10,1/20); for every outcome vector z the polynomial coefficient is Σw_i z_i; its value on y is 1/10, its value on y' is 1371721/13920200, their difference is the nonzero number −20299/13920200; y=y' on the close set and `∀i,y'_i=y_i+1_{i=5}/100`; both RD statistics are 401/4000; M=200 and labels are (25,75,100,100,125,175); the coarsened normal equations have d coefficient 401/4000 for both y and y', and every such coefficient equals that value; all y_i,y'_i lie strictly between 0 and 1; polynomial OLS is not localized. Additionally C_k={2,3}; RD(y)=y_3−y_2; RD as a function of arbitrary outcomes is localized; and `∀y ∀y' ∀b ∀b'`, equality of y,y' on C_k and the two coarsened normal-equation assertions imply b=b'.

## T2 — SAP.P023.T2

Again there is no antecedent. J=7, k=1/5, the sixteen margins are `(−1,−7/8,−3/4,−5/8,−1/2,−3/8,−1/4,−1/8,1/8,1/4,3/8,1/2,5/8,3/4,7/8,1)`, and d is 0 on indices 0–7 and 1 on indices 8–15. The specified y vector is
`(11/25,94859017/209715200,755573/1638400,3929035/8388608,6079/12800,100923253/209715200,798719/1638400,103546879/209715200,127139841/209715200,1003521/1638400,129763467/209715200,8001/12800,26492169/41943040,1046667/1638400,135827703/209715200,33/50)`.
y' agrees except its last entry is 67/100. The weight vector is
`(−175,725,−685,−643,554,1289,239,−2911,2911,−239,−1289,−554,643,685,−725,175)/1607`.

It asserts TwoParty, Condition1, full rank, and exact model `y_i=1/2+d_i/10+x_i/20+x_i^7/100`. For every real vector z, polynomial OLS is its dot product with these weights. Its y value is 1/10; its y' value is 3249/32140; the difference is the nonzero number 7/6428. The vectors agree on C_k and `∀i,y'_i=y_i+1_{i=15}/100`. Both RD values are 11796481/104857600. M=4 and labels are `(0,0,0,0,1,1,1,2,2,3,3,3,4,4,4,4)`. Each coarsened regression has that RD coefficient, and every coarsened coefficient for either vector equals it. All outcomes lie strictly between 0 and 1. The polynomial estimator is not localized, and every displayed weight is nonzero. Finally C_k={7,8} and RD(y)=y_8−y_7.

## T3 — SAP.P023.T3

The theorem is the conjunction of the following eight propositions, whose quantifiers are independent.

1. For every finite observation type, every k with 0<k<1, every x,d,y satisfying TwoParty, and every real b: the bin-intercept normal equations with coefficient b hold if and only if there exists a coefficient vector for the printed omitted-bin design satisfying its normal equations and having d coefficient b. No close-count or rank hypothesis occurs here.
2. For every finite observation type, k with 0<k<1, x,d,y satisfying TwoParty, positive n_1,n_0, and b satisfying the bin-intercept normal equations: b is both Σ_i coarsenedWeight_i y_i and RD(y); weights vanish off C_k; each close winner has weight 1/n_1, and each close loser has weight −1/n_0.
3. For every finite observation type, k with 0<k<1, x,d,y,y' satisfying TwoParty, positive n_1,n_0, equality y=y' on C_k, and b,b' satisfying their respective bin normal equations: b=b'. Outcome vectors are universally quantified before the equality and normal-equation hypotheses.
4. For every finite observation type with decidable equality, every J≥1, and x,d satisfying TwoParty and full rank of `(1,d,x,…,x^J)`: writing r,w for the finite residual and weight, `r·d=r·r>0`; r is orthogonal to x^j for every natural j≤J; `∀y,b_J(y)=r·y/(r·r)=w·y`; `Σw=0`, `Σw_i x_i^j=0` for 1≤j≤J, `Σw_i d_i=1`; and `∀y ∀i ∀t,b_J(y+t1_i)−b_J(y)=w_i t`.
5. For every finite observation type with decidable equality, every J≥1, every 0<k<1 and x,d satisfying TwoParty and full rank, existence of both a winner and a loser, and positive close counts on both sides: at most J distinct negative margins and at most J distinct positive margins have zero polynomial weight. If more than 2J distinct nonzero margins occur outside C_k, there exist an outside index i and outcomes y,y' that agree at every other index and on C_k, for which polynomial coefficients differ and RD values agree; additionally every pair of coarsened coefficients agrees, conditional again on the positive-close-count conditions. Distinct margin values, not the number of observations with repetitions, are counted.
6. For every finite observation type, every measurable Ω, probability P, J≥1, x,d satisfying TwoParty and full rank, real α,β, arbitrary real function h, and integrable random outcomes Y_i with `E_P Y_i=α+βd_i+h(x_i)`: `E_P bhat−β=r·h(x)/(r·r)`; for every polynomial p of degree at most J agreeing with h at all observed margins, `E_P bhat=β`. Defining `u_i=Y_i−(α+βd_i+h(x_i))`, if every u_i² is integrable and `E_P[u_i u_l]=0` whenever i≠l, then `E_P[(bhat−E_P bhat)²]=Σ_i w_i² E_P[u_i²]`. For every i and σ²>0, w_i≠0 implies w_i²σ²>0. There is no assumption of mutual independence of these finite outcomes, no density requirement, and no h(0)=0 condition.
7. Under U the projection polynomials are P_1,P_7 at every real x; `v_1=1/16`, `v_7=1225/65536`; normalized residuals at 9/10 are −14/5 and −20283449/6125000; `E_U[1_{|x|≥1/2}r_1²]/v_1=1/8` and the degree-seven counterpart is 572158921/10276044800. The two means `m_1=1/2+D/10+x/20` and `m_7=m_1+x^7/100` have population coefficients 1/10 in their respective degrees. For every 0<k≤1 their RD values are `1/10+k/20` and `1/10+k/20+k^7/400`, and each population RD tends to 1/10 as k decreases to zero.
8. For every measurable Ω, P, arbitrary sample map (not assumed IID or measurable), J,k,β: assume P is a probability law, J≥1, every k_N>0, fixed-degree OLSAdmissible and RDAdmissible, and separately that both bhat_{N,J} and Rhat_{N,k_N} converge in P-probability to β. Then their difference converges in P-probability to zero. It asserts no new consistency criterion beyond those hypotheses.

## T4 — SAP.P023.T4

This is the conjunction of the following population, prediction and sampling assertions.

For every real a,η with a>0 and 0<η≤1, s=s_{a,η} is globally continuous, odd, has s(0)=0 and is globally (a/η)-Lipschitz. The law W(U,s) has conditional mean 1/2+s. For every 0<k≤η, population RD is ak/η and its limit as k↓0 is zero. For every J≥1 the population polynomial coefficient equals `2a−(a/v_J)∫_[0,η] r_J(x)(1−x/η) dx`, where this displayed integral is Lebesgue, not U expectation. The degree-one value is `2a(1−η)²`. The U mean square error of s from the jump function a(2D−1) is a²η/3. For every J≥1 the infimum of U squared approximation errors over the polynomial-plus-D model is between 0 and a²η/3. For every fixed J≥1 and a>0, the population coefficient tends to 2a as η↓0.

At a=1/20, η=1/10000, the degree-one coefficient is 99980001/1000000000 and the degree-seven coefficient is `4896723787999993532000048047999857/49000000000000000000000000000000000`. W-almost surely, `7/20≤Y≤13/20`, and a²η/3=1/12000000.

For every a>0 and 0<η≤1, let ν=W(U,s). It is a probability with margin law U, and its conditional-mean prediction risk is 1/100. For every J≥1, fitted risk lies in `[1/100,1/100+a²η/3]`; for every measurable f with integrable squared prediction error, `Q_{ν,J}−Q_ν(f)≤a²η/3`; and `(Q_{ν,J}−1/100)/Q_{ν,J}≤100a²η/3`. If a=1/20 the degree-seven coefficient for every such η is `1/10−(4096/6125)η+(6/5)η²−(33/25)η⁴+(858/875)η⁶−(143/490)η⁸`.

For every measurable Ω, P, sample, IIDSample with the fixed a=1/20,η=1/10000 law, positive sequence k_N→0 with Nk_N→∞, OLSAdmissible in degrees 1 and 7, and RDAdmissible: bhat_{N,1} and bhat_{N,7} converge in probability to the two displayed population constants, while sample RD converges to zero.

For every J≥1 and every x≠0, `r_J(−x)=−r_J(x)` under U. For every x>0, `r_1(x)=1/2−3x/4` and `r_7(x)=1/2−(11025x−40425x³+63063x⁵−32175x⁷)/4096`. Both displayed v constants are repeated. For every J≥1 the fixed witness law has relative risk bound 1/120000. For every real a, a²η/3→0 as η↓0. Finally for every real a and every natural J, including J=0, there exists a coefficient vector representing `1/2+a(2D−1)` identically for every real x in the polynomial-plus-D design.

## T5 — SAP.P023.T5

For every 0<d≤1/2: μ_d is a probability supported on [-1,1], with no mass at zero, and every interval (a,b) with −1≤a<b≤1 has positive mass. ρ_d is globally continuous and at least d⁴/2 on [-1,1]. The function h_d is globally continuous, zero at 0 and whenever |x|≤1/2−d, odd, globally 1-Lipschitz, bounded in absolute value by d/2, and has supremum absolute value d/2 on [-1,1]. The law W(μ_d,h_d) has conditional mean 1/2+h_d.

Its moments satisfy `E X=E h_d=E[(D−1/2)h_d]=0`, `E[XD]=1/4`, `E X²=(1−d⁴)(1/4+(d/2)²/6)+d⁴/3`, and `E[Xh_d]=(1−d⁴)(d/2)²/6+2d⁴(d/2)³`. The degree-one population coefficient for mean 1/2+h_d equals `−(1−d⁴+6d⁵)/(1−d⁴+2d²)`. Population RD is zero for every 0<k<1/2−d. `E h_d²≤(d/2)²`.

At d=1/1000 this coefficient is `−499999999999503/500000999999500` and `799/2000≤Y≤1201/2000` almost surely under W. As d↓0 the coefficients tend to −1. There is no real C with `∀d∈(0,1/2], |b_1(μ_d,1/2+h_d)|≤C(d/2)`.

Independently, for every 0<d≤1/2, ν=W(μ_d,h_d) is a probability, has margin μ_d, satisfies `Q_ν(1/2+h_d)=1/100`, `Q_ν(1/2)=1/100+E_μ h_d²`, and for every measurable f with integrable squared error, `Q_ν(1/2)−Q_ν(f)≤(d/2)²`. For every J≥1 fitted risk is at most the constant-predictor risk and, for every such f, `Q_{ν,J}−Q_ν(f)≤(d/2)²`.

Finally for every natural J, zero polynomial has natural degree at most J and `∀x∈[-1,1],|h_{1/1000}(x)−0|≤1/2000`; and d/2→0 as d↓0.

## T6 — SAP.P023.T6

U is a probability supported on [-1,1]. Its amplification A_J tends to +∞. There exist a real C≥0 and natural J₀ such that for every J≥J₀ with J≥1, `|A_J−(4/π)log J|≤C`. For each J≥1, A_J is exactly the real supremum of L_J(h) over all h continuous on [-1,1], with h(0)=0 and |h|≤1 on that interval.

There exist ONE function h:ℝ→ℝ and ONE strictly increasing degree sequence D:ℕ→ℕ such that: h is continuous on [-1,1], h(0)=0, |h|≤1/12 there; for every natural m≥1, `L_{D(m)}(h)≥m/4` and `b_{D(m)}(U,1/2+h)≥m/4`; for every J≥1, `b_J(U,1/2+h)=L_J(h)`; for every real B and natural J₀ there is J≥J₀ with `B≤b_J(U,1/2+h)`; the mean 1/2+h is continuous on [-1,1], equals 1/2 at zero, and lies in [5/12,7/12] there; the coefficients along D(m) tend to +∞, the full sequence of coefficients does not tend to zero; population RD tends to zero as k↓0; and there is no real L bounding `|h(x)−h(x')|≤L|x−x'|` for all x,x'∈[-1,1]. The statement does not assert existence of an IID sample or sampling limit for this particular witness.

## T7 — SAP.P023.T7

First, universally quantify in this order: joint law ν, probability/support/second-moment hypotheses, α,β,h, measurability of h, boundedness of h on [-1,1], ConditionalMean for `m=α+βD+h`, J≥1 and positive definiteness of its moment matrix. With μ=margin ν, v=v_J, b=b_J(μ,m), it asserts:

* the chosen p_J satisfies the degree and normal-equation definition of projection, v>0, and r_J is orthogonal to every polynomial of degree at most J;
* `E r_J=0`, `E[r_JD]=v`, and `b=L_J(m)`;
* for every polynomial p of degree at most J, `b−β=L_J(h)=L_J(h−p)`, `|b−β|≤A_J supError(h,p)` and `|b−β|≤rmsError(h,p)/sqrt(v)`;
* A_J≥2; for every polynomial p of degree at most J, h=p μ-almost everywhere implies b=β;
* for every t>0, `|b−β|≤t` iff `|E[r_Jh]|≤tv`; if `A_J inf_{deg p≤J}supError(h,p)≤t` then `|b−β|≤t`; and if `inf_{deg p≤J}rmsError(h,p)≤t sqrt(v)` then `|b−β|≤t`.

Second it asserts the following constants under U: U is a supported probability; `∀J≥1,v_J=c_floor((J+1)/2)²/4` (integer division is floor); p_1=P_1 and p_7=P_7 at every real x; `v_1=1/16`, `v_7=1225/65536`; `E|r_1|=5/24`; `A_1=10/3`; `1/sqrt(v_1)=4`, `1/sqrt(v_7)=256/35`; and `4.7642006857252250<A_7<4.7642006857252260`.

Third it includes the entire finite residual and weight proposition, item 4 of T3 with exactly its quantifiers and hypotheses. Fourth it universally quantifies: finite observation type; measurable Ω; probability P; J≥1; x,d satisfying TwoParty AND `∀i,d_i=D(x_i)`; full rank; α,β,h; integrable Y_i; and `E Y_i=α+βd_i+h(x_i)`. It concludes `Σr_i²>0` and `E bhat−β=r·h(x)/(r·r)`. The equality d=D(x) is extra at tied margins compared with TwoParty alone. Neither population nor finite bias propositions assume h(0)=0 or continuity of h.

## T8 — SAP.P023.T8

Universally quantify: measurable Ω; P; ν; sample; α,β,h,c,δ,L,σ²; all the RepairedRegularity conditions spelled out above; IIDSample P ν; bandwidth sequence k; every k_N>0; k_N→0; Nk_N→∞; RDAdmissible; OLSAdmissible for every fixed J≥1; and, for EVERY degree schedule D_N→∞ for which `(D_N+2)²/(N λ_{D_N}³)→0`, OLSAdmissible for that schedule. The growing-schedule admissibility hypothesis precedes every conclusion and is uniform over schedules. With μ=margin ν and m=α+βD+h it concludes ALL of:

1. For every J≥1 moment positive definiteness and `v_J≥cδ/(4(J+1))`.
2. For every J≥1 there exists a polynomial p of degree at most J with p(0)=0 and `supError(h,p)≤4KL/(J+1)`.
3. For every J≥1, `|b_J(μ,m)−β|≤8KL/sqrt(cδ(J+1))`; and b_J→β as J→∞.
4. For every fixed J≥1, bhat_{N,J}→_P b_J(μ,m).
5. For every real 0<k'≤δ, `|populationRD(μ,m,k')−β|≤2Lk'`; sample RD→_P β.
6. For every ε>0 there exists J₀ such that EVERY J≥J₀ with J≥1 has both `bhat_{N,J}−Rhat_{N,k_N}→_P b_J−β` and `|b_J−β|<ε`. Here J is fixed before the probability limit in N.
7. For EVERY D_N→∞ satisfying the displayed rate, `bhat_{N,D_N}−b_{D_N}(μ,m)→_P0` and `bhat_{N,D_N}−Rhat_{N,k_N}→_P0`.
8. There EXISTS a degree schedule D_N≥1 for every N, tending to infinity, with the displayed rate tending to zero. The expression at N=0 uses totalized real division but limits are at infinity.

## T9 — SAP.P023.T9

For EVERY finite set S⊆ℕ×ℕ, every 0<k<1, every x,d,y indexed by the subtype of members of S, with TwoParty and Condition1, and every real b satisfying the bin-intercept normal equations: writing B_i=B_k(x_i), r_i=d_i−mean_{B_i}(d), z_i=y_i−mean_{B_i}(y), one has `∀i ∀j∈{0,…,M}, x_i belongs to printed bin j iff B_i=j`; the observed central bin is exactly C_k; r_i=0 off C_k; `Σ_{C_k}r_i²>0`; and `b=(Σ_{C_k}r_i²)^{-1}Σ_{C_k}r_i z_i`. The finite-set subtype carries no multiplicity; different pairs may have equal margins. S=∅ is syntactically quantified but cannot satisfy Condition1.

## T10 — SAP.P023.T10

The first conjunct is exactly coarsened localization, item 3 of T3, with its positive close counts and normal-equation existence hypotheses. The second conjunct is the negation of the following universal statement, including this quantifier order: for every n, every natural J (including 0), every x,d:Fin n→ℝ, and every real k, if 0<k<1, TwoParty, Condition1, full rank of the polynomial design, AND there exists a coefficient vector c whose fitted values at ALL observations lie strictly between 0 and 1, then the polynomial estimator is localized for ALL real outcome vectors. Thus it asserts the existence of a failing design for this localization assertion; it does not assert that every polynomial design fails localization. The fitted-value existence hypothesis is independent of the arbitrary outcome vectors quantified by localization.

## T11 — SAP.P023.T11

For every finite observation type, every real k with 0<k<1, every x,d,y satisfying TwoParty and Condition1, and every coefficient vector c satisfying the normal equations for the printed coarsened regression `(1,d,bin1,…,binM)`, its d entry is RD(y). There is no full-rank or no-empty-bin assumption, and it is an assertion about every solution rather than a chosen solution. Condition1 supplies both nonzero close denominators under TwoParty.

## T12 — SAP.P023.T12

This is the NEGATION of a closed universally quantified proposition. The proposition being negated universally quantifies in this order: measurable Ω; P; joint law ν; sample; functions g,f; real α; ν probability; μ supported on [-1,1]; integrable Y²; g continuous on [-1,0); f continuous on [0,1]; g(x)→α as x↑0; ConditionalMean for the piecewise mean `m(x)=g(x)` when x<0 and f(x) otherwise; IIDSample P ν; moment positive definiteness for EVERY J≥1; sequence k with all k_N>0, k_N→0, Nk_N→∞; existence of k₀>0 such that EVERY interval (a,b) contained in [-k₀,k₀] with a<b has positive μ mass; and UsualRDRegularity (including no atom at zero, diverging expected counts separately on both sides, and the local integrated noise bound).

For ALL those objects and hypotheses, the proposition being negated concludes BOTH `Rhat_{N,k_N}→_P(f(0)−α)` and: for every ε>0 there exists J₀ such that every fixed J≥J₀ with J≥1 satisfies `bhat_{N,J}−Rhat_{N,k_N}→_P b_J(μ,m)−(f(0)−α)` and `|b_J(μ,m)−(f(0)−α)|<ε`. T12 therefore asserts at least one instance satisfying ALL these hypotheses in which this conjunction fails. It does not merely negate a premise-free continuity statement, does not assume estimator consistency, and does not include OLSAdmissible or RDAdmissible as premises of the proposition it refutes. The auxiliary `appendixSmooth(g,f,α,β)` means g−α on x<0 and f−(α+β) otherwise, but is not used in this proposition.

## Mathlib interpretation references inspected in the blind stage

`MeasureTheory/Integral/Bochner/Basic.lean` (real Bochner integrals and nonintegrable-zero convention); `MeasureTheory/Measure/Map.lean` (pushforwards and nonmeasurable convention); `MeasureTheory/Measure/Restrict.lean`; `MeasureTheory/Measure/WithDensity.lean`; `Probability/Independence/Basic.lean` (independence of generated sigma algebras); `Algebra/Order/Floor/Defs.lean` (natural ceiling); `Order/ConditionallyCompleteLattice/{Defs,Basic}.lean` (conditional extrema). Polynomial evaluation, finite sums, absolute value, real square root, and filter limits have their ordinary Mathlib meanings; no custom SAP structure overrides them.
