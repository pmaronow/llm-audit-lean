# Blind reading of the Challenge

This file was written from `SAP/P039/Defs.lean`, `Defs/Part1.lean` through `Part5.lean`, `Challenge.lean`, `Challenge/Part1.lean`, and the Mathlib definitions they use, before opening `claims.json` or `record.json`. There are seven theorem stubs, with no theorem-level parameters: `SAP.P039.Ti : TiStatement`, for i=1,...,7. The quantifiers below are inside these propositions. Challenge docstrings are descriptions, not additional hypotheses.

## Mathematical meanings of the definitions

`Fin n → ℝ` is the space of real vectors with coordinates 0,...,n−1. `Matrix (Fin n) (Fin p) ℝ` is an n by p real matrix. Dot product is Σ_i v_i w_i, squaredLength is Σ_i v_i², and mulVec is ordinary matrix-vector multiplication. Matrix rank is the real dimension of the range of its linear map. FullColumnRank(A) means that b ↦ Ab is injective. The matrix inverse is Mathlib's nonsingular inverse: adj(A)/det(A) when invertible, and the zero matrix when singular. The definitions do not themselves require invertibility.

Write B_A(y)=(AᵀA)⁻¹Aᵀy, e_A(y)=y−AB_A(y), S_A(y)=||e_A(y)||². For A with p columns define V_Aj(y)=S_A(y)/(n−p) · [(AᵀA)⁻¹]jj, s_A(y)=√(S_A(y)/(n−p)), t_Aj(y)=B_A(y)_j/√V_Aj(y), and T²_Aj(y)=B_A(y)_j²/V_Aj(y). These are exactly `ols`, `olsResidual`, `olsSSE`, `olsSESquared`, `olsResidualStandardError`, `olsT`, and `olsTSquared`. `IsLeastSquares A y b` means ∀b′∈ℝ^p, ||y−Ab||²≤||y−Ab′||²; uniqueness is asserted only where explicitly stated.

`residualLine(x)` is L_x=[1,x], `fullDesign(Z,x)` is F_x=[Z,x], with x in coordinate k when Z has k columns. P_Z=Z(ZᵀZ)⁻¹Zᵀ, M_Z=I−P_Z. These definitions have no hidden rank hypotheses.

All divisions in ℝ use 1/0=0. √u is the ordinary nonnegative square root for u≥0 and is 0 for u<0. Natural-number subtraction is truncated at zero; real-number subtraction is not. Finset.range m is {0,...,m−1}; erase removes one member. The quarterly differences 15−k never truncate on the stated finite ranges. The sample-size subtractions in T6 are natural subtractions of explicitly listed cardinalities.

GaussianReal(m,v) is N(m,v), where v is the variance (not standard deviation), and is Dirac at m if v=0. The finite product Measure.pi is the joint law of independent coordinates. A measure map is a pushforward for an almost everywhere measurable map; Mathlib assigns a fallback measure otherwise. Every map used here is a Borel function built from finite-dimensional linear maps, polynomials, square roots, and totalized division, so that fallback is inapplicable. Define C_ν as the law of Σ_{i=0}^{ν−1}G_i² for independent standard normal G_i; this is `chiSquaredLaw ν`. Define D_ν as the law of G_0/√((Σ_{i=1}^ν G_i²)/ν), using ν+1 independent standard normals; this is `studentLaw ν`. For positive ν this is Student's t law, apart from the immaterial definition on the zero-denominator null set. Here ν is only 3 or 4.

Integrals are real Bochner integrals, defined to be zero when the integrand is not integrable. `Integrable f μ` asserts almost everywhere strong measurability and finite integral of |f|. Cov_μ(ε)ij=∫(ε_i−∫ε_i)(ε_j−∫ε_j)dμ. T3 explicitly asserts integrability for the three second moments it uses. T4 explicitly assumes first and pairwise second-product integrability for its input noise.

The two named analytic functions are F₄(t)=1−(3/2)z+(1/2)z³, z=t/√(4+t²), and F₃(t)=1−(2/π)(arctan q+q/(1+q²)), q=t/√3. They are functions given by formulas. None of the theorems identifies these functions with probabilities under D₄ or D₃, respectively.

Mathlib source anchors inspected: `Data/Matrix/Mul.lean:72,698`; `LinearAlgebra/Matrix/Rank.lean:134`; `LinearAlgebra/Matrix/NonsingularInverse.lean:169`; `Analysis/Real/Sqrt.lean:112`; `Probability/Distributions/Gaussian/Real.lean:49,166,222`; `MeasureTheory/Constructions/Pi.lean:210`; `MeasureTheory/Measure/Map.lean:97`; `MeasureTheory/Measure/Prod.lean:171`; `MeasureTheory/Integral/Bochner/Basic.lean:158`; `MeasureTheory/Function/L1Space/Integrable.lean:59`; and the finite-set range/erase definitions.

## T1 — SAP.P039.T1

QuarterGrowth is any function h:ℕ→ℝ. Set N_d(h)=h(16)/3+Σ_{q=2}^{15}d^(16−q)h(q), D_d=1/3+Σ_{j=1}^{14}d^j, G_d(h)=N_d(h)/D_d. Set Ñ_d(h)=N_d(h)+d^15h(1), D̃_d=D_d+d^15, G̃_d(h)=Ñ_d(h)/D̃_d. These displayed expansions follow the actual definitions, independently of T1's equalities.

The theorem is a conjunction of the following unconditional assertions.

1. For every real d, if d≥0, then D_d>0 and D̃_d>0; for every h,h′:ℕ→ℝ, if ∀q∈ℕ, 2≤q≤16 implies h(q)=h′(q), then N_d(h)=N_d(h′) and G_d(h)=G_d(h′); for every h, Ñ_d(h)−N_d(h)=d^15h(1); and D̃_d−D_d=d^15. The order is d, nonnegativity, then the independently quantified h,h′ and h clauses.
2. Let h*=1_{q=1}. Then 0<1/2<1, h*(1)=1, h*(q)=0 for every q with 2≤q≤16; N_{1/2}(h*)=G_{1/2}(h*)=0; Ñ_{1/2}(h*)=1/32768; D̃_{1/2}=131069/98304; G̃_{1/2}(h*)=3/131069>0; and this last value differs from G_{1/2}(h*).
3. 0<9/10<1; N_{9/10}(h*)=G_{9/10}(h*)=0; Ñ_{9/10}(h*)=205891132094649/10^15; D̃_{9/10}=22440939433444477/(3·10^15); G̃_{9/10}(h*)=617673396283947/22440939433444477>0; and it differs from G_{9/10}(h*).
4. (1/2)^15=1/32768; 1/3+32767/32768=131069/98304; and (9/10)^15=205891132094649/10^15.

## T2 — SAP.P039.T2

For every real d and then every h:ℕ→ℝ, if d≥0: D_d≥1/3, D_d>0, D̃_d>0; for every h′ agreeing with h at every q=2,...,16, both N_d and G_d agree; Ñ_d(h)=N_d(h)+d^15h(1); D̃_d=D_d+d^15; G̃_d(h)−G_d(h)=d^15(h(1)−G_d(h))/D̃_d; and G̃_d(h)=G_d(h) if and only if d=0 or h(1)=G_d(h).

Independently, for every h:ℕ→ℝ: D_0=1/3; G_0(h)=h(16); D_1=43/3; G_1(h)=(3/43)(h(16)/3+Σ_{q=2}^{15}h(q)); 0^0=1; ∀k∈ℕ, 1^k=1; and ∀k∈ℕ with k≥1, 0^k=0. There is no assumption d≤1 anywhere.

## T3 — SAP.P039.T3

Define u=(1,−1,0,0,0,0), v=(0,0,1,−1,0,0), w=(0,0,0,0,1,−1), y=u+(3/2)v+w, Z=[1,u], r=e_Z(y). The theorem has no hypotheses. It asserts every following conjunction.

* ZᵀZ=diag(6,2), Z has full column rank, r=(3/2)v+w, S_Z(y)=13/2, M_Z is symmetric and idempotent of rank 4, and M_Zy=r.
* For each row in the following table, the design has full column rank, the stated coefficient vector is the unique least-squares minimizer (both minimization and ∀b, minimizer(b)⇒b=stated vector are asserted), and the residual, SSE, slope variance V, and squared t statistic have the displayed values. The slope is the last coordinate; all rows are actual OLS computations.

| Design and outcome | Coefficients | Residual | SSE | V | T² |
|---|---|---|---|---|---|
| L_v, r | (0,3/2) | w | 2 | 1/4 | 9 |
| [Z,v], y | (0,1,3/2) | w | 2 | 1/3 | 27/4 |
| L_(u+v), r | (0,3/4) | −(3/4)u+(3/4)v+w | 17/4 | 17/64 | 36/17 |
| [Z,u+v], y | (0,−1/2,3/2) | w | 2 | 1/3 | 27/4 |

* (u+v)ᵀM_Z(u+v)=2, ||u+v||²=4, and 3/4=(3/2)·2/4.
* Z,L_v,[Z,v] have full column rank; t_{L_v,1}(r)=3; t_{[Z,v],2}(y)=3√3/2; F₄(t_{L_v,1}(r))<1/20<F₃(t_{[Z,v],2}(y)). Also F₄(3)=1−45/(13√13)<1/20 and F₃(3√3/2)=1/2−(2/π)(arctan(1/5)+6/13)>1/20.
* All five preceding designs Z,L_v,[Z,v],L_(u+v),[Z,u+v] have full rank; the first two squared statistics are explicitly unequal (9 versus 27/4), and the correlated-regressor slopes are explicitly unequal (3/4 versus 3/2).
* Finally, for every nonnegative real σ, if σ>0, then for every γ∈ℝ², let μ be the product of six N(0,σ²) laws, let stat(ε)=t_{L_v,1}(e_Z(Zγ+ε)), U(ε)=vᵀε/(σ√2), and V(ε)=S_[Z,v](Zγ+ε)/σ². Then the joint law of (U,V) is N(0,1)×C₃; for every ε∈ℝ⁶, stat(ε)=U(ε)/√(V(ε)/4); the law of stat is the pushforward of D₃ by t↦√(4/3)t; ∫stat²dμ=4, ∫t²dD₃=3, ∫t²dD₄=2; the stat law is not D₄; and all three squared functions just integrated are integrable under their respective measures. The order is σ, positivity, γ, the displayed definitions, and conclusions; there is no assumed Student-distribution premise.

## T4 — SAP.P039.T4

This is a conjunction of a deterministic statement and a covariance statement.

For every n,k∈ℕ, Z∈ℝ^(n×k), x,y∈ℝ^n, in that order, assume: Z has full column rank; ∃c∈ℝ^k, Zc=1; ¬∃c∈ℝ^k, Zc=x; and k+1<n. Define P=P_Z, M=M_Z, r=My, x̄=(Σ_i x_i)/n, x_c=x−x̄1, s_m=xᵀMx, s_c=||x_c||², c=xᵀr, a=c/s_c, b=c/s_m, S_r=||r||²−c²/s_c, and S_f=||r||²−c²/s_m. The following conclusions all hold:

1. Pᵀ=P, P²=P, Mᵀ=M, M²=M, MZ=0; Σ_i r_i=0; Mx_c=Mx; x_cᵀr=c; and c=xᵀMy.
2. s_c=s_m+||Px_c||²; 0<s_m≤s_c; s_m=s_c iff Px_c=0; and Px_c=0 iff for every control column j, x_c is orthogonal to Z_j.
3. B_Lx(r)=(−a x̄,a); this vector is a least-squares minimizer; S_Lx(r)=S_r; ∃!β minimizing ||y−[Z,x]β||²; the final coordinate of B_[Z,x](y) is b; and S_[Z,x](y)=S_f.
4. a=b s_m/s_c; a>0 iff b>0; a<0 iff b<0; |a|≤|b|; a=b iff b=0 or Px_c=0; and S_f≤S_r.
5. V_Lx,1(r)=S_r/((n−2)s_c) and V_[Z,x],k(y)=S_f/((n−k−1)s_m), with real denominator subtraction.
6. If S_f>0, then T²_Lx,1(r)=(n−2)c²/(s_c||r||²−c²); T²_[Z,x],k(y)=(n−k−1)c²/(s_m||r||²−c²); and T²_Lx,1(r)/(n−2)≤T²_[Z,x],k(y)/(n−k−1). Within that positive-S_f implication, if Px_c=0, then a=b, e_Lx(r)=e_[Z,x](y), t_Lx,1(r)=√((n−2)/(n−k−1))t_[Z,x],k(y), and, if k≥2 and the full-model t is nonzero, |t_[Z,x],k(y)|<|t_Lx,1(r)|. Thus even the residual-equality and a=b clauses in this last implication are guarded by S_f>0; earlier a=b characterization is not.

The second conjunct quantifies a type Ω with a measurable space, a probability measure μ on it, n,k∈ℕ, Z∈ℝ^(n×k), x∈ℝ^n, γ∈ℝ^k, ε:Ω→ℝ^n, and σ∈ℝ. In order, assume σ>0, FullColumnRank(Z), 1∈col(Z), x∉col(Z), k+1<n, ∀i integrability of ε_i, ∀i,j integrability of ε_iε_j, ∀i ∫ε_i dμ=0, and Cov_μ(ε)=σ²I. Put r(ω)=M_Z(Zγ+ε(ω)). Conclude ∀ω, r(ω)=M_Zε(ω); Cov_μ(r)=σ²M_Z; rank(M_Z)=n−k; rank(Cov_μ(r))=n−k; and Cov_μ(r)≠σ²I. Those ranks use natural subtraction, but full rank and dimension assumptions ensure k<n. No independence, Gaussian law, or Student law is assumed or concluded in this conjunct. x appears only in its hypotheses.

## T5 — SAP.P039.T5

The measures j range over the five indices 0,...,4. Let E_j be the election-year sets and e_j(t) the exact rational score data in the tables below; e_j(t)=0 outside the listed data, with those placeholder values never included in the optimization. `relativeExtremism(I,C,R)=(|I−R|−|C−R|)/2` is also defined, but no theorem connects score data to underlying positions or invokes this definition.

This unconditional theorem asserts:

1. 1972,1980∈E₁ and E₃; |e₁(1972)|−|e₁(1980)|=85077519648341/250000000000000; |e₃(1972)|−|e₃(1980)|=307808774046123/10^15; and each difference is strictly positive.
2. 1980,1984∈E₂; e₂(1980)<0<e₂(1984); −2.23e₂(1984)=−1526436622492473/2500000000000000<0 and differs from 1.38; and ∀t∈E₂, e₂(t)≤e₂(1984).
3. For every j, the year s_j=(1984,1996,1984,2012,1968)_j belongs to E_j, has positive score, and ∀t∈E_j with t≠s_j, e_j(t)<e_j(s_j). These are unique signed maxima, not absolute-value maxima.
4. For every j, e_j(s_j) equals (0.235890938802093,0.336875932107128,0.27380029103004,0.34241131733838,0.116)_j exactly.

## T6 — SAP.P039.T6

Let m_j=(1980,1972,1980,1972,1964)_j, c_j=(1972,2004,1972,2008,1968)_j, and δ_j=(33171961114209/250000000000000,85752092421407/500000000000000,20648643625509/125000000000000,12092835415297/50000000000000,13/125)_j. Define E_j(false)=E_j, and E_j(true)=E_j\{1948} for j=0,2, otherwise E_j. Define H(β,j)=β e_j(m_j).

The theorem is an unconditional conjunction of:

1. ∀j, m_j∈E_j, e_j(m_j)<0, and ∀t∈E_j with t≠m_j, |e_j(t)|<|e_j(m_j)|.
2. ∀j, δ_j>0, c_j∈E_j, c_j≠m_j, |e_j(m_j)|−|e_j(c_j)|=δ_j, and ∀t∈E_j with t≠m_j, δ_j≤|e_j(m_j)|−|e_j(t)|. Thus the positive gap is attained by the named competitor.
3. ∀j and then bp∈{false,true}, m_j∈E_j(bp) and is its unique absolute-value maximizer; |E_j(false)|−5=(12,6,12,6,3)_j; and |E_j(true)|−6=(10,5,10,5,2)_j. Both cardinality formulas occur for each bp. They use natural subtraction on sets with at least 8 members.
4. ∀β∈ℝ, ∀g∈ℝ, ∀j: [∀x∈ℝ, (g+βx)−(g+β·0)=βx] and [∀t∈E_j, |βe_j(t)|≤|H(β,j)|]. The scalar x here is unrelated to T4's regressor.
5. ∀β∈ℝ, ∀j: H(β,j)>0 iff β<0; H(β,j)=0 iff β=0; H(β,j)<0 iff β>0.
6. (−2.23)(−0.62)=1.3826∈[1.375,1.385), and e₂(1980)∈[−0.625,−0.615).
7. ∀j, e_j(m_j) equals (−0.498138285011637,−0.51177218671487,−0.621023999873778,−0.60215659702977,−0.22)_j exactly.

The theorem does not fit model coefficients or calculate model p-values. The general β is arbitrary, including zero.

## T7 — SAP.P039.T7

This is a conjunction of five groups, without outer hypotheses.

1. For every n,k₁,k₂∈ℕ, Z₁∈ℝ^(n×k₁), Z₂∈ℝ^(n×k₂), and q∈ℝ^n, assume ∀a∈ℝ^k₁ ∃b∈ℝ^k₂, Z₁a=Z₂b (nested column spaces), FullColumnRank([Z₁,q]), FullColumnRank([Z₂,q]), k₁+1<n, and k₂+1<n. Put R_i=S_Zi(q). Each auxiliary fit has a minimizer attaining R_i; 0<R₂≤R₁; the last diagonal entry of ([Z_i,q]ᵀ[Z_i,q])⁻¹ is 1/R_i for i=1,2. Then, for every y∈ℝ^n, if both S_[Zi,q](y)>0, put s_i=√(S_[Zi,q](y)/(n−k_i−1)) and se_i=√V_[Zi,q],ki(y). Conclude se₁=s₁/√R₁, se₂=s₂/√R₂, se₁/s₁≤se₂/s₂, and se₁≤se₂s₁/s₂. No intercept or strict control-dimension nesting is assumed.
2. For every Z₁∈ℝ^(17×2), Z₂∈ℝ^(17×3), q,y∈ℝ^17, assume nested column spaces and full rank of both augmented designs. If se₁∈[1.35,1.45], se₂∈[0.955,0.965], s₁∈[4.615,4.625], s₂∈[4.695,4.705], then False. The four intervals are closed. This is an explicit impossibility statement; simultaneous satisfaction of these four numerical premises is what it denies.
3. 0.965·4.625/4.695=7141/7512<0.951 and 27/20−7141/7512=15001/37560>0.
4. For every Z₁,Z₂,q,y of the same dimensions as group 2, assume nesting, both augmented ranks full, both outcome SSEs positive, se₂≤0.965, s₁≤4.625, and s₂≥4.695, in that order. Conclude se₁≤7141/7512.
5. The exact 17-row table below defines y as its outcome column, A₁=[1,income,tenure], A₂=[1,income,tenure,war], and A₃=[1,income,tenure,war,extremism]. Each A_i has exactly one least-squares minimizing coefficient vector. For income (coordinate 1) it asserts all these exact values and intervals:

| Fit | Exact income coefficient | Income coefficient interval | Income SE interval |
|---|---|---|---|
| A₁ | 7146187962914975000000/1117667657915636289559 | [6.385,6.395) | [0.935,0.945) |
| A₂ | 315309901567374756223272228924480076940000000/49481205176565031631955325062456554157036059 | [6.365,6.375) | [0.955,0.965) |
| A₃ | 560959205595590684404193874010188762669512981839878401170000000/87848341864933029922153613743599975715147930782629447955391927 | [6.385,6.395) | [0.95,1.05) and [1.005,1.015) |

For A₁ it additionally asserts V=7736251837253462080128985902187500000000000/8744266954854366478686864008983610246901367 and 0.935²≤V<0.945². The SEs use denominators 14,13,12 respectively. There is no significance-star, p-value, or alternative sqrt(SSE/n) assertion.

## Exact data defining the finite assertions

The tables appended below are exact finite-decimal expansions of the rational literals in the definitions, generated only from those definition files. A dash in the extremism table means that the year is not in that measure's election set. The function value at such a year is the default zero and does not participate in a maximum.

### Regression input table

| Year | Outcome margin | Income growth | Tenure | War fatalities | Extremism |
|---|---|---|---|---|---|
| 1948 | 4.48 | 3.869657666 | 16 | 0 | 0.239968578 |
| 1952 | -10.85 | 2.417476109 | 20 | 190.4152679 | 0.087977536 |
| 1956 | 15.4 | 0.576370472 | 4 | 0 | -0.051046667 |
| 1960 | -0.17 | 0.01682935 | 8 | 0 | -0.053180451 |
| 1964 | 22.58 | 3.258883307 | 4 | 0.948843002 | -0.318262019 |
| 1968 | -0.7 | 1.398802867 | 8 | 145.6291504 | 0.219451428 |
| 1972 | 23.15 | 2.429039464 | 4 | 0 | -0.455834851 |
| 1976 | -2.06 | 0.78535125 | 8 | 2.086606979 | 0.050846194 |
| 1980 | -9.74 | -0.828480492 | 4 | 0 | -0.621024 |
| 1984 | 18.21 | 2.566651066 | 4 | 0 | 0.273800291 |
| 1988 | 7.72 | 1.512362024 | 8 | 0 | 0.173195729 |
| 1992 | -5.56 | 0.77430623 | 12 | 0 | 0.192515613 |
| 1996 | 8.51 | 1.135307588 | 4 | 0 | -0.146050087 |
| 2000 | 0.51 | 1.675421874 | 8 | 0 | -0.169644956 |
| 2004 | 2.46 | 1.039046624 | 4 | 3.860627651 | 0.249490684 |
| 2008 | -7.27 | -0.699703182 | 8 | 13.98476601 | -0.119001519 |
| 2012 | 3.84 | 0.347024884 | 4 | 4.8 | 0.040330327 |

### Extremism scores and election sets

| Year | j=0 | j=1 | j=2 | j=3 | j=4 |
|---|---|---|---|---|---|
| 1948 | 0.186449401704861 | — | 0.239968577629729 | — | — |
| 1952 | 0.068356278600414 | — | 0.0879775359846345 | — | — |
| 1956 | -0.039661945232703 | — | -0.051046667334368 | — | — |
| 1960 | -0.041319840049504 | — | -0.0531804508563835 | — | -0.068 |
| 1964 | -0.24728138844441 | — | -0.318262019168295 | — | -0.22 |
| 1968 | 0.170508105389464 | — | 0.219451428379582 | — | 0.116 |
| 1972 | -0.365450440554801 | -0.51177218671487 | -0.455834850869706 | -0.60215659702977 | -0.041 |
| 1976 | 0.044642638216102 | -0.231688492759438 | 0.0508461944446885 | -0.22548493653085 | — |
| 1980 | -0.498138285011637 | -0.171462108121506 | -0.621023999873778 | -0.294347822983647 | — |
| 1984 | 0.235890938802093 | -0.0356144375420135 | 0.27380029103004 | 0.00229491468593002 | 0.0385 |
| 1988 | 0.153129340875841 | -0.296507211564452 | 0.173195729075055 | -0.276440823365235 | — |
| 1992 | 0.133646079679683 | -0.061530236247573 | 0.192515613229452 | -0.00266070269781005 | — |
| 1996 | -0.104467146002477 | 0.336875932107128 | -0.14605008654561 | 0.295292991563994 | 0.0415 |
| 2000 | -0.0859714651726795 | 0.237764496391801 | -0.169644956461836 | 0.154091005102645 | — |
| 2004 | 0.048727587431465 | -0.340268001872056 | 0.249490683526865 | -0.139504905776655 | 0.052 |
| 2008 | -0.061819369305165 | -0.30311773910617 | -0.119001518922825 | -0.36029988872383 | -0.0045 |
| 2012 | 0.0294616125544001 | 0.33154260332366 | 0.0403303265691201 | 0.34241131733838 | — |
