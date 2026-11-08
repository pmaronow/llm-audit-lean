# Blind reading of the Challenge

Saved before opening `claims.json` or `record.json`. This reading concerns the propositions, independently of their docstrings' descriptions of the paper. The six stubs have no arguments: each asserts the entire closed proposition named `TnStatement`.

## Conventions traced to Mathlib

All finite indices `Fin J` mean the integers 0 through J−1; sums are over all indices unless a set is displayed. All coefficients are real and fixed, rather than functions of the outcome. Finite rational expectations below are ordinary rational weighted sums, not Bochner integrals.

For a measurable space Ω, `IsProbabilityMeasure μ` means μ(Ω)=1. Write E(X)=∫X dμ. Mathlib's Bochner integral is defined as zero for a nonintegrable function. Its `variance X μ` is the real conversion of ∫⁻|X−E(X)|² dμ, with infinite values converted to zero. Here every probabilistic variance identity explicitly assumes `MemLp X 2 μ` for its input variables. `MemLp` is finiteness of `eLpNorm`; at exponent 2 this includes almost everywhere strong measurability and a finite second moment. On a probability space it ensures all the displayed expectations, variances and covariance products are integrable and have their ordinary meanings. Cov(X,Y)=E((X−E(X))(Y−E(Y))). These definitions were checked in Mathlib's `Probability/Moments/{Variance,Covariance}.lean`, `MeasureTheory/Function/LpSeminorm/Defs.lean`, `MeasureTheory/Integral/Bochner/Basic.lean`, and `MeasureTheory/Measure/Typeclasses/Probability.lean`.

`IndepFun X Y μ` means independence of the sigma algebras pulled back by X and Y (checked in `Probability/Independence/Basic.lean`); `Pairwise` here requires this for every distinct pair of observations, not joint independence of all observations. Equality `=ᵐ[μ]` means equality μ-almost everywhere. `Real.sqrt` is the nonnegative real square root on nonnegative arguments (zero for negative arguments).

The SAP definitions expand as follows:

- p_j=1/v_j; W(v)=Σ_j p_j; a_j(v)=p_j/W(v).
- P(a,D)(ω)=Σ_j a_j D_j(ω).
- V_diag(v)=Σ_j a_j(v)²v_j.
- Q(a,Σ)=Σ_jΣ_k a_j a_k Σ_jk.
- O(a,Σ)=Σ_{j<k}a_j a_k Σ_jk, for indices `Fin J`.
- For a finite subset B, a^B_j=(1/v_j)/(Σ_{k∈B}1/v_k) when j∈B, and zero otherwise.
- An arm sample mean of n observations is their sum divided by the real cast of n.
- Corr(X,Y)=Cov(X,Y)/(sqrt(Var X) sqrt(Var Y)).
- For a finite set S, E_S f=(Σ_{s∈S}f(s))/|S|, and Cov_S(f,g)=E_S((f−E_S f)(g−E_S g)). Finite rational means, variances and covariances use exactly these formulas over ℚ, with variance E_S((f−E_S f)²).
- For N fixed population values U_i, M(U)=Σ_i U_i/N and S(U,V)=Σ_i(U_i−M(U))(V_i−M(V))/(N−1), where N−1 is natural subtraction before casting to ℝ.

Real and rational division by zero would return zero. The relevant positive-variance, positive-size and nonempty-set assumptions, or the explicit nonempty finite constructions, are recorded below. The linear identities with J=0 have empty sums, but the precision and refutation clauses explicitly require J>0.

## SAP.P042.T1

Asserts the conjunction of the following two entirely specified finite witnesses, with no hypotheses.

### Six-person witness

There are six people, indexed by i=0,…,5, and three potential treatment labels g=0,1,2. Their rational potential outcome is Y_i(g)=1 if i<3 and 0 otherwise, independent of g. The allocation set S consists of ordered disjoint pairs (A,B) of two-element subsets of the six people. The control group is C={0,…,5}∖(A∪B). For any group G, its mean is Σ_{i∈G}Y_i(0)/2. Let D₁=mean(A)−mean(C) and D₂=mean(B)−mean(C). The theorem asserts all of:

1. For every i,g, Y_i(g)=Y_i(0).
2. |S|=90 and binom(6,2)binom(4,2)=90.
3. Every (A,B)∈S has |A|=|B|=|C|=2 and A∩B=∅.
4. Under the uniform rational average on S, E_S D₁=E_S D₂=0, Var_S D₁=Var_S D₂=3/10, and Cov_S(D₁,D₂)=3/20.
5. For the two marginal variances v₀=v₁=3/10, a₀=a₁=1/2 and V_diag(v)=1/W(v)=3/20.
6. Var_S((D₁+D₂)/2)=9/40, E_S(((D₁+D₂)/2)²)=9/40, Var_S((D₁+D₂)/2)=(3/2)(3/20), and 3/20<Var_S((D₁+D₂)/2).

### Binomial witness

Let x₀,x₁,x₂ each range from 0 to 100. Give a single coordinate x mass p(x)=binom(100,x)/2¹⁰⁰ and give triples the product mass p(x₀)p(x₁)p(x₂). All expectations, variances and covariances in this witness are rational sums against these masses. Define D₁=(x₁−x₀)/100, D₂=(x₂−x₀)/100 and H=(D₁+D₂)/2. For real estimate h and radius r, `coversZero h r` means h−r≤0≤h+r.

For natural r define

K(r)=Σ_{x=0}^{100} binom(100,x) Σ_{t=max(0,2x−r)}^{min(200,2x+r)} binom(200,t),

and C(r)=K(r)/2³⁰⁰ as a rational number. The lower endpoint is natural truncated subtraction, giving the displayed max with zero; the inner set is a closed finite integer interval, empty if its lower endpoint exceeds its upper endpoint. The definition of `binomialCountEvent` is the rational indicator of |x₁+x₂−2x₀|≤r, using signed integer arithmetic; it is not itself used in `T1Statement`.

The theorem asserts all of:

1. Every p(x)≥0 and Σ_x p(x)=1.
2. ED₁=ED₂=0; Var D₁=Var D₂=1/200; Cov(D₁,D₂)=1/400; Var(x₀/100)=1/400.
3. For v₀=v₁=1/200, a₀=a₁=1/2, V_diag(v)=1/W(v)=1/400.
4. For every triple, H=(x₁+x₂−2x₀)/200. Moreover EH=0, Var H=3/800=(3/2)(1/400)>1/400.
5. With the particular multiplier 49/25, (49/25)sqrt(1/400)=49/500.
6. For every triple, writing the signed integer q=x₁+x₂−2x₀: the interval with center H and radius 49/500 covers zero iff |q|≤19; the interval with center H and radius (49/25)sqrt(3/800) covers zero iff |q|≤24.
7. 24²<200²(49/25)²(3/800)=14406/25<25².
8. The product-mass expectation of the coverage indicator for radius (49/25)sqrt(1/400) equals C(19), and that for radius (49/25)sqrt(3/800) equals C(24).
9. C(19)=56571224212801903286613058436266763680981055287737934836552182663205237639665445537726383/2²⁹⁵; the integer numerator is coprime to 2²⁹⁵.
10. 888/1000<C(19)<889/1000<95/100<C(24).

No normal quantile occurs in the proposition.

## SAP.P042.T2

Asserts a conjunction of eight universally quantified laws. Every measurable space Ω in these laws is of Lean type `Type`; μ is any probability measure on it. All random variables take values in ℝ. Each law has its own independent universal quantifiers.

### 1. LinearPoolingLaw

For every such Ω,μ, every natural J (including zero), every coefficient vector a∈ℝ^J, and every family D_j with D_j∈L²(μ), let Σ_jk=Cov(D_j,D_k). Then

E(P(a,D))=Σ_j a_j ED_j,

Var(P(a,D))=Q(a,Σ), and

Q(a,Σ)=Σ_j a_j²Var(D_j)+2O(a,Σ).

There are no positivity, normalization or independence assumptions on a or D.

### 2. PrecisionPoolingLaw

For every Ω,μ, every J>0, and every family D_j∈L²(μ) with Var(D_j)>0 for every j, set v_j=Var(D_j), a_j=a_j(v), Σ_jk=Cov(D_j,D_k). Then:

1. W(v)>0, every a_j>0, and Σ_j a_j=1.
2. V_diag(v)=1/W(v).
3. Var(P(a,D))=1/W(v)+2O(a,Σ).
4. Var(P(a,D))=1/W(v) iff O(a,Σ)=0.
5. If every off-diagonal Σ_jk=0, then Var(P(a,D))=1/W(v).
6. If every off-diagonal Σ_jk≥0 and some Σ_jk>0 with j<k, then Var(P(a,D))>1/W(v).
7. For every real z, z sqrt(Var(P(a,D)))=z sqrt(Q(a,Σ)).
8. For every real z>0, z sqrt(Var(P(a,D)))=z sqrt(1/W(v)) iff O(a,Σ)=0.

The final two assertions identify variance-based half-widths; they make no coverage assertion.

### 3. SharedControlLaw

For every Ω,μ and A,B,C∈L²(μ), if Cov(A,B)=Cov(A,C)=Cov(B,C)=0, then Cov(A−C,B−C)=Var(C). Joint independence is not required.

### 4. IndependentArmLaw

For every Ω,μ, every three positive natural sizes n₀,n₁,n₂, and every family X indexed by the disjoint union of those three groups, assume every X_i∈L²(μ) and every distinct pair X_i,X_j is independent. For every real σ²>0 such that all Var(X_i)=σ², define C as the average in group 0, A in group 1, B in group 2, and D₁=A−C,D₂=B−C. Then

Var D₁=σ²(1/n₁+1/n₀), Var D₂=σ²(1/n₂+1/n₀),

Cov(D₁,D₂)=σ²/n₀, and

Corr(D₁,D₂)=sqrt(n₁n₂/((n₁+n₀)(n₂+n₀))).

Means need not be identical; σ² is a name for a positive real, not the square of a separate quantified parameter.

### 5. CovarianceBoundLaw

For every Ω,μ, natural J (possibly zero), vectors a,s∈ℝ^J and family D_j∈L²(μ), assume a_j≥0, s_j>0 and Var(D_j)=s_j² for every j. Then |Cov(D_j,D_k)|≤s_js_k for every j,k, and Var(P(a,D))≤(Σ_j a_js_j)². In addition, for every Z∈L²(μ) with EZ=0 and Var Z=1, if D_j−ED_j=s_jZ almost everywhere for every j, then equality holds in the latter variance bound. This is a conditional equality assertion, not an existential assertion of a Z for arbitrary D or Ω. Normalization Σ_j a_j=1 is not assumed.

### 6. PooledDifferenceLaw

For every Ω,μ, every finite type ι with decidable equality, every nonempty disjoint finite subsets N,A⊆ι, and every family D_j∈L²(μ) whose variances v_j are strictly positive for every j∈ι, form a^N,a^A and b=a^N−a^A. Then

Var(P(a^N,D)−P(a^A,D))=Q(b,Σ), and

Var(P(a^N,D)−P(a^A,D))=Var(P(a^N,D))+Var(P(a^A,D))−2Cov(P(a^N,D),P(a^A,D)).

Variables outside N∪A are also required to be square integrable and have positive variance.

### 7. ThreeContrastLaw

For every Ω,μ, J>0, family D_j∈L²(μ) of positive variances, injective map e:{0,1,2}→{0,…,J−1}, and reals a,c₁₂,c₁₃,c₂₃, suppose the normalized precision weight of each D_{e(g)} is a. Suppose also that, for every distinct j,k, their covariance is c₁₂ on the unordered pair {e(0),e(1)}, c₁₃ on {e(0),e(2)}, c₂₃ on {e(1),e(2)}, and zero on every other pair. Then

Var(P(a(v),D))=1/W(v)+2a²(c₁₂+c₁₃+c₂₃).

If in addition c₁₂=c₁₃ and c₁₃=c₂₃, this variance is 1/W(v)+6a²c₁₂. The injection forces J≥3, and covariance parameters are constrained by the existence of the assumed random variables.

### 8. FinitePopulationLaw

For every natural N≥2, every vector of positive natural group sizes n₀,n₁,n₂ with n₀+n₁+n₂≤N, and every fixed real array Y_i(g), i∈{0,…,N−1}, g∈{0,1,2}, let S be the finite set of assignments z:{0,…,N−1}→{0,1,2,3} for which group g has exactly n_g people for g=0,1,2. Label 3 is the remaining group of size N−Σ_g n_g. Let mean_g(z)=Σ_{i:z(i)=g}Y_i(g)/n_g, D₁=mean₁−mean₀, D₂=mean₂−mean₀, τ₁_i=Y_i(1)−Y_i(0), and τ₂_i=Y_i(2)−Y_i(0). Then:

1. S is nonempty.
2. Cov_S(D₁,D₂)=S(Y(0),Y(0))/n₀−S(τ₁,τ₂)/N.
3. S(τ₁,τ₂)=S(Y(1),Y(2))−S(Y(1),Y(0))−S(Y(0),Y(2))+S(Y(0),Y(0)).
4. If for every i, Y_i(1)=Y_i(0) and Y_i(2)=Y_i(0), then Cov_S(D₁,D₂)=S(Y(0),Y(0))/n₀.

All assignment expectations are uniform finite averages; the positive group sizes imply N≥3, so neither population divisor vanishes.

## Shared numerical definitions for SAP.P042.T3 and T4

Two real effect inputs are d₀=58247/25000=2.32988, d₁=21649/25000=0.86596. Standard error inputs are s₀=1741/3125=0.55712 and s₁=40891/50000=0.81782. Put v_j=s_j², W=Σ_j1/v_j, θ=Σ_j a_j(v)d_j, and V=1/W. Define

Q=Σ_j(1/v_j)(d_j−θ)²,

C=W−(Σ_j(1/v_j)²)/W,

τ²=max(0,(Q−1)/C), u_j=v_j+τ²,

θ_R=Σ_j a_j(u)d_j, V_R=1/W(u).

`RoboFixedExact` is the conjunction:

- v₀=3031081/9765625 and v₁=1672073881/2500000000.
- W=23906548994140625/5068191371295361.
- θ=114191974724271/61200765425000.
- V=5068191371295361/23906548994140625.

`RoboRandomExact` is the conjunction:

- Q=(d₀−d₁)²/(v₀+v₁)=5357654416/2448030617 and Q>1.
- C=2/(v₀+v₁)=5000000000/2448030617.
- τ²=2909623799/5000000000.
- 1/u₀=5000000000/4461537271 and 1/u₁=5000000000/6253771561.
- θ_R=12592252377/7319600000.
- V_R=27901434903721350031/53576544160000000000.

`RoboRandomRounding` asserts θ_R∈[1.7195,1.7205), and, for every real z with 1.9599≤z≤1.96, simultaneously

θ_R−z sqrt(V_R)∈[0.3055,0.3065),

θ_R+z sqrt(V_R)∈[3.1345,3.1355).

These are exact rational rounding bins, with no model for the original input rounding and no standard-normal quantile defined or bounded.

## SAP.P042.T3

With no hypotheses, asserts `RoboFixedExact`, `RoboRandomExact`, and `RoboRandomRounding`, together with all of:

1. 1.8655<θ<1.8665 and θ>1.7205.
2. For every real z, if 1.9599≤z≤1.96, then θ−z sqrt(V)>0.9625, 0.3065<0.9625, θ+z sqrt(V)<2.7685, and 2.7685<3.1345.

It therefore separates the fixed calculation from all three alternative rounding bins, at every multiplier in that interval. It does not quantify over an actual observed sample or assert that z is a distributional quantile.

## SAP.P042.T4

With no hypotheses, asserts `RoboFixedExact`, `RoboRandomExact`, and `RoboRandomRounding`, together with:

1. θ∈[1.8655,1.8665).
2. For every real z∈[1.9599,1.96], θ−z sqrt(V)∈[0.9625,0.9635) and θ+z sqrt(V)∈[2.7675,2.7685).
3. For every real z∈[0,1.96], θ−z sqrt(V)>0.
4. For every measurable space Ω, every probability μ, and every pair D₀,D₁∈L²(μ), if Var(D_j)=v_j for both j and Cov(D₀,D₁)=0, then Var(Σ_j a_j(v)D_j)=V.

The last assertion makes no assumption about the means of D_j. There is no conclusion implementing an editorial or software change.

## SAP.P042.T5

With no hypotheses, asserts the conjunction of two negations:

1. It is false that for every measurable space Ω, probability μ, J>0, and family D_j∈L²(μ) with all Var(D_j)>0, Var(P(a(v),D))=1/W(v), where v_j=Var(D_j).
2. It is false that for every measurable space Ω, probability μ, finite type ι with decidable equality, nonempty disjoint finite subsets N,A⊆ι, and family D_j∈L²(μ) with all Var(D_j)>0, Var(P(a^N,D)−P(a^A,D))=(Σ_{j∈N}1/v_j)⁻¹+(Σ_{j∈A}1/v_j)⁻¹.

Classically these assert the existence of one admissible counterexample to each universal formula. They need not be different examples, and neither negation says that the formula fails for every family. There is no reference to a historical pool, data set, confidence interval, significance test, or empirical point estimate.

## SAP.P042.T6

Asserts the following universal finite-randomization law, conjoined with one arithmetic identity.

First, for every natural N,m with N≥2, 1≤m and m≤N−1 (the last subtraction is natural), and for every fixed real array Y_i(t), i∈{0,…,N−1}, t∈{false,true}, let S be all m-element subsets s of the population, with the uniform finite average E_S. `powersetCard` in Mathlib means exactly the subsets of the given cardinality. For any vector U, let T_s(U)=Σ_{i∈s}U_i/m and C_s(U)=Σ_{i∉s}U_i/(N−m). Observed assigned outcome is Y_i(true) for i∈s and Y_i(false) otherwise. Then:

1. For every t∈{false,true}, E_S T_s(Y(t))=M(Y(t)) and E_S C_s(Y(t))=M(Y(t)).
2. The expected observed treatment-minus-control contrast equals M(Y(true)−Y(false)).
3. For every fixed Boolean vector c_i with k=#{i:c_i=true}>0, define p=k/N, δ=Σ_{i:c_i=true}(Y_i(true)−Y_i(false))/k, and ITT=M(Y_i(c_i)−Y_i(false)). For assignment s, contact is c_i for assigned people and false for unassigned people; the observed contacted outcome is Y_i(c_i) for i∈s and Y_i(false) otherwise. Let diff_s be the treatment mean of these outcomes minus their control mean, and R_s=Σ_{i∈s}1_{c_i=true}/m. Then, together:

   - ITT=pδ.
   - E_S diff=ITT.
   - E_S R=p.
   - E_S R>0.
   - δ=(E_S diff)/(E_S R).

The quantifier over c and its positive-count hypothesis comes after Y and is local to assertion 3. The model represents one-sided contact and outcomes depending on the person's own contact using fixed Y_i(t); no additional potential outcomes indexed by other people's assignment occur. The ratio is a ratio of expectations, not an expectation of a random ratio. The size bounds ensure S is nonempty and both group denominators are positive. The k>0 condition ensures the complier mean and the final ratio are defined by positive denominators.

Second, (9.4−7.0)/(1/2)=4.8 as an equality of real numbers.

## Files read in the blind stage

`SAP/P042/Defs.lean`, all eight `SAP/P042/Defs/Part*.lean`, `SAP/P042/Challenge.lean`, `SAP/P042/Challenge/Part1.lean`, and the Mathlib definition sources cited above. No claims or architect record has been opened at this stage.
