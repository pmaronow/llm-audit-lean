# Blind mathematical reading

Saved before opening `claims.json` or `record.json`. This reading uses only the Defs, Challenge, and the Mathlib sources to which their notation resolves. Challenge comments are descriptions, not additional hypotheses or conclusions.

## Shared definitions and conventions

A finite population is a finite type Ω and real weights w(i) ≥ 0 with Σ_i w(i) = 1. Thus any supplied population has nonempty support and Ω cannot be empty, although a separate `Nonempty Ω` instance is not required. Write E[f] = Σ_i w(i)f(i), 1_A for the real-valued indicator of A, P(A) = E[1_A], and E[f | A] = E[1_A f]/P(A). The last expression is Lean real division and would be zero at a zero denominator; individual applications below must be checked for a positive event probability.

Assignment t ranges over Bool = {false,true}, represented numerically by x(false)=0, x(true)=1. Let a_p(true)=p and a_p(false)=1-p. The joint assignment/type mass is a_p(t)w(i). For f(t,i), its arm mean is Σ_i a_p(t)w(i)f(t,i)/a_p(t); Δ_p f is its true arm mean minus its false arm mean. Whenever 0<p<1 these are E[f(true,·)]−E[f(false,·)]. The design mean is E_p f=(1-p)E[f(false,·)]+pE[f(true,·)]. Cov_p(f,g)=E_p(fg)−E_p(f)E_p(g), Var_p(f)=Cov_p(f,f), and the assignment slope is Cov_p(x,f)/Var_p(x). Uniform populations have weights 1/|Ω|; product populations multiply their component weights.

A mediation model consists of arbitrary real functions K_t(i) and S_t(k,i), with t Boolean and k real. Observed support is Y_t(i)=S_t(K_t(i),i), which builds in consistency. Define RF=Δ_p Y, M=E[S_0(K_1,i)−S_0(K_0,i)], and D=E[S_1(K_1,i)−S_0(K_1,i)]. The linear model with real parameters α,a,σ,b,c and functions u₁,u₂ is K_t=α+a x(t)+u₁ and S_t(k)=σ+bk+c x(t)+u₂.

For measure-law versions, Ω is any type with a measurable space, μ is a probability measure (Mathlib `IsProbabilityMeasure`: μ(Ω)=1), and p belongs to the subtype [0,1] of ℝ. `bernoulliMeasure true false p` gives mass p to true and 1−p to false: Mathlib defines it as p·δ_true+(1−p)·δ_false. The assignment law is μ×Bernoulli(p). Its arm mean is the integral of f(t,i) over the arm {second coordinate=t}, divided by the real value of that arm's measure. Law versions of RF, M, D use these arm means and μ integrals. Integrals are Bochner integrals; Mathlib sets a nonintegrable integral to zero. `Integrable f μ` is the conjunction of almost-everywhere strong measurability and finite integral of the norm. In T2, the five relevant potentials are explicitly integrable; sums and differences are consequently integrable, and assignment-arm masses are positive and finite.

An IV model has natural-valued K_t(i) and real response S(k,i), with k a natural number. There is no assignment argument in S, so exclusion is built in. Observed support is Y_t=S(K_t,i), so consistency is built in. FS=Δ_p K (casting K to ℝ), RF_IV=Δ_p Y, W=RF_IV/FS. An increaser has K_0<K_1 and its effect is S(K_1,i)−S(K_0,i); τ_inc is the conditional population mean of that effect among increasers. The conditional observable point-mass law at (t,k,y) is P(K_t=k and Y_t=y); the complete joint point-mass law multiplies this by a_p(t). Equal laws here mean equality as functions on Bool×(ℕ×ℝ).

`Fin n` is the n-element type {0,…,n−1}; `Finset.range J` is {0,…,J−1}. Sums in these definitions are finite sums over the stated entire finite type or range. All probabilities, effects, covariance expressions and displayed quotients are real numbers. Natural subtraction in S(j−1) is truncated, but every telescoping sum uses j=r+1≥1.

Mathlib source checks: `Probability/Distributions/Bernoulli.lean:47`, `MeasureTheory/Measure/Typeclasses/Probability.lean:64`, `MeasureTheory/Function/L1Space/Integrable.lean:59`, `MeasureTheory/Integral/Bochner/Basic.lean:158`, and `Topology/UnitInterval.lean:32`.

## SAP.P043.T1

This is a closed conjunction, with no hypotheses and no existential choice of witnesses: the populations and models are fixed as follows. Both assignments have p=1/2.

**Linear witness.** Ω=Bool×Bool, each type has mass 1/4. Let u₁(i)=1/5 when its first coordinate is true and −1/5 otherwise, and u₂(i)=1/10 when its second coordinate is true and −1/10 otherwise. K_t=8+(6/5)x(t)+u₁, and S_t(k)=23/10+(k−8)/20−(3/50)x(t)+u₂. The theorem asserts all of the following:

1. For every t and type i, the joint assignment/type mass is 1/8. For every r,s in Bool, P(i₁=r and i₂=s)=1/4. For every r, both coordinate marginal probabilities P(i₁=r) and P(i₂=r) are 1/2.
2. For every i, K_1−K_0=6/5>0. For every t, real k,h, and i, if h>0 then S_t(k+h,i)−S_t(k,i)=h/20>0.
3. ΔK=6/5; M=3/50; D=−3/50; RF=0; Var(x)=1/4; Cov(x,Y)=0; Cov(x,K)=3/10; the assignment slopes for Y and K are respectively 0 and 6/5. Also (6/5)(1/20)=3/50 and (6/5)(1/20)−3/50=0.
4. For every t and every real y, the arm probability P(Y_t=y | t) is 1/4 if y is one of 219/100, 221/100, 239/100, 241/100, and is zero otherwise.
5. RF<M and M>0.

**Integer witness.** Ω=Fin 5×Fin 100, each type has mass 1/500. For i=(a,b), K_t(i)=8+x(t)(1+1_{a=4}), S_t(k,i)=2+1_{b+1≤36+5(k−8)−6x(t)}, where b is cast to ℝ, and the separately defined general-knowledge outcome is identically 2. The theorem asserts:

1. For every t,i, the joint mass is 1/1000. For every t,i, K_t(i) belongs to {8,9,10}, Y_t(i) belongs to {2,3}, and general knowledge equals 2.
2. For every t and real k, if k=8 or k=9 then (i) for every i, S_t(k+1,i)−S_t(k,i) belongs to {0,1}, and (ii) the population mean of that increment is 1/20.
3. The false/true knowledge arm means are 8 and 46/5. E[K_1−K_0]=6/5. The means of S_0(K_0), S_0(K_1), S_1(K_1) are 59/25, 121/50, 59/25 respectively. M=3/50, D=−3/50, RF=0.
4. For every t and every real y, the arm probability of y is 16/25 at y=2, 9/25 at y=3, and zero otherwise. RF<M and M>0.

The outer conjunction repeats RF=0, M=3/50, D=−3/50 for both witnesses. Finally, for every population predicate A and every t, in each witness separately, Σ_i jointMass(t,i)1_A(i)=a_{1/2}(t)P(A). Thus assignment is independent of every event in the finite type; arbitrary fixed potential responses are functions of that type.

## SAP.P043.T2

The theorem is a conjunction of a universal result and a fixed counterexample. In the universal result the quantifier order is: for every type Ω (in its universe), every measurable-space structure on Ω, every probability measure μ on Ω, every p∈[0,1], **if** 0<p<1, then for every mediation model (K,S), **if** each of K_0, K_1, S_0(K_0), S_0(K_1), S_1(K_1) is μ-integrable, the following conclusions hold. Assignment is the independent product law and the observed response is the consistent one defined above.

1. RF=∫S_1(K_1)dμ−∫S_0(K_0)dμ=M+D.
2. RF≥M iff D≥0, and RF>M iff D>0. In addition, D≥0 implies RF≥M; D≥0 and RF≤0 imply M≤0; D≥0 and RF=0 imply M≤0.
3. For every i (pointwise, not merely almost everywhere), S_1(K_1,i)−S_0(K_0,i)=[S_1(K_1,i)−S_0(K_1,i)]+[S_0(K_1,i)−S_0(K_0,i)].
4. For every α,a,σ,b,c∈ℝ and every u₁,u₂:Ω→ℝ, if u₁ and u₂ are μ-integrable, then the corresponding linear model has ΔK=a, M=ab, D=c, RF=ab+c, and RF≥M iff c≥0. For every natural n and d:Fin n→ℝ, if c=Σ_j d(j), then RF≥M iff Σ_j d(j)≥0. If additionally a>0, then RF/a=b+c/a and RF/a≥b iff c≥0. These linear conclusions quantify over new linear models, independently of whether the preceding arbitrary model is linear.
5. For every natural n and d:Fin n→ℝ, if every d(j)≥0 then Σ_j d(j)≥0. There exists d:Fin 2→ℝ with Σ_j d(j)≥0 but not every d(j)≥0.

The second conjunct uses exactly the fixed finite linear witness of T1: RF=0, M=3/50, D=−3/50, and M>0. It witnesses the failure of an unconditional null inference when the sign premise on D is absent. There are no bounds on general K or S, no nonatomicity or finiteness restriction on μ, and no mean-zero or independence premise on u₁,u₂.

## SAP.P043.T4

This is a closed conjunction about three fixed IV models, each with independent assignment p=1/2. Put H(k)=1_{9≤k} for all k∈ℕ.

**Two-type witness.** Ω=Bool: true (an up type) has weight 2/3, false (a down type) has weight 1/3. For true, (K_0,K_1)=(8,9), S(k)=3+H(k). For false, (K_0,K_1)=(9,8), S(k)=2+2H(k). The theorem asserts:

1. Knowledge arm means are 25/3 and 26/3; FS=1/3>0. Both support arm means are 10/3; RF_IV=0; W=0.
2. Cov(x,K)=1/12, Cov(x,Y)=0, and their ratio Cov(x,Y)/Cov(x,K)=0.
3. P(increaser)=2/3; τ_inc=1; and (2/3)·1+(1/3)·(−2)=0.
4. For every i, increaser(i) iff i=true. If i is an increaser, K_0=8, K_1=9, and S(9,i)−S(8,i)=1. For every t, K_t∈{8,9} and K_t≤18. For every k∈ℕ, S(k,i)∈{2,3,4}, 0≤S(k,i)≤7, and k↦S(k,i) is nondecreasing.

**Five-type witnesses.** Each has Ω=Fin 5 with uniform weights 1/5. In order i=0,…,4, both models have K_0=[8,8,9,8,9]. Model A has K_1=[9,9,8,8,9] and response functions [3+H,3+H,2+2H,2,4]. Model B has K_1=[9,9,8,9,8] and response functions [3+H,3+H,2+2H,2+2H,2+2H]. The theorem asserts:

1. For each model separately, the knowledge arm means are 42/5 and 43/5; FS=1/5>0; both support arm means are 16/5; RF_IV=0 and W=0.
2. Their entire joint observable point-mass laws on (t,k,y) are equal. More explicitly, for every t,k,y, both models have the following same conditional law: when t=true, mass 2/5 at (8,2) and 3/5 at (9,4); when t=false, mass 1/5 at (8,2), 2/5 at (8,3), and 2/5 at (9,4); zero elsewhere. Joint laws multiply these masses by 1/2.
3. τ_inc(A)=1 and τ_inc(B)=4/3. Each increaser event has nonzero probability, although this statement does not assert its exact probability.
4. For every i in each model, every K_t∈{8,9} and K_t≤18; for every natural k, 0≤S(k,i)≤7; the response is nondecreasing in k; and every increaser has K_0=8, K_1=9.
5. There does not exist a real-valued function F of real point-mass functions on Bool×(ℕ×ℝ) that simultaneously sends A's observable law to τ_inc(A) and B's observable law to τ_inc(B). This is an explicit full-observable-law failure of identification on these two models, with no continuity, measurability, or other restriction on F.

## SAP.P043.T5

Quantifier order: for every finite type Ω and finite-population weights P, and every real p, **if** 0<p<1, then for every IV model m and every natural J, **if** (i) every K_0(i),K_1(i)≤J, (ii) every K_0(i)≤K_1(i), and (iii) E[K_1−K_0]>0 (subtraction in ℝ), all the following hold. Exclusion, consistency and independent assignment are built into the objects. There is no monotonicity premise on the outcome response S and zero-weight types are allowed; the knowledge bounds and monotonicity are required even on zero-weight types.

For natural j, write Δ_j(i)=S(j,i)−S(j−1,i), C_j(i)=1_{K_0(i)<j≤K_1(i)}, R_j(i)=1_{j≤K_1(i)}−1_{j≤K_0(i)}, π_j=P(K_0<j≤K_1), w_j=π_j/FS, and τ_j=E[Δ_j | K_0<j≤K_1]. Then:

1. FS=E[K_1−K_0] and RF_IV=E[S(K_1)−S(K_0)]. Cov(x,K)=p(1−p)FS and Cov(x,Y)=p(1−p)RF_IV. If FS≠0, Cov(x,Y)/Cov(x,K)=W (the positive-first-stage premise already ensures this condition).
2. For every i, S(K_1,i)−S(K_0,i)=Σ_{j=1}^J C_j(i)Δ_j(i), and K_1(i)−K_0(i)=Σ_{j=1}^J C_j(i) in ℝ.
3. RF_IV=Σ_{j=1}^J E[C_jΔ_j] and FS=Σ_{j=1}^J π_j.
4. For every natural j, w_j≥0; Σ_{j=1}^J w_j=1; and W=Σ_{1≤j≤J, π_j>0} w_j τ_j. Thus conditional effects in this formula occur only at positive-probability margins; FS is strictly positive.
5. For every new IV model m′ on this same Ω, every natural J′, and every i, **if** K′_0(i),K′_1(i)≤J′, then S′(K′_1,i)−S′(K′_0,i)=Σ_{j=1}^{J′} R′_j(i)Δ′_j(i), and K′_1(i)−K′_0(i)=Σ_{j=1}^{J′} R′_j(i) in ℝ. No monotonicity is required of m′ in these identities.
6. For every i,j, if i is not an increaser of the original model then C_j(i)=0. For every i,j, R_j(i) belongs to {−1,0,1} and R_j(i)=C_j(i); these assertions concern the original, monotone model.
7. For every new model m′, every i,j, **if** K′_1(i)<j≤K′_0(i), then R′_j(i)=−1. This implication requires no monotonicity of m′.

All conclusions, including population-contrast and covariance identities, sit within the outer monotonicity, positive-first-stage, and finite-population hypotheses, even when a particular identity could be stated more generally. J=0 cannot satisfy the positive-first-stage premise. The theorem contains no separate full-law nonidentification conclusion.

## SAP.P043.T6

For every pair of natural numbers n,q, every map s:Fin n→Fin(q+1), and every coefficient vector γ:Fin q→ℝ, the following conjunction holds. Labels 0,…,q−1 are nonreference strata, label q (`Fin.last q`) is the reference. For each observation i and nonreference k, D_{ik}=1 if s(i)=k and zero otherwise; g_i=Σ_{k=0}^{q−1}γ_k D_{ik}. Let γ̃(r)=γ_r for r<q, and γ̃(q)=0 (the `Fin.lastCases` function).

1. For every i,k, if s(i)=k then g_i=γ_k.
2. For every i, if s(i)=q then g_i=0.
3. For every i, Σ_{k=0}^{q−1}D_{ik}=1−1_{s(i)=q}, with subtraction in ℝ.
4. For every binary regressor X:Fin n→Fin 2, every u,Y:Fin n→ℝ, and every β₀,β₁∈ℝ, the equations Y_i=β₀+β₁·val(X_i)+g_i+u_i for all i are equivalent to Y_i=(β₀+γ̃(s(i)))+β₁·val(X_i)+u_i for all i.

No sampling, error-mean, rank, treatment-randomization, or occupied-stratum assumptions occur. This is an identity about an arbitrarily specified regression equation, not an estimator or identification theorem. n=0 is included as an empty-observation case, but the theorem also quantifies over every nonempty sample; q=0 is the ordinary single reference stratum, with g_i=0 and no nonreference coefficients.
