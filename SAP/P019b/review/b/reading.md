# Blind reading of the Lean statements

This reading was written from `SAP/P019b/Defs*.lean`, `SAP/P019b/Defs/Part1`–`Part5.lean`, and `SAP/P019b/Challenge*.lean` only, before opening `claims.json` or `record.json`. The Challenge contains eleven theorems, T12–T22, each asserting the proposition of the corresponding name in Defs. The mathematical content below comes from those propositions, rather than their descriptive comments.

## Common objects and definitions

All studies have a finite sample space Ω (a Lean `Fintype`). A finite law P assigns a real number p(ω) ≥ 0 to each atom, with Σω p(ω) = 1. Its expectation, probability, conditional expectation, variance and conditional variance mean, exactly,

* E[f] = Σω p(ω)f(ω), P(D) = Σω p(ω)1_D(ω);
* E[f | D] = E[f 1_D]/P(D);
* Var(f) = E[f²] − E[f]² and Var(f | D) = E[f² | D] − E[f | D]².

The conditional definitions themselves do not require P(D)>0. Lean real division by zero is zero. Below I explicitly record the positivity premises wherever supplied. Finite sums, including all sample moments, are always finite. An empty Ω cannot carry a `FiniteLaw`, because its total mass would have to be both zero and one.

A study S comprises such a law and random variables W,V:Ω→ℕ and X,Y,Z:Ω→Bool. In formulas Bool variables denote their numerical indicators, 0 or 1 (`bitVal`). The event C_zy is {Z=z,Y=y}, with z,y in {0,1}. The four named assumptions are:

1. `monotone`: for every atom ω with p(ω)>0, Y(ω)=1 implies X(ω)=1.
2. `noLiarsDesign`: for every atom with p(ω)>0, V(ω)=W(ω)+X(ω)Z(ω), as an equality of real numbers.
3. `treatmentIndependent`: for every function f:ℕ×Bool×Bool→ℝ and each z∈Bool, E[1_{Z=z} f(W,X,Y)] = P(Z=z) E[f(W,X,Y)]. This is full independence of Z from (W,X,Y), not just vanishing covariances.
4. `nondegenerate`: for each of the four pairs (z,y), P(C_zy)>0 and Var(V | C_zy)>0, and also Var(Z)>0 and Var(Y)>0.

`standing` is the conjunction of these four assumptions, in this order. It implies 0<P(Y=1)<1 and 0<P(Z=1)<1; monotonicity then implies P(X=1)>0. Consequently the population conditioning probabilities in the standing-assumption statements are positive.

The population functionals used below are:

* μ=P(X=1), τ=E[Y | X=1], γ=P(Z=1), m_zy=E[V | C_zy];
* C=E[Y]+E[1−Y](m_10−m_00), called `combined`;
* β=m_11−m_01;
* δ=E[Y | Z=1]−E[Y | Z=0].

Here the first subscript is Z. All subtractions in these formulas are real subtraction.

## Samples and limit conventions

For each natural n, the entire ordered sample s:{0,…,n−1}→Ω has probability Π_i p(s_i). The definition `iid` uses this unconditioned product law; there is no conditioning on nonempty groups. Expectations and variances of estimators are finite sums over all these samples.

Write ȳ=n⁻¹Σ_i Y_i, N_zy=Σ_i 1_{C_zy}(s_i), A_z=Σ_i 1_{Z_i=z}, and γ̂=A_1/n. At n=0 the quotients ȳ and γ̂ are zero. For a fixed real c, m̂_zy(c) is the empirical V mean in C_zy if N_zy>0, and c otherwise. The empirical arm mean v̂_z(c) is the V mean among Z=z if A_z>0, and c otherwise. The empirical direct-response mean q̂_z(c) is the Y mean among Z=z if A_z>0, and c otherwise. Thus

* μ̂(c1,c0)=ȳ+(1−ȳ)(m̂_10(c1)−m̂_00(c0));
* μ̂_standard(d1,d0)=v̂_1(d1)−v̂_0(d0);
* β̂(c1,c0)=m̂_11(c1)−m̂_01(c0);
* δ̂(c1,c0)=q̂_1(c1)−q̂_0(c0).

Let s²_zy be Σ_{i∈C_zy}(V_i−m̂_zy(0))²/(N_zy−1) if N_zy≥2, and zero otherwise. The subtraction in this denominator is performed after casting N_zy to ℝ, not truncated natural subtraction. Let t²_z be the analogous sample variance of Y in arm z, with denominator A_z−1 if A_z≥2, and zero otherwise.

The three estimated variances, each with a fixed whole-estimate completion cV, are:

* v̂_μ(c1,c0,cV) = [(1−μ̂)² ȳ/(1−ȳ) + (1−ȳ)(s²_10/γ̂+s²_00/(1−γ̂))]/n if N_10,N_00≥2, ȳ<1, and 0<γ̂<1; otherwise cV.
* v̂_β(cV)=s²_11/N_11+s²_01/N_01 if N_11,N_01≥2; otherwise cV.
* v̂_δ(cV)=t²_1/A_1+t²_0/A_0 if A_1,A_0≥2; otherwise cV.

The population variance formulas are

σ² = [(1−μ)²/(1−μτ)]μτ + (1−μτ)[Var(V | C_10)/γ + Var(V | C_00)/(1−γ)],

σ²_standard = Var(V | Z=1)/γ + Var(V | Z=0)/(1−γ).

`normalCDF(t)` is Φ(t)=P(G≤t) for G distributed as Mathlib `gaussianReal 0 1`. Mathlib's second Gaussian parameter is the **variance**, a nonnegative real, not a standard deviation. `normalQuantile(u)` is inf{x∈ℝ:u≤Φ(x)}; it is used in these statements only for u strictly between zero and one, where this is the usual normal quantile. `gaussianReal 0 σ².toNNReal` is N(0,max(σ²,0)); T19 separately asserts σ²>0. Gaussian measures are probability measures, so taking their values' `ENNReal.toReal` does not convert an infinite measure value to zero.

`WeakLimit(P,T,Q)` means: for every f:E→ℝ, if f is continuous and there exists a real C with |f(x)|≤C for all x, then E_{P^n}[f(T_n)]→∫f dQ. In these theorems E=ℝ and Q is a Gaussian probability measure. Such f are measurable and integrable, so Mathlib's zero value for the Bochner integral of a nonintegrable function does not intervene. `ProbabilityLimit(P,T,a)` means: for every real ε>0, P^n(ε<|T_n−a|)→0. Limits are as natural n→∞ (`atTop`) in the usual real topology (`nhds`).

`RootNTight(S,c1,c0)` spells out: for every real ε>0 there is a real M>0 and a natural N such that for every natural n≥N, P^n(|√n(μ̂(c1,c0)−μ)|>M)<ε.

`normalPValue(e,h,v)` is 2Φ(−|e−h|/√v). Mathlib's real square root is zero for v≤0, and real division by zero is zero, so the corresponding statistic is zero and p-value is one at v≤0. Completion parameters are arbitrary fixed real numbers, quantified before the limits; they are not allowed to vary with n.

Mathlib source endpoints inspected: `Probability/Distributions/Gaussian/Real.lean` (`gaussianReal`, probability-measure instance); `Analysis/Real/Sqrt.lean` (`Real.sqrt`); `Basic/NNReal/Defs.lean` (`Real.toNNReal` conventions); `Basic/ENNReal/Basic.lean` (`toReal`); `MeasureTheory/Integral/Bochner/Basic.lean` (`integral`); `MeasureTheory/Function/L1Space/Integrable.lean` (integrability by a constant bound); `Order/Filter/Defs.lean` (`Tendsto`); `Order/Filter/AtTopBot/Defs.lean` (`atTop`); `Topology/Defs/Filter.lean` (`nhds`); and `Probability/CDF.lean` (CDF limit conventions).

## Theorems

### SAP.P019b.T12

For every finite type Ω and every study S on Ω: if S is monotone, satisfies the no-liars design equation, has full treatment independence, P(C_01)>0, and P(C_11)>0 (premises in that order), then β=1. There is no nondegeneracy or sample-asymptotics premise or conclusion in this theorem.

### SAP.P019b.T13

This is a conjunction about one specified study, without external hypotheses. Its sample space is {0,…,11}. Write j=⌊ω/4⌋∈{0,1,2}, b0=(ω mod 2), and b1=(⌊ω/2⌋ mod 2). Each atom with j=0 or j=1 has mass 1/16; each with j=2 has mass 1/8. Set W=1+b0, X=1_{j<2}, Y=1_{j=0}, Z=b1, V=W+XZ. Two labels indexed by a Boolean b are defined on this same study: watching Q_b=1_{j=0}∨(b∧1_{j=1}), and reading R_b=(¬b)∧1_{j=1}.

The asserted conjunction, in order, is:

1. This study satisfies all four standing assumptions.
2. For every Boolean b and every ω∈{0,…,11}, X(ω)=R_b(ω)∨Q_b(ω).
3. P(Q_false=1)=1/4 and P(Q_true=1)=1/2.
4. P(Y≠Q_false)=0 and P(Y≠Q_true)=1/4.
5. C=1/2, μ=1/2, β=1, and δ=0.

The two readings use identical law and identical observable random variables. The probabilities are weighted probabilities, not fractions of the twelve atoms. The theorem does not separately assert a numerical table of conditional moments.

### SAP.P019b.T14

For every finite Ω, study S, and pair of Boolean variables R,Q on Ω, assume in order:

1. For every ω, Y(ω)=Q(ω).
2. For every ω, X(ω)=R(ω)∨Q(ω).
3. S satisfies the no-liars design equation on positive-mass atoms.
4. For every f:ℕ×Bool×Bool→ℝ and Boolean z, E[1_{Z=z}f(W,R,Q)]=P(Z=z)E[f(W,R,Q)].
5. 0<P(Z=1)<1, and 0<P(Q=1)<1.

Put b=P(Q=1), a=P(R=1,Q=0), and L=E[V | Z=1]−E[V | Z=0]. Then the following conjunction holds: S is monotone, satisfies the no-liars design equation, and has treatment independence; m_10−m_00=E[X | Y=0]; E[X | Y=0]=a/(1−b); C=b+a; μ=b+a; L=b+a; E[Y]=b; C−b=a; L−b=a; (C=b iff a=0); (L=b iff a=0); β=1; and δ=0. No nondegeneracy of V is assumed or concluded. All conditioning events are positive as consequences of the independence and strict marginal-probability assumptions.

### SAP.P019b.T15

Define A=p1(1−p1)+p2(1−p2), B=(p1+p2)(1−(p1+p2)/2), d=|p1−p2|. For real n,p1,p2,c, define

F=Φ((√n d−c√B)/√A), O=Φ((−√n d−c√B)/√A),

H=P(c√(B/n)<|d+√(A/n)G|), G~N(0,1).

The first conjunct quantifies over all real n,p1,p2,α, then assumes n>0, 0≤p1≤1, 0≤p2≤1, A>0, and 0<α<1, in that order. With c=Φ⁻¹(1−α/2), it concludes the conjunction: c>0; B−A=(p1−p2)²/2; B−A≥0; H=F+O; O=1−Φ((√n d+c√B)/√A); 0<O≤α/2; (O=α/2 iff p1=p2); and H−F=O.

The second conjunct has no hypotheses. With c=Φ⁻¹(39/40), it asserts A(1/2,1/2)=1/2, B(1/2,1/2)=1/2, |1/2−1/2|=0, F(50,1/2,1/2,c)=Φ(−c), Φ(−c)=1/40, O(50,1/2,1/2,c)=1/40, and H(50,1/2,1/2,c)=1/20. The theorem's numerical n is 50; it does not define a total sample-size variable N.

### SAP.P019b.T16

On {0,1,2,3,4}, use the probability masses (81,216,216,96,16)/625. Write w for the corresponding natural number, U(w)=w+1 and A(w)=min(w+1,4), cast to real. For every real ρ, if ρ≥0 and ρ≤1, then

E[(1−ρ)U(w)+ρA(w)]−E[w] = 1−(16/625)ρ.

The expectation is under the specified fixed law, the Binomial(4,2/5) law. The mixture's mean is explicitly a convex combination with the same constant ρ at every w. There are no sample sizes, hypothesis-test rejection events, or other response mechanisms in this proposition.

### SAP.P019b.T17

For every finite Ω and study S, two implications hold as a conjunction:

1. If all four standing assumptions hold, then μ=C.
2. If the no-liars design equation, full treatment independence and nondegeneracy hold, and P(X=0,Y=1)>0, then C=μ+P(X=0,Y=1) and μ<C.

The second implication has no monotonicity hypothesis. It uses a positive-probability false-confession event, rather than a pointwise inequality or an explicit negation of monotonicity. The theorem does not expressly conclude E[X | Y=1]<1.

### SAP.P019b.T18

For every finite Ω and study S, if all four standing assumptions hold, then for every pair of fixed reals c1,c0,

n Var_{P^n}(μ̂(c1,c0)) → σ².

This is convergence of the actual unconditioned sampling variance, not merely a distributional convergence or a variance of a limiting Gaussian.

### SAP.P019b.T19

For every finite Ω and study S, assume all four standing assumptions; then for every three fixed reals c1,c0,cV the following conjunction holds:

1. σ²>0.
2. √n(μ̂(c1,c0)−μ) is tight with the ε,M,N quantifier order given above.
3. √n(μ̂(c1,c0)−μ) converges weakly to N(0,σ²).
4. n v̂_μ(c1,c0,cV) converges in probability to σ².
5. For every real α, if 0<α<1, then P^n(|μ̂(c1,c0)−μ|≤Φ⁻¹(1−α/2)√v̂_μ(c1,c0,cV)) → 1−α.

The completion constants are selected before α and before taking any limits. A negative variance completion is permitted and its square root is zero on the affected samples.

### SAP.P019b.T20

For every finite Ω and study S, assume all four standing assumptions; then for every four fixed reals c1,c0,d1,d0 the following conjunction holds:

n Var_{P^n}(μ̂(c1,c0))→σ²; n Var_{P^n}(μ̂_standard(d1,d0))→σ²_standard; and σ²<σ²_standard.

The last comparison is strictly between the two limiting variance coefficients. It is not a finite-n comparison.

### SAP.P019b.T21

For every finite Ω and study S, assume all four standing assumptions; then for every three fixed reals c1,c0,cV the conjunction holds:

1. β=1.
2. (β̂(c1,c0)−1)/√v̂_β(cV) converges weakly to N(0,1).
3. For every real u, if 0<u<1, then P^n(2Φ(−|β̂(c1,c0)−1|/√v̂_β(cV))≤u)→u.

There is no conditioning on successful sample cell counts. For zero or negative estimated variance the statistic is zero and its p-value one, using the totalized arithmetic specified above.

### SAP.P019b.T22

For every finite Ω and study S, two implications hold as a conjunction:

1. If treatment independence holds, P(Z=0)>0 and P(Z=1)>0, then δ=0.
2. If treatment independence and nondegeneracy hold, then for every three fixed reals c1,c0,cV: δ=0; δ̂(c1,c0)/√v̂_δ(cV) converges weakly to N(0,1); and for every real u with 0<u<1, P^n(2Φ(−|δ̂(c1,c0)|/√v̂_δ(cV))≤u)→u.

Neither implication assumes monotonicity or the no-liars design equation. The same zero-statistic/one-p-value convention applies at nonpositive estimated variance. There is no causal assignment mechanism or questionnaire-order variable in this statement.
