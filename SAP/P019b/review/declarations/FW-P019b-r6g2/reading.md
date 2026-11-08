# Blind reading

Written from `closure.json`, the Challenge docstrings/statements, their source definitions, and scratch inspection of the generated closure declarations. No claims, record, earlier review, or architect report has been opened at this stage.

Throughout, a Boolean is interpreted as its indicator in the real numbers: true is 1 and false is 0. All natural-number counts in real expressions are cast into the real numbers, preserving their value. A limit is a Mathlib `Filter.Tendsto` limit along natural numbers tending to infinity. No theorem here is merely about a selected subsequence.

## SAP.P019b.T17

Source: `Challenge/Part1.lean:48–54`; statement: `Defs/WholeW1.lean:150–160`.

Objects, definitions, and hypotheses, fully unfolded:

* First quantify over every type Ω in `Type`, every measurable-space structure on Ω, and every probability measure P on it. Then quantify over measurable functions W,V: Ω → ℕ and X,Y,Z: Ω → Bool. The structure also requires that there exist a single natural J with W ≤ J and V ≤ J+1 P-almost surely. A probability measure is finite and hence sigma-finite. No standard-Borel structure on Ω is required by this statement.
* For real f, write E[f] for the Bochner integral ∫ f dP; for an event A, write p(A) for `(P A).toReal`. All events actually used here are measurable. Define m(f,A)=E[1_A f]/p(A), v(f)=E[f²]−E[f]², and v(f,A)=m(f²,A)−m(f,A)². These are literal ratios and moment differences, not opaque conditional expectations.
* Let C(z,y)={Z=z,Y=y}, for Booleans z,y. Let m(z,y)=m(V,C(z,y)), μ=p(X=true), a=p(Y=true), F=p(X=false,Y=true), and q=m(1_{X=true},{Y=true}). The combined functional is B=E[1_{Y=true}]+E[1−1_{Y=true}](m(true,false)−m(false,false)).
* A1 means Y=true implies X=true P-almost surely. A2 means V=W+1_{X=true}1_{Z=true} P-almost surely. A3 is Mathlib independence of the pair of random objects (W,X,Y) and Z (equivalently, the joint probability factors for every pair of measurable target events). A4 means p(C(z,y))>0 and v(V,C(z,y))>0 for all four Boolean pairs, together with v(1_{Z=true})>0 and v(1_{Y=true})>0. `standing` is exactly A1 ∧ A2 ∧ A3 ∧ A4, with no additional hypothesis in that abbreviation.

Conclusion and quantifier order:

For each such model the theorem asserts the conjunction of two implications. First, A1–A4 imply μ=B. Independently, A2, then A3, then A4 imply all of: a>0; B=μ+F; F=a(1−q); (not A1) iff F>0; (not A1) iff q<1; and, if not A1, μ<B and q<1. The second implication does not assume A1. Negation of A1 is failure of the almost-sure implication, not a failure confined to a null point.

Junk values and boundary cases:

* The real ratio defining m is zero when its denominator is zero. Here every list-mean cell has positive probability under A4, and the confessor event has positive probability because it contains a positive-probability cell. Thus this convention does not supply any claimed identity.
* `ENNReal.toReal` would send infinity to zero. All measures of events used here are bounded by the probability mass 1, so infinity never occurs.
* A Bochner integral of a nonintegrable function is defined to be zero. The bounded natural counts, their squares, Boolean indicators, and their restricted versions are measurable and almost surely bounded under a probability measure. They are integrable; this default cannot affect the conclusions. The generic mean/variance definitions permit other functions, but the statement never uses them.
* The probability-measure field rules out an empty Ω with no points. J=0 is syntactically permitted, although A4 rules out models whose relevant cell variances vanish. The constructor's field names and projections are ordinary structure data, not conclusions encoded in definitions.
* There is no natural-number subtraction, logarithm, square root, real power, infimum, supremum, limsup, liminf, or partial-function default in this closure.

## SAP.P019b.T18

Source: `Challenge/Part1.lean:56–62`; statement: `Defs/Part5.lean:12–15`.

Objects, definitions, and hypotheses, fully unfolded:

* Quantify over every finite type Ω with a `Fintype`, weights w: Ω→ℝ satisfying w(ω)≥0 and Σω w(ω)=1, functions W,V: Ω→ℕ and X,Y,Z: Ω→Bool. Define E[f]=Σω w(ω)f(ω), p(A)=Σω w(ω)1_A(ω), m(f,A)=E[1_A f]/p(A), v(f)=E[f²]−E[f]², and v(f,A)=m(f²,A)−m(f,A)². All functions on this finite space have finite moments. There is no additional uniform sampling assumption on the weights; zero masses are allowed.
* A1 is ∀ω, w(ω)>0 → (Y(ω)=true → X(ω)=true). A2 is ∀ω, w(ω)>0 → V(ω)=W(ω)+1_{X(ω)=true}1_{Z(ω)=true}, interpreted in ℝ. A3 is the following full factorization: for every f:ℕ→Bool→Bool→ℝ and every Boolean z,
  E[1_{Z=z} f(W,X,Y)]=p(Z=z)E[f(W,X,Y)]. A4 requires that for every z,y, C(z,y)={Z=z,Y=y} has p(C(z,y))>0 and v(V,C(z,y))>0, and additionally v(1_{Z=true})>0 and v(1_{Y=true})>0. All four assumptions are required by `standing`.
* Define μ=p(X=true), r=m(1_{Y=true},{X=true}), and γ=p(Z=true). The variance constant is
  σ²=((1−μ)²/(1−μr))μr +(1−μr)[v(V,C(true,false))/γ+v(V,C(false,false))/(1−γ)].
* After choosing a model satisfying these hypotheses, quantify over every fixed pair c1,c0∈ℝ. For every n∈ℕ the ordered sample space is Ω^{Fin n}; its weight at s is ∏i w(s(i)). These are unconditioned independent identically distributed draws, not fixed cell sizes or a sample conditioned on nonempty cells. The closure's generated proof 1 certifies nonnegativity of the product and proof 2 certifies its sum is 1.
* For sample s, let a_n=Σi 1_{Y(s(i))=true}/n and N(z,y)=Σi 1_{C(z,y)}(s(i)). Let M(z,y;c)=c when N(z,y)=0, and otherwise Σi 1_{C(z,y)}(s(i))V(s(i))/N(z,y). The estimator is b_n=a_n+(1−a_n)[M(true,false;c1)−M(false,false;c0)]. Sample variance is the weighted second moment of b_n under the full product law minus the square of its weighted mean.

Conclusion and quantifier order:

For every finite model, if A1–A4 hold, then for every fixed c1,c0, lim_{n→∞} n Var_{w^{⊗n}}(b_n)=σ². The conclusion concerns actual finite-sample variances and their limit; it does not only introduce a name for an asymptotic variance. The docstring expressly limits the underlying probability space to a finite one and omits the arbitrary-space extension.

Junk values and boundary cases:

* Conditional means divide by zero outside positive-probability events. Here A4 makes all cells positive, makes γ and 1−γ positive, and gives 0<p(Y=true)<1. A1 and p(Y=true)>0 imply μ>0, so r is genuine. A1 also implies μr=p(Y=true), giving 1−μr>0. Thus every population denominator used in σ² is nonzero.
* Empty sample cells use the explicitly quantified real constants; these are meaningful completions rather than implicit claims about conditional means on empty cells. Positive cell probabilities make emptiness exponentially unlikely. The constants cannot depend on n or the realized sample.
* At n=0, the empty sum divided by zero makes a_n=0; the cell means are c1,c0. The empty product yields mass 1 on the unique empty sample. The n=0 term of n Var is zero. A single initial term cannot alter the limit.
* A finite Ω may syntactically be empty, but nonnegative weights summing to 1 rule it out. Natural-number casts preserve values; no truncated subtraction occurs.
* There are no Bochner integrals, infinite extended-real masses, square roots, logarithms, real powers, infima/suprema, limsup/liminf, or partial-function defaults in this closure.

## SAP.P019b.T19

Source: `Challenge/Part1.lean:64–71`; statement: `Defs/Part5.lean:17–27`.

Objects, definitions, and hypotheses, fully unfolded:

* Quantify first over every finite Ω, all real weights w≥0 summing to 1, and W,V:Ω→ℕ, X,Y,Z:Ω→Bool. E, p, conditional moment m and unconditional/conditional variance v are respectively weighted sums, indicator-weighted sums, E[1_A f]/p(A), E[f²]−E[f]², and m(f²,A)−m(f,A)².
* Require A1: Y⇒X on every positive-mass atom; A2: V=W+1_X1_Z on every positive-mass atom; A3: E[1_{Z=z}f(W,X,Y)]=p(Z=z)E[f(W,X,Y)] for every real f on ℕ×Bool×Bool and every z; and A4: every C(z,y)={Z=z,Y=y} has positive probability and positive conditional V variance, and both Boolean Z and Y have positive variance.
* Define μ=p(X=true), r=E[1_{X=true}1_{Y=true}]/p(X=true), γ=p(Z=true), and
  σ²=((1−μ)²/(1−μr))μr +(1−μr)[v(V,C(true,false))/γ+v(V,C(false,false))/(1−γ)].
* Quantify next over arbitrary fixed c1,c0,cV∈ℝ. For n, use sample weights ∏i w(s(i)) on Ω^{Fin n}. For s define N(z,y)=Σi 1_{C(z,y)}(s(i)), H(z)=Σi 1_{Z=z}(s(i)), a_n=Σi 1_Y(s(i))/n, and g_n=H(true)/n. Define M(z,y;c) to be c at N(z,y)=0 and otherwise the sample V average in that cell. Define b_n=a_n+(1−a_n)(M(true,false;c1)−M(false,false;c0)).
* Let Q(z,y)=0 if N(z,y)<2; otherwise Q(z,y)=Σi 1_{C(z,y)}(s(i))[V(s(i))−M(z,y;0)]²/(N(z,y)−1), with real subtraction. The variance estimate vhat_n equals
  {[(1−b_n)²/(1−a_n)]a_n +(1−a_n)[Q(true,false)/g_n+Q(false,false)/(1−g_n)]}/n
  if N(true,false),N(false,false)≥2, a_n<1, and 0<g_n<1; otherwise it equals the single fixed real cV. The within-cell sample variances themselves have the fixed zero completion at deficient cells.
* Φ(t)=((gaussianReal 0 1)((−∞,t])).toReal, the standard normal CDF. For u, z(u)=inf{x∈ℝ:u≤Φ(x)}, implemented using the conditionally complete real `sInf`. A Gaussian `gaussianReal 0 (σ².toNNReal)` uses the second argument as variance. `toNNReal` truncates a negative real to zero.
* Weak convergence is literally convergence, for every continuous f:ℝ→ℝ admitting a real bound C with |f(x)|≤C for all x, of the product-law weighted average of f(T_n) to ∫ f dQ. Probability convergence of U_n to a means that for every ε>0 the product probability of ε<|U_n−a| tends to zero. Root-n tightness means ∀ε>0 ∃M>0 ∃N∈ℕ ∀n≥N, product probability of M<|sqrt(n)(b_n−μ)| is <ε.

Conclusion and quantifier order:

For every such model satisfying A1–A4 and every fixed triple c1,c0,cV, simultaneously: σ²>0; the preceding root-n tightness condition holds; sqrt(n)(b_n−μ) converges weakly to the centered Gaussian of variance σ²; n vhat_n converges in probability to σ²; and for every α∈ℝ, 0<α<1 implies
lim P_{w^{⊗n}}(|b_n−μ|≤z(1−α/2)sqrt(vhat_n))=1−α.
The interval is closed, symmetric, and based on the unscaled variance estimate. The docstring discloses the finite underlying-space restriction.

Junk values and boundary cases:

* As for T18, A4 and A1 ensure p(X=true)>0, γ∈(0,1), μr=p(Y=true)∈(0,1), and every population conditioning event is positive. No population zero denominator is used to obtain a claimed result.
* Empty means use c1,c0 and the variance estimate uses cV when its explicit guard fails. The whole estimate may therefore be negative on deficient samples if cV<0. Lean sqrt of a nonpositive real is zero, so the displayed interval then has zero half-width. This is an actual completion convention; positive-probability cells and positive limiting variance make the exceptional events asymptotically negligible.
* The guards N≥2 ensure the N−1 denominator in Q is a positive real. Subtraction is in ℝ, not truncated ℕ subtraction. The vhat guard also forces n>0 and avoids 1−a_n=0, g_n=0 and 1−g_n=0. At n=0, a_n and g_n are zero by real division; vhat_n=cV, sqrt(n)=0. These initial values cannot affect any limit.
* The conclusion σ²>0 prevents `toNNReal` from truncating its Gaussian variance. The proof named `T19Statement._proof_1` is only the generated `(1+1).AtLeastTwo` arithmetic instance, not an additional substantive assumption.
* Quantiles are evaluated only at 1−α/2∈(1/2,1), where the Gaussian upper-level set is nonempty and bounded below. Thus the empty/unbounded `sInf` default is never used. Φ's measure is at most 1, so `toReal` never sees infinity. The Gaussian integral of a bounded continuous f is integrable; its Bochner fallback zero is not used.
* Probability weights exclude empty Ω, while Fin 0 is harmless as described above. No logarithm, rpow, sSup, limsup, liminf, or partial-function default occurs.

## SAP.P019b.T20

Source: `Challenge/Part1.lean:73–79`; statement: `Defs/Part5.lean:29–35`.

Objects, definitions, and hypotheses, fully unfolded:

* Quantify over a finite Ω, weights w:Ω→ℝ with w≥0 and Σw=1, W,V:Ω→ℕ and X,Y,Z:Ω→Bool. Define E,p,m,v by weighted sum, event indicator sum, restricted-sum/probability ratio, second moment minus squared first moment, and conditional second moment minus squared conditional first moment.
* A1 requires Y⇒X at all positive-mass atoms. A2 requires V=W+1_X1_Z at those atoms. A3 requires E[1_{Z=z}f(W,X,Y)]=p(Z=z)E[f(W,X,Y)] for every f:ℕ×Bool×Bool→ℝ and every Boolean z. A4 requires p(C(z,y))>0 and v(V,C(z,y))>0 for each C(z,y)={Z=z,Y=y}, and v(1_Z)>0 and v(1_Y)>0. These assumptions are conjoined, not alternatives.
* Define μ=p(X=true), r=E[1_X1_Y]/p(X=true), γ=p(Z=true),
  σ²=((1−μ)²/(1−μr))μr +(1−μr)[v(V,C(true,false))/γ+v(V,C(false,false))/(1−γ)], and
  τ²=v(V,{Z=true})/γ+v(V,{Z=false})/(1−γ).
* Quantify over four fixed reals c1,c0,d1,d0. For n, the sample probability at s:Fin n→Ω is ∏i w(s(i)). Define a_n=Σi 1_Y(s(i))/n and N(z,y)=Σi 1_{C(z,y)}(s(i)). Complete the within-cell V means by c1,c0 when their cells are empty; b_n=a_n+(1−a_n)(M(true,false;c1)−M(false,false;c0)). Define H(z)=Σi 1_{Z=z}(s(i)); an arm V mean is d_z at H(z)=0 and otherwise Σi 1_{Z=z}(s(i))V(s(i))/H(z). The standard estimator t_n is the treated arm mean completed by d1 minus the control arm mean completed by d0. Product-law variance is the finite weighted second moment minus the square of the weighted mean.

Conclusion and quantifier order:

For each model with A1–A4 and each fixed quadruple of completions, the theorem asserts together lim n Var(b_n)=σ², lim n Var(t_n)=τ², and σ²<τ². It is an asymptotic strict comparison, not an assertion Var(b_n)<Var(t_n) for every finite n. The docstring discloses precisely the finite underlying-space scope and says the arbitrary-space limits and comparison are omitted.

Junk values and boundary cases:

* A4 supplies positive cell and arm probabilities; A1 plus A4 supplies μ>0 and μr=p(Y=true)∈(0,1). All denominators in σ², τ², and the population conditional variances are nonzero.
* Empty sample cells/arms use explicitly quantified fixed reals. Their probabilities go to zero exponentially under the actual unconditioned iid law. A constant may be arbitrarily large but cannot grow with n. Conditional nonempty sample means are guarded against division by zero.
* At n=0, a_n=0 and all means use their completions; the sample law is concentrated on the unique empty sample. Both scaled variance expressions have factor n=0. No conclusion depends on this initial convention.
* The weight sum 1 prevents empty Ω. Casts from ℕ to ℝ preserve values. This closure uses no truncated subtraction, Bochner integral, `toReal`, square root, logarithm, rpow, infimum, supremum, limsup/liminf, or partial-function default.

## SAP.P019b.T21

Source: `Challenge/Part1.lean:81–89`; statement: `Defs/WholeW1.lean:165–179`.

Objects, definitions, and hypotheses, fully unfolded:

* A model consists of any type Ω in `Type` with a measurable-space structure, a probability measure P, measurable W,V:Ω→ℕ and X,Y,Z:Ω→Bool, and a natural J with W≤J and V≤J+1 P-almost surely. Expectations are Bochner integrals, event probabilities are `(P A).toReal`, conditional means are E[1_A f]/p(A), and variances are E[f²]−E[f]² (conditionally, the same difference of conditional moments).
* A1 means Y⇒X almost surely; A2 means V=W+1_X1_Z almost surely; A3 means (W,X,Y) is independent of Z; A4 means all C(z,y)={Z=z,Y=y} have positive probability and positive conditional V variance, and the two Boolean Y and Z variances are positive. `standing` conjoins A1–A4.
* Let m(z,y)=E[1_{C(z,y)}V]/p(C(z,y)), β=m(true,true)−m(false,true). For every real t the control atom is E[1_{C(false,true)}1_{V=t}]/p(C(false,true)); the shifted treated atom is E[1_{C(true,true)}1_{V=t+1}]/p(C(true,true)). The distributional null is positivity of these two confessor-cell probabilities and equality of these two atom probabilities for every real t. Finite almost-sure support of V makes this equality equivalent to equality of the complete conditional distributions of V in control and V−1 in treatment. The subtraction is in ℝ, so no underflow of natural counts is hidden.
* For sample size n, the law is the genuine product measure P^{Fin n}, implemented by `Measure.pi`, on the product measurable space. For an event D, sample probability is `(P^{Fin n} D).toReal`. The empty product is the probability law on a single empty sample.
* For s:Fin n→Ω, N(z,y)=Σi 1_{C(z,y)}(s(i)). A cell mean M(z,y;c) equals c if N=0, otherwise Σi 1_C(s(i))V(s(i))/N. Let Q(z,y)=0 if N<2, otherwise Σi 1_C(s(i))[V(s(i))−M(z,y;0)]²/(N−1), using real arithmetic. For any fixed c1,c0,cV, βhat_n=M(true,true;c1)−M(false,true;c0), and vhat_n=Q(true,true)/N(true,true)+Q(false,true)/N(false,true) when both counts are ≥2, or cV otherwise.
* Φ(t)=((gaussianReal 0 1)((−∞,t])).toReal. The p-value is 2Φ(−|βhat_n−1|/sqrt(vhat_n)). A weak limit to standard normal means that for every continuous real f bounded in absolute value by some real constant, the integral of f of the sample statistic under P^{Fin n} tends to ∫f d(gaussianReal 0 1).
* An observation is the triple (Z,Y,V) in Bool×Bool×ℕ. A test at n is a function `reject:(Fin n→(Bool×Bool×ℕ))→Bool`. Its rejection probability is the product-law probability of `reject(i↦(Z(s(i)),Y(s(i)),V(s(i))))=true`. It receives the entire ordered observable sample. It is a deterministic Boolean rule, with no separately quantified auxiliary random seed.

Conclusion and quantifier order (three conjoined assertions):

1. For every model, A1, then A2, then A3, then positive control-confessor probability, then positive treated-confessor probability imply the distributional null just defined. A4 is not required for this part.
2. For every model, A1–A4 imply β=1 and, for every fixed real c1,c0,cV, both (βhat_n−1)/sqrt(vhat_n) ⇒ N(0,1) and, for every real 0<u<1, lim P^{Fin n}(2Φ(−|βhat_n−1|/sqrt(vhat_n))≤u)=u.
3. First quantify over n∈ℕ, α∈ℝ, and a test reject; assume 0≤α≤1. Assume that for every measurable probability model of the specified bounded-count type satisfying the distributional null, its rejection probability is ≤α. Then for every such model satisfying A1–A3 and the two positive confessor-cell conditions, its rejection probability is ≤α. The level premise is uniform over null models; it does not assume the particular conclusion for the alternative family as an unexplained extra hypothesis.

Junk values and boundary cases:

* Positive confessor probabilities are explicit in part 1 and part 3 and supplied by A4 in part 2. Thus all relevant conditional means and atom probabilities have nonzero denominators.
* Each event probability is finite because P and its finite products are probability measures. `ENNReal.toReal ∞=0` therefore cannot change any result. The observed sample takes values in a countable discrete type; every Boolean rejection rule on it gives a measurable event. No arbitrary nonmeasurable subset is used as a test event.
* Counts and squares are almost surely bounded and measurable. The cell sample expressions and all fixed completions are integrable for each finite n. The studentized statistic uses total real arithmetic and is measurable, and bounded continuous test functions are integrable against probability measures. The zero default for nonintegrable Bochner integrals cannot generate the asserted limits.
* Empty cell means and deficient variance estimates use the fixed real completions. If vhat_n≤0 then Lean sqrt(vhat_n)=0 and real division by zero makes the statistic zero, giving p-value 2Φ(0)=1. This applies also when a nondeficient empirical variance happens to be zero. A4 ensures nonzero population variances and positive cells, so the relevant defective-sample events vanish asymptotically.
* N−1 is a positive real in the guarded sample variance branch, not truncated natural subtraction. At n=0 all means are completed and the product sample is the unique empty sample; asymptotic conclusions ignore that initial term, while the level-test implication still makes sense for n=0.
* A probability measure rules out empty Ω. The closure has no logarithm, rpow, sInf/sSup, limsup/liminf, or partial-function default. It uses no quantile definition. Interior CDF limits plus p-value range [0,1] express asymptotic uniformity, even though the statement spells out only 0<u<1.

All closure entries have been read, including the structure constructors/projections, iid nonnegativity/normalization proofs, and T19's generated arithmetic proof. Declarations in `WholeW1.lean` concerning finite encodings and agreement structures are not dependencies of these theorem statements and impose no hypotheses on them.
