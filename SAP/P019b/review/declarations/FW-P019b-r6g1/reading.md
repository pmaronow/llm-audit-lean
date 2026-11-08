# Blind reading

This file was written before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. The sources read were the five Challenge docstrings and statements, `closure.json`, and every SAP declaration in their combined closure. `scratch/BlindTypes.lean` prints the definitions and checks all generated proof auxiliaries; its successful output is in `scratch/BlindTypes.out`. The auxiliaries prove numerical denominator facts or the nonnegativity and normalization of the explicitly given finite laws. They add no statistical assumptions.

Throughout, a Boolean is identified with its real indicator (true = 1, false = 0). Natural counts are cast into the reals before real arithmetic. In formulas below, (P(D)) and (E(f)) mean actual probability and expectation, not uninterpreted SAP parameters. For a finite law with atom masses (m_i\geq0), (Σ_i m_i=1), they mean (Σ_{i:D(i)}m_i) and (Σ_i m_i f(i)). Write (E(f\mid D)=E(f1_D)/P(D)), and (σ^2(f\mid D)=E(f^2\mid D)-E(f\mid D)^2). All conditionings that the reviewed assertions use have positive probability, as detailed below. Variance is (E(f^2)-E(f)^2).

## SAP.P019b.T12

Source: `Challenge/Part1.lean:7–13`; statement `Defs/WholeW1.lean:145–149`.

Quantifiers, in order: for every type (Ω), every measurable-space structure on (Ω), and every probability measure (P) and measurable variables (W,V:Ω\to\mathbb N), (X,Y,Z:Ω\to\{0,1\}), such that for some fixed natural (J), (W\leq J) and (V\leq J+1) almost surely, assume:

1. Almost surely (Y=1\Rightarrow X=1).
2. Almost surely (V=W+XZ), as an equality of real-valued casts.
3. The joint variable ((W,X,Y)) is independent of (Z) under (P) (Mathlib `IndepFun`, equivalently factorization of measurable preimage events).
4. (P(Z=0,Y=1)>0), then (P(Z=1,Y=1)>0).

Let (D_{zy}=\{Z=z,Y=y\}), (m_{zy}=E(V\mid D_{zy})), and (β=m_{11}-m_{01}). The conclusion is the conjunction of (β=1) and the following conditional inference assertion. It requires an additional hypothesis: every one of the four (D_{zy}) has positive probability and strictly positive conditional variance of (V), and both (Z) and (Y) have strictly positive variance. Thus this nondegeneracy is needed only for inference, not for the population equality.

Under that additional hypothesis, for every three fixed real constants (c_1,c_0,c_V), two conclusions hold. For each (n\in\mathbb N), sample (s=(s_i)_{i\in\mathrm{Fin}(n)}) with the genuine product measure (P^{\otimes n}). Define

- (N_{zy}(s)=Σ_i1_{D_{zy}}(s_i)).
- (̄V_{zy}^{c}=c) if (N_{zy}=0), otherwise (Σ_i1_{D_{zy}}(s_i)V(s_i)/N_{zy}).
- (S_{zy}^2=0) if (N_{zy}<2), otherwise (Σ_i1_{D_{zy}}(s_i)(V(s_i)-̄V_{zy}^{0})^2/(N_{zy}-1)), where the subtraction in the denominator is in (ℝ).
- (̂β=̄V_{11}^{c_1}-̄V_{01}^{c_0}).
- (̂v=S_{11}^2/N_{11}+S_{01}^2/N_{01}) if both counts are at least two, and (̂v=c_V) otherwise.

First, (T_n=(̂β-1)/\sqrt{̂v}) converges weakly to the real Gaussian measure with mean zero and variance one. Explicitly, for every continuous (f:\mathbb R\to\mathbb R), if there exists a real (C) such that (|f(x)|\leq C) for every (x), then (∫ f(T_n(s))\,dP^{\otimes n}(s)\to∫ f\,dN(0,1)). The test-function bound is quantified after the constants and does not restrict the underlying random variables.

Second, for every real (u), if (0<u<1), then

 (P^{\otimes n}\{2Φ(-|̂β-1|/\sqrt{̂v})\leq u\}\to u),

where (Φ(t)=N(0,1)((-\infty,t])). These are all interior CDF limits for the p-value, hence the usual uniform limit. The theorem does not quantify over a coupling of different sample sizes; each sample size uses its own product measure.

Junk-value audit: conditional means are real division, so a zero conditioning probability would give zero; the two population means are protected by explicit positivity. Under the inference hypothesis all four population conditional means/variances are protected. Means are Bochner integrals, which would return zero if not integrable, but measurable, almost surely bounded counts under a probability measure have finite moments. The bounded continuous test functions are integrable on the product probability space. All probability `toReal` calls have finite arguments, since the law and its finite products are probability measures. An empty underlying space cannot support such a probability measure. The (n=0) sample is a singleton with product mass one, and empty sums have value zero; its completed estimates are harmless in a limit at infinity. Empty sample means use the explicitly quantified constants. Cells of size zero or one have variance zero by definition; the estimate uses (c_V) whenever either relevant cell has fewer than two observations. If a completed variance is nonpositive, Mathlib's real square root is zero and real division by zero is zero; the statistic becomes zero and its p-value becomes (2Φ(0)=1). This convention can affect finite samples, but the statement explicitly quantifies every fixed real completion. Even a nondeficient sample can have zero empirical variance, with the same convention. There is no natural truncated subtraction, quantile, logarithm, real power, supremum, limsup, or partial-function default here. The count-to-real casts are exact.

Docstring reading: it asserts the population placebo equality under assumptions 1–3 with defined confessor cells, and standard normal/studentized-p-value limits after adding nondegeneracy. It explicitly acknowledges usual measure conditions, arbitrary underlying spaces, and fixed completions.

## SAP.P019b.T13

Source: `Challenge/Part1.lean:15–23`; statement `Defs/WholeW1.lean:187–229`, including `Defs/Part4.lean:19–28`.

This is a closed conjunction about explicit data, without an antecedent. The underlying set is the twelve integers (i=0,\dots,11). Let (t=\lfloor i/4\rfloor\in\{0,1,2\}), (b_0=i\bmod2), and (z=\lfloor i/2\rfloor\bmod2). Each atom in types 0 and 1 has mass (1/16); each type-2 atom has mass (1/8). Thus type probabilities are (1/4,1/4,1/2), the baseline (W=1+b_0) is equally likely one or two, assignment (Z=z) is fair, and all three factors are independent. Set (X=1_{t<2}), (Y=1_{t=0}), (V=W+XZ).

For world (b\in\{0,1\}), let watching (Q_b=1_{t=0}\lor(b\land1_{t=1})), and reading (R_b=(1-b)\land1_{t=1}). The same atom masses and the same (W,X,Y,Z,V) are used for both worlds. The explicit type table, asserted for every world and atom, is:

| type | (R_b,Q_b,X,Y) |
| --- | --- |
| 0 | (0,1,1,1) |
| 1 | (1-b,b,1,0) |
| 2 | (0,0,0,0) |

The first part asserts all four standing conditions for these fixed variables: (Y=1\Rightarrow X=1) on positive atoms, (V=W+XZ) on positive atoms, independence of (Z) from the joint ((W,X,Y)) (factorization for every real function (f(W,X,Y)) and each Boolean value of (Z)), and positive probabilities and positive conditional (V)-variances in all four ((Z,Y)) cells, along with positive variances of (Z) and (Y). It also asserts, in order:

- For every world (b) and atom, (X=R_b\lor Q_b).
- (P(Q_0=1)=1/4), (P(Q_1=1)=1/2), (P(Y\ne Q_0)=0), and (P(Y\ne Q_1)=1/4).
- With (μ=P(X=1)), (β=E(V\mid Z=1,Y=1)-E(V\mid Z=0,Y=1)), (δ=E(Y\mid Z=1)-E(Y\mid Z=0)), and (C=E(Y)+E(1-Y)[E(V\mid Z=1,Y=0)-E(V\mid Z=0,Y=0)]), one has (C=μ=1/2), (β=1), and (δ=0).

The additional conjunction asserts the full joint type/baseline/assignment table: for every (t\in\mathrm{Fin}(3)), (w\in\mathrm{Fin}(2)), (z\in\{0,1\}),

 (P(t(i)=t,W=1+w,Z=z)=q_t(1/2)(1/2)), (q_0=q_1=1/4,q_2=1/2),

and explicitly asserts each of the three marginal tables. After the type table and the pointwise support assertion (W=1\lor W=2), it gives, for every Boolean (z,y), the following cell table:

| (z,y) | probability | conditional mean of (V) | conditional variance of (V) |
| --- | --- | --- | --- |
| (0,0) | (3/8) | (3/2) | (1/4) |
| (0,1) | (1/8) | (3/2) | (1/4) |
| (1,0) | (3/8) | (11/6) | (17/36) |
| (1,1) | (1/8) | (5/2) | (1/4) |

It next asserts (σ^2(Y)=3/16), (σ^2(Z)=1/4), (E(Y)=1/4), (E(1-Y)=3/4), the unconditional-arm contrast (E(V\mid Z=1)-E(V\mid Z=0)=1/2), and (C=1/4+(3/4)(11/6-3/2)).

For every (z,y\in\{0,1\}) and every natural (v), the joint probability (P(Z=z,Y=y,V=v)) is the following entire table, including zero outside the listed support:

| (z,y) | (v=1) | (v=2) | (v=3) |
| --- | --- | --- | --- |
| (0,0) | (3/16) | (3/16) | 0 |
| (0,1) | (1/16) | (1/16) | 0 |
| (1,0) | (1/8) | (3/16) | (1/16) |
| (1,1) | 0 | (1/16) | (1/16) |

This table is a function (M:\{0,1\}\to\{0,1\}\to\mathbb N\to\mathbb R). Then (Y=Q_0) pointwise. For every atom, if (X=1) and (Y=0), then in world 0 the atom is a reader, is not a watcher, and answers (Y=Q_0); in world 1 the atom is not a reader, is a watcher, and answers (Y\ne Q_1). For every (b), (C=P(Q_b=1)\leftrightarrow b=1), while (C=P(R_b\lor Q_b=1)) for every (b). Finally there is no function (F) from such whole observable tables to (ℝ) such that, for every (b\in\{0,1\}), (F(M)=P(Q_b=1)). The order is a negated existential (F) followed by a universal world; (F) receives the same full table in both worlds.

Junk-value audit: every population conditional probability is positive by the actual table, including (P(Y=0)=3/4) and (P(Z=z)=1/2). Thus none of the real divisions uses a zero denominator. Finite sums make all functions integrable and finite, independently of measurability notation. The law proves nonnegative masses and total one. `Fin 12`, `Fin 3`, and `Fin 2` are nonempty and bounded; their numeric constructor proofs have no default branch. `fairBit i k` uses natural quotient by (2^k>0) and remainder modulo 2; natural quotient by 4 is also intentional and nonzero. The bit definitions implement binary digits. No natural subtraction occurs. No `toReal`, square root, real power, infimum/supremum, limit, or partial-function default is used in the assertion. The unrestricted function (F) is an ordinary total function; its failure to exist follows from two different target prevalences, not any measurability issue.

Docstring reading: this is an indistinguishability/nonidentification witness for watching, with independent type, baseline, and assignment, all standing conditions for reading-or-watching, exact observables and moments, and truthful answers in A versus withholding watchers in B.

## SAP.P019b.T14

Source: `Challenge/Part1.lean:25–31`; statement `Defs/Part4.lean:30–51`.

Quantifiers, in order: every type (Ω) with a finite enumeration, every law (m_i\geq0) with total one, every (W,V:Ω\to\mathbb N), (X,Y,Z:Ω\to\{0,1\}), and every (R,Q:Ω\to\{0,1\}). Assume, in order:

1. For every atom, (Y=Q) (including zero-mass atoms).
2. For every atom, (X=R\lor Q) (including zero-mass atoms).
3. On every positive-mass atom, (V=W+XZ).
4. For every real function (f:\mathbb N\to\{0,1\}\to\{0,1\}\to\mathbb R) and each Boolean (z), (E(1_{Z=z}f(W,R,Q))=P(Z=z)E(f(W,R,Q))). This says assignment is independent of the joint ((W,R,Q)). Despite the name `tripleIndependent`, it does not require (W,R,Q) to be independent of each other.
5. (0<P(Z=1)), then (P(Z=1)<1).
6. (0<P(Q=1)), then (P(Q=1)<1).

Define (b=P(Q=1)), (a=P(R=1,Q=0)), and (L=E(V\mid Z=1)-E(V\mid Z=0)). Define (m_{zy}=E(V\mid Z=z,Y=y)), (C=E(Y)+E(1-Y)(m_{10}-m_{00})), (μ=P(X=1)), (β=m_{11}-m_{01}), and (δ=E(Y\mid Z=1)-E(Y\mid Z=0)). Then the theorem concludes all of:

- On positive-mass atoms (Y=1\Rightarrow X=1), and (V=W+XZ).
- For every real (f(W,X,Y)) and each (z), (E(1_{Z=z}f(W,X,Y))=P(Z=z)E(f(W,X,Y))).
- (m_{10}-m_{00}=E(X\mid Y=0)=a/(1-b)).
- (C=b+a), (μ=b+a), (L=b+a), and (E(Y)=b).
- (C-b=a), (L-b=a), (C=b\leftrightarrow a=0), and (L=b\leftrightarrow a=0).
- (β=1) and (δ=0).

All (E,P), conditional means and variances here are the explicit finite sums in the opening notation. There is no nondegeneracy hypothesis for conditional variances and no statistical sampling/asymptotics conclusion.

Junk-value audit: (1-b>0) by assumption. Both assignment arms and both (Y) classes have positive probability, and the independence plus (Y=Q) makes all four joint cells have positive probability. Hence no conditional denominator is zero. All real-valued observations are integrable on this finite set. Nonnegative masses summing to one exclude an empty underlying set. The counts are natural, with exact real casts, and finite (Ω) implies a finite count bound without adding one. There is no truncated subtraction, square root, `toReal`, inverse CDF, infimum/supremum, limit, or partial default. The pointwise truthful equalities are stronger than equalities almost surely, explicitly acknowledged in the docstring.

Docstring reading: a disclosed restriction to finite underlying spaces and pointwise truthful labels; it states the union identified by list/combined functionals, the reader-only excess over watching, and the two population placebo restrictions. The arbitrary-space/almost-sure version is expressly omitted.

## SAP.P019b.T15

Source: `Challenge/Part1.lean:33–37`; statement `Defs/Part4.lean:53–73`.

Write (Φ(t)=N(0,1)((-\infty,t])), and (q(u)=\inf\{x\in\mathbb R:u\leqΦ(x)\}), using Mathlib's real `sInf`. Set (S=p_1(1-p_1)+p_2(1-p_2)), (V=(p_1+p_2)(1-(p_1+p_2)/2)), and (d=|p_1-p_2|). For arbitrary real inputs, the actual definitions are

 (F(n,p_1,p_2,c)=Φ((\sqrt n\,d-c\sqrt V)/\sqrt S)),

 (O(n,p_1,p_2,c)=Φ((-\sqrt n\,d-c\sqrt V)/\sqrt S)),

 (H(n,p_1,p_2,c)=N(0,1)\{g:c\sqrt{V/n}<|d+\sqrt{S/n}\,g|\}).

These are respectively the defined favored tail, opposite tail, and a genuine two-sided Gaussian event probability, with the last probability converted from extended nonnegative reals to (ℝ). They are not definitions of a finite binomial test's exact power.

The assertion is a conjunction. Its first part quantifies, in order, every real (n,p_1,p_2,α). Hypotheses, in order, are (n>0), (p_1\geq0), (p_1\leq1), (p_2\geq0), (p_2\leq1), (S>0), (α>0), and (α<1). With (c=q(1-α/2)), it concludes:

- (c>0).
- (V-S=(p_1-p_2)^2/2) and (V-S\geq0).
- (H=F+O).
- (O=1-Φ((\sqrt n\,d+c\sqrt V)/\sqrt S)).
- (0<O\leqα/2).
- (O=α/2\leftrightarrow p_1=p_2).
- (H-F=O).

The second part has no hypotheses. At (c=q(1-(1/20)/2)), it asserts (S(1/2,1/2)=V(1/2,1/2)=1/2), (|1/2-1/2|=0), (F(50,1/2,1/2,c)=Φ(-c)=1/40), (O(50,1/2,1/2,c)=1/40), and (H(50,1/2,1/2,c)=1/20). The literal sample-size argument is 50; the docstring calls this an (N=100) example, but no (N) or relation between (N) and (n) is defined in these SAP definitions.

Junk-value audit: Gaussian probabilities are finite so `toReal` never sees infinity. Under the hypotheses (1-α/2\in(1/2,1)), so the quantile's upper-level set is nonempty and bounded below; the real infimum is the ordinary, finite normal quantile. At (u\leq0) the set would be unbounded below, and at (u\geq1) it would be empty, invoking a junk infimum convention (zero in (ℝ)); those inputs never occur. (n>0), (S>0), and (V=S+(p_1-p_2)^2/2>0) protect all divisions and square roots. At arbitrary off-hypothesis inputs the same total formulas would assign zero to nonpositive square-root inputs and division by zero, but the theorem does not use them. The fixed example also satisfies all protections. There are no Bochner means, natural casts/subtractions, empty index types, powers outside their domains, logarithms, limsup/liminf, or partial-function defaults. The probability event is Borel.

Docstring reading: a corrected two-tail normal planning calculation, a positive missing-tail error bounded by (α/2) with equality only at the null, and the specified null numerical example. It does not itself state a limit from an exact finite-sample rejection probability.

## SAP.P019b.T16

Source: `Challenge/Part1.lean:39–46`; statement `Defs/Part4.lean:75–77`.

The underlying baseline set is (w\in\mathrm{Fin}(5)=\{0,1,2,3,4\}) with probability masses

 ((81,216,216,96,16)/625).

These are Binomial(4,2/5) probabilities. The unaffected treated response is (u(w)=w+1), as a real value. The affected treated response is (a(w)=\min(w+1,4)), taking the minimum in (ℕ) and then casting to (ℝ). For a real parameter (ρ), the defined contrast is

 (B(ρ)=Σ_{w=0}^4 m_w[(1-ρ)(w+1)+ρ\min(w+1,4)]-Σ_{w=0}^4m_w w).

The theorem quantifies every real (ρ), then assumes (0\leqρ), then (ρ\leq1), and concludes (B(ρ)=1-(16/625)ρ). The weighted average has the ordinary interpretation of an independent affected-status mixture: the same baseline law appears in both affected and unaffected terms. An affected-status random variable is not separately constructed or quantified. No list experiment, direct answer, liar mechanism, false-confessor mechanism, statistic, or rejection event is in this statement. Its baseline and response functions are fixed, not universally quantified.

Junk-value audit: finite nonnegative probabilities with total one, a nonempty fixed baseline set, fixed nonzero denominator 625, total real finite sums, exact natural casts, and ordinary minimum. The subtraction (1-ρ) and subtraction of means are in (ℝ), not truncated natural subtraction. The vector literal has exactly five entries and is indexed by `Fin 5`, so there is no out-of-range default. There are no conditional divisions, square roots, Bochner integrals, `toReal`, infima/suprema, limits, logarithms, real powers, or partial-function defaults. The convex-mixture bounds keep the stated probabilistic interpretation valid; neither is an assumption of the conclusion.

Docstring reading: a disclosed restriction to this one population ceiling contrast with the fixed binomial baseline and independent mixing. It expressly omits liar/false-confessor response rules, all rejection probabilities and the numerical power examples, all finite-sample power curves, and their dependence on sample size and violation share.
