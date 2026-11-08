# Blind reading

Saved before opening either `claims.json` or `record.json`. Sources read: both Challenge parts, Defs Parts 1–6, WholeW1, and every entry of `closure.json`. The 26 distinct generated `_proof_` dependencies were also printed and inspected in `scratch/ClosurePrint.log`. They prove numeral-instance facts, positivity/normalization of product designs and the fair coin, or nonnegativity of `c/s`; they add no assumptions to the propositions. Constructors and projections in the closure have their ordinary structure meanings.

The notation below is mathematical shorthand for the following explicit finite sums, not additional SAP assumptions. All finite sample spaces carry their discrete sigma algebra if viewed as measure spaces. A design on a finite type Ω is a function `w : Ω → ℝ` with `w(z)>0` for every z and `Σ_z w(z)=1`. Thus Ω cannot be empty. For arbitrary real functions, `E_w X=Σ_z w(z)X(z)`, `Cov_w(X,Y)=Σ_z w(z)X(z)Y(z)−(Σ_z w(z)X(z))(Σ_z w(z)Y(z))`, `Var_w X=Cov_w(X,X)`, and `Pr_w A=Σ_z (if A(z) then w(z) else 0)`. All these are finite sums of real numbers; none is a potentially undefined integral.

For the population definitions used below, the unit set is `{0,…,N−1}` and the exposure set is `{0,…,K−1}`. A population is an arbitrary exposure map `D : Ω × Fin N → Fin K` and arbitrary deterministic potential outcomes `y : Fin N × Fin K → ℝ`. Put `I_id(z)=1` when `D(z,i)=d` and zero otherwise; `p_id=Σ_z w(z)I_id(z)`; `p_ij,de=Σ_z w(z)I_id(z)I_je(z)`; and `Y_i(z)=y_i,D(z,i)`. Define `T_d=Σ_i y_id`, `μ_d=T_d/N`, `τ_de=(T_d−T_e)/N`, `H_d(z)=Σ_i I_id(z)y_id/p_id`, `M_d(z)=H_d(z)/N`, and `H_de(z)=(H_d(z)−H_e(z))/N`. SAP positivity for exposure d means `0<p_id<1` for every i, including the strict upper bound.

For complete expansion of the variance estimator appearing in T7 and T9, all sums over `i≠j` below are ordered sums. Put

```
Q_ij,de(z) = I_id(z) I_je(z)
              * (p_ij,de − p_id p_je) / p_ij,de
              * (y_id/p_id) * (y_je/p_je),
B_d(z) = Σ_i I_id(z)(1−p_id)(y_id/p_id)^2
           + Σ_{i≠j} Q_ij,dd(z),
A_d(z) = Σ_{i≠j : p_ij,dd=0}
           [I_id(z)y_id^2/(2p_id) + I_jd(z)y_jd^2/(2p_jd)],
C_de(z) = Σ_{i≠j : 0<p_ij,de} Q_ij,de(z)
           − Σ_{i,j : p_ij,de=0}
             [I_id(z)y_id^2/(2p_id) + I_je(z)y_je^2/(2p_je)],
Vhat_de(z) = [B_d(z)+A_d(z)+B_e(z)+A_e(z)−2C_de(z)]/N^2.
```

Every division here is Lean real-field division. In particular a zero-joint `Q` is zero by totalized division. With a positive finite design a zero joint probability means its indicator product is zero at every atom; this is precisely omission of an impossible observed pair. This convention needs checking against the intended estimator, rather than treating a displayed `0/0` as an ordinary quotient.

For a sequence of finite designs w_n and functions X_n, convergence in probability to a means: for every real ε>0, `Pr_{w_n}(ε<|X_n−a|)→0` as n→∞. Normal convergence with parameters μ and v≥0 means `Pr_{w_n}(X_n≤x)→CDF(N(μ,v))(x)` for every real x. Mathlib's `gaussianReal μ v` uses v as the **variance**. The normal limits used by these targets all have strictly positive variance. Write Φ for the CDF of `gaussianReal 0 1` and `q_α=inf{x∈ℝ : 1−α/2≤Φ(x)}`. Convergence and lower limits use Mathlib's `Filter.atTop` on ℕ and the ordinary real topology.

## SAP.P013a.T6

Location: `Challenge/Part1.lean:34–36`; actual proposition: `Defs/Part5.lean:171–182`. Its three conjuncts are independently universally quantified, in the following order.

1. For every natural N, every Boolean matrix h on `Fin N × Fin N`, and every pair of finite unit subsets A,B, the assertion that there do not exist i,j with `h_ij=true` and either `(i∈A,j∈B)` or `(j∈A,i∈B)` is equivalent to `∀i∈A,∀j∈B, h_ij=false ∧ h_ji=false`. The source repeats each of the two disjuncts; this has no logical effect. If h is symmetric, the same no-edge assertion is equivalent to just `∀i∈A,∀j∈B,h_ij=false`. This conjunct does not require A,B disjoint.
2. For every finite Ω, all naturals N,K, every design w, every population D,y, and every Boolean h, assume the following vector independence property: for all finite unit sets A,B, if A and B are disjoint and no directed h-edge in either direction crosses between them, then, for every pair of complete exposure patterns a,b in `Fin N → Fin K`,

   `Pr_w((∀i∈A,D_i=a_i) ∧ (∀j∈B,D_j=b_j))`
   `=Pr_w(∀i∈A,D_i=a_i) Pr_w(∀j∈B,D_j=b_j)`.

   Define the natural number `g_ij` to be 1 exactly when `i=j` or `h_ij=true` or `h_ji=true`, and 0 otherwise. Then (a) for all i,j with `g_ij=0`, for every exposure pair d,e, `p_ij,de=p_id p_je`; and (b) for every natural m, if each row of h has at most m true entries, then `Σ_iΣ_j g_ij≤N(2m+1)`, and additionally symmetry of h implies `Σ_iΣ_j g_ij≤N(m+1)`.
3. For every experiment sequence S described next, a uniform row bound on genuine (possibly directed) dependency matrices implies the pair-dependence sparsity condition. An experiment at index n consists of a natural support size s_n, a natural exposure size k_n, a positive normalized design on `Fin s_n`, and a population with N=n+1 units and k_n exposure values. The sequence additionally supplies treated/control exposures d_n,e_n that are distinct, with `0<p_i,d_n<1` and `0<p_i,e_n<1` for all n,i. The antecedent is: there exist a single natural m and Boolean matrices h_n such that, for every n, the vector independence property in item 2 holds and each row has at most m true entries. The conclusion is: there exist Boolean matrices g_n such that for every n,i,j, `g_n(i,j)=false` implies `p_ij,de=p_id p_je` for **all** d,e, and `Σ_iΣ_j 1_{g_n(i,j)=true}/(n+1)^2→0`.

The docstring calls this the corrected edge condition, both counting bounds, and the implication from Condition 5 to Condition 4. No positivity, boundedness or variance condition is required in the finite graph/counting conjuncts. Positivity and two distinct exposure labels are fields of the sequence used in the final conjunct.

Junk-value/domain audit: N=0 is permitted in the first two conjuncts; then unit sums are zero and unit assertions are vacuous, consistently with empty populations. K=0 cannot coexist with nonempty units and a design admitting an exposure map, but the empty-population special case is legitimate. Designs themselves cannot have empty support. The final ratio has `(n+1)^2>0`, so never divides by zero. Counting, m arithmetic and casts are in ℕ followed by exact casts to ℝ; there is no truncated subtraction, logarithm, square root, rpow, integral, `toReal`, infimum or supremum in this closure. The dependency property is not an assumption of the conclusion: it concerns joint vector laws, while the conclusion concerns pair probabilities and counts.

## SAP.P013a.T7

Location: `Challenge/Part1.lean:38–40`; actual proposition: `Defs/Part6.lean:14–70`. This is a conjunction of assertions about a **specified** sequence, with no free experiment hypothesis.

The fixed outcome table is defined as follows. Let `b_0=0` and `b_r=2^(2^r)` for every r≥1. For every natural i let `r(i)=min{r∈ℕ : 1≤r and i≤b_r}`. Thus for positive i, `b_{r(i)−1}<i≤b_{r(i)}`. On odd r(i), set `y_i0=y_i1=1`. On even r(i), put `t_i=i−b_{r(i)−1}−1` and alternate `(y_i0,y_i1)=(0,2)` when t_i is even and `(2,0)` when it is odd. Write `σ_i=1` when t_i is even, and −1 otherwise. The first block has four units, all with both outcomes 1.

For each natural N, the sample space is the functions `z : Fin N → Fin 2`. Each has weight `∏_{i<N}(1/2)`; these are independent fair exposure assignments. Unit i uses coordinate z_i as its exposure and uses the fixed table at positive label i+1 as its potential outcomes. Let B_N be the set of i<N for which r(i+1) is even, and let a_N=|B_N|. All occurrences of τ,H,Vhat below are the explicit finite sums above with d=1,e=0. Write `R(z_i)=2(z_i.val)−1`, so its values are −1,+1.

The finite conjunct is: for **every** natural N and proof N≥1,

- for all units/exposures, `p_id=1/2` and `|y_id|≤2`;
- for all distinct i,j and every d,e, `p_ij,de=1/4`;
- the graph `h_ij=1_{i=j}` has the full vector independence property stated in T6 and every row has at most one true entry;
- `|τ_10|≤2/N`;
- for every z, `H_10(z)−τ_10=(2/N)Σ_i R(z_i)`;
- `Var H_10=4/N`;
- for every z, `Vhat_10(z)=(4/N^2)Σ_i Y_i(z)^2` and
  `N Vhat_10(z)=4+4a_N/N+(8/N)Σ_{i∈B_N}σ_{i+1}R(z_i)`;
- `E(N Vhat_10)=4+4a_N/N`, `Var(N Vhat_10)=64a_N/N^2≤64/N`.

A separate conjunct says `Vhat_10(z)>0` for every N≥1 and every assignment z.

For every r≥1, if r is odd then `0≤a_{b_r}/b_r≤b_{r−1}/b_r`; if r is even then `0≤1−a_{b_r}/b_r≤b_{r−1}/b_r`. For r≥2 the last upper bound equals `1/2^(2^(r−1))`.

For the full sequence N=n+1 define w_n to be its product design, `V_n=Var H_10`, `W_n=N Vhat_10`, and `T_n=(H_10−τ_10)/sqrt(Vhat_10)`. The last conjunct asserts all of the following together:

- for every n, `N V_n=4≤E W_n`;
- `Var W_n→0`;
- `(H_10−τ_10)/sqrt(V_n)` converges to N(0,1) in the CDF sense;
- there is no real s with `W_n→s` in probability;
- there is no real s with `sqrt(V_n/Vhat_10)→s` in probability;
- there is no measure μ on ℝ with `IsProbabilityMeasure μ` such that `Pr(T_n≤x)→CDF(μ)(x)` at **every continuity point** of CDF(μ).

Along the odd block endpoints `N=b_{2n+1}`, the limits of W and `sqrt(V/Vhat)` in probability are 4 and 1, and T converges to N(0,1). Along the even endpoints `N=b_{2n+2}`, the corresponding limits are 8, `1/sqrt(2)`, and N(0,1/2). Quantification over the subsequence index n is again n∈ℕ beginning at zero. The assertion uses the two actual subsequences rather than assuming a nonconvergent expectation as a hypothesis.

The docstring describes a fixed block family with a concentrating scaled estimate, two subsequential limits, and no limiting ratio or studentized distribution. The asserted concentration is supported by the explicit variance tending to zero; the statement does not assert concentration about a single constant.

Junk-value/domain audit: `blockIndex` uses a natural `sInf`, which would default to zero for an empty set, but its defining set is nonempty for every finite i because the block endpoints are unbounded. All uses of the outcome table/sign in this theorem have i≥1. Then r(i)≥1 and the truncated natural subtractions `r(i)−1` and `i−b_{r(i)−1}−1` agree with ordinary nonnegative integer subtraction. At i=0 the auxiliary definitions still have total values, but the population never uses that label. The endpoint subtraction r−1 occurs only under r≥1, and the exact ratio identity only under r≥2. All N denominators have N≥1; endpoint sizes are positive. The separate pointwise positivity conjunct removes both division-by-zero and nonpositive-square-root conventions from studentization and ratios. The normal limits have positive variances 1 and 1/2. Finite probability and variance sums have no non-integrability defaults. There is no logarithm, real rpow, `toReal`, unbounded real `limsup`/`liminf`, or partial function in this target's actual statement. Numerals such as 1 in `Fin 2` have their intended values; the printed auxiliary instances include `NeZero 2`.

## SAP.P013a.T8

Location: `Challenge/Part2.lean:7–13`; actual proposition: `Defs/WholeW1.lean:89–119` (the older `T8Statement` in Part6 is not this target).

Quantifier order: universally choose a sequence of finite types L_n, their finite-type instances, designs w_n, real statistics `estimate_n,Vhat_n : L_n→ℝ`, and real sequences `target_n,V_n`. Assume for every n that `V_n=Var_{w_n}(estimate_n)>0`. Next universally choose real c>0 and assume:

1. `(n+1)V_n→c`;
2. `(estimate_n−target_n)/sqrt(V_n)` converges to N(0,1) in the all-real-threshold CDF sense;
3. for every n, `(n+1)V_n≤E_{w_n}[(n+1)Vhat_n]`;
4. `Var_{w_n}((n+1)Vhat_n)→0`.

Set `W_n=(n+1)Vhat_n` and `v_n=(n+1)V_n`. The conclusion is the conjunction of:

- `W_n−E W_n→0` in probability;
- for every real ε with 0<ε<1, for every n,
  `Pr(W_n<(1−ε)v_n)≤Var(W_n)/(ε^2 v_n^2)`, and these lower-tail probabilities tend to zero;
- for every real α with 0<α<1, and then every real ε with 0<ε<1,
  `2Φ(q_α sqrt(1−ε))−1≤liminf_n C_n(α)`, and also `1−α≤liminf_n C_n(α)`,
  where `C_n(α)=Pr(Vhat_n≥0 and |estimate_n−target_n|≤q_α sqrt(Vhat_n))`;
- for every real s with c≤s, **if** `E W_n→s`, then all of the following hold: `W_n→s` in probability; `Pr(Vhat_n≤0)→0`; the function equal to `sqrt(V_n/Vhat_n)` when Vhat_n>0 and zero otherwise converges in probability to `sqrt(c/s)`; `0<sqrt(c/s)≤1`; and the function equal to `(estimate_n−target_n)/sqrt(Vhat_n)` when Vhat_n>0 and zero otherwise converges to N(0,c/s).

There is no pointwise nonnegativity or positivity hypothesis on Vhat, no unbiasedness hypothesis on estimate, and no unconditional finite-expectation-limit hypothesis. The nonpositive-estimate event limit is explicitly included in the final, finite-s conditional branch. The earlier centered and coverage conclusions apply without that branch.

The docstring describes centered concentration, a finite lower-tail inequality, both coverage lower limits, and the finite-expectation-limit conclusions, with a zero extension of the ratio and statistic. The extension is exactly the pair of conditional definitions in WholeW1:76–81.

Junk-value/domain audit: all E/Var/Pr are the finite real sums at the start of this file, so they exist without integrability side conditions. Every `v_n` is positive; the Chebyshev denominator has ε>0. `sqrt(V_n)` has positive argument, and the coverage event explicitly requires Vhat_n≥0. Each quotient involving Vhat in the final branch is guarded by Vhat_n>0, and the other branch is explicitly zero; these are declared extensions rather than accidental use of real division at zero. Since s≥c>0, `c/s>0`, so its square root and the limiting Gaussian variance are nondegenerate. `sqrt(1−ε)` has positive argument. In every quantile use, 0<α<1 gives a nonempty, lower-bounded set `{x:1−α/2≤Φ(x)}` and a finite positive infimum. Outside that domain this real `sInf` could use the conditionally complete order's fallback value, but no such α occurs here. Coverage probabilities lie in [0,1], so their real `liminf` is bounded and genuine. There is no logarithm, rpow, truncated subtraction, infinite-measure conversion, or partial function.

## SAP.P013a.T9

Location: `Challenge/Part2.lean:15–21`; actual proposition: `Defs/WholeW1.lean:146–159`. There are four independently universally quantified conjuncts.

1. For every experiment sequence S, assume (a) every exposure d at every n has `0<p_id<1` for every unit, (b) there are real constants c1≥0,c2>0 such that for every n,i,d, `|y_id|≤c1` and `|1/p_id|≤c2`, and (c) there exist Boolean matrices g_n with `g_n(i,j)=false` implying `p_ij,de=p_id p_je` for every d,e, and `Σ_iΣ_j 1_{g_n(i,j)=true}/(n+1)^2→0`. Then, jointly, `M_d−μ_d→0`, `M_e−μ_e→0`, and `H_de−τ_de→0` in probability, where the treated d=d_n and control e=e_n may be supplied separately at every n. S has exactly the experiment data and positivity/distinctness fields described in T6. Unit count is always N=n+1. No stability of outcomes between different n is required by the elaborated statement.
2. For every experiment sequence S, assume comparison boundedness (there are c1≥0,c2>0 bounding the absolute outcomes and reciprocal probabilities for just d_n,e_n at every n,i), genuine symmetric bounded-degree dependence (there exist a single natural m and h_n such that h_n is symmetric, the full disjoint-set vector independence property stated in T6 holds, and every row contains at most m true entries), positive limiting scaled variance (`N Var(H_de)→c` for some real c>0), and the additional lower-tail condition

   `∀δ>0, Pr(N Vhat_de < N Var(H_de)−δ)→0`.

   Then for every 0<α<1,
   `1−α≤liminf_n Pr(Vhat_de≥0 and |H_de−τ_de|≤q_α sqrt(Vhat_de))`.

   In this formula Vhat is exactly the expanded B,A,C expression given above. This conjunct does not require the all-exposure boundedness of item 1, and the quantifiers do not share S between conjuncts.
3. For every four real numbers a,t,V,Vhat, first assume V>0 and then Vhat>0. The exact identity is
   `(a−t)/sqrt(Vhat)=((a−t)/sqrt(V))*sqrt(V/Vhat)`.
4. For every finite Ω, all naturals N,K, every design w and population F, assume N>0; choose d with `0<p_id<1` for every unit; choose a natural R≥1; choose a real p0 which is an **attained** minimum of the p_id. Generate R assignments independently with weights `∏_{r<R}w(z_r)`, and independently generate the realized assignment z with weight w(z). Let `C_i=Σ_{r<R}I_id(z_r)`, `pHat_i=(C_i+1)/(R+1)`, and `Hhat=Σ_i I_id(z)Y_i(z)/pHat_i`. Let `E=Σ_{z,zs} w(z)(∏_r w(z_r))Hhat(z,zs)`, `T=Σ_i y_id`, and `κ=(Σ_i |y_id|)/|T|`. Then

   - `E=Σ_i y_id[1−(1−p_id)^(R+1)]=T−Σ_i y_id(1−p_id)^(R+1)`;
   - `|E−T|≤(1−p0)^(R+1)Σ_i|y_id|`;
   - **if** T≠0, then `κ≥1` and `|(E−T)/T|≤κ(1−p0)^(R+1)`;
   - within that T≠0 branch, if all y_id are nonnegative or all are nonpositive, then κ=1, the factor-free relative bound holds, and for every b>0 the inequality `R≥log(b)/log(1−p0)−1` implies `|(E−T)/T|≤b`;
   - still within the T≠0 branch but without the sign restriction, for every b>0, `R≥log(b/κ)/log(1−p0)−1` implies `|(E−T)/T|≤b`.

There is no numerical replicate threshold in this target, and the simulation statement concerns the fixed **population total**, not a random realized estimate. Independence of the simulations from one another and the realized experiment is encoded by the full product weights, not left implicit. The docstring describes all four corrected-target components, including the contrast as the center of coverage.

Junk-value/domain audit: N=n+1 in sequence statements and N>0 in simulation prevent division by zero in means or contrasts. Comparison positivity is supplied by S even where all-exposure positivity is not separately assumed. Zero joints in the expanded pair expression are omitted by totalized division as explained above; impossible pairs have zero indicator products, while corrections explicitly sum the zero-joint cases. Ordered sums and the full i,j range in the negative part of C include the same-unit missing cross-exposure cases. Empty sample spaces are incompatible with Design, and nonempty units/exposure maps plus S's distinct labels exclude empty exposure types. The all-exposure reciprocal bounds are not made spuriously true by `1/0=0` because positivity is explicit. Each simulated pHat_i is strictly positive since C_i≥0 and R+1>0; the product law supplies actual independent draws. The attained minimum and positivity give 0<p0<1, hence 0<1−p0<1 and log(1−p0)<0, never zero. κ is defined as zero when T=0 by real division, but every assertion using its relative-bias meaning is conditional on T≠0. In that branch κ≥1, and b/κ>0; all logarithms have positive arguments. Square roots in the algebraic identity have positive arguments; coverage includes its nonnegativity guard. Gaussian quantiles and probability `liminf` have the same nonempty/bounded safeguards as T8. There is no real rpow, `toReal`, unbounded lower limit, or partial function.

## SAP.P013a.T10

Location: `Challenge/Part2.lean:23–25`; actual proposition: `Defs/Part6.lean:114–122`. For real x,p, the rounding predicate means the **closed** interval `p−1/2000≤x≤p+1/2000`, i.e. absolute error at most 0.0005.

The statement is a conjunction of four universal assertions:

1. For every real center e, scale s and multiplier z, `(e−zs)+(e+zs)=2e`.
2. For every real e,L,U, it is impossible simultaneously that `e∈[0.2945,0.2955]`, `L∈[0.0495,0.0505]`, `U∈[0.5355,0.5365]`, and `L+U=2e`.
3. For every real e,L,U, it is impossible simultaneously that `e∈[0.3055,0.3065]`, `L∈[0.2115,0.2125]`, `U∈[0.4035,0.4045]`, and `L+U=2e`.
4. For every real e,s,z, both corresponding three-bin conjunctions are impossible with L=e−zs and U=e+zs. There are no sign, confidence-level or normality hypotheses on s,z, so this includes every symmetric interval.

The docstring says the two printed WLS triples are incompatible with symmetric intervals even under permissive three-decimal rounding. The two exact triples specified are `(0.295,0.050,0.536)` and `(0.306,0.212,0.404)`. The theorem does not reconstruct a particular regression, standard error, corrected estimate or corrected endpoints, and does not rule out asymmetric intervals.

Junk-value/domain audit: all fractions are real rational constants with positive denominators 1000 or 2000. `e−zs` and all bin endpoints use real subtraction, not truncated natural subtraction. The auxiliary dependencies are only numeral-instance proofs, including the shared numeral-2 auxiliary from T7; they introduce no statistical assumptions. There are no finite index types, sample spaces, probability quantities, division by a variable, roots, logarithms, rpow, integrals, limits, infima/suprema or partial functions. Each individual three-bin antecedent is inhabited (take its displayed values); only its conjunction with symmetry is excluded.
