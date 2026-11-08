# Blind reading

Saved before opening `claims.json` or `record.json`. This reading uses the Challenge source, every unit declaration listed in `closure.json`, and the relevant Mathlib meanings. `scratch/Inspect.lean` also prints the generated declarations in the closure: the population and regularity constructors, `olsVariance._proof_1`, `WaldComparison._proof_1`, `HeterogeneousFinite._proof_1` through `_proof_4`, and `HeterogeneousLimit._proof_1`. The auxiliary proofs only construct numeral `AtLeastTwo` instances; they add no statistical assumptions.

## Common mathematical notation, fully expanded

The following notation abbreviates finite sums and ordinary real limits, not further SAP predicates. Each section below uses this same expansion.

A population is a tuple `(n1,n0,y1,y0)`, where `n1,n0` are natural numbers, `N=n1+n0`, and `y1,y0 : Fin N → ℝ`. Here `Fin N` is the set of natural numbers strictly less than `N`. A sequence `E : ℕ → Population` specifies a possibly different finite population at each natural index `k`.

For a finite set `s` of units and a real vector `y`, write

- `m_s(y) = (Σ_{i∈s} y_i)/|s|`;
- `Q_s(y) = Σ_{i∈s}(y_i-m_s(y))²`;
- `s_s²(y) = Q_s(y)/(|s|-1)`, where the subtraction is in ℝ;
- `m(y)=m_{Fin N}(y)` and `S²(y)=s_{Fin N}²(y)`.

The average effect is `τ=m(y1)-m(y0)`, and the unit-effect vector is `d_i=y1_i-y0_i`. The sharp-null predicate means `∀i∈Fin N, y1_i=y0_i`. The constant-effects predicate means `∀i∈Fin N, d_i=τ`.

An assignment `z` is a finite subset of `Fin N`. Its complement is relative to all of `Fin N`. The randomization support is `Ω={z⊆Fin N: |z|=n1}` (`Finset.univ.powersetCard n1`). Every assignment in `Ω` receives probability `1/|Ω|`; assignments outside it receive no mass. In particular, `|Ω|=binomial(N,n1)>0`, even when an arm is empty. Set `yobs_i(z)=y1_i` for `i∈z`, and `y0_i` otherwise. The difference-in-means estimate is `h(z)=m_z(yobs(z))-m_{zᶜ}(yobs(z))`.

For an assignment function `X`, its randomization mean is `M(X)=(Σ_{z∈Ω}X(z))/|Ω|`, its variance is `V(X)=M((X-M(X))²)`, and the probability of an assignment predicate `A` is `Pr(A)=|{z∈Ω:A(z)}|/|Ω|`. These are finite sums; no unspecified probability measure or independence premise is being inserted.

Write the following three real assignment functions:

- `O(z)=[(Q_z(yobs(z))+Q_{zᶜ}(yobs(z)))/(N-2)](1/n1+1/n0)` (pooled OLS variance);
- `D(z)=s_z²(yobs(z))/n1+s_{zᶜ}²(yobs(z))/n0` (Neyman variance estimate);
- `F(z)=N S²(yobs(z))/(n1 n0)` (Fisher variance).

All counts in these formulas are cast into ℝ before division or subtraction. At sequence index `k`, add subscripts `k` to these objects. Set `A_k=S²(y1_k)`, `B_k=S²(y0_k)`, and `C_k=S²(d_k)`.

For real parameters `(p,v1,v0,vt,t)`, the regularity hypothesis consists of **all** of:

1. `N_k→∞` as a sequence of natural numbers.
2. Eventually `n1_k≥2` and `n0_k≥2`.
3. `0<p<1`.
4. `n1_k/N_k→p` as real numbers.
5. `A_k→v1`, `B_k→v0`, `C_k→vt`, and `τ_k→t`.
6. There exists a real `b≥0` such that, for **every** natural `k`, `(Σ_{i∈Fin N_k}(y1_{k,i}⁴+y0_{k,i}⁴))/N_k≤b`.

These assumptions do not explicitly assert positive limiting variances. They do not contain any estimator consistency or central limit conclusion. Write `L_O=v1/(1-p)+v0/p` and `L_D=v1/p+v0/(1-p)`.

An expression `X_k→ᵖc` below means exactly `∀ε∈ℝ, ε>0 ⇒ Pr_k(ε<|X_k-c|)→0`. An expression `X_k=o_p(1/N_k)` means exactly `N_k X_k→ᵖ0`. Each real convergence uses `Filter.Tendsto` from the cofinite upper-tail filter `atTop` on ℕ to the usual real neighborhood filter. Thus these are row-wise probabilities for changing finite randomization spaces; no coupling across `k` is required.

## SAP.P053.T6

Source: `SAP/P053/Challenge/Part1.lean:38–45`; statement expanded from `SAP/P053/Defs/Part5.lean:30–59` and the common definitions above.

Quantifiers, in order: **for every** population sequence `E`, then **for every** real `p,v1,v0,vt,t`, **if** all six regularity conditions above hold, the following three implications hold jointly:

1. **If** `τ_k→0`, then `(F_k-O_k)=o_p(1/N_k)`. In addition, **if** `L_O>0` and **if** eventually **every** `z∈Ω_k` has `O_k(z)>0`, then `F_k/O_k→ᵖ1`. The positivity assumptions apply to this ratio, not to the preceding difference conclusion.
2. **If**, for **every** `k` and **every** unit `i`, `y1_{k,i}-y0_{k,i}=τ_k`, then `O_k-V_k(h_k)=o_p(1/N_k)` and `N_k(F_k-V_k(h_k))-τ_k²→ᵖ0`. The population parameters supplied to the named approximation predicate are unused there.
3. **If**, for **every** `k` and unit `i`, `y1_{k,i}=y0_{k,i}`, **and if** `v0>0`, **and if** eventually every supported assignment has `O_k(z)>0`, then both:
   - for **every** real `x`, `Pr_k(h_k/√O_k≤x)→Φ(x)`;
   - for **every** real `α`, **if** `0<α<1`, `Pr_k(q_α<|h_k|/√O_k)→α`.

Here `Φ(x)` is the mass of `(-∞,x]` under Mathlib's real Gaussian measure with mean zero and variance one, converted from `ENNReal` to ℝ. It is the ordinary standard normal CDF. `q_α=inf{r∈ℝ:1-α/2≤Φ(r)}`; for the stated `α` this is its upper two-sided normal critical value. Rejection uses a strict inequality. The first conclusion is CDF convergence at every real point, with no centering needed under the sharp null.

The docstring describes local variance difference/ratio limits, constant-effect approximations, and sharp-null normality/size. It expressly omits FRT/Wald equivalence under local alternatives and conditional FRT laws, quantiles, p-values, and rejection comparisons. It expressly mentions eventual assignment-wise OLS positivity. The formal statement separately requires `L_O>0` for the ratio and `v0>0` for the Wald conclusions.

Junk-value review:

- Real division by zero equals zero in Lean. Means of empty groups equal zero; singleton sample variances are `0/0=0`; an empty sample variance is `0/(-1)=0`. `N-2` can be zero at `N=2`; zero arm sizes also occur in the general `Population` type. Regularity excludes all such cases eventually, which suffices for each asymptotic conclusion. The constant-effect/sharp-null conditions are vacuous on an empty population at an early index, but no asymptotic consequence is obtained from that alone.
- `Ω_k` is always nonempty because `n1_k≤n1_k+n0_k`. Thus randomization means/probabilities never use a zero support-cardinality denominator.
- A nonempty population's sample variance is nonnegative; on the eventual domain all finite sample variance divisors and the residual divisor are positive. OLS can still be exactly zero for individual assignments. The additional eventual positivity hypothesis excludes that for ratios and studentization. Earlier values, including junk quotients, affect no limit.
- `Real.sqrt x=0` for `x≤0`. Studentization is only asserted with eventual strictly positive OLS variance. The separately imposed positive limit conditions are substantive mathematical hypotheses, not definitions of convergence.
- `Φ` uses `ENNReal.toReal`, which sends `∞` to zero, but a Gaussian probability is at most one, so that fallback cannot occur. The Gaussian variance is exactly one, so its variance-zero Dirac branch is unused.
- A real `sInf` has default values for an empty set or a set unbounded below. For `0<α<1`, the normal-CDF defining set is nonempty and bounded below, so neither convention affects this theorem. No assertion uses `q_α` outside that range.
- No natural subtraction occurs in these formulas: `|s|-1` and `N-2` are real subtractions. Natural casts are exact. There is no logarithm, real power, Bochner integral of a user function, limsup/liminf, partial-function default, or arbitrary empty-index average beyond the finite means already described.

## SAP.P053.T8

Source: `SAP/P053/Challenge/Part1.lean:52–56`; statement expanded from `SAP/P053/Defs/Part7.lean:17–58` and the common definitions above.

The statement is a conjunction. Its first conjunct quantifies **every** population sequence `E`, followed by **every** real `p,v1,v0,vt,t`; **if** all regularity conditions hold, then:

1. The deterministic sequence `N_k V_k(h_k)` tends to `L_D-vt`; `L_D-vt≤L_D`; and `N_k D_k→ᵖL_D`.
2. **If** constant effects hold at **every** index and unit, then all of the following hold jointly: for **every** `k`, `A_k=B_k` and `C_k=0`; `v1=v0` and `vt=0`; `N_k V_k(h_k)→L_D`; `L_D=L_O`; `(O_k-D_k)=o_p(1/N_k)`; and, for **every** `k`, `√A_k=√B_k` and `√C_k=0`.

The next conjunct quantifies **every** natural `k` and asserts finite formulas for one **fixed, explicitly defined** sequence. Put `m=k+1`, `n1=2m`, `n0=8m`, `N=10m`; on `Fin N`, let `y0_i=1` when `i<5m` and `-1` otherwise, and `y1_i=2y0_i`. The assertions at every `k` are exactly:

- `τ=0`;
- `B=N/(N-1)`, `A=4N/(N-1)`, and `C=N/(N-1)`;
- `V(h)=81/[4(N-1)]`;
- `A/n0+B/n1=10/(N-1)`;
- `A/n1+B/n0=85/[4(N-1)]`;
- `10/(N-1)<V(h)`.

The next conjunct asserts that this same sequence satisfies all regularity conditions with `(p,v1,v0,vt,t)=(1/5,4,1,1,0)`, that `τ_k=0` for **every** `k`, that `N_k V_k(h_k)→81/4`, that `N_k O_k→ᵖ10`, and that the numerical coefficients `L_O=10`, `L_D=85/4`, and `10<81/4` hold. The last conjunct is the numerical inequality `81/4<85/4`. The Neyman probability limit `N_kD_k→ᵖ85/4` follows by applying the first conjunct to this certified regular sequence; it is not repeated inside the named heterogeneous-limit predicate. No rejection probabilities or confidence-interval coverage probabilities occur in this declaration.

The docstring describes a variance bound, constant-effect equality/agreement, and the explicit heterogeneous zero-average-effect sequence with actual, OLS, and Neyman coefficients `81/4`, `10`, and `85/4`.

Junk-value review:

- For arbitrary regular sequences the empty-population, singleton, empty-arm, and `N=2` conventions are the same as in T6 and are excluded eventually. Every support is nonempty. Sample variance uses the real subtraction `N-1`, with the empty and singleton cases both giving zero.
- Constant-effect variance equalities and their square-root versions are also asserted at early indices; if the population is empty or a singleton, both population variances and effect variance really are zero under the finite-sum definitions. Hence the conventions do not create a contrary nonzero variance or a false equality there.
- In the specified witness `m=k+1≥1`, `N≥10`, `n1≥2`, and `n0≥8` at **every** index. Every displayed finite-formula denominator is strictly positive. The witness has no dependence on zero-denominator values and has genuinely varying unit effects (`+1` and `-1`).
- `p` and `1-p` are positive under regularity. All limits are ordinary finite real limits and probability limits; no `sInf`, `sSup`, `toReal`, log, rpow, unbounded limsup, or partial-function convention is used. `Real.sqrt` is applied only to nonnegative population variances, including legitimate zero effect variance. Natural additions, products, comparisons, and casts in the witness are exact; `N-1` is real subtraction, not truncated natural subtraction.

## SAP.P053.T7

Source: `SAP/P053/Challenge/Part1.lean:47–50`; statement expanded from `SAP/P053/Defs/Part6.lean:16–44` and the common definitions above.

Quantifiers, in order: **for every** population sequence `E`, followed by **every** real `p,σ1,σ0,vt,t`, **if** `σ1≥0`, **if** `σ0≥0`, and **if** all regularity conditions hold with `v1=σ1²` and `v0=σ0²`, the following conjunction holds. Thus the two `σ` parameters are nonnegative standard-deviation limits rather than arbitrary signed square roots.

Write `a_k=A_k/n0_k+B_k/n1_k` and `b_k=A_k/n1_k+B_k/n0_k`, with `A_k,B_k` still the actual finite-population variances. The first part asserts:

1. `D_k-b_k=o_p(1/N_k)`.
2. `O_k-D_k-(a_k-b_k)=o_p(1/N_k)`.
3. `N_kO_k→ᵖσ1²/(1-p)+σ0²/p` and `N_kD_k→ᵖσ1²/p+σ0²/(1-p)`.
4. `L_O-L_D=[(σ1²-σ0²)(2p-1)]/[p(1-p)]`.
5. **If** `L_O≠L_D`, then `σ1²≠σ0²` and `p≠1/2`.

The second part says **if** `L_O≠L_D`, then `σ1≠σ0` and `p≠1/2`. This strengthens the wording to standard deviations; it does not assert finite-sample equality when the limits agree.

The third part is conditional: **if** the deterministic sequence `τ_k→0`, then `F_k-D_k-(a_k-b_k)=o_p(1/N_k)`, `N_kF_k→ᵖL_O`, and `N_kD_k→ᵖL_D`. Both probability limits are retained in this local Fisher branch. The signed difference identity and unequal-limit necessary conditions are already unconditional conclusions about those same deterministic coefficients. All unnamed `vt` and `t` arguments of the comparison predicates are unused; their role is confined to the outer regularity assumptions.

The docstring describes Neyman/OLS expansions, their limits, the difference identity and necessary conditions, plus the local Fisher expansion and limits. There is no limiting law or rejection-probability comparison for the actual Wald test statistics in the statement.

Junk-value review:

- Sample means/variances, OLS/Neyman/Fisher estimates, and finite probabilities have the same totalized zero-denominator conventions described above. Regularity excludes empty arms, singleton arm samples, and `N≤2` eventually. Support cardinalities are always positive. Early empty populations cannot establish or destroy a tail convergence claim.
- The limits use `p` and `1-p` only with `0<p<1`, so all limiting coefficient and difference-identity denominators are nonzero. No inverse of an estimated variance occurs, so eventual positivity of every OLS assignment is not a hypothesis here.
- `σ1²` and `σ0²` use natural square powers, with the nonnegative standard deviations required explicitly. `1-p`, `2p-1`, and all count-minus-one/count-minus-two expressions are real arithmetic. No real square root, log, real power, integral, `toReal`, `sInf`/`sSup`, limsup/liminf, or default value of a partial function is used in this target's closure.
