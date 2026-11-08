# Blind reading

This file was written before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. Source references are to the current numbered Lean files. I read every declaration listed in `closure.json`, including the generated declarations printed in `scratch/Blind.lean`.

## SAP.P001d.T58

The theorem asserts the conjunction `T58WholeStatement` (Challenge/Part1.lean:11–19; Defs/WholeW2.lean:109–136). There are no external hypotheses.

Write

* `K(t)=1` if `|t|≤1`, `K(t)=-1/2` if `1<|t|≤2`, and `K(t)=0` otherwise.
* For a natural number `n`, data `x : Fin n → ℝ`, and real bandwidth `h`, write `d(K,h,x,u)=(1/n)∑ᵢ K((u-xᵢ)/h)/h` and `H(K,h,x,t)=∫_{(-∞,t]}d(K,h,x,u)du`, where the integral is the Mathlib real Bochner integral with respect to Lebesgue measure.
* A real function `G` is a CDF here precisely when: for every real `t`, `0≤G(t)≤1`; it is nondecreasing; at every `t` its limit from `[t,∞)` is `G(t)`; and its limits at minus and plus infinity are respectively 0 and 1.
* `p(t)=max(0,4-16|t-3/2|)` and `P(A)=∫⁻_A ENNReal.ofReal(p(t))dt`. The real CDF of a real random variable `Y` on a measure space `(Ω,μ)` is `t↦(μ{ω:Y(ω)≤t}).toReal`; the real probability of an arbitrary set is similarly its measure followed by `toReal`.

The conjuncts, in order, are:

1. `K(t)=K(-t)` for every real `t`, `K` is Lebesgue integrable, and `∫K=1`. For every real `a`, the one-point, bandwidth-one density is `K(u-a)` for every real `u`, and `H(K,1,(a),a-1)=-1/2`.
2. For every real `a`, `H(K,1,(a),·)` is strictly decreasing on `(a-2,a-1)` and fails the above CDF predicate.
3. `p` is continuous and everywhere nonnegative; for every real `t`, `p(t)=0` iff `t∉(5/4,7/4)`; `p` is Lebesgue integrable with integral 1; `P` is a probability measure; its identity-variable CDF is a CDF in the above sense and is zero at 0.
4. For every natural `n>0` and every real `n`-tuple `x`, if all `xᵢ∈[5/4,7/4]`, then `H(K,1,x,0)=(1/n)∑ᵢ(xᵢ-2)/2∈[-3/8,-1/8]`.
5. For every type `Ω` with a measurable space, probability measure `μ`, and sequence `X : ℕ → Ω → ℝ`, if all `Xᵢ` are measurable, the entire sequence is mutually independent (`iIndepFun`), all its coordinates have the same distribution as `X₀`, and `μ.map X₀=P`, then for `μ`-almost every `ω`, simultaneously for every natural `n>0`, the preceding interval bound holds for `(X₀(ω),…,X_{n-1}(ω))`; its integrated density is not a CDF; and no real `r` satisfies `r²=H(K,1,x,0)`.

The docstring calls this a refutation of a printed claim and describes the functional `G↦sqrt(G(0))` on the CDF domain. The actual statement does not quantify over functionals or mention `wholeSqrtFunctional`; the CDF-domain failure and the absence of any real square root are asserted explicitly.

Junk conventions: real division by 0 would return 0, and a zero-length density would be identically 0, but every density here uses `n=1` or an explicit `n>0`, and `h=1`. Bochner integrals are 0 for non-integrable or insufficiently measurable functions, but the displayed signed kernel and triangular density are explicitly integrable; their finitely many translates and positive scalings are integrable, so the set integrals have their ordinary meanings. `ENNReal.ofReal` clips negative values to 0, but `p` is nonnegative. `toReal(∞)=0`, but all set measures in the statement are bounded by probability-measure mass 1. Types `Fin 1` and `Fin n` for `n>0` are nonempty; the probability hypotheses prevent an empty sample space. Casts `ℕ→ℝ` are exact. There is no real logarithm, square-root operation, real power, truncated subtraction, partial-function default, `sInf`, `sSup`, `limsup`, or `liminf` in this statement's closure. The no-square-root clause uses a natural square, not Lean's totalized `Real.sqrt`.

## SAP.P001d.T59

The theorem asserts `T59Statement` (Challenge/Part1.lean:21–23; Defs/Part1.lean:95–102). Its quantifiers, in order, are: every natural `n`, assuming `n>0`; every real data tuple `X : Fin n → ℝ`; every real function `K`; assuming `K≥0` Lebesgue-almost everywhere, `∫_ℝ K(t)dt=1`, and `K(t)=K(-t)` for every real `t`; every real `h`, assuming `h>0`.

With `d(u)=(1/n)∑ᵢ K((u-Xᵢ)/h)/h` and `H(x)=∫_{(-∞,x]}d(u)du`, the conclusion is the conjunction: `d≥0` Lebesgue-almost everywhere; `∫d=1`; `H` is nondecreasing; `H` is continuous on the real line; `H(x)→0` as `x→-∞`; and `H(x)→1` as `x→+∞`. Thus the claimed CDF is continuous, and its values lie in `[0,1]` as a consequence of monotonicity and the two endpoint limits. No population distribution or random sampling hypothesis is present or needed for this deterministic assertion.

Junk conventions: although `K` has no separate `Integrable` hypothesis, the real Bochner equality `∫K=1` rules out its non-integrable default 0, so it implies integrability, including almost-everywhere strong measurability. Positive `h` and nonzero `n` rule out zero division; finite positive scalings and translations preserve integrability of the density and its half-line restrictions. `n` is cast exactly into `ℝ`. Empty data and empty finite sums are excluded by `n>0`. Almost-everywhere nonnegativity permits exceptional negative point values; these have no effect on the measure density or its integrals. There is no `toReal`, logarithm, root, real power, truncated subtraction, `sInf`/`sSup`, `limsup`/`liminf`, or partial-function default in the closure.

## SAP.P001d.T60

The theorem asserts `T60Statement` (Challenge/Part1.lean:25–27; Defs/Part1.lean:104–110). For every natural `n>0`, every real tuple `X : Fin n → ℝ`, and every real bandwidth `h>0`, it gives two conjuncts:

1. For every real function `K`, if `K` is Lebesgue integrable, then for every real `x`,
   `∫_{(-∞,x]}[(1/n)∑ᵢ K((u-Xᵢ)/h)/h]du = (1/n)∑ᵢ∫_{(-∞,(x-Xᵢ)/h]}K(t)dt`.
   No positivity, normalization, or symmetry is required of `K` in this part.
2. For every real `x`, if `Xᵢ≠x-h` for every index, then the density using `R(t)=1/2` for `|t|≤1` and 0 otherwise is
   `d(R,h,X,x)=[Fₙ(x+h)-Fₙ(x-h)]/(2h)`, where `Fₙ(y)=(1/n)∑ᵢ 1_{Xᵢ≤y}`. The excluded lower endpoint is needed because the rectangular kernel includes both endpoints whereas this CDF difference includes `x+h` and excludes `x-h`.

Junk conventions: `n>0`, `h>0` ensure every denominator is nonzero; `n` is an exact natural-to-real cast. Integrability of `K` makes the Bochner integrals ordinary integrals, including after affine changes of variable and restriction. All finite index sets used are nonempty. The conditionals in `R` and `Fₙ` are total case distinctions, not partial functions. No probability `toReal`, roots, logarithms, real powers, truncated subtraction, extrema, or sequence upper/lower limits occur.

## SAP.P001d.T61

The theorem asserts `T61WholeStatement` (Challenge/Part1.lean:29–39; Defs/WholeW2.lean:138–183), with no external hypotheses. The following are its fully unfolded objects.

For `a<b`, let `U[a,b]` be the measure with Lebesgue density `1/(b-a)` on the closed interval `[a,b]`, zero elsewhere. Define the real probability measure
`P=(1/2)U[-1,1]+(1/4)(u↦2^(1/u²))_*U[0,1]+(1/4)(u↦-2^(1/u²))_*U[0,1]`.
Powers with real exponent mean Mathlib's real power, with positive base 2. Write `F(t)=P((-∞,t])` in real units.

For a real tuple `x : Fin n → ℝ`, sort its entries in nondecreasing order. `Mₙ(x)` is its zero-based entry `n/2` (upper middle entry at an even positive size). `Lₙ(x)` is its zero-based entry `(n-1)/2` (lower middle entry at an even positive size). Both sorting definitions return 0 if the requested index is absent. Write `Eₓ(t)=#{i:xᵢ≤t}/n` and `aₓ=Eₓ(0)`. Define the total real functional
`T₀(G)=G(0)-1/2` if `G(0)∈[1/4,3/4]`, and otherwise `inf{t:1/2≤G(t)}`.
The odd-size auxiliary statistic `Sₙ(x)` equals `aₓ-1/2` when `aₓ∈[1/4,3/4]` and otherwise `Mₙ(x)`. The all-size statistic is `Qₙ(x)=T₀(Eₓ)`.

For any real statistic `A` on tuples of size `n`, the conditional bootstrap uses every label map `b:Fin n→Fin n` with weight `n^(-n)`. Thus each of the `n` resampled labels is independently uniform. Its mean is `m_A(x)=n^(-n)∑_b A(x∘b)` and variance is `v_A(x)=n^(-n)∑_b[A(x∘b)-m_A(x)]²`. For a real test function `f`, its centered, scaled test average is `B_{A,x}(f)=n^(-n)∑_b f(sqrt(n)[A(x∘b)-A(x)])`.

For a probability measure `μ`, convergence in probability of real random variables `Yₖ` to `c` means: for every real `ε>0`, `μ{ω:ε≤|Yₖ(ω)-c|}→0`. Distributional convergence `Yₖ⇒ν` means convergence of their real CDF values at every continuity point of the real CDF of `ν`. Conditional bootstrap convergence to `ν` along sizes `s(k)` means: for every continuous bounded `f:ℝ→ℝ`, `B_{A,(X₀,…,X_{s(k)-1})}(f)` converges in `μ`-probability to `∫f dν`. Here `N(0,v)` denotes Mathlib's `gaussianReal 0 v`, whose second parameter is variance, not standard deviation.

The theorem is the following ordered conjunction:

1. `P` is a probability measure and `F` is a CDF (bounds, monotonicity, right continuity, endpoint limits as defined for T58).
2. For every real `x≥2`, `P([x,∞))=1/[4 sqrt(log(x)/log(2))]`.
3. For every `|x|≤1`, `F(x)=1/2+x/4`. Moreover `F(0)=1/2`, `F(x)<1/2` for every `x<0`, and `F(x)>1/2` for every `x>0`.
4. For every natural `j>0`, `P([2^(j²),∞))=1/(4j)`.
5. `T₀(F)=0`. For every real function `G` satisfying `|G(x)-F(x)|<1/4` at every real `x`, `T₀(G)-T₀(F)=G(0)-F(0)`.
6. The derivative assertion quantifies first over every real function `h` with bounded absolute range, then over every positive real sequence `tₖ→0` and every sequence of real functions `vₖ` whose individual absolute ranges are bounded. If `vₖ→h` uniformly on all of `ℝ`, then `[T₀(F+tₖvₖ)-T₀(F)]/tₖ→h(0)`. Directions need not be CDFs, continuous, or supported on any special set. This is an explicit sequential Hadamard derivative for the local extension to all bounded directions.
7. For every natural `n>0` and real tuple `x`, `Eₓ` is a CDF; `{t:1/2≤Eₓ(t)}` is nonempty and bounded below; its real infimum is `Lₙ(x)`; and if `n` is odd then `Qₙ(x)=Sₙ(x)`.
8. For every `n>0` and real `c`, `Qₙ(c,…,c)=c`.
9. For every `n>0`, tuple `x`, and label `i:Fin n`, the constant-label resample has statistic `xᵢ` and the exact probability of that label map is `(1/n)^n`.
10. For every measurable space `Ω`, probability measure `μ`, and real sequence `Xᵢ`, if all coordinates are measurable, mutually independent, identically distributed, and have common law `P`, all of the following hold:
    * `T61Statement Ω` holds. This nested proposition itself re-quantifies over **all** probability measures and IID real sequences on that same measurable space `Ω` with common law `P`. For each such sequence, along odd sizes `r(k)=2k+1`, `sqrt(r(k)) M_{r(k)}⇒N(0,4)`, its centered conditional bootstrap has the same limit, for every odd `n≥5` the probability of `n v_M>5` is at least `3/16`, and `r(k)v_M` does not converge in probability to 4. Additionally the local affine identity in item 5 holds; `sqrt(r(k))S_{r(k)}⇒N(0,1/4)`; the same lower bound holds for `n v_S` at every odd `n≥5`; and `r(k)v_S` does not converge in probability to `1/4`. This auxiliary proposition does not assert conditional weak convergence for `S`.
    * Along **all** positive sizes `r(k)=k+1`, `sqrt(r(k))Q_{r(k)}⇒N(0,1/4)` and its centered conditional bootstrap converges in probability to the same Gaussian law.
    * At every odd `n≥5`, `μ{n v_Q>5}≥3/16`, and along all positive sizes `r(k)v_Q` does not converge in probability to `1/4`.

Junk conventions: `U[a,b]` is meaningful as a uniform probability law only when `a<b`; every use has endpoints `(-1,1)` or `(0,1)`. `ofReal` then clips no negative density. In the heavy tail, `1/0²=0` in `ℝ`, so at `u=0` the tail map returns `2^0=1`, rather than infinity. This endpoint is Lebesgue-null and its arbitrary finite value does not change the pushforward law. The base 2 of every real power is strictly positive; no negative-base or `0^0` real-power convention affects those maps. In the survival identity `x≥2` ensures both logarithms are defined in their usual positive-domain sense, `log(2)>0`, their quotient is positive, and the square root and denominator are positive. Although `Real.log(0)=0` and `Real.log` uses `log|x|` at negative inputs, these extensions are not used. `Real.sqrt` returns 0 on negative inputs, but every other square root is of a nonnegative natural size. Natural squares and all casts are exact.

The general total functional can use `sInf` on an empty or unbounded-below set, where the real conditionally complete lattice does not give a mathematical quantile (in particular `sInf ∅=0`). In the theorem, proper CDFs have a nonempty, bounded-below half-quantile set; empirical CDFs have these properties asserted explicitly. Arbitrary nearby functions use the linear branch, and the derivative's perturbations eventually use that branch; any initial values of the total extension are irrelevant to the limit. There is thus no reliance on a junk quantile for a CDF or in the local derivative. At size 0, `Eₓ=0`, the median uses its default 0, and the bootstrap normalization would use `0^0=1`; all meaningful uses have positive size. `n-1` in the lower median is truncated natural subtraction, but `n>0` makes it the usual subtraction and both requested order-statistic indices lie in range. The finite label law has `n^n>0` entries, and all conditional moments are finite sums of finite real numbers. Its constant maps are individual possible outcomes of independent resampling, not an imposed dependence among the draws. Every measure converted using `toReal` is a probability measure, including Gaussian limits, so infinity is excluded. Bounded continuous Gaussian test functions are integrable. No `limsup` or `liminf` is used here.

## SAP.P001d.T62

The theorem asserts `T62WholeStatement` (Challenge/Part1.lean:41–51; Defs/WholeW2.lean:185–239). First quantify over every type `Ω`, its measurable space, and every probability measure `μ`. For each such choice there are four conjuncts.

The definitions of IID, `cdf`, real probabilities, convergence in probability, distributional convergence, first `n` observations, exact finite bootstrap mean/variance and bounded-continuous-test conditional weak convergence are as unfolded in T61: in particular, IID includes mutual independence of all coordinates, and the resampling law independently chooses all labels uniformly from the observed tuple.

1. For every sequence `X:ℕ→Ω→ℝ` satisfying IID and every size-indexed real statistic `T : {n:ℕ}→(Fin n→ℝ)→ℝ`, assume that for every natural `k` and every label map `b:Fin(k+1)→Fin(k+1)`, the function `ω↦T((X₀(ω),…,X_k(ω))∘b)` is measurable. This includes the unresampled statistic by taking `b=id`; it does not require global Borel measurability of `T` on every possible tuple. Next quantify over real `θ,φ`, with `φ>0`. Assume the marginal distributional limit `sqrt(k+1)[T(X₀,…,X_k)-θ]⇒N(0,φ²)` and conditional bootstrap weak convergence to `N(0,φ²)` along all positive sizes. Then the following are equivalent:
   * For every real `ε>0`, as the **real** cutoff `K→+∞`,
     `limsup_{k→∞} μ{ω: ε < E_*[Z_{k,ω}² 1_{|Z_{k,ω}|>K}]} → 0`,
     where `Z_{k,ω}=sqrt(k+1)[T(x∘b)-T(x)]`, `x=(X₀(ω),…,X_k(ω))`, and `E_*` is exactly the finite average over all `(k+1)^(k+1)` label maps.
   * `(k+1)v_T(X₀,…,X_k)→φ²` in `μ`-probability.
   Additionally, if the latter variance convergence holds, `sqrt(k+1)sqrt(v_T(X₀,…,X_k))→φ` in `μ`-probability.
2. For every natural `n>0` and real tuple `x`, with `bar x=(1/n)∑ᵢxᵢ`, the exact finite-bootstrap identity is `n v_mean(x)=(1/n)∑ᵢxᵢ²-(bar x)²`.
3. For every real IID sequence `X`, if `X₀` is in Mathlib `L²(μ)` (`MemLp (X 0) 2 μ`) and `Var_μ(X₀)>0`, then `(k+1)v_mean(X₀,…,X_k)→Var_μ(X₀)` and `sqrt(k+1)sqrt(v_mean)→sqrt(Var_μ(X₀))` in probability. Here Mathlib variance is the extended integral `∫⁻|X₀-E[X₀]|²dμ` followed by `toReal`; under `L²` on a probability space this is the usual finite real variance.
4. For every real IID sequence `X`, every real `m`, real function `f`, and real `δ>0`, assume its common distribution restricted to the open metric ball `(m-δ,m+δ)` equals Lebesgue measure there with density `ENNReal.ofReal(f)`; `f≥0` at every point of that ball; `f` is almost-everywhere measurable for restricted Lebesgue measure; `f` is continuous at `m`; and `f(m)>0`. Also assume `F(m)=1/2`, `F(x)<1/2` for all `x<m`, and `F(x)>1/2` for all `x>m`, where `F(x)=μ{X₀≤x}`. For every real `η>0`, if `E|X₀|^η<∞` (expressed as integrability of that real function), then `(k+1)v_M(X₀,…,X_k)→1/[4f(m)²]` and `sqrt(k+1)sqrt(v_M)→1/[2f(m)]` in probability, along **all** positive sizes. The order statistic `M` is the upper middle one at even sizes, defined by sorting as in T61.

Junk conventions: all sample sizes are `k+1` or explicitly positive `n`; all casts to `ℝ` are exact, all bootstrap and mean denominators are positive, and finite label sums have no infinite conditional moments. The branch expression `if K<|z| then z² else 0` is a strict tail cutoff with real `K`; negative cutoffs are allowed for initial values but the limit is at `+∞`. `Filter.limsup` on `ℝ` is the infimum of eventual upper bounds; all the values whose upper limits are taken are real probabilities in `[0,1]`, so the eventual-upper-bound set is nonempty and bounded below. No junk upper limit of an unbounded sequence is involved. These probability values cannot invoke `toReal(∞)=0`, because `μ` has total mass 1. Measurability of every finite resampled statistic makes the tail events and finite averages measurable. Bounded continuous Gaussian test functions are integrable, so their Bochner expectations do not use default 0. The `L²` assumption in the mean clause rules out both a non-integrable expectation and an infinite variance becoming 0 through `toReal`. Real square roots have nonnegative arguments: positive sizes, finite averages of squared differences, and a finite nonnegative population variance. The positive density value ensures nonzero denominators in the median constants. The moment power `|X₀|^η` has nonnegative base and `η>0`; at base 0 it is 0 in the usual sense. The density `ofReal` clips no negative values on its restricted domain. The median's default 0 can only occur at size 0, which is excluded. There is no quantile `sInf`, truncated natural subtraction, logarithm, `sSup`, or `liminf` in this statement's closure.

## Generated dependencies

All line-0 declarations in the closure were printed, as was `instDecidable_sAP_1`. They supply only decidability, numeral `AtLeastTwo` proofs, the measure outer-measure class, the ENNReal scalar-tower instance, and the elementary proof `∀φ,0≤φ²` used to package Gaussian variance as a nonnegative real. In particular `T73WholeStatement._proof_2`, despite its name, is only the numeral proof `(4+1).AtLeastTwo`; it imports no assertion about T73 into these statements. None introduces a hidden mathematical hypothesis or encodes a conclusion.

## Post-save technical clarification

After saving the blind reading, I also checked Mathlib's exact `Measure.map` default in `MeasureTheory/Measure/Map.lean:94–107`. For a function that is not almost-everywhere measurable, it returns zero when the original measure is zero and an arbitrary Dirac probability measure otherwise. This convention is relevant to the pushforwards in T58, T61 and T62, although it does not affect any of them: IID explicitly makes every coordinate measurable, the identity is measurable, and the two transformed-uniform tail maps are Borel (the reciprocal has a total value at zero and positive-base real exponentiation is continuous in the exponent). No conclusion or claim comparison changed from this clarification; the original blind reading above is preserved.
