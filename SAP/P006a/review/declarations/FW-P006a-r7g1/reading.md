# Blind reading of P006a T1–T5

This file was written before opening `claims.json` or `record.json`. Sources read:
`closure.json`, the five Challenge docstrings and statements, and all unit
declarations in their closures. The 116 distinct closure declarations were also
printed from the compiled environment in `scratch/ClosurePrint.lean` and
`scratch/ClosurePrint.log`. This includes structure constructors and projections,
the classical decidability instance, and all 28 generated numeral-proof
declarations. Those proof declarations certify only that specified natural
numeral bases are at least two; they impose no experimental assumptions.

## SAP.P006a.T1

The theorem is a closed conjunction, with no premises or free experimental
parameters. A binary policy is a pair `(a,b)` of **real** numbers. The feasible
set is exactly `0 ≤ a ≤ 1` and `0 ≤ b ≤ 1`. Its function on the two-element type
`Bool` takes value `a` at false and `b` at true. Write `m(false)=9/10` and
`m(true)=1`. The printed rule at `x` is one if `m(x)>0` and
`∀ z : Bool, m(z)≤m(x)`, and zero otherwise.

All expectations here are explicit finite sums, not axioms about an unspecified
experiment. For a Boolean `t`, its real indicator is one at true and zero at
false. Put `c(q,true)=q` and `c(q,false)=1-q`. The two-unit joint mass of
`(x0,x1,t0,t1)` is

`(1/2)(1/2)c(π(x0),t0)c(π(x1),t1)`.

Thus the covariates are independent fair bits and the treatments are conditionally
independent Bernoulli draws with the respective policy probabilities. The
potential outcomes are zero and `m(x)`; realized outcome `yi` is `m(xi)` if
`ti=true` and zero otherwise. If `N=1{t0}+1{t1}`, the ATO statistic is
`(y0*1{t0}+y1*1{t1})/N` for `N>0` and zero for `N=0`.
`witnessReward(π)`, denoted `R(π)`, sums this statistic against the displayed
joint mass. `rewardE001ATT(π)` uses the same joint mass and the same statistic
after subtracting the deterministic zero estimator from each supplied potential
treated outcome. Supplying the treated potential outcomes for untreated entries
does not affect a term because those entries are multiplied by zero.

`witnessWelfare(π)`, denoted `W(π)`, is the one-unit finite sum
`Σx,t (1/2)c(π(x),t)((if t then m(x) else 0)-0)`.
`IsBest(S,f,p)` means exactly `p∈S` and `∀p'∈S, f(p')≤f(p)`;
it is an attained maximum, not merely a supremum.

The assertions, in order, are:

1. For every Boolean `x`, the printed rule equals the rule of `(0,1)`.
   `R(0,1)=3/4`, `R(1,1)=19/20`, and the former is strictly smaller.
   For every feasible `π`, `R(π)≤R(17/18,1)` and
   `R(π)=R(17/18,1) ↔ π=(17/18,1)`.
   `R(17/18,1)=1369/1440`.
   `(1,1)` is a welfare maximizer over the feasible square, and
   `W(1,1)-W(17/18,1)=1/40`, `W(1,1)-W(0,1)=9/20`.
2. For every feasible `π=(a,b)`, `rewardE001ATT(π)=R(π)`, and
   `R(π)=(9a+10b)(4-a-b)/40`,
   `1369/1440-R(π)=(9/40)(a-17/18)^2+(1-b)(30-19a-10b)/40`,
   and `W(π)=(9a+10b)/20`.
3. On the index type `Fin 2`, the population conditional average with masses
   `(1/2,1/2)`, scores `(9/10,1)`, and policy `(0,1)` is one. This average means
   `Σi pi mi πi / Σi pi πi` if the denominator is positive, and zero otherwise.
   Also `R(0,1)=3/4<1`.
4. `W(1,1)=19/20`, `W(17/18,1)=37/40`, and `W(0,1)=1/2`.

The docstring calls this a counterexample to printed Propositions 6 and 7,
including their proof displays, and describes the asserted optimum and gaps.

Junk-value audit: the zero-on-empty value of the ATO/ATT reward is explicit and
affects the unconditional reward. It is not hidden cancellation of `0/0`.
Every executed division in its positive branch has positive integer denominator.
The finite conditional average has positive denominator `1/2` in this assertion.
All other denominators are nonzero real numerals. Boolean indices and `Fin 2`
are nonempty and vectors are total functions on those types. No Bochner integral,
conditional expectation, supremum, truncated subtraction, logarithm, square
root, real power, infinite-value conversion, limit, or partial function occurs.
All subtraction is real subtraction. `coinMass` can be a signed weight for
arbitrary real input, but every probability input used here is in `[0,1]`.

## SAP.P006a.T2

The first conjunct quantifies, in this order, arbitrary types `Ω,C`, measurable
spaces on both, a natural number `n`, an experiment `E`, and a proof of the
following standing outcome/design conditions. The experiment itself contains
`n>0`, a measure `PX` on `C`, functions `μ0,μ1:C→ℝ`, a policy-indexed measure
`law(π)` on `Ω`, functions `Xi:Ω→C`, `Y0i,Y1i:Ω→ℝ` for `i:Fin n`,
policy-indexed treatments `Ti(π):Ω→Bool`, and an estimator
`μhat(π,ω,x):ℝ`. Here and throughout, an admissible policy is a measurable
function `π:C→ℝ` with `0≤π(x)≤1` at every `x`.

The standing conditions are all of these:

* `PX` is a probability measure; `μ0,μ1` are measurable and integrable under it.
* For every admissible policy, `law(π)` is a probability measure; all units'
  covariates, potential outcomes, and treatments are measurable; both potential
  outcomes of each unit are integrable.
* For every admissible policy and every unit, the pushforward law of `Xi` is
  `PX`. For each unit the joint law of `(Xi,Y0i,Y1i)` is unchanged between any
  two admissible policies.
* Under each admissible policy the family
  `(Xi,Y0i,Y1i,Ti(π))`, indexed by `Fin n`, is independent and identically
  distributed. In Mathlib terms this is `iIndepFun` and pairwise `IdentDistrib`.
* With `σ(Xi)` the measurable-space comap of `Xi`, the conditional expectations
  `E[Y0i|σ(Xi)]` and `E[Y1i|σ(Xi)]` equal `μ0(Xi)` and `μ1(Xi)` almost surely.
* `E[1{Ti}|σ(Xi)]=π(Xi)` almost surely.
* For every measurable `B⊆ℝ×ℝ`,
  `E[1{Ti}1{(Y0i,Y1i)∈B}|σ(Xi)]`
  `=π(Xi) E[1{(Y0i,Y1i)∈B}|σ(Xi)]` almost surely.

The type structure and its constructor add exactly the listed fields. No
estimator assumption is included in these standing conditions.

Write `τ=μ1-μ0`, `Yi=Y1i` when `Ti=true` and `Yi=Y0i` otherwise,
`N=Σi 1{Ti}`, `q(π)=∫π dPX`, `A(m,π)=∫mπ dPX`, and
`h_n(q)=Σ(j=0,...,n-1)(1-q)^j`. Set `F_m(π)=h_n(q(π))A(m,π)`.
The realized ATO reward is `Σi Yi 1{Ti}/N` when `N>0`, and zero otherwise.
The ATT reward replaces each `Yi` in that expression by
`Yi-μhat(π,ω,Xi)`. Expected rewards are Bochner integrals of those real
statistics under `law(π)`.

For arbitrary `m,π` and statistic `r`, the predicate `AveragePolicyFacts` is
exactly the following conjunction under `law(π)`:

* `Pr(N=0)=(1-q)^n` and `Pr(N>0)=1-(1-q)^n` (measure values are converted
  from extended nonnegative reals to reals).
* `E[r]=F_m(π)` and
  `F_m(π) = if q>0 then (1-(1-q)^n)A(m,π)/q else 0`.
* If `q>0`, then for **every** unit `i`,
  `E[m(Xi)|Ti=true]=A(m,π)/q`, and `E[r|N>0]=A(m,π)/q`.
  These event means are defined as the integral over the event divided by its
  real probability, rather than as a conditional-law construction.

Under the standing conditions, the first conjunct concludes all five clauses:

1. For every admissible `π`, these facts hold for `m=μ1` and the ATO statistic.
2. For every function `π:C→ℝ`, being an ATO best response over all admissible
   policies is equivalent to maximizing `F_μ1` over the same class.
3. For every set `P⊆(C→ℝ)`, if all its members are admissible, the evaluated
   estimator `ω↦μhat(π,ω,Xi(ω))` is integrable for every `π∈P` and every `i`,
   and
   `E[μhat(π,ω,Xi)|σ((Xj)j,(Tj)j)]=μ0(Xi)` almost surely for every such
   `π,i`, then the facts hold for every `π∈P`, `m=τ`, and ATT; and for
   every function `π`, ATT-best over `P` is equivalent to `F_τ`-best over `P`.
4. Replacing the estimator by the deterministic function `μ0(x)` gives both
   evaluated integrability and that vector conditional-mean identity over
   **all** admissible policies.
5. For every `P` of admissible policies, suppose evaluated estimator
   integrability holds on `P`, and for every `π∈P` and **every fixed** `x∈C`,
   `μhat(π,·,x)` is integrable with integral `μ0(x)`. Suppose also there exist
   a type `A:Type`, a measurable space on it, a measurable `Z:Ω→A`, and
   `f:(C→ℝ)→A→C→ℝ`, such that for each `π∈P`, `f(π,·,·)` is jointly
   measurable, `μhat(π,ω,x)=f(π,Z(ω),x)` for all `ω,x`, and `Z` is independent
   of the entire covariate-and-treatment vector under `law(π)`.
   Then the vector conditional-mean identity holds on `P`.

The second conjunct quantifies `K:ℕ` with `K>0`, `n:ℕ` with `n>0`, then
`p,m:Fin K→ℝ` with every `pi>0`, `Σpi=1`, and `m` antitone in the index order.
Define feasible finite policies by `0≤πi≤1` for every index,
`Q(π)=Σpiπi`, `M(π)=Σpimiπi`, `Pj=Σ(i<j)pi`, and `Bj=Σ(i<j)pimi`.
For `j:Fin K` define `θ(j,q)i=1` for `i<j`, `(q-Pj)/pj` for `i=j`, and zero
for `i>j`. The fixed-mass frontier `H(q)` is the **real supremum** of
`{M(π):π feasible, Q(π)=q}`. The assertions are:

* For every `j,q` with `Pj≤q≤Pj+pj`, the policy `θ(j,q)` is feasible, has mass
  `q`, has marked mass `Bj+mj(q-Pj)`, and bounds above every feasible policy's
  marked mass with that same `q`.
* There exist `j,q` in such a segment for which `θ(j,q)` maximizes
  `h_n(Q(π))M(π)` over all feasible finite policies.
* For every `q∈[0,1]` the fixed-mass maximum is attained. For every segment
  above, `H(q)=Bj+mj(q-Pj)`. The scalar objective `h_n(q)H(q)` has an attained
  maximum over `[0,1]`, and its supremum equals that of
  `h_n(Q(π))M(π)` over finite policies.
* If `m0>0`, the rule that treats exactly the points attaining the positive
  global maximum of `m` maximizes the population average
  `M(π)/Q(π)` (defined as zero when `Q≤0`), with value `m0`.
  If `m0≤0`, the zero policy maximizes that population average.

The remaining three conjuncts are closed assertions:

* In the two-fair-bit, two-unit experiment of T1, now supplying treated potential
  outcomes directly to the ATO statistic, `(17/18,1)` is the unique reward
  optimum over `[0,1]^2`; it gives positive probability to false although
  `m(false)<m(true)`.
* For every `n:ℕ` and real `q>0`,
  `Σ(j<n)(1-q)^j=(1-(1-q)^n)/q`.
* For every real `q,A`, `h_1(q)A=A`.

Junk-value audit: ATO and ATT explicitly use zero for an empty treated sample.
The comparison with the population conditional average also uses an explicit
zero at zero treatment mass. These choices matter to the optimization claims.
`eventMean` would be zero for a null event (real division has `a/0=0`); its
occurrences are guarded by `q>0`, so each conditioning event has positive
probability. All probability measures are finite, so `ENNReal.toReal(∞)=0`
cannot affect these assertions. Real Bochner integrals are zero for
non-integrable functions, and conditional expectation is zero if its function
is not integrable, its sigma algebra is not a subalgebra, or the trimmed measure
is not sigma-finite. The stated measurability, probability, potential-outcome
integrability, and evaluated-estimator L1 assumptions prevent those fallback
cases in each asserted use. Fixed-point estimator integrability and evaluated
integrability are separate and both appear where needed.

The frontier's supremum would use Mathlib's total real `sSup` convention on
empty or unbounded fibers. Here positive normalized masses and `q∈[0,1]`
give nonempty compact fibers with bounded marked masses; segment conditions
imply the same interval restriction. Both global optimization sets are nonempty
and bounded in objective value. Division by `pj` is protected by `pj>0`.
`n>0` and `K>0` exclude empty index sets wherever samples, a first unit, or a
first score are used. The geometric identity also quantifies `n=0`, when its
empty sum and numerator are both zero, consistently. Powers have natural
exponents, with the usual `0^0=1` term for `j=0`; this makes `h_n(1)=1`
for `n>0`. `range n`, finite indices, and numeral casts have their ordinary
natural-number meanings; subtraction in these formulas is real subtraction.
There are no logarithms, square roots, real powers, limsups, infima, or partial
functions in this closure. Classical propositional decidability only chooses
branches of already specified real-valued rules.

## SAP.P006a.T3

The first conjunct quantifies arbitrary measurable types `Ω,C`, `n:ℕ`, an
experiment with `n>0`, and the outcome/design standing assumptions. Explicitly:
the covariate law and every admissible-policy law are probabilities; the mean
functions are measurable and integrable; all unit covariates, treatments, and
potential outcomes are measurable with integrable potential outcomes;
covariates have the prescribed common law; each unit's joint covariate and
potential-outcome law is policy invariant; the covariate/outcome/treatment
quadruples are independent and identically distributed across units under each
policy; conditional potential means are `μ0(Xi),μ1(Xi)`; conditional treatment
means are `π(Xi)`; and treatment satisfies the conditional event-factorization
identity against every measurable event of the two potential outcomes.

Next it quantifies a policy set `P`, assuming all members are measurable
functions into `[0,1]`, the function identically zero is a member, evaluated
estimator integrability holds for every member and unit, and
`E[μhat(π,·,Xi)|σ((Xj)j,(Tj)j)]=μ0(Xi)` almost surely for every member and
unit. These are premises before any optimum is mentioned. No countability or
atomicity of `C` is assumed.

For each policy, let `Yi=Y1i` if treated and `Y0i` otherwise. Define
`V(π)=∫(Y0th-observed-Y0,0th) d law(π)`, using unit index `0:Fin n`;
thus it is the mean observed-minus-untreated outcome of the first unit.
Let `q=∫π dPX`, `A(τ,π)=∫(μ1-μ0)π dPX`, and
`h_n(q)=Σ(j<n)(1-q)^j`. Expected ATT is the integral of the treated-sample
average of `Yi-μhat(π,·,Xi)`, set to zero on an empty treated sample.
The welfare best value is `sSup {V(π):π∈P}`, a **real** supremum, and regret
is that real value minus the welfare of the selected policy.

The conclusions are, in this order:

1. For every `π∈P`, `V(π)=A(τ,π)`,
   `E[ATT(π)]=h_n(q(π))V(π)`, and `h_n(q(π))≥1`.
2. The zero policy has expected ATT zero and welfare zero.
3. `{V(π):π∈P}` is nonempty and bounded above.
4. For every `b:C→ℝ`, if `b∈P` and
   `∀π∈P, E[ATT(π)]≤E[ATT(b)]`, then expected reward and welfare of `b` are
   nonnegative and `regret(b)≤sSup V(P)`.
   Inside this implication, for every `s:C→ℝ`, if `s∈P` and
   `∀π∈P,V(π)≤V(s)`, then `sSup V(P)=V(s)` and
   `regret(b)=V(s)-V(b)`.

The second conjunct is a closed finite counterexample calculation. Covariates
are independent fair Booleans, `n=2`, `Y0=0`, `Y1(false)=9/10`, `Y1(true)=1`,
and the estimator is deterministically zero. Both ATO and ATT expectations sum
their zero-on-empty statistics against the product mass
`(1/4)c(π(x0),t0)c(π(x1),t1)` over four Booleans, where `c(q,t)` is `q` or
`1-q`. For **every** real pair `π` (not just feasible pairs), the ATT and ATO
finite expressions are equal. Over `[0,1]^2`, ATT is uniquely maximized by
`(17/18,1)`. Welfare is `(9/20)a+(1/2)b`. Its regret at that optimizer is
`1/40`. The expression named `printedRegretE001` is explicitly

`Σx (1/2)m(x) 1{m(x)>0 and not (∀z,m(z)≤m(x))}`;

it equals `9/20` and differs from the actual regret. The docstring describes
both the general nonnegative-welfare bound and this disagreement with the
printed formula.

Junk-value audit: the empty treated average has the stated zero convention.
There are no conditional event means and thus no null-event divisions here.
The experiment and the standing assumptions exclude an empty sample or a
probability measure on an empty population; zero membership excludes an empty
feasible class. Integrability, measurable comap sigma algebras, and finite
probability measures exclude the zero fallbacks of Bochner integrals and
conditional expectations. The theorem explicitly establishes nonemptiness and
boundedness of the welfare image before asserting supremum/regret properties;
the finite example has a nonempty compact square and a bounded linear welfare
function. All denominators in finite constants are nonzero. The unconditionally
quantified identity between the two finite reward expressions is algebraic
outside the feasible square, where weights need not be probabilities; the
counterexample and optimization conclusions only use genuine probabilities.
Natural powers include `0^0=1` in `h_n(1)`. No truncated subtraction, infinite
conversion, empty/unbounded limit, logarithm, root, real power, or partial
function is used. Generated numeral proofs and structure constructors add no
extra hypotheses.

## SAP.P006a.T4

This is a closed conjunction about two completely specified one-unit finite
experiments. Policies are real pairs `(a,b)` and the feasible set is `[0,1]^2`.
There is one fair Boolean public covariate `X`; the estimator's random state is
that same covariate, not an independent draw. For a fixed state `s` and queried
covariate `x`, define

`eA(s,x)= if x=s then 1 else -1`, `eB(s,x)=-eA(s,x)`.

The fixed-query mean is `Σs (1/2)e(s,x)`. Treatment given `X=x` has probability
`π(x)`, with probability mass `c(π(x),t)`. TT is the finite sum
`Σi (Yi-μhat(Xi))1{Ti}`: the general weighted version multiplies the `i`th
term by `g(Xi)`, and unweighted TT uses `g=1`.

Here each experiment has `Y0=0`. In A, `Y1=1/2` and the estimator state is `X`
with query value `eA(X,X)`. In B, `Y1=-1/2` and the corresponding query is
`eB(X,X)`. Thus
`RA(π)=Σx,t (1/2)c(π(x),t)(1/2-eA(x,x))1{t}` and
`RB(π)=Σx,t (1/2)c(π(x),t)(-1/2-eB(x,x))1{t}`.
The code supplies `Y1` even in untreated vector entries, which does not affect
these statistics because those entries are multiplied by zero.
Welfare is `WA(π)=(a+b)/4`, `WB(π)=-(a+b)/4`.
An ATT statistic is the same residual sum divided by its positive treated count
and is zero at count zero. With one unit it therefore equals TT pointwise.

`IsBest` is membership plus comparison with every feasible pair.
`bestValue(S,f)=sSup(f '' S)` is the real supremum, and
`regret(S,V,π)=sSup(V '' S)-V(π)`. Marginal heterogeneity of two Boolean
baseline functions is `Σx (1/2)|b0(x)-μ0(x)|`.
The treated estimator mean for a policy is
`[Σx (1/2)π(x)e(x,x)]/[Σx (1/2)π(x)]`.

The asserted clauses are:

1. For every fixed Boolean `x`, both fixed-query estimator means are zero.
   For every `x`, `eA(x,x)=1` and `eB(x,x)=-1`.
2. Over the feasible square, A's unique reward maximizer is `(0,0)`;
   `(1,1)` maximizes A's welfare; its regret at `(0,0)` is `1/2`;
   and `RA(1,1)≠WA(1,1)`.
3. B's unique reward maximizer is `(1,1)`; `(0,0)` maximizes B's welfare;
   its regret at `(1,1)` is `1/2`; its maximal welfare is zero.
4. For every feasible `(a,b)`,
   `RA=-(a+b)/4`, `WA=(a+b)/4`, `RB=(a+b)/4`, `WB=-(a+b)/4`.
5. The marginal heterogeneity between two identically zero functions is zero,
   and twice that zero is strictly less than A's regret at `(0,0)`.
6. For every feasible policy, the respective one-unit ATT rewards equal
   `RA` and `RB`.
7. At the all-treated policy, the two treated estimator means are `1` and `-1`.
8. For every feasible policy, `RA(π)=WA(π) ↔ π=(0,0)`.
   A's maximal welfare is `1/2`, and `WB(1,1)=-1/2`.

There are no hypotheses to make inconsistent. The docstring says the
pointwise-unbiased witnesses refute implications from Assumption 1 alone and
include a zero-private-heterogeneity example.

Junk-value audit: all probability weights are nonnegative and sum to one at
feasible policies. Every fixed-query and evaluated estimator is bounded on a
finite space. All reward and mean expressions are explicit finite sums; no
Bochner-integral or conditional-expectation convention is involved. The ATT
zero-on-empty convention is used at the no-treatment optimum and is material.
The treated-mean ratio is evaluated only at `(1,1)`, whose denominator is one;
its totalized value at the zero policy is not asserted. Supremum sets are images
of the nonempty compact feasible square under linear functions, hence nonempty
and bounded, with the stated attained extrema. All numerical denominators are
nonzero. There are no empty index types, infinite conversions, partial
functions, logarithms, square roots, real powers, limits, or truncated
subtractions. Boolean comparison and vectors are total.

## SAP.P006a.T5

This is a closed conjunction about two agents with one unit each. Both have
fair Boolean covariates, and their two covariates `Xj,Xk` are independent: joint
mass is `1/4` at each pair. Both use the **same** random estimator

`e(xj,xk,x)=1{x=xj}-1{x=xk}`.

Each agent's policy is a real pair `(a,b)` in `[0,1]^2`, interpreted as a
treatment probability at false and true. The TT reward is the sum of treated
residual outcomes; with one unit it is `(Y1-e(Xj,Xk,Xagent))1{T}`.
Both untreated potential outcomes are zero, agent j's treated outcome is
`1/4`, and agent k's is `1/8`. Accordingly the expected scores are explicitly

`Sj(π)=Σxj,xk,t (1/4)c(π(xj),t)(1/4-e(xj,xk,xj))1{t}`,

`Sk(π)=Σxj,xk,t (1/4)c(π(xk),t)(1/8-e(xj,xk,xk))1{t}`,

where `c(q,true)=q` and `c(q,false)=1-q`. The weighted TT definition in the
closure evaluates each unit's own weight inside the sum; here its weight is
identically one. Best responses mean membership in `[0,1]^2` plus comparison
against every feasible pair, and best values are real suprema of feasible
score images.

The assertions are:

1. For every fixed query `x:Bool`,
   `Σxj,xk (1/4)e(xj,xk,x)=0`.
2. For every `xj`, `Σxk (1/2)e(xj,xk,xj)=1/2`;
   for every `xk`, `Σxj (1/2)e(xj,xk,xk)=-1/2`.
3. `(0,0)` maximizes `Sj`; `(1,1)` maximizes `Sk`; their maximal scores are
   respectively zero and `5/8`, with strict inequality between them.
4. The treatment-effect constants satisfy `1/8≤1/4`.
5. For every feasible `(a,b)`, `Sj=-(a+b)/8` and `Sk=5(a+b)/16`.
6. `0<1/8<1/4`.

There are no existential or conditional hypotheses; the witnesses are built
directly into the sums. The docstring calls this a reversal of both ranking
orders under pointwise Assumption 1 alone. The mathematical statement encodes
the effect comparison through the two constant outcomes and their inequalities;
it does not introduce general ranking predicates or a separate reference
measure. The common fair law can serve as such a reference in this example.

Junk-value audit: there is no random denominator or division by zero; all
denominators are positive real numerals. Joint and treatment weights are genuine
probabilities on feasible policies. The estimator and outcomes are bounded
functions on finite nonempty spaces. Neither Bochner integrals nor conditional
expectations occur. The score images of the compact nonempty feasible square
are bounded and have the stated maxima, so real `sSup` does not use an empty or
unbounded-set fallback. No truncated subtraction, infinite conversion,
logarithm, square root, real power, limit, partial function, or empty index type
is involved.
