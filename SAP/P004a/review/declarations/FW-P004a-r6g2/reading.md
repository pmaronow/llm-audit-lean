# Blind statement reading

This file was written before opening `claims.json` or `record.json`. The sources
read were the five docstrings and statements in `Challenge/Part1.lean`, the
declarations listed in each target's `closure.json` entry, and the Mathlib
conventions mentioned below. Compiler-generated closure declarations were
inspected in `scratch/ClosurePrint.lean`; they supply ordinary numeral,
nonempty-singleton, modular-index, or real continuous-scalar-action proofs.

## Common mathematical notation and totalization conventions

All scalar quantities below are real. A population size is a natural number
`N`; its nodes are the finite set `{0,...,N-1}`. An assignment is a function
`z : Fin N → Bool`, identified with a binary vector, and `z_i` in a scalar
formula means 1 for `true` and 0 for `false`. For a vector `p`, write

`w_p(z) = ∏_i p_i^{z_i}(1-p_i)^{1-z_i}`,
`E_p f = ∑_z w_p(z) f(z)`, and
`P_p(A) = ∑_z w_p(z) 1_A(z)`.

Here the powers in this mathematical abbreviation mean the two branches of
`coin`, not an extra Lean real-power operation. When `0 < p_i < 1`, this is
exactly independent Bernoulli assignment. The definitions are also total for
arbitrary real `p`; without probability guards their weights can be signed.
Covariance is `E_p(fg) - E_p f E_p g`, and variance is its specialization to
`f=g`. All these are finite sums and need no integral convention.

For a table `R : Fin N → (Fin N → Bool) → ℝ`, put

`m_i(a) = E_p[1_{z_i=a} R_i(z)] / (p_i if a=true else 1-p_i)`,
`τ_i = m_i(true)-m_i(false)`, and `τ = N⁻¹ ∑_i τ_i`.

These unfold `marginal`, `nodeEffect`, and `ame`. With strict propensity bounds
they are the conditional mean, individual marginalized effect, and node mean.
For masses `a_k` and values `v_k`, `finiteAverage a v` is exactly
`(∑_k a_k v_k)/(∑_k a_k)`.

Real inverse of zero and real division by zero give zero. Empty finite sums are
zero and empty products are one. For `N=0`, the assignment type has exactly one
element, although the node type is empty; node means divided by `N` are zero.
Natural-number casts to reals are exact. There is no natural-number truncated
subtraction in these five statements; occurrences such as `1-p` and `3N²-2N`
are real subtraction. The integer divisions and remainders used in the star
geometry are ordinary natural division by 5 and remainder modulo 5, with
positive divisor and proved in-range indices.

The real normal CDF is
`Φ(x) = (gaussianReal 0 1 (Iic x)).toReal`, and its quantile is
`q(a) = inf {x : ℝ | a ≤ Φ(x)}`. The measure is a probability, so this `toReal`
never sees infinity. Quantile levels used below are strictly between 1/2 and 1,
so these real infima are of nonempty sets bounded below. In general real
`sInf` of an empty set or a set unbounded below is zero; the domain guards here
avoid that behavior.

`Real.sqrt x` is zero for negative `x`. `Real.log 0=0`, and for negative `x`
the real logarithm is `log |x|`. A nonintegrable real Bochner integral is zero.
`ENNReal.toReal ⊤=0`. Matrix inverse is determinant inverse times adjugate, and
is the zero matrix at a singular real matrix. These conventions are tracked
separately in each section below. There are no partial functions with chosen
default values, and no `limsup` or `liminf` operations in the statements:
asymptotic upper and lower bounds are expressed directly using eventual
inequalities.

## SAP.P004a.T6

Source: `Challenge/Part1.lean:65-73`, `Defs/Part3.lean:169-197`, and its
eleven-entry dependency closure.

### Quantifiers, hypotheses, and conclusions

The theorem has no hypotheses outside its proposition. Its proposition is a
conjunction of the following three universally quantified assertions.

1. For every measurable space `A` (in the specified universe), natural numbers
   `N,m`, measure `ζ` on `A`, sets `B_{ik} ⊆ A`, real outcome function
   `Y : A → (Fin N → Bool) → ℝ`, and vector `p : Fin N → ℝ`, assume, in this
   order: `N>0`; `m>0`; every `B_{ik}` is measurable; for each fixed `i` the
   `m` sets are pairwise disjoint; each has strictly positive finite measure;
   each `Y(·,z)` is integrable on each bin; and `0<p_i<1` for every node.
   Define `a_{ik}=(ζ B_{ik}).toReal`,
   `R_{ki}(z)=(∫_{B_{ik}} Y(x,z) dζ)/a_{ik}`, and
   `U_i(z)=(∫_{⋃_k B_{ik}} Y(x,z) dζ)/(ζ(⋃_k B_{ik})).toReal`.
   Then all of these hold:
   - for every `i,z`, `U_i(z)=(∑_k a_{ik}R_{ki}(z))/(∑_k a_{ik})`;
   - for every `i` and Boolean arm `a`, the conditional marginalized mean of
     `U_i` given `z_i=a` is the same weighted average of the bin conditional
     means defined above;
   - for every `i`, `τ_i(U)=(∑_k a_{ik}τ_i(R_k))/(∑_k a_{ik})`;
   - `τ(U)=N⁻¹∑_i (∑_k a_{ik}τ_i(R_k))/(∑_k a_{ik})`;
   - for every node `i` and real bounds `lo,hi`, if every bin's individual
     effect at that node lies in `[lo,hi]`, so does its union effect;
   - for every node `i` and real `c`, if all its bin masses equal `c`, its union
     individual effect is `m⁻¹∑_k τ_i(R_k)`.
2. For every real `c,s,t`, if `c>0`,
   `|c s| ≥ |c t| ↔ |s| ≥ |t|`.
3. For every natural `N`, arbitrary real weight function `w` on all binary
   assignments, arbitrary real statistic `T`, observed assignment `obs`, and
   real `c>0`, the two sums
   `∑_z w(z) 1_{|c T(z)|≥|c T(obs)|}` and
   `∑_z w(z) 1_{|T(z)|≥|T(obs)|}` are equal.

In (3), `w` is not assumed nonnegative or normalized. Equality therefore holds
also for all probability weights and expresses exact randomization p-value
invariance, but the statement does not assert that arbitrary `w` itself is a
probability law. No Monte Carlo draw law is specified here.

### Junk-value audit

Positive `N,m`, positive finite bin measures, and finitely many disjoint bins
ensure all means and union denominators in (1) are positive and finite.
Integrability on bins gives integrability on their finite union. Strict
propensity bounds avoid the conditional-mean zero denominators. The equal-mass
constant is automatically positive. Clauses (2)-(3) have no division, and their
strict scale guard excludes loss of ordering at zero. Empty `N` is allowed in
(3) and gives an ordinary equality of two singleton-assignment sums. No
logarithm, square root, real power, matrix inverse, or infinite extrema occur.

### Docstring scope, without a claim comparison

The docstring explicitly retains the above integral and marginal identities,
node mean, bounds, equal-mass formula, and scaling identities. It explicitly
omits two negative aggregation assertions and empirical numbers or conclusions.

## SAP.P004a.T7

Source: `Challenge/Part1.lean:75-86`, `Defs/Part3.lean:200-237`, and all entries
of its dependency closure (including generated numeral/index proofs).

### Spatial and statistical definitions fully expanded

A spatial population of size `N` consists of a metric measurable space `X`, a
nonempty subset `S_i` for every node, a measure `ζ`, a real field `Y(x,z)`, and
a function assigning a set of radii `D(d) ⊆ ℝ` to each real `d`. Write
`δ_i(x)=infDist(x,S_i)`,
`C_i(d)={x : δ_i(x)∈D(d)}`, and
`R_i(d,z)=(∫_{C_i(d)}Y(x,z)dζ)/(ζ(C_i(d))).toReal`.
The distance between nodes `i,j` is
`D_{ij}=inf {dist(x,y) : x∈S_i, y∈S_j}`.
The neighborhoods at radius `h` are `{j : D_{ij}≤h}`.

Node `j` influences row `i` of a table if `i=j`, or there exist two assignments
equal at every coordinate other than `j` with different row-`i` outcomes. Rows
`i,j` share a source if some node influences both. Locality at distance `h`
means `D_{ij}>h` implies that they do not share a source.

The asserted spatial conditions mean exactly:

- some `b>0` bounds `|Y_N(x,z)|<b` for all `x,z` for all sufficiently large `N`;
- some real function `h(d)` is nonnegative for every `d≥0`, and for every such
  `d` locality of the circle table at radius `h(d)` holds for all sufficiently
  large `N` (the starting index may depend on `d`);
- some real function `c(r)` bounds the cardinality of every node's radius-`r`
  neighborhood for every `r≥0` and all sufficiently large `N` (the starting
  index may depend on `r`).

`WellDefined(P,d)` means, for every node, that `C_i(d)` is measurable, has
strictly positive finite measure, and every assignment's outcome field is
integrable on it. Nondegeneracy of a variance sequence `V_N` means there is a
real `v>0` such that `N V_N≥v` eventually.

For arbitrary table `R`, write `n_a(z)=∑_i 1_{z_i=a}`,
`r_a(z)=n_a(z)⁻¹∑_{i:z_i=a}R_i(z)`,
`H_R(z)=r_true(z)-r_false(z)`,
`e_i(z)=R_i(z)-r_{z_i}(z)`, and
`λ_i(z)=z_i/n_true(z)-(1-z_i)/n_false(z)`.
For a real matrix `Q`,
`V(z,e,Q)=∑_{ij}λ_iλ_j e_i e_j Q_{ij}`.
Let `X` have rows `(1,z_i)`, and let
`P_z=I-X(XᵀX)⁻¹Xᵀ`. Put
`A(z,Q)=(n_true n_false/N) P_z diag(λ) Q diag(λ) P_z`,
`μ(z,Q)=tr A(z,Q)`, and `η(z,Q)=2 tr(A(z,Q)²)`.
These are the exact `adjustmentMatrix`, `adjustmentMu`, and `adjustmentNu`.

For any propensities and table, let `b_a=N⁻¹∑_i m_i(a)`. The linearized Hajek
variable is
`L(z)=N⁻¹∑_i[b_true-b_false + z_i(R_i(z)-b_true)/p_i
                         -(1-z_i)(R_i(z)-b_false)/(1-p_i)]`.
For fits `g_i(a)` and neighborhoods `B_i`, the homophily quantity is
`N⁻¹∑_i∑_{j∈B_i}[τ_i-(g_i(true)-g_i(false))]
                         [τ_j-(g_j(true)-g_j(false))]`.

The Student density for real degree `ν` is
`Γ((ν+1)/2)/(sqrt(νπ) Γ(ν/2)) · (1+x²/ν)^(-(ν+1)/2)`.
Its CDF is the real Lebesgue integral on `(-∞,x]`, and
`t_ν(a)=inf {x : a≤CDF_ν(x)}`.

### Fixed witness, quantifiers, and conclusions

There are no external hypotheses or existential choices of witness. Each
population `N` is explicitly constructed in the Euclidean plane. Node `i`
is the singleton at `(10 floor(i/5),0)` plus offset `(0,0),(1,0),(0,1),
(-1,0),(0,-1)` according to `i mod 5`. The measure is the sum of Dirac masses
at all these nodes. The field is independent of assignment and equals the
profile `(0,1,1,-1,-1)` at each block's points, and zero elsewhere. Its bands
are `[0,d]`. Thus radius zero averages read this profile. For `N=5m`, write
this table as `R^m_i(z)=y_{i mod 5}`.

Define the five-node star matrix `K` to have diagonal and central row/column
all ones, with all other entries zero. For `v=(2,-1,-1,-1,-1)`, put
`Q=K+vvᵀ/8`. Write `K_m,Q_m` for their `m`-block diagonal repetitions.
The cutoff kernel for a node distance function and cutoff `h` has entry one
when `D_{ij}≤h`, and zero otherwise.

The conjunction asserts:

1. At `m=4`, the fixed assignment
   `(1,1,0,1,0, 0,1,0,1,0, 1,1,0,1,0, 0,1,0,1,0)` has arm counts 10 and 10,
   both arm means zero, `V(z,e,K_4)=V(z,e,Q_4)=4/25`,
   `μ(z,K_4)=41/50`, `μ(z,Q_4)=101/100`, and
   `V(z,e,Q_4)/μ(z,Q_4)=16/101 < 8/41=V(z,e,K_4)/μ(z,K_4)`.
2. The full population sequence has the spatial conditions above. For every
   `N>0` its radius-zero averages are well defined. For every `N`, the
   homophily expression at `p_i=1/2`, radius `6/5`, and constant-arm fits `b_a`
   is zero. The variance of its linearized Hajek variable is nondegenerate.
3. For every natural `m`, the cutoff distance kernel at radius `6/5` for
   `5m` nodes equals `K_m`. For every `N`, its radius-zero table is local at
   distance `6/5`.
4. For every `m>0`, `(5m) Var_{1/2}(L(R^m))=16/5`.
5. Put `C=2Φ(q(39/40)sqrt(15/16))-1`. For every real `ε>0`, for all
   sufficiently large natural `m`, the *unconditional* independent-fair-coin
   probability of the event
   `n_true>0 ∧ n_false>0 ∧ μ(z,Q_m)>0 ∧ η(z,Q_m)>0 ∧
    |H_{R^m}(z)|≤t_{2μ²/η}(39/40) sqrt(V(z,e,Q_m)/μ)`
   is strictly less than `C+ε`. Also `C<19/20`.

This is an eventual coverage upper bound, not a convergence equality. It
excludes invalid realizations by conjunction and never divides by their
probability. The assertion does not separately say their probability tends
to zero. The actual target effect of this assignment-invariant field is zero.

### Junk-value audit

For general input tables, empty-arm means, weights, OLS inverses, and adjustment
ratios have totalized values. The finite witness has both counts 10. The
coverage event requires both counts positive and positive `μ,η`, so `XᵀX`
is invertible, the Student degree is positive, and the adjustment denominator
is positive on every counted realization. `Q` is the positive spectral part
of this star matrix, so its quadratic variance is nonnegative. Positive-degree
Student densities have positive real-power base and positive Gamma and square
root factors; their CDFs and interior-level quantiles have their usual values.
Off this domain, Gamma vanishes at nonpositive integers, square root and real
division are totalized, and real powers of nonpositive bases use Mathlib's
complex-real-part extension; no counted realization relies on these cases.

All node sets are nonempty, so infimum distances are of nonempty nonnegative
sets and `infDist` does not use its empty-set value zero. Radius-zero node
regions have positive finite atomic mass. Integrals are actual integrals of
finite-support bounded fields. At `N=0` node assertions are empty and scalar
means can be zero; asymptotic and positive-`m` clauses do not use this prefix.

### Docstring scope, without a claim comparison

The docstring accurately calls the displayed result a finite adjusted-order
reversal and a guarded asymptotic upper bound. It lists the spectral
certificates, block moments, several convergence formulas, and the Gaussian
limit as omitted. It explicitly disclaims conditional-on-validity coverage.

## SAP.P004a.T8

Source: `Challenge/Part1.lean:88-98`, `Defs/WholeW2.lean:13-120`, and its full
dependency closure. All spatial, finite-assignment, star, variance, and Student
definitions in the preceding sections have the same fully expanded meanings.

### Further definitions

For every symmetric real `N×N` matrix `K`, let `K_+` be the matrix reconstructed
from Mathlib's orthonormal eigenvectors and eigenvalues, replacing every
eigenvalue by its maximum with zero. In coordinates it is
`(K_+)_{ij}=∑_k max(λ_k,0) U_{ik} U_{jk}`. This is exactly `positiveKernel`:
its other branch returns zero for a non-Hermitian matrix. Over reals,
Hermitian means symmetric. `spectralKernel` is this same reconstruction, with
untrimmed eigenvalues when its Boolean flag is false.

For any real `V,μ`, define the capped variance
`Vcap(V,μ)=V/min(μ,1)` if `μ>0`, and `V` otherwise. With `X` the intercept and
treatment matrix defined above, the sandwich matrix is
`(XᵀX)⁻¹ Xᵀ diag(e) K diag(e) X (XᵀX)⁻¹`.
Its entry `(1,1)` means the treatment/slope coordinate, using zero-based
indices. An assignment is valid precisely when both arm counts are positive.

### Quantifiers, hypotheses, and conclusions

The theorem has no external hypotheses. It asserts four conjuncts.

1. For every real `ν,a`, if `ν>0` and `1/2<a<1`, the set
   `{x : a≤CDF_ν(x)}` is nonempty and bounded below, and `q(a)≤t_ν(a)`.
2. For every natural `N`, real symmetric `N×N` matrix `K`, assignment `z`,
   and real vector `e`, assume both treatment arms are nonempty. Put `Q=K_+`
   and `Vcap=Vcap(V(z,e,Q),μ(z,Q))`. Then:
   - the slope sandwich entries for `K` and `Q` equal `V(z,e,K)` and
     `V(z,e,Q)` respectively;
   - `V(z,e,Q)≤Vcap` and `max(V(z,e,K),0)≤V(z,e,Q)`;
   - for every real `α,c,err`, if `0<α<1`, `q(1-α/2)≤c`,
     `V(z,e,K)≥0`, and `|err|≤q(1-α/2)sqrt(V(z,e,K))`, then
     `|err|≤c sqrt(Vcap)`;
   - for every real `α,ν,err`, if `0<α<1`, `ν>0`, `V(z,e,K)≥0`,
     and the same normal-interval inequality holds, then
     `|err|≤t_ν(1-α/2)sqrt(Vcap)`.
3. For every sequence of metric measurable spaces and every corresponding
   sequence of spatial populations `P`, for every real `p,d,h,α`, assume
   `0<p<1`, `d≥0`, `h≥0`, `0<α<1`, the spatial conditions expanded above,
   eventual well-definedness of the radius-`d` averages, eventual locality
   at distance `h`, and nondegeneracy of the variance of the linearized Hajek
   variable. In addition assume eventual nonnegativity of the homophily
   expression at constant propensity `p`, distance neighborhoods of radius
   `h`, and constant-arm mean fits `b_a`. Then both conclusions hold:
   - for every family of real critical values `c_N(z)` dominating
     `q(1-α/2)` on valid assignments, for every `ε>0` eventually
     `P_p(valid(z) ∧ |H_R(z)-τ(R)|≤c_N(z) sqrt(Vcap_N(z)))≥1-α-ε`;
   - for every family of real degrees `ν_N(z)` positive on valid assignments,
     the same bound holds with `c_N(z)=t_{ν_N(z)}(1-α/2)`.
   Here `R_i(z)` is the actual radius-`d` integral average,
   `Q=(1_{D_{ij}≤h})_+`, and
   `Vcap_N(z)=Vcap(V(z,e(z),Q),μ(z,Q))`. Neither orthogonal spectral data nor
   independent critical values are supplied as assumptions. The probability
   is unconditional and counts valid realizations by conjunction.
4. The repeated-star populations satisfy the following statements: spatial
   conditions; well-defined radius-zero averages for every `N`; locality at
   distance `6/5`; zero homophily at fair-coin assignment and that distance;
   nondegenerate linearized variance; for every `m`, their `5m`-node table is
   `R^m` and its AME is zero; and the positive part of their cutoff kernel is
   exactly `Q_m`. The probability that either arm is empty or `μ≤0` or
   `η≤0` tends to zero. For every `ε>0`, eventually the unconditional valid,
   positive-`μ,η` uncapped Student coverage event from T7 has probability
   `<2Φ(q(39/40)sqrt(15/16))-1+ε`, and this constant is `<19/20`.

The final conjunct supplies a genuine failure of a universal uncapped
guarantee because it also asserts that invalid-interval probability tends to
zero. The asymptotic lower bound is the direct epsilon/eventual definition of
conservatism, not a totalized real `liminf`.

### Junk-value audit

The finite clauses guard both arm counts; the sandwich inverse is consequently
an actual inverse. Spectral positive parts are only used on symmetric matrices
(including symmetric infimum-distance cutoff matrices). Their non-Hermitian
zero branch is irrelevant. Capping's `μ≤0` branch is a deliberate specified
fallback, with no division. On its positive branch `min(μ,1)>0`. The PSD
quadratic forms are nonnegative before taking square roots, and interval
inclusion explicitly guards the original quadratic form's nonnegativity.
Student quantiles use `ν>0`, `1/2<a<1`, and their nonempty and bounded-below
sets are explicitly certified. The normal quantiles likewise use interior
probability levels.

The spatial integral and distance conventions are exactly as audited for T7;
well-definedness is an eventual hypothesis for general populations. Invalid
arm assignments are excluded from coverage. All statements about limits are
unchanged by any zero-sized finite prefix. The uncapped witness explicitly
guards its ratios and also proves these guards fail with vanishing
probability. No division by a validity probability occurs.

### Docstring scope, without a claim comparison

The docstring describes symmetric kernels, positive Student degrees, capped
coverage under spatial and variance assumptions, and an uncapped
counterexample with validity probability tending to one. Its phrase “under
C1-C5” must be compared later with the actual hypotheses recorded above.

## SAP.P004a.T9

Source: `Challenge/Part1.lean:100-109`, `Defs/WholeW2.lean:122-211`,
`Defs/Part1.lean:21-31`, `Defs/Part2.lean:176-181`, and every closure entry.

### Logistic and stochastic-rate definitions fully expanded

For fixed natural dimension `k`, deterministic covariates `O_{Ni}∈ℝ^k`,
true coefficient `θ₀∈ℝ^k`, parameter set `Θ`, and estimator
`θhat_N : (Fin N → Bool) → ℝ^k`, `LogisticConditions` is the conjunction:

1. `Θ` is compact and `θ₀∈Θ` (interiority is not included).
2. There exists real `U` such that `|O_{Ni,j}|≤U` for every `N,i,j`.
3. There exists real `c>0` such that eventually in `N`, for every `v∈ℝ^k`,
   `c∑_j v_j² ≤ N⁻¹∑_i (∑_j O_{Ni,j}v_j)²`.
4. For every `N,z`, `θhat_N(z)∈Θ`, and for every `θ∈Θ`,
   `ℓ_N(θ;z)≤ℓ_N(θhat_N(z);z)`, where
   `ℓ_N(θ;z)=∑_i[z_i⟨O_{Ni},θ⟩-log(1+exp⟨O_{Ni},θ⟩)]`.

The logistic function is `g(t)=exp(t)/(1+exp(t))`, propensities are
`p_{Ni}=g(⟨O_{Ni},θ₀⟩)`, and overlap means that a single `ε∈(0,1/2)`
satisfies `ε<p_{Ni}<1-ε` for all `N,i`. Information and normalized score are
`I_N=N⁻¹∑_i p_{Ni}(1-p_{Ni}) O_{Ni}O_{Ni}ᵀ` and
`S_N(z)=N⁻¹∑_i(z_i-p_{Ni})O_{Ni}`.

For a scalar random family `U_N(z)`, convergence to zero in probability means
that for every real `ε>0`, `P_{p_N}(|U_N|>ε)→0` as `N→∞`.
`U=o_p(r_N)` means this for `U_N/r_N`. `U=O_p(r_N)` means that for every
real `ε>0` there is real `C>0` such that eventually
`P_{p_N}(|U_N|>C|r_N|)<ε`. The assignment law in each probability is the
independent Bernoulli product described above.

### Fixed witness and complete conclusions

The dimension is one, every covariate is 1, `θ₀=0`, and `Θ=[0,1]`, represented
as functions `Fin 1→ℝ` whose sole coordinate is in that interval. Let
`n(z)=∑_i z_i`, `q_N(z)=n(z)/N`, and define the estimator

`θhat_N(z)=0` if `q_N≤1/2`,
`θhat_N(z)=1` otherwise if `g(1)≤q_N`,
`θhat_N(z)=log(q_N/(1-q_N))` otherwise.

Let `Z_N(z)=∑_i(2z_i-1)`,
`L_N(z)=4(n(z)/N-1/2)`, `R_N(z)=θhat_N(z)-L_N(z)`, and
`ℓ_z(t)=n(z)t-N log(1+exp t)`.
There are no external hypotheses. The theorem asserts all of the following.

1. The logistic conditions and overlap hold for the explicit estimator.
   `Θ` is compact, `θ₀∈Θ`, every covariate has absolute value at most 1,
   and every propensity equals `1/2`, lying strictly between `1/4` and `3/4`.
   For every `N>0`, the scalar covariate Gram average is 1 and information
   is the one-by-one matrix `(1/4)I`.
2. For every `N>0` and assignment `z`: `ℓ_z(t)` is the sum of the individual
   logistic likelihood terms for every real `t`; its first derivative is
   `n-Ng(t)` and that derivative's derivative is
   `-N exp(t)/(1+exp(t))²<0` for every real `t`. The estimator lies in
   `[0,1]` and is the unique constrained maximizer there. If `n≤N/2` it is
   zero; in particular `n=0` gives zero and `n=N` gives one. For
   `0<n<N` it equals `min(1,max(0,log((n/N)/(1-n/N))))`.
3. For every `N>0,z`: `Z_N=2n-N`; the sole coordinate of `I_N⁻¹S_N` is
   `L_N`; `L_N=2Z_N/N`; on `Z_N<0`, `R_N=-2Z_N/N`; and on
   `Z_N<0` and `Z_N²>N/4`, `sqrt(N)|R_N|>1`.
4. For every `N>0`, under independent fair coins,
   `E Z_N²=N`, `E Z_N⁴=3N²-2N>0`,
   `9N²/[16(3N²-2N)] ≤ P(Z_N²>N/4)`,
   `P(Z_N<0 ∧ Z_N²>N/4)=P(Z_N²>N/4)/2`, and
   `P(sqrt(N)|R_N|>1) ≥ 9N²/[32(3N²-2N)] ≥ 3/32`.
5. `R_N` is not `o_p(N^{-1/2})`.
6. For every real `x`, `P(sqrt(N)L_N≤x)→Φ(x/2)`. For every real `x≠0`,
   `P(sqrt(N)θhat_N≤x)` tends to zero for `x<0` and to `Φ(x/2)` for
   `x>0`. Additionally `P(θhat_N=0)→1/2`. Thus the second law is
   `2 max(G,0)` for a standard normal `G`, with its atom at zero specified.
7. `|θhat_N|→0` in probability and `|θhat_N|=O_p(N^{-1/2})`.

### Junk-value audit and refutation reading

All moment, likelihood-uniqueness, and algebra formulas that divide by `N`
are guarded by `N>0`. At `N=0` the first estimator branch returns zero,
information and score are zero, and the leading term defined separately is
`-2`; this single prefix does not affect any stochastic limit or rate.
Likelihood logarithms have positive argument `1+exp(t)`. In the estimator's
log branch `1/2<q_N<g(1)<1`, so its log argument is strictly positive and
finite. Endpoint observations take the clipping branches, without relying
on `log 0` or division by zero. Information is invertible for `N>0`.
The fourth moment denominator is positive for every positive integer `N`.
Rates `1/sqrt(N)` are positive eventually. CDF limits use the actual normal
probability law, and the discontinuity at zero is explicitly excluded from
the general weak-limit formula and separately addressed by the atom clause.

The printed reading asserted by the docstring is: under compact parameter
membership, bounded nonsingular covariates, independent logistic assignment,
and overlap, every constrained logistic MLE has the usual little-o root-N
score remainder. The witness has compact membership, bounded constant
covariates, Gram value 1, independent fair-coin assignment, strict overlap,
and an actual unique constrained maximizer; its true coefficient is on the
boundary. Whether the printed claim requires interior truth must be checked
against the canonical material in the next stage.

## SAP.P004a.T10

Source: `Challenge/Part1.lean:111-114`, `Defs/Part4.lean:25-38`, and every
dependency in its closure. The logistic, probability, information, score,
overlap, and stochastic-rate formulas are exactly those fully expanded in
the T9 section; none depends on the boundary example.

### Quantifiers, hypotheses, and conclusions

For every natural dimension `k`, every deterministic triangular array of
covariates `O : ∀ N, Fin N → Fin k → ℝ`, every true coefficient `θ₀`, every
set `Θ ⊆ (Fin k→ℝ)`, and every estimator
`θhat : ∀ N, (Fin N→Bool) → (Fin k→ℝ)`, assume `LogisticConditions` in
the complete four-part sense above, followed by overlap for the true
logistic propensities. Under the independent Bernoulli product law with those
propensities, conclude:

1. `‖θhat_N-θ₀‖→0` in probability.
2. `‖θhat_N-θ₀‖=O_p(N^{-1/2})`.
3. If, in addition, `θ₀∈interior(Θ)` in the ordinary finite-dimensional
   topology, then for
   `D_N=θhat_N-θ₀-I_N⁻¹S_N`, both
   `‖D_N‖=O_p(N^{-1})` and `‖D_N‖=o_p(N^{-1/2})`.

The norm on the function space `Fin k→ℝ` is Mathlib's supremum norm
`max_j |v_j|`, with value zero in dimension zero. In a fixed finite dimension
it is equivalent to the Euclidean norm. There is no convexity, uniqueness,
interiority, or score-equation hypothesis for conclusions (1)-(2).
Interiority is an antecedent only for (3). The estimator is an exact global
maximizer on the compact set for every assignment and every `N`.

### Junk-value audit and docstring

The uniform positive lower Gram bound, overlap, and eventual `N>0` make
`I_N` positive definite and invertible eventually. A singular finite-prefix
information matrix has totalized inverse zero, with no effect on these
rates. Both rate sequences are positive eventually, so the division in
little-o does not erase the asymptotic assertion. Logistic denominators
and likelihood log arguments are always positive. All probability spaces
are finite, and no nonintegrable means enter. The `k=0` subcase has an empty
vector and zero norm; it is a legitimate degenerate subcase, not an
inconsistency of the positive-dimensional assumptions. There are no square
roots of negative quantities, infinite `toReal` conversions, unbounded
extrema, or partial-function defaults.

The docstring distinguishes compact-membership consistency and root-N rate
from the interior-truth score expansions, in agreement with the displayed
logical implication. A canonical-claim comparison has not yet been made.

## Closure inventory

The inventory below is copied from the machine dependency closure, including
the automatically generated declarations. All named non-generated definitions
have been unfolded into the mathematical descriptions above. Generated proof
types and bodies are available in `scratch/ClosurePrint.log`; they do not add
assumptions or computational default branches.

### SAP.P004a.T6 dependency entries

- `SAP.P004a.Assignment` — `SAP.P004a.Defs.Part1:15`
- `SAP.P004a.CircleTable` — `SAP.P004a.Defs.Part1:50`
- `SAP.P004a.T6AggregationStatement` — `SAP.P004a.Defs.Part3:169`
- `SAP.P004a.T6Statement` — `SAP.P004a.Defs.Part3:190`
- `SAP.P004a.ame` — `SAP.P004a.Defs.Part1:205`
- `SAP.P004a.coin` — `SAP.P004a.Defs.Part1:115`
- `SAP.P004a.designWeight` — `SAP.P004a.Defs.Part1:117`
- `SAP.P004a.expect` — `SAP.P004a.Defs.Part1:120`
- `SAP.P004a.finiteAverage` — `SAP.P004a.Defs.Part2:68`
- `SAP.P004a.marginal` — `SAP.P004a.Defs.Part1:123`
- `SAP.P004a.nodeEffect` — `SAP.P004a.Defs.Part1:127`

### SAP.P004a.T7 dependency entries

- `SAP.P004a.Assignment` — `SAP.P004a.Defs.Part1:15`
- `SAP.P004a.CircleTable` — `SAP.P004a.Defs.Part1:50`
- `SAP.P004a.LocalAt` — `SAP.P004a.Defs.Part1:59`
- `SAP.P004a.Nondegenerate` — `SAP.P004a.Defs.Part1:149`
- `SAP.P004a.PopulationSequence` — `SAP.P004a.Defs.Part1:47`
- `SAP.P004a.SpatialLocalConditions` — `SAP.P004a.Defs.Part1:81`
- `SAP.P004a.SpatialPopulation` — `SAP.P004a.Defs.Part1:40`
- `SAP.P004a.SpatialPopulation.bands` — `SAP.P004a.Defs.Part1:45`
- `SAP.P004a.SpatialPopulation.mk` — `SAP.P004a.Defs.Part1:40`
- `SAP.P004a.SpatialPopulation.node` — `SAP.P004a.Defs.Part1:41`
- `SAP.P004a.SpatialPopulation.outcome` — `SAP.P004a.Defs.Part1:44`
- `SAP.P004a.SpatialPopulation.zeta` — `SAP.P004a.Defs.Part1:43`
- `SAP.P004a.T1Statement._proof_1` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T1Statement._proof_10` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T1Statement._proof_3` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T3Statement._proof_1` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T3Statement._proof_2` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T5Statement._proof_1` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7FiniteStatement` — `SAP.P004a.Defs.Part3:200`
- `SAP.P004a.T7FiniteStatement._proof_1` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7FiniteStatement._proof_2` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7FiniteStatement._proof_3` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7FiniteStatement._proof_4` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7FiniteStatement._proof_5` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7Statement` — `SAP.P004a.Defs.Part3:215`
- `SAP.P004a.T7Statement._proof_1` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7Statement._proof_2` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7Statement._proof_3` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7Statement._proof_4` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7Statement._proof_5` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.T7Statement._proof_6` — `SAP.P004a.Defs.Part3:0`
- `SAP.P004a.WellDefined` — `SAP.P004a.Defs.Part1:110`
- `SAP.P004a.adjustmentMatrix` — `SAP.P004a.Defs.Part2:129`
- `SAP.P004a.adjustmentMu` — `SAP.P004a.Defs.Part2:134`
- `SAP.P004a.adjustmentNu` — `SAP.P004a.Defs.Part2:159`
- `SAP.P004a.angularFraction._proof_1` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.angularFraction._proof_2` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.areaBinaryShare._proof_4` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.armCount` — `SAP.P004a.Defs.Part2:27`
- `SAP.P004a.armMean` — `SAP.P004a.Defs.Part2:84`
- `SAP.P004a.augmented` — `SAP.P004a.Defs.Part1:157`
- `SAP.P004a.ball` — `SAP.P004a.Defs.Part1:78`
- `SAP.P004a.barMu` — `SAP.P004a.Defs.Part2:150`
- `SAP.P004a.bit` — `SAP.P004a.Defs.Part1:19`
- `SAP.P004a.circleAverage` — `SAP.P004a.Defs.Part1:69`
- `SAP.P004a.coin` — `SAP.P004a.Defs.Part1:115`
- `SAP.P004a.cov` — `SAP.P004a.Defs.Part1:152`
- `SAP.P004a.designMatrix` — `SAP.P004a.Defs.Part2:122`
- `SAP.P004a.designWeight` — `SAP.P004a.Defs.Part1:117`
- `SAP.P004a.expect` — `SAP.P004a.Defs.Part1:120`
- `SAP.P004a.hajek` — `SAP.P004a.Defs.Part2:87`
- `SAP.P004a.homophilyQ` — `SAP.P004a.Defs.Part1:134`
- `SAP.P004a.interferes` — `SAP.P004a.Defs.Part1:52`
- `SAP.P004a.kernelVariance` — `SAP.P004a.Defs.Part2:102`
- `SAP.P004a.lambda` — `SAP.P004a.Defs.Part2:99`
- `SAP.P004a.linearHajek` — `SAP.P004a.Defs.Part2:153`
- `SAP.P004a.marginal` — `SAP.P004a.Defs.Part1:123`
- `SAP.P004a.nodeDistance` — `SAP.P004a.Defs.Part1:62`
- `SAP.P004a.nodeEffect` — `SAP.P004a.Defs.Part1:127`
- `SAP.P004a.nodeSeparation` — `SAP.P004a.Defs.Part1:74`
- `SAP.P004a.normalCDF` — `SAP.P004a.Defs.Part1:200`
- `SAP.P004a.normalQuantile` — `SAP.P004a.Defs.Part1:214`
- `SAP.P004a.prob` — `SAP.P004a.Defs.Part1:162`
- `SAP.P004a.region` — `SAP.P004a.Defs.Part1:65`
- `SAP.P004a.residual` — `SAP.P004a.Defs.Part2:106`
- `SAP.P004a.residualEffect` — `SAP.P004a.Defs.Part1:130`
- `SAP.P004a.residualMaker` — `SAP.P004a.Defs.Part2:125`
- `SAP.P004a.sharesSource` — `SAP.P004a.Defs.Part1:56`
- `SAP.P004a.spatialNeighborhoods` — `SAP.P004a.Defs.Part1:181`
- `SAP.P004a.starAssignment20` — `SAP.P004a.Defs.Part2:90`
- `SAP.P004a.starBlockKernel` — `SAP.P004a.Defs.Part2:117`
- `SAP.P004a.starBlockTable` — `SAP.P004a.Defs.Part2:96`
- `SAP.P004a.starBlockTable._proof_2` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starKernel` — `SAP.P004a.Defs.Part2:109`
- `SAP.P004a.starKernel._proof_1` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starNegativeVector` — `SAP.P004a.Defs.Part2:112`
- `SAP.P004a.starPD` — `SAP.P004a.Defs.Part2:114`
- `SAP.P004a.starPD._proof_1` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starPoint` — `SAP.P004a.Defs.Part2:137`
- `SAP.P004a.starPopulation` — `SAP.P004a.Defs.Part2:142`
- `SAP.P004a.starPopulation._proof_1` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starPopulation._proof_2` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starY` — `SAP.P004a.Defs.Part2:94`
- `SAP.P004a.studentCDF` — `SAP.P004a.Defs.Part2:166`
- `SAP.P004a.studentDensity` — `SAP.P004a.Defs.Part2:162`
- `SAP.P004a.studentQuantile` — `SAP.P004a.Defs.Part2:168`
- `SAP.P004a.uniformDistanceKernel` — `SAP.P004a.Defs.Part2:156`
- `SAP.P004a.variance` — `SAP.P004a.Defs.Part1:155`

### SAP.P004a.T8 dependency entries

- `SAP.P004a.Assignment` — `SAP.P004a.Defs.Part1:15`
- `SAP.P004a.CircleTable` — `SAP.P004a.Defs.Part1:50`
- `SAP.P004a.Conservative` — `SAP.P004a.Defs.Part1:211`
- `SAP.P004a.LiminfAtLeast` — `SAP.P004a.Defs.Part1:208`
- `SAP.P004a.LocalAt` — `SAP.P004a.Defs.Part1:59`
- `SAP.P004a.Nondegenerate` — `SAP.P004a.Defs.Part1:149`
- `SAP.P004a.PopulationSequence` — `SAP.P004a.Defs.Part1:47`
- `SAP.P004a.SpatialLocalConditions` — `SAP.P004a.Defs.Part1:81`
- `SAP.P004a.SpatialPopulation` — `SAP.P004a.Defs.Part1:40`
- `SAP.P004a.SpatialPopulation.bands` — `SAP.P004a.Defs.Part1:45`
- `SAP.P004a.SpatialPopulation.mk` — `SAP.P004a.Defs.Part1:40`
- `SAP.P004a.SpatialPopulation.node` — `SAP.P004a.Defs.Part1:41`
- `SAP.P004a.SpatialPopulation.outcome` — `SAP.P004a.Defs.Part1:44`
- `SAP.P004a.SpatialPopulation.zeta` — `SAP.P004a.Defs.Part1:43`
- `SAP.P004a.T8AsymptoticWhole` — `SAP.P004a.Defs.WholeW2:63`
- `SAP.P004a.T8Coverage` — `SAP.P004a.Defs.WholeW2:54`
- `SAP.P004a.T8FiniteWhole` — `SAP.P004a.Defs.WholeW2:36`
- `SAP.P004a.T8FiniteWhole._proof_1` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8StudentComparison` — `SAP.P004a.Defs.WholeW2:30`
- `SAP.P004a.T8StudentComparison._proof_1` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8UncappedWhole` — `SAP.P004a.Defs.WholeW2:79`
- `SAP.P004a.T8UncappedWhole._proof_1` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8UncappedWhole._proof_2` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8UncappedWhole._proof_3` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8UncappedWhole._proof_4` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8UncappedWhole._proof_5` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8UncappedWhole._proof_6` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8UncappedWhole._proof_7` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8UncappedWhole._proof_8` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8WholeStatement` — `SAP.P004a.Defs.WholeW2:106`
- `SAP.P004a.ValidArms` — `SAP.P004a.Defs.WholeW2:27`
- `SAP.P004a.WellDefined` — `SAP.P004a.Defs.Part1:110`
- `SAP.P004a.adjustmentMatrix` — `SAP.P004a.Defs.Part2:129`
- `SAP.P004a.adjustmentMu` — `SAP.P004a.Defs.Part2:134`
- `SAP.P004a.adjustmentNu` — `SAP.P004a.Defs.Part2:159`
- `SAP.P004a.ame` — `SAP.P004a.Defs.Part1:205`
- `SAP.P004a.angularFraction._proof_1` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.angularFraction._proof_2` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.areaBinaryShare._proof_4` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.armCount` — `SAP.P004a.Defs.Part2:27`
- `SAP.P004a.armMean` — `SAP.P004a.Defs.Part2:84`
- `SAP.P004a.augmented` — `SAP.P004a.Defs.Part1:157`
- `SAP.P004a.ball` — `SAP.P004a.Defs.Part1:78`
- `SAP.P004a.barMu` — `SAP.P004a.Defs.Part2:150`
- `SAP.P004a.bit` — `SAP.P004a.Defs.Part1:19`
- `SAP.P004a.cappedVariance` — `SAP.P004a.Defs.Part2:174`
- `SAP.P004a.circleAverage` — `SAP.P004a.Defs.Part1:69`
- `SAP.P004a.coin` — `SAP.P004a.Defs.Part1:115`
- `SAP.P004a.cov` — `SAP.P004a.Defs.Part1:152`
- `SAP.P004a.designMatrix` — `SAP.P004a.Defs.Part2:122`
- `SAP.P004a.designWeight` — `SAP.P004a.Defs.Part1:117`
- `SAP.P004a.expect` — `SAP.P004a.Defs.Part1:120`
- `SAP.P004a.hajek` — `SAP.P004a.Defs.Part2:87`
- `SAP.P004a.homophilyQ` — `SAP.P004a.Defs.Part1:134`
- `SAP.P004a.interferes` — `SAP.P004a.Defs.Part1:52`
- `SAP.P004a.kernelVariance` — `SAP.P004a.Defs.Part2:102`
- `SAP.P004a.lambda` — `SAP.P004a.Defs.Part2:99`
- `SAP.P004a.linearHajek` — `SAP.P004a.Defs.Part2:153`
- `SAP.P004a.marginal` — `SAP.P004a.Defs.Part1:123`
- `SAP.P004a.nodeDistance` — `SAP.P004a.Defs.Part1:62`
- `SAP.P004a.nodeEffect` — `SAP.P004a.Defs.Part1:127`
- `SAP.P004a.nodeSeparation` — `SAP.P004a.Defs.Part1:74`
- `SAP.P004a.normalCDF` — `SAP.P004a.Defs.Part1:200`
- `SAP.P004a.normalQuantile` — `SAP.P004a.Defs.Part1:214`
- `SAP.P004a.positiveKernel` — `SAP.P004a.Defs.WholeW2:13`
- `SAP.P004a.prob` — `SAP.P004a.Defs.Part1:162`
- `SAP.P004a.region` — `SAP.P004a.Defs.Part1:65`
- `SAP.P004a.residual` — `SAP.P004a.Defs.Part2:106`
- `SAP.P004a.residualEffect` — `SAP.P004a.Defs.Part1:130`
- `SAP.P004a.residualMaker` — `SAP.P004a.Defs.Part2:125`
- `SAP.P004a.sharesSource` — `SAP.P004a.Defs.Part1:56`
- `SAP.P004a.spatialNeighborhoods` — `SAP.P004a.Defs.Part1:181`
- `SAP.P004a.spectralKernel` — `SAP.P004a.Defs.Part2:170`
- `SAP.P004a.starBlockKernel` — `SAP.P004a.Defs.Part2:117`
- `SAP.P004a.starBlockTable` — `SAP.P004a.Defs.Part2:96`
- `SAP.P004a.starBlockTable._proof_2` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starKernel` — `SAP.P004a.Defs.Part2:109`
- `SAP.P004a.starKernel._proof_1` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starNegativeVector` — `SAP.P004a.Defs.Part2:112`
- `SAP.P004a.starPD` — `SAP.P004a.Defs.Part2:114`
- `SAP.P004a.starPD._proof_1` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starPoint` — `SAP.P004a.Defs.Part2:137`
- `SAP.P004a.starPopulation` — `SAP.P004a.Defs.Part2:142`
- `SAP.P004a.starPopulation._proof_1` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starPopulation._proof_2` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.starY` — `SAP.P004a.Defs.Part2:94`
- `SAP.P004a.studentCDF` — `SAP.P004a.Defs.Part2:166`
- `SAP.P004a.studentDensity` — `SAP.P004a.Defs.Part2:162`
- `SAP.P004a.studentQuantile` — `SAP.P004a.Defs.Part2:168`
- `SAP.P004a.uniformDistanceKernel` — `SAP.P004a.Defs.Part2:156`
- `SAP.P004a.variance` — `SAP.P004a.Defs.Part1:155`
- `SAP.P004a.wholeSandwich` — `SAP.P004a.Defs.WholeW2:20`

### SAP.P004a.T9 dependency entries

- `SAP.P004a.Assignment` — `SAP.P004a.Defs.Part1:15`
- `SAP.P004a.BigOp` — `SAP.P004a.Defs.Part1:196`
- `SAP.P004a.InProb` — `SAP.P004a.Defs.Part1:165`
- `SAP.P004a.LittleOp` — `SAP.P004a.Defs.Part1:168`
- `SAP.P004a.LogisticConditions` — `SAP.P004a.Defs.Part1:21`
- `SAP.P004a.Overlap` — `SAP.P004a.Defs.Part1:102`
- `SAP.P004a.T8StudentComparison._proof_1` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T8UncappedWhole._proof_6` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T9AlgebraWhole` — `SAP.P004a.Defs.WholeW2:161`
- `SAP.P004a.T9LikelihoodWhole` — `SAP.P004a.Defs.WholeW2:143`
- `SAP.P004a.T9LikelihoodWhole._proof_1` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T9LimitLaws` — `SAP.P004a.Defs.WholeW2:185`
- `SAP.P004a.T9ModelWhole` — `SAP.P004a.Defs.WholeW2:131`
- `SAP.P004a.T9TailsWhole` — `SAP.P004a.Defs.WholeW2:171`
- `SAP.P004a.T9TailsWhole._proof_1` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T9TailsWhole._proof_2` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T9TailsWhole._proof_3` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.T9WholeStatement` — `SAP.P004a.Defs.WholeW2:197`
- `SAP.P004a.angularFraction._proof_2` — `SAP.P004a.Defs.Part2:0`
- `SAP.P004a.armCount` — `SAP.P004a.Defs.Part2:27`
- `SAP.P004a.bit` — `SAP.P004a.Defs.Part1:19`
- `SAP.P004a.boundaryLeading` — `SAP.P004a.Defs.WholeW2:128`
- `SAP.P004a.boundaryLeading._proof_1` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.boundaryLikelihood` — `SAP.P004a.Defs.WholeW2:126`
- `SAP.P004a.boundaryMLE` — `SAP.P004a.Defs.Part2:176`
- `SAP.P004a.boundaryO` — `SAP.P004a.Defs.WholeW2:122`
- `SAP.P004a.boundaryParameterSet` — `SAP.P004a.Defs.WholeW2:124`
- `SAP.P004a.boundaryParameterSet._proof_1` — `SAP.P004a.Defs.WholeW2:0`
- `SAP.P004a.boundaryRemainder` — `SAP.P004a.Defs.WholeW2:129`
- `SAP.P004a.boundarySignSum` — `SAP.P004a.Defs.WholeW2:125`
- `SAP.P004a.boundaryTheta` — `SAP.P004a.Defs.WholeW2:123`
- `SAP.P004a.coin` — `SAP.P004a.Defs.Part1:115`
- `SAP.P004a.designWeight` — `SAP.P004a.Defs.Part1:117`
- `SAP.P004a.dot` — `SAP.P004a.Defs.Part1:17`
- `SAP.P004a.expect` — `SAP.P004a.Defs.Part1:120`
- `SAP.P004a.information` — `SAP.P004a.Defs.Part1:138`
- `SAP.P004a.logistic` — `SAP.P004a.Defs.Part1:105`
- `SAP.P004a.logisticScore` — `SAP.P004a.Defs.Part2:180`
- `SAP.P004a.normalCDF` — `SAP.P004a.Defs.Part1:200`
- `SAP.P004a.prob` — `SAP.P004a.Defs.Part1:162`
- `SAP.P004a.propensities` — `SAP.P004a.Defs.Part1:107`
- `SAP.P004a.threeTypeTheta._proof_1` — `SAP.P004a.Defs.Part1:0`

### SAP.P004a.T10 dependency entries

- `SAP.P004a.Assignment` — `SAP.P004a.Defs.Part1:15`
- `SAP.P004a.BigOp` — `SAP.P004a.Defs.Part1:196`
- `SAP.P004a.InProb` — `SAP.P004a.Defs.Part1:165`
- `SAP.P004a.LittleOp` — `SAP.P004a.Defs.Part1:168`
- `SAP.P004a.LogisticConditions` — `SAP.P004a.Defs.Part1:21`
- `SAP.P004a.Overlap` — `SAP.P004a.Defs.Part1:102`
- `SAP.P004a.T10Statement` — `SAP.P004a.Defs.Part4:25`
- `SAP.P004a.bit` — `SAP.P004a.Defs.Part1:19`
- `SAP.P004a.coin` — `SAP.P004a.Defs.Part1:115`
- `SAP.P004a.designWeight` — `SAP.P004a.Defs.Part1:117`
- `SAP.P004a.dot` — `SAP.P004a.Defs.Part1:17`
- `SAP.P004a.expect` — `SAP.P004a.Defs.Part1:120`
- `SAP.P004a.information` — `SAP.P004a.Defs.Part1:138`
- `SAP.P004a.logistic` — `SAP.P004a.Defs.Part1:105`
- `SAP.P004a.logisticScore` — `SAP.P004a.Defs.Part2:180`
- `SAP.P004a.prob` — `SAP.P004a.Defs.Part1:162`
- `SAP.P004a.propensities` — `SAP.P004a.Defs.Part1:107`
- `SAP.P004a.threeTypeTheta._proof_1` — `SAP.P004a.Defs.Part1:0`
