# Blind reading

Saved before reading `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. This is a reading of the current statements, not a
comparison with their intended claims. Source line numbers below refer to the
current files. `scratch/BlindCheck.lean` prints the elaborated statements and
all auto-generated proof declarations in the supplied closures.

The common probability notation is fully expanded here. For a probability
measure μ, `prob μ A` is `(μ A).toReal`. For measurable events this is their
ordinary real-valued probability. `CP μ Z c` says that for **every** real ε>0,
the real probabilities μ{ω : ε ≤ dist(Z_n(ω),c)} tend to zero as n→∞. On ℝ
this distance is absolute difference; on `Fin k → ℝ` it is the maximum of
the coordinatewise absolute differences. `IID μ X` is the conjunction of
measurability of every X_i, Mathlib's mutual independence `iIndepFun X μ`,
and equality of the distributions of X_i and X_0 for every i (including the
almost-everywhere measurability built into `IdentDistrib`). `firstSample X n ω`
is the function i↦X_i(ω), i∈Fin n, so the observations are 0 through n−1.

The closure's generated proofs have also been read: the various `_proof_1`
and `_proof_2` terms are instances certifying nonzero finite cardinalities,
numeral denominators, scalar towers, and an outer-measure class, or the
implication v>0 ⇒ v≥0 used in the Gaussian variance subtype. None adds a
statistical assumption. `instDecidable_sAP` is classical proposition
decidability, used in ordinary if expressions and finite sums.

## SAP.P001g.T121

Sources: `Challenge/Part1.lean:44–56`, `Defs/WholeW2.lean:15–92`, and common
definitions `Defs/Part1.lean:18,26–28,35–37,62–63`.

Put a=√2/4 and c=1−√2/2. The outcome space is the finite discrete space
{0,1,2}. Its fixed first component is q=(a,a,c). A second component indexed
by b=(b₀,b₁) on the Euclidean circle b₀²+b₁²=1 is

    A(b)=(a+b₀/10, a+(b₁−b₀)/10, c−b₁/10).

The full parameter is t=(p,b₀,b₁)∈ℝ³ with 0≤p≤1 and b₀²+b₁²=1; call this
set Θ. Its outcome masses are m_t(y)=p q_y+(1−p)A(b)_y. The designated true
parameter t_b is (1,b₀,b₁), and hence all such true parameters have the same
outcome law q. The sample likelihood for s:Fin n→Fin 3 is the actual
product L_s(t)=∏_{i∈Fin n}m_t(s_i).

An estimator is an entire collection T_n:(Fin n→Fin 3)→ℝ³. The property
`CircleMLEW2 T` requires, for **every** natural n and **every** possible
sample s, (1) T_n(s)∈Θ, (2) L_s(t)≤L_s(T_n(s)) for every t∈Θ, and (3) if
n>0, every t∈Θ with equal likelihood is exactly T_n(s). Thus the maximum
must be attained and unique at every positive sample size, not merely almost
surely. At n=0 only attainment and membership are required. The extra closed
disc declaration encountered through a generated finite-index proof is
{z∈ℝ²:z₀²+z₁²≤1}; the affine formula A is defined on all ℝ² even though its
PMF interpretation is on the disc/circle.

The theorem is the **negation** of the following universally quantified
statement, in this order: for every measurable space Ω in universe u,
probability μ on Ω, sequence X_i:Ω→Fin 3 with the IID property, every
b∈ℝ² on the circle for which

    μ.map X_0 = Σ_{y∈Fin 3} ofReal(m_{t_b}(y)) · dirac_y,

and every estimator collection T satisfying `CircleMLEW2`, the vector
T_n(firstSample X n ω) converges in probability to t_b. In classical
mathematics, its negation gives some Ω, μ, IID X, circle b, correct true law,
and globally unique-maximizing T with failure of this convergence. It does
not just assert absence of an estimator. The docstring describes this as a
counterexample to a printed consistency-and-efficiency assertion without
full-vector identification.

Junk conventions: √2 has a positive argument; divisions by 4, 2, and 10
are by fixed nonzero reals. `ofReal` would truncate negative numbers to
zero, but these mixtures on Θ have strictly positive coordinates (the
circle coordinates are bounded by one) and masses sum to one, so it
does not alter them. `toReal ∞=0` is excluded by the probability hypotheses.
All relevant events and statistics are measurable: each finite-sample
domain is finite discrete, and X_i are measurable. The empty product at
n=0 is 1, and Fin 0 has one empty sample; uniqueness is deliberately not
required there. Fin 3 and Fin 2 are nonempty. The theorem uses neither logs,
argmax choice defaults, infima/suprema, nor limsup/liminf. `IsMaxOn` means
the displayed inequalities, not a partially defined maximizing operator.
There is no nonintegrable mean in this statement.

## SAP.P001g.T124

Sources: `Challenge/Part1.lean:58–60`, `Defs/Part7.lean:13–74`,
`Defs/Part3.lean:44–60`, and `Defs/Part1.lean:13,18,35–37,54–60`.

The underlying space is Ω=ℕ→Fin 12, with its product σ-algebra. For a cell
j∈{0,…,11}, define

    x_j = −1 if floor(j/4)=0; 0 if floor(j/4)=1; 1 otherwise,
    z_j = −1 if (j mod 4)<2; 1 otherwise,
    d_j = 1 if (j mod 2)=1; 0 otherwise,
    w_j = x_j²+z_j/2,
    R_j=(1,x_j), F_j=(1,x_j,w_j).

These are three x levels crossed with two z levels and two d levels.
The X and W variables in the statement are one-dimensional real vectors
(functions on Fin 1), not scalars of an unspecified dimension.

For real weights q_j, G_H(q) has entries Σ_j q_j H_{ja}H_{jb};
c_H(q)_a=Σ_j q_j H_{ja}d_j; β_H(q)=G_H(q)⁻¹c_H(q); and
r_H(q)=Σ_j q_j(d_j−Σ_a H_{ja}β_H(q)_a)². Here the inverse is Mathlib's
square-matrix nonsingular inverse and all the sums are finite. For a sample
s:Fin n→Fin 12, q_j(s)=#{i:s_i=j}/n. `placeboGood s` means n>3,
det G_R(q(s))≠0, det G_F(q(s))≠0, and r_F(q(s))>0.

The unnormalized regression statistic is obtained by constructing the
n-row restricted design (1,x_{s_i}) and full design (1,x_{s_i},w_{s_i}),
computing β=(HᵀH)⁻¹Hᵀd and RSS=Σ_i(d_{s_i}−(Hβ)_i)² for each, then

    F(s)=[(RSS_R−RSS_F)/1]/[RSS_F/(n−3)].

The reference measure for natural k,v is the pushforward of the product of
k+v independent N(0,1) coordinates by

    [Σ_{i<k}z_i²/k]/[Σ_{k≤i<k+v}z_i²/v].

The theorem asserts existence of a measure μ on Ω and real critical values
c_n, in that order, with all of these conjunctions:

1. μ is a probability measure.
2. The triples (X_i,W_i,D_i)=((x_{ω_i}),(w_{ω_i}),d_{ω_i}) are measurable,
   mutually independent, and identically distributed across i.
3. There exists a proof of measurability of X_0 and, for every measurable
   A⊆ℝ¹ and B⊆ℝ, the conditional expectation given σ(X_0) of
   1_{W_0∈A,D_0∈B} equals almost surely the product of the two conditional
   expectations of 1_{W_0∈A} and 1_{D_0∈B}. This is conditional independence
   of W_0 and D_0 given X_0, not unconditional independence.
4. Every D_i at every ω equals 0 or 1.
5. For μ-almost every ω, all sufficiently large samples are good as defined
   above.
6. For every n>3 the reference F(1,n−3) law assigns probability exactly 1/2
   to (−∞,c_n]. Values c_n for n≤3 are unconstrained.
7. The probability of {good sample and c_n<F(sample)} tends to 1.

There is no prescribed cell law, no full-support premise, no linear CEF
premise, and no homoskedastic regression premise. The docstring calls this
a refutation of a nominal-half-level conditional-independence placebo test.

Junk conventions: natural division/modulo in the cell coding are by fixed
positive integers, with the ordinary integer quotient/remainder meaning.
Empirical frequencies at n=0 are 0 because real 0/0=0. A singular matrix
has inverse 0 in Mathlib, but good samples explicitly exclude singularity
for both normalized Grams; n>3 relates these to the ordinary sample Grams.
The statistic is total even if n≤3 or RSS_F=0, but those cases never count
as rejections. Its n−3 denominator is real subtraction, positive on good
samples. The reference degrees n−3 use **natural truncated subtraction**,
but are used in the quantile condition only when n>3. For such n, k=1 and
v=n−3 are positive and the Gaussian denominator vanishes only on a null
set. Thus the totalized real division at that null set does not change the
reference law. Product index types in that use are nonempty. General unused
k=0 or v=0 reference values have no F-law interpretation, but are outside
the quantile clause. μ and the finite products of Gaussians are probability
measures, so `toReal ∞=0` is irrelevant. Conditional expectation defaults
to zero for a nonintegrable input, an invalid sub-σ-algebra, or lack of
σ-finiteness on it; the bounded indicators, probability μ, and measurability
of X exclude all three. Finite-valued X,W,D and sample statistics also
exclude nonmeasurable-event issues. There are no logarithms, roots,
unbounded set extrema, or unspecified partial functions in the statistic.

## SAP.P001g.T125

Sources: `Challenge/Part1.lean:62–64`, `Defs/Part6.lean:16–19`, and
`Defs/Part1.lean:18–20,26–28,35–40`.

For every measurable space Ω (arbitrary universe), every probability μ,
and every sequence X_i:Ω→ℝ, if the sequence is IID in the expanded sense
above and X_0∈L²(μ), then for every ε>0,

    μ{|(Σ_{i=0}^{n−1}X_i)/n − ∫X_0 dμ| ≥ ε} → 0.

`MemLp (X 0) 2 μ` means almost-everywhere strong measurability and finite
L² seminorm; for measurable real X_0 and probability μ it means finite
second moment. It implies integrability, and identical distribution gives
the same for all observations. No strictly positive variance is required.
The docstring states exactly this finite-second-moment weak law.

Junk conventions: n is cast from ℕ to ℝ without loss; at n=0 the empty sum
and division by zero make the sample mean 0. This single value has no
effect on an atTop limit. The Bochner integral is 0 for a nonintegrable
function, but the L² probability hypothesis rules that out here. All events
are measurable and μ is finite, so neither outer-event values nor
`toReal ∞=0` affects the assertion. There are no other partial functions,
roots/logarithms, extrema, limsup/liminf, or arbitrary empty index types.

## SAP.P001g.T126

Sources: `Challenge/Part1.lean:66–68`, `Defs/Part6.lean:21–44`, and
`Defs/Part1.lean:18–24,30–40,75–77`.

The theorem is a conjunction of three **separately universally quantified**
assertions (possibly in three different universes). Each ranges over every
measurable Ω, probability μ, IID sequence X_i:Ω→ℝ, X_0∈L²(μ), and positive
variance v=Var_μ(X_0)>0. Write m=∫X_0dμ and M_n=Σ_{i<n}X_i/n.
The first concludes √n(M_n−m) converges in distribution to N(0,v).
The second concludes Z_n=(M_n−∫M_n dμ)/√Var_μ(M_n) converges in
distribution to N(0,1). The third additionally quantifies over **every**
natural n>0 and asserts the conjunction

    √Var(M_n)=√v/√n,
    ∀ω, Z_n(ω)=√n(M_n(ω)−m)/√v,
    ∫Z_n dμ=0, Var(Z_n)=1, √Var(Z_n)=1.

Each variance here is Mathlib's real variance:

    (∫⁻ω ‖X(ω)−∫X dμ‖ₑ² dμ).toReal.

Each convergence-in-distribution assertion means that **for every** real x
at which the target CDF t↦ν(−∞,t] is continuous, the CDF
μ{Z_n≤x} tends to ν(−∞,x]. `gaussianReal 0 v` uses v as the variance,
not the standard deviation. The target is the usual Gaussian probability
measure; since v>0 it is its Gaussian Lebesgue-density case. The docstring
describes both CLT forms and the finite standardization identity/moments.

Junk conventions: as for T125, M_0=0 by empty sum and real division by
zero; standardizedMean_0 is also zero by 0/0. Finite-n moment assertions
are restricted to n>0 and limits ignore n=0. Finite second moments and
IID imply integrability and finite variance of each M_n; the variance's
`toReal ∞=0` and Bochner nonintegrability defaults do not apply. At positive
n, Var(M_n)=v/n>0, so the standardization denominator is nonzero; all
square roots are of nonnegative reals and √v>0. Negative-argument sqrt
totalization (to zero) is not used. Probability values are finite and the
events measurable. No truncated natural subtraction, general real powers,
empty extrema, or limsup/liminf occurs.

## SAP.P001g.T127

Sources: `Challenge/Part1.lean:70–72`, `Defs/Part6.lean:46–51`, and
`Defs/Part1.lean:18,26–28,35–37,45–47,62–63,82–85`.

For every measurable Ω, probability μ, IID real-valued observations X_i,
every function f:ℝ→ℝ satisfying the following exact PDF definition,

    f is a.e. measurable for Lebesgue measure,
    ∀x, f(x)≥0,
    ∫|f| dx<∞,
    μ.map X_0 = volume.withDensity(x↦ENNReal.ofReal(f(x))),

and globally continuous f, and every deterministic bandwidth sequence
h:ℕ→ℝ with h_n>0 for **all** n (including 0), h_n→0, and n h_n→+∞,
the following holds **for every** real x: the random variables

    fhat_n(x) = (1/n) Σ_{i<n} [(1/(2h_n)) 1_{|(x−X_i)/h_n|≤1}]

converge in probability to f(x). Equivalently the indicator is
|x−X_i|≤h_n, since h_n>0. This is pointwise consistency, not a statement
about a uniform supremum over x. The PDF conditions plus the probability
law imply ∫f=1; no separate normalization assumption is missing. The
docstring states the rectangular-kernel, continuous-density result with
these bandwidth limits.

Junk conventions: `ofReal` would discard negative f, but f≥0 everywhere;
the density is explicitly integrable and continuous. `Measure.map` has no
nonmeasurability default here because IID includes measurability. The
kernel is exactly 1/2 on the closed interval [−1,1] and 0 outside. Its
endpoint choice is well defined and has no population mass under a
density law. Bandwidth division never uses zero, even at n=0. At n=0 the
finite sum is empty and the outer real division makes fhat_0=0; this does
not affect the limit. All sample and kernel events are measurable, μ is
a probability measure, and no expectation is evaluated by a
nonintegrability default. No roots, logs, real powers, truncated subtraction,
empty extrema, or limsup/liminf occur. The only casts are exact natural
counts/sample sizes into ℝ.
