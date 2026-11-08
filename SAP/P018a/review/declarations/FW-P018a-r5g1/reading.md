# Blind reading

This file was completed before opening `claims.json` or `record.json`.
Sources: the complete closure inventory in `closure.json`, the five docstrings
in `Challenge/Part1.lean`, and all their source definitions. The 97 generated
declarations with line 0 were also printed and inspected using
`scratch/ClosurePrint.lean`; the output is `scratch/closure-print.txt`. They are
numeric/index-bound proofs, measure instances, overlap decidability, and the
recursor/matcher for the finite sign average. None adds a statistical assumption.

## Common notation, fully unfolded

This notation is used in each of the five sections below, not as an additional
assumption. A vector of dimension k is a function `Fin k → ℝ`; a matrix is a
function `Fin k → Fin k → ℝ`. Inner products are finite sums `Σa x_a y_a`,
outer products have entry `x_a y_b`, and matrix products/matrix-vector products
are the corresponding finite sums. `sandwich P M` means `P M P` (there is no
transpose in this definition; the breads used here are symmetric).

For a natural N, the dyads are all two-element subsets of `{0,...,N-1}`.
Their endpoints are their actual minimum and maximum. There is no default
endpoint: existence follows from cardinality two. Two dyads overlap if their
intersection is nonempty, including equality; a neighbor is a distinct
overlapping dyad. All double sums over overlapping dyads are ordered and include
each diagonal once. Write `D=N(N-1)/2`, where both subtractions are real
subtractions after casting N, not truncated natural subtraction. For scores q_d,
the meat is `Σd,f: d∩f≠∅ q_d q_fᵀ`.

A kernel comprises a measurable-space type U, a measure μ on U, a function
`X:U×U→ℝ^k`, and `Y:U×U→ℝ`. The sample law P_N is the finite product μ^N
on functions `Fin N → U`: its coordinates are independent draws, including in
every example below. Put

* `Q=E_{μ⊗μ}[XXᵀ]`, `β=Q⁻¹ E[XY]`, `e(u,v)=Y(u,v)-X(u,v)ᵀβ`,
  `q(u,v)=X(u,v)e(u,v)`, `S=Σd q_d`;
* `G=Σd X_d X_dᵀ`, `βhat=G⁻¹Σd X_dY_d`, `r_d=Y_d-X_dᵀβhat`,
  `Vhat=G⁻¹(Σoverlap X_dr_d r_fX_fᵀ)G⁻¹`;
* `H=E[qqᵀ]`, `g(u)=∫q(u,v)dμ(v)`, `Γ=E[g gᵀ]`,
  `V_N=(N/D²)Q⁻¹ Var(S) Q⁻¹`, `V_*=4Q⁻¹ΓQ⁻¹`.

Every vector/matrix expectation is the coordinatewise real Bochner integral.
`Cov(f,g)_{ab}=∫(f_a-∫f_a)(g_b-∫g_b)` and `Var(f)=Cov(f,f)`.
Real scalar `ProbabilityTheory.variance` is the extended integral of the
squared centered norm followed by `toReal`; under square integrability it is
the ordinary variance.

`Standing K` means, in this exact conjunction: μ is a probability measure;
X and Y are measurable on U×U; X and Y are symmetric at every pair; a single
finite nonnegative C bounds both `‖X‖` and `|Y|` μ⊗μ-almost everywhere;
there is an index j in `Fin k` for which `X_j(u,v)=1` everywhere; and `det Q≠0`.
It does not impose conditional mean zero. The vector norm here is the usual
finite-function sup norm; the matrix norm used for convergence is the finite
entry sup norm.

For these varying sample spaces, convergence in probability of f_N to zero
means: for every real ε>0, `P_N{ε≤‖f_N‖}.toReal → 0`. Weak convergence to ν
means each f_N is almost-everywhere measurable, ν is a probability measure,
and for every bounded continuous real h, `∫h(f_N)dP_N → ∫h dν`.
A centered normal law of covariance V means V is positive semidefinite, ν is
a probability measure, and every contrast c has pushforward
`gaussianReal 0 (cᵀVc).toNNReal`. Mathlib's second Gaussian parameter is variance.

The full design sigma algebra is the comap of `ω↦(d↦X_d(ω))` from the Borel
sigma algebra on the finite array. Write `m_d=E[e_d|X]` and
`C_df=E[(e_d-m_d)(e_f-m_f)|X]`. The conditional term is
`A_df=E[C_df X_dX_fᵀ]`; the printed middle factor is `Σoverlap A_df`.

A repeated kernel has a measure μ, deterministic natural counts T(N,d), and
record functions X_{Ndt}(u,v),Y_{Ndt}(u,v) for `t<T(N,d)`. Samples still use
independent units with law μ^N. Set `L=Σd T(N,d)`,
`G_R=Σdt X_dtX_dtᵀ`, `b_R=(E G_R)⁻¹ EΣdt X_dtY_dt`,
`H_R=L⁻¹ E G_R`, and `q_d=Σt X_dt(Y_dt-X_dtᵀb_R)`.
Its target is `(N/L²)H_R⁻¹ Var(Σd q_d) H_R⁻¹`.
With fixed real record weights w_dt, replace each summand of G_R and XY by
w_dt times that summand, define b_w using these weighted expected equations,
and q_d by the weighted residual score sum. The weighted normalized Gram is
`H_w=D⁻¹ E G_w`; its target is `(N/D²)H_w⁻¹Var(Σd q_d)H_w⁻¹`.
For a single record and dyad weights, these reduce to weighted Gram
`Σd w_dX_dX_dᵀ` and its analogous population coefficient.
`RepeatedAtSize R N` requires a probability μ, every T(N,d)>0, measurable
record kernels, and one finite nonnegative almost-everywhere bound at that N
for every record's X and Y. It does not require equal counts, equal kernels,
positive weights, or a uniform bound over N.

## SAP.P018a.T1

There are no theorem arguments or hypotheses. The statement is a conjunction
about the fixed model μ=uniform[-1,1], `X(z,t)=(1,2+z+t)`, `Y(z,t)=(z+t)²`.
The uniform law is Lebesgue measure restricted to [-1,1] and divided by 2.

It asserts Standing, and for every natural N≥3, almost-sure `det G≠0`.
The population values are
`Q=[[1,2],[2,14/3]]`, `det Q=2/3`, `β=(2/3,0)`,
`H=[[28/45,56/45],[56/45,3448/945]]`, and
`Γ=[[4/45,8/45],[8/45,632/945]]`. Γ is positive definite and
`det Γ=1184/42525`. The residual formula `e(z,t)=(z+t)²-2/3`
holds for all real z,t, even outside the support. For z,t∈[-1,1] it asserts
`0≤2+z+t≤4`, `0≤Y≤4`, and `-2/3≤e≤10/3`.
Also `E[XY]=(2/3,4/3)`.

For every N≥3 and every dyad d, the conditional expectation of Y_d given its
own row X_d equals `(X_{d,1}-2)²` almost surely. There exists no b∈ℝ²
such that `Y=Xᵀb` μ⊗μ-almost everywhere. Each score has zero mean (with
both `E e_d=0` and `E[X_{d,1}e_d]=0` separately asserted). Disjoint score
cross-moments vanish; distinct overlapping score cross-moments equal Γ.

For every N≥3, every d,f has `C_df=0` almost surely, the sparse printed
factor and also the full sum `Σd,f A_df` are zero. The repeated conditional
factor with one record per dyad and the weighted conditional factor with
every weight 1 are zero as well. In the repeated definition conditioning is
on the entire stacked design and all record pairs are summed; in the
weighted definition both external weights multiply the conditional
residual covariance. The actual score covariance is nonzero and equals
`D H+N(N-1)(N-2)Γ`. It also equals the explicit matrix with entries
`2N(N-1)(2N+3)/45`, `4N(N-1)(2N+3)/45` off the diagonal, and
`4N(N-1)(158N+115)/945` bottom right. At N=3 it equals
`[[12/5,24/5],[24/5,4712/315]]`.

The variance limits are `(N/D²)Var(S)→4Γ`, `V_N→V`, where
`V=[[3664/315,-592/105],[-592/105,296/105]]=4Q⁻¹ΓQ⁻¹`.
V is positive definite and `det V=4736/4725`. There exists a centered normal
probability law ν of this covariance with `sqrt(N)(βhat-β)⇒ν`, and
`N Vhat-V→0` in probability. Finally, for every z∈ℝ³, the determinant of
the two design rows `(1,2+z0+z1)` and `(1,2+z0+z2)` is z2-z1.

Junk conventions: all real fractions with constant denominators are safe.
D=0 at N=0,1; the target and estimator then use real inverse-of-zero and
singular-matrix zero completions. All asserted finite-sample inverse and
covariance identities use N≥3; the limits ignore these initial sizes.
Sample inverses at N≥3 are ordinary inverses almost surely, with zero on
null singular sets. Population Q is explicitly nonsingular. All integrands
are bounded on the support; conditional expectations use valid sub-sigma
algebras of probability spaces, so their zero fallback for invalid sigma
algebras, nonsigmafinite restrictions, or nonintegrability is not invoked.
The conditional covariances vanish because the responses are measurable
functions of the regressors. `toReal` is applied to finite probabilities.
`sqrt N` has nonnegative input; the normal covariance is explicitly positive
definite, so `toNNReal` does not discard a negative variance. No sInf/sSup,
log, rpow, natural truncated subtraction, or partial-function default occurs.

## SAP.P018a.T2

The first parts are universal: for every measurable-space type U, natural k,
and kernel K satisfying Standing, all the following hold. For every N≥2:

* The population score mean and every sampled dyad score mean are zero;
  disjoint raw cross-moments are zero.
* `Var(S)=E[Σoverlap q_dq_fᵀ]=D H+N(N-1)(N-2)Γ`.
* With `M=Var(Σd X_dm_d)`, `Var(S)=Σd,f A_df+M`, M is positive
  semidefinite, and equality without M holds if and only if M=0.
  `Var(S)-Σoverlap A_df=M+Σdisjoint A_df`.
* `E[S|X]=Σd X_dm_d` almost surely, M is also `Var(E[S|X])`, and
  `Σd,f A_df=E[Var(S|X)]`, with conditional covariance defined entrywise
  by conditional expectation of centered score products. Thus the full
  law of total covariance is explicitly asserted.
* The corrected meat is the diagonal-plus-distinct-neighbor sum both of
  `E[e_de_f X_dX_fᵀ]` and of `E[E[e_de_f|X]X_dX_fᵀ]`.
  The equal-dyad moment is H; the distinct overlapping moment is Γ.
* `V_N=Q⁻¹[(2/(N-1))H+(4(N-2)/(N-1))Γ]Q⁻¹`, and the corrected
  overlap-meat sandwich equals V_N. Conditional zero means for all e_d
  imply M=0.

Γ is symmetric positive semidefinite, and `V_N→4Q⁻¹ΓQ⁻¹`.
There exists a kernel on ℝ with two regressors and a natural N≥2 satisfying
Standing, every sampled score mean zero, but M≠0. This existence is
unconditional and is separate from the preceding universal quantifiers.

The repeated part universally quantifies U,k,N,R, then assumes k≥1, N≥2,
and RepeatedAtSize at N. If `det H_R≠0`, its conclusions hold; separately,
for every fixed real record weight array w, if `det H_w≠0`, the weighted
conclusions hold. In each case all block score coordinates are square
integrable, and scores of disjoint dyads are independent. Write
`B=Σoverlap Cov(q_d,q_f)`, `R0=Σoverlap E[q_dq_fᵀ]`,
`F0=Σall E[q_dq_fᵀ]`, and `M0=Σoverlap (E q_d)(E q_f)ᵀ`.
The conclusions are
`E S=0`, `Var(S)=F0=B=R0-M0`, `R0=Var(S)+M0`,
`R0=Var(S) iff M0=0`, and `Σd E q_d=0`.
If every block score is centered, R0=Var(S).
The expectation of the normalized sample Gram equals H_R or H_w.
The targets equal their sparse-covariance sandwiches and the covariance of
`H⁻¹(sqrt(N)/L)S` or `H⁻¹(sqrt(N)/D)S`, respectively. L>0 is also asserted
in the unweighted case. There is no assertion of fitted-residual consistency.

Finally there exists R on the one-point type with k=1 at N=4, satisfying
RepeatedAtSize and `det H_R≠0`, for which `E S=0`, `Var(S)=0`, but
`R0=M0=[[2]]`. Neither common record functions nor a bound over all N
is imposed on this existential in the statement.

Junk conventions: the real denominators D,N-1,L are nonzero in these
finite claims. The expected Gram determinants exclude singular population
breads even with negative or zero weights. No sample Gram inverse is needed
for these covariance assertions. k≥1 excludes the empty-dimensional
repeated branch, and Standing excludes k=0 in the single-record branch
through existence of an intercept. Finite record sets and bounded kernels
give finite moments at each N. All conditional quantities condition on
measurable full-design arrays in probability spaces, so conditional
expectation's invalid-input defaults are excluded. Events in probability
limits have finite measure. No unsupported log, sqrt, toReal-of-infinity,
sInf/sSup, truncated subtraction, or default endpoints affect the statement.

## SAP.P018a.T3

This is an unconditional conjunction of fixed examples and universal finite
identities. First take independent fair signs z_i∈{-1,1}, k=1, X_d=1,
Y_d=z_i+z_j. Put S_z=Σi z_i, and let Mhat be the actual fitted meat and
vhat the actual scalar sandwich defined in the common notation.

Standing, eventual almost-sure sample rank, and `Proposition1Extra` hold.
The latter means: a uniform almost-sure fitted-residual bound for every N;
every entry of Q and of `E[X01 X02ᵀ]` is nonzero; eventually every fitted
residual second moment and every distinct overlapping fitted residual
cross-moment is nonzero. The population coefficient is 0 and Q=[[1]].
For every N≥4 and every sample, `G=[[D]]`, D>0,
`βhat=2S_z/N`, `e_d=Y_d`, `r_ij=z_i+z_j-2S_z/N`, and `|r_d|≤4`.
`Var(Σd e_d)=printedSigma=[[N(N-1)²]]`, and V_N=[[4]].

For every natural N and every real array r indexed by dyads,
`Σoverlap r_dr_f=Σi(Σd:i∈d r_d)²-Σd r_d²`.
For every N≥4 and every sample:
`Mhat=(N-2)(N-3)(N-S_z²/N)`, `vhat=Mhat/D²`, and
`N vhat=[4(N-2)(N-3)/(N-1)²](1-S_z²/N²)`.
Its expectations are
`E Mhat=(N-1)(N-2)(N-3)` and
`E vhat=4(N-2)(N-3)/(N²(N-1))`.
`E Mhat-N(N-1)²=(-4N+6)(N-1)` tends to minus infinity, whereas
`(N/D²)` times that error is `(-16N+24)/(N(N-1))` and tends to zero.
`E[N vhat]=4(N-2)(N-3)/(N(N-1))→4`, while `E vhat-4→-4`.
`N vhat→4` in probability.

For every N, `E S_z⁴=3N²-2N` and `Var(S_z²)=2N(N-1)`.
For every N≥4,
`Var(N vhat)=32(N-2)²(N-3)²/[N³(N-1)³]→0`.
For every N and four real coefficient arrays a,b,c,d,
`Cov((a·z)(b·z),(c·z)(d·z))=(a·c)(b·d)+(a·d)(b·c)-2Σi a_i b_i c_i d_i`.

For every N≥6, the four actual dyads 01,02,34,35 are distinct; the
endpoint union of the first two is disjoint from that of the last two;
each pair overlaps. Actual fitted products have covariance
`Cov(r01 r02,r34 r35)=16(N+6)/N³>0`, while the corresponding products
of population residuals have covariance zero. At N=8 the actual fitted
residual for each distinct i,j is `z_i+z_j-(Σl z_l)/4`.
The recursively defined `fairAverage 8` averages all 2^8 sign assignments
with equal weights. For arbitrary real f,g of eight real coordinates, its
raw-moment covariance equals their ordinary covariance under the fair-sign
product law. The displayed values include
`Cov(r01 r02,r34 r35)=7/16`, the population counterpart 0, and
`Cov(r01 r02,r03 r04)=-1/16`.

The deterministic example uses the one-point probability measure and the
constant unscaled estimator 1 and target 1. Its unscaled expectation error
and the variance of N times it are zero for every N, but `N-1` neither
tends to zero nor converges in probability to zero.

For every N≥1 the spike law `P_N=(1/N)δ_N+(1-1/N)δ_1` is a probability
measure. With coordinate x, `x-1→0` in probability,
`E x=2-1/N→2`, and `Var x=N-3+3/N-1/N²→+∞`.

The inverse example uses the probability density `1_{t≥1}/t²` with respect
to real Lebesgue measure, `X(u,v)=(1,exp(-u)+exp(-v))`, Y=0. Standing
holds; `det Q=2Var(exp(-T))>0`. The inverse of the normalized sample
Gram converges in probability to Q⁻¹. For every N≥3 it is almost surely
nonsingular and, for every natural m≥1, its extended expected Euclidean
operator norm is at least `exp(2m)/(4m^N)` and equals infinity. A redundant
weaker conjunct says there exists N0≥3 with these conclusions for N≥N0.
The norm definition is `sup{sqrt(Σa(Mx)_a²):Σa x_a²≤1}`, a supremum
in the real numbers. It is the operator norm of a finite real matrix.

Junk conventions: every finite-sample formula with denominators N,D,N-1
is guarded by N≥4; the all-size sign-sum identities use no denominator.
The recursor at zero averages the single empty assignment. The singular
matrix zero completion is used at small sizes and possibly null events;
rank is asserted where inverses matter. The spike definition at N=0 gives
δ_1 via real 0⁻¹=0; all displayed spike moment formulas require N≥1,
so that harmless initial value cannot affect a limit. The Pareto density's
t⁻¹ is only used on t≥1. Its exp transforms and X are bounded on support.
The operator-norm supremum has a nonempty defining set (x=0) and is bounded
above for every finite matrix, including singular completions. Its square
root is always applied to a sum of squares. The inverse norm has genuinely
infinite *extended* integral: no `toReal ∞=0` is used for this conclusion.
Inverse convergence is in probability and does not require this expectation
finite. The finite sign/spike moments are defined and finite at every
relevant N. No log, rpow, limsup/liminf, or truncated subtraction occurs.

## SAP.P018a.T4

Three universal statements are conjoined, with no external hypotheses.

1. For every measurable U, k, and K satisfying exactly Standing as unfolded
   above, `N Vhat-V_N→0` in probability under the independent-unit sample
   laws. This is absolute consistency for the unconditional score target;
   there is no conditional-centering, positive Γ, sample-rank, or fitted
   residual bound hypothesis.
2. For every measurable Ω, probability measure μ, square-integrable real
   random variable Z, every real V, and every real c>0,
   `μ{|Z-V|>c}.toReal ≤ c⁻²[Var Z+(E Z-V)²]`.
3. For every sequence of measurable spaces Ω_N, probability laws μ_N, and
   square-integrable Z_N, and then every fixed real V, if `E Z_N-V→0`
   and `Var Z_N→0`, then for every c>0,
   `μ_N{|Z_N-V|>c}.toReal→0`.

Junk conventions: the sample/poulation inverse and N=0,1 conventions are
as in the common notation. Standing excludes a singular population Gram;
the consistency limit ignores small N, and eventual high-probability rank
follows from Gram convergence rather than being assumed. The single-time
inequality has c>0, excluding division by zero, and MemLp exponent 2
excludes undefined expectations and variance's infinite-toReal fallback.
All tail measures are finite probabilities. The last statement uses the
strict tail event `c<|Z_N-V|`; the earlier inProbability definition uses
the closed tail, an equivalent convergence criterion. No domain problem
with sqrt/log/rpow, no sInf/sSup, no natural truncated subtraction or
partial-function default affects this statement.

## SAP.P018a.T5

Three statements are conjoined. The first two are fixed finite matrix
calculations, not random-effect derivations.

Use dyad order 01,02,12. The first-role incidence rows are (1,0,0),
(1,0,0),(0,1,0); the second-role rows are (0,1,0),(0,0,1),(0,0,1).
`C(τ,σ)=τ(Z1+Z2)(Z1+Z2)ᵀ+σI`, and
`W(t1,t2,s)=t1 Z1Z1ᵀ+t2 Z2Z2ᵀ+sI`.
For every three reals t1,t2,s,
`C(1,1)=[[3,1,1],[1,3,1],[1,1,3]]`,
`W=[[t1+t2+s,t1,0],[t1,t1+t2+s,t2],[0,t2,t1+t2+s]]`, and C(1,1)≠W.
The inequality therefore holds in particular for variance parameters ≥0.

Set `F=[[1,1],[1,3],[1,2]]`,
`Winv=(1/21)[[8,-3,1],[-3,9,-3],[1,-3,8]]`,
`R=(1/16)[[71,-27],[-27,15]]`, and
`L=[[19/16,-13/16,5/8],[-7/16,9/16,-1/8]]`.
It asserts `Winv W(1,1,1)=I`, `R(FᵀWinv F)=I`,
`R FᵀWinv=L`, `LF=I`,
`L C(1,1)Lᵀ=(1/64)[[379,-135],[-135,67]]`,
and `R00/(L C Lᵀ)00=284/379<1`.

The final statement quantifies in order: any measurable Ω, probability
measure μ, natural N≥1, independent family `(a_i)_{i<N}` of random real
variables each with law `gaussianReal 0 1`; then a natural D, response
map `yc:Ω→ℝ^D` and function `estimate:ℝ^D→ℝ`. Assume estimate is
translation equivariant for *all* y,c:
`estimate(y+c·1_D)=estimate(y)+c`. Assume yc is independent of
`abar=(Σi a_i)/N`, estimate is measurable, and both
`estimate(yc)` and `estimate(yc+2 abar·1_D)` are square integrable.
Then
`Var(estimate(yc+2 abar·1_D))=Var(estimate(yc))+4/N`, hence it is at
least 4/N. No particular design is linked to yc and no Gaussian
average/centered-response independence is derived in this statement.

Junk conventions: the fixed finite matrix constants have nonzero denominators;
the reported ratio has positive denominator 379/64. The matrix calculations
use explicit matrices and multiplication, not an unguarded symbolic matrix
inverse. N≥1 ensures N≠0. `HasLaw` includes almost-everywhere
measurability of the a_i, and both estimator moments are explicitly finite.
The usual measurability convention applies to yc, which is not given a
separate explicit measurability hypothesis. No real scalar variance can
use its infinity-toReal fallback under these hypotheses. D=0 is permitted
as a natural, but no translation-equivariant real estimate on the empty
vector space satisfies the stated equality for all c; D=1 provides
nonempty satisfiable instances. This empty-index branch does not trivialize
the other branches or finite matrix assertions. There are no sqrt/log/rpow,
sInf/sSup, truncated-subtraction or partial-function-default issues.
