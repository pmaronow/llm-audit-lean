# Blind reading, saved before the claims and review history were opened

This reading uses only `closure.json`, the Challenge/Defs sources, the elaborated
declarations, and Mathlib definitions. All 111 distinct positive-line closure
declarations were also printed in `scratch/ClosureDeclarations.out`; all 41
distinct line-zero helpers were printed in `scratch/ClosureProofs.out`. The latter
are numeral/typeclass evidence, decidability, or nonemptiness evidence and add no
statistical assumptions. Constructors and projections in the closure have their
ordinary structure-field meanings. The source line numbers below refer to the
current files, which sometimes differ from closure.json's recorded lines.

## SAP.P018b.T20

The stub at Challenge/Part1.lean:90 asserts the conjunction at
Defs/WholeW1.lean:482. Its docstring explicitly calls the consistency portion a
restriction, gives two sets of premises C1 and C2, and does not claim equivalence
to an unavailable T10 contract.

Here is all the notation used in the following expansion. A vector is a function
`Fin k → ℝ`; a matrix is a real `Fin k × Fin k` matrix. The inner product is
`sum_a x_a y_a`, and `xy'` means the matrix with entry `x_a y_b`. Matrix products
and matrix-vector products are ordinary finite sums. A sandwich is `P M P`,
without a transpose in the definition. All Gram matrices here are symmetric, so
this agrees with the covariance transformation when the inverse exists.

For a natural number N, units are `Fin N` and dyads are precisely the
two-element subsets of `Fin N` (the subtype of `univ.powersetCard 2`). A dyad's
endpoints are its minimum and maximum. Its member set is that underlying
two-element finite set. Dyads overlap when their intersection is nonempty. Every
double sum below is over **ordered** pairs and includes the diagonal. Write
`D_N=(N:ℝ)((N:ℝ)-1)/2`.

A repeated model consists of a measurable type U, a measure μ on U, a
deterministic natural count `T_Nd`, and functions
`X_Ndt : U × U → ℝ^k`, `Y_Ndt : U × U → ℝ`, for `t : Fin T_Nd`.
The law of a sample `ω : Fin N → U` is the finite product `μ^N`. The observed
record evaluates these functions at `ω_min(d),ω_max(d)`. Set

* `L_N=sum_d (T_Nd:ℝ)`; `G_N(ω)=sum_dt X_Ndt(ω) X_Ndt(ω)'`;
  `q_N(ω)=sum_dt X_Ndt(ω)Y_Ndt(ω)`;
* `β_N=(E G_N)^(-1) E q_N`, and `βhat_N(ω)=G_N(ω)^(-1)q_N(ω)`;
* `b_Nd(β,ω)=sum_t X_Ndt(ω)(Y_Ndt(ω)-X_Ndt(ω)'β)`;
  `S_N=sum_d b_Nd(β_N)`; `H_N=(1/L_N) E G_N`;
* `M(q)=sum_{d,f:d∩f≠∅} q_d q_f'`;
  `Vhat_N=G_N^(-1) M(b_Nd(βhat_N)) G_N^(-1)`;
* `V_N=(N/L_N²) H_N^(-1) Cov(S_N) H_N^(-1)`.

Each expectation is a coordinatewise real Bochner integral.
`Cov(F,G)_ab=integral (F_a-E F_a)(G_b-E G_b)`; `Cov(F)=Cov(F,F)`.
For any deterministic real weights `w_dt`, define
`G_w=sum_dt w_dt X_dt X_dt'`, `q_w=sum_dt w_dt X_dt Y_dt`,
`β_w=(E G_w)^(-1)E q_w`, `βhat_w=G_w^(-1)q_w`,
`b_w,d(β)=sum_t w_dt X_dt(Y_dt-X_dt'β)`,
`S_w=sum_d b_w,d(β_w)`, `H_w=(1/D_N)E G_w`,
`Vhat_w=G_w^(-1) M(b_w,d(βhat_w))G_w^(-1)`, and
`V_w=(N/D_N²)H_w^(-1)Cov(S_w)H_w^(-1)`.

Convergence in probability of a possibly changing-domain random element F_N to
zero means: for **every real ε>0**, the real number
`(μ_N {ω : ε ≤ ‖F_N(ω)‖}).toReal` tends to zero as N tends to infinity.
The norm on these finite coordinate spaces is the Mathlib norm (the matrices use
the elementwise norm scope). Weak convergence means each F_N is a.e.
measurable, the limit law ν is a probability measure, and, for **every bounded
continuous real function g**, `E g(F_N) → integral g dν`.

The eight conjuncts, with quantifier order, are:

1. **Finite unweighted identities.** For every measurable U, every natural k,N
   and repeated model R, assume μ is a probability measure, `T_Nd>0` for every
   dyad, all record functions at this N are measurable, and there is a real
   C≥0 bounding `‖X_Ndt‖` and `|Y_Ndt|` μ×μ-a.e. for every d,t. Also assume
   N≥2 and `det H_N≠0`. Then `E S_N=0`,
   `V_N=Cov(H_N^(-1)(sqrt(N)/L_N)S_N)`,
   `E[(1/L_N)G_N]=H_N`, and, a.e. in the sample, **if** `det G_N≠0`,
   `sqrt(N)(βhat_N-β_N)=[(1/L_N)G_N]^(-1)(sqrt(N)/L_N)S_N`.
   Every coordinate of the linearized vector on the covariance's right side is
   in L². No sample-rank premise, intercept, symmetry, or positive weights are
   needed in this conjunct.
2. **Finite weighted identities.** For every such U,k,N,R and **every fixed real
   weight array**, impose the same fixed-N probability, positive-count,
   measurability and boundedness premises, N≥2, and `det H_w≠0`. The five
   conclusions of (1) hold with `S_w,H_w,V_w,G_w,βhat_w,β_w` and normalization
   D_N in place of their unweighted counterparts. The representation of the
   coefficient error is again conditional on the sample's weighted determinant
   being nonzero, a.e.
3. **C1 unweighted consistency.** For every U,k,R, assume: μ is a probability;
   all counts are positive for N≥2; all pair record functions are measurable;
   one C≥0 bounds X and Y μ×μ-a.e. uniformly in N,d,t; and there is one
   coordinate j with `X_Ndt(u,v)_j=1` for all N,d,t,u,v. Next assume there are
   common functions `fX : ℕ → U × U → ℝ^k`, `fY : ℕ → U × U → ℝ` such that
   `X_Ndt=fX_t`, `Y_Ndt=fY_t` pointwise for all indices, and a natural T0 with
   `T_Nd≤T0` for all N,d. Then for **every matrix H**, if H is positive
   definite, `H_N→H`, and
   `(N/L_N²)sum_{d∩f≠∅}(E b_Nd(β_N))(E b_Nf(β_N))'→0`, conclude
   `N Vhat_N-V_N→p0`. There is no endpoint-symmetry hypothesis in this
   conjunct. The displayed mean-score condition includes diagonal pairs and is
   a substantive limit premise.
4. **C2 weighted directed consistency.** For every U,k,R satisfying the
   probability, positive counts, common bound, record measurability and
   intercept conditions in (3), assume `T_Nd≤2`. For every common ordered-pair
   kernel X,Y and deterministic Boolean orientation map
   `dir_Nd : Fin T_Nd → Bool`, assume each orientation map is injective and
   each record is X,Y evaluated at `(u,v)` when dir is false and `(v,u)` when
   dir is true, pointwise. For every weight array w_Ndt and scale a_N, assume
   `a_N>0` for all N and there exists one real C with
   `0<w_Ndt/a_N≤C` for all N,d,t. For every positive definite H, if
   `H_(w/a),N→H`, conclude `N Vhat_w,N-V_w,N→p0`. No uniform positive lower
   bound on normalized weights is assumed.
5. **UI and actual covariances.** For every sequence of measurable types Ω_N,
   every probability law μ_N, every natural k, every vector error e_N and
   measure ν on ℝ^k, put `ξ_N=sqrt(N)e_N`. Assume every coordinate of e_N is
   in L² for every N; ξ_N converges weakly to ν as defined above; every
   coordinate of ξ_N is in L²; for every ε>0 there is C>0 such that, for
   **all N**, `E[sum_a ξ_Na² * 1_{sum_a ξ_Na²>C}]<ε`; the coordinates under
   ν are in L²; and `integral x dν=0`. Conclude `E ξ_N→0`, for every N
   `N Cov(e_N)=Cov(ξ_N)`, and `N Cov(e_N)→Cov_ν(id)`. In addition, for every
   deterministic matrix sequence A_N converging to that last covariance,
   `N Cov(e_N)-A_N→0`. The L² condition on e_N at N=0 is an explicit premise
   even though ξ_0 vanishes.
6. **An unweighted moment-failure model exists.** There exist a measurable
   type U and a two-coordinate repeated model R satisfying all repeated
   standing conditions in (3), such that `det H_N>0` for every N≥2 and
   `det G_N(ω)>0` for every sample whenever N≥2, but for every N≥3 its slope
   error is not L², its unit-weight WLS slope error is not integrable, and the
   squared scaled unweighted vector errors fail the UI condition in (5).
   This existential conjunct does **not** explicitly assert the C1 common
   kernel, bounded-count or limiting-design premises.
7. **An admissible directed moment-failure model exists.** There exist a
   measurable type U, a probability μ, measurable coordinates m,c:U→ℕ and
   A,B:U→Bool, with `c(u)<m(u)+1` for every u and exact joint atom masses
   `P(m=m0,c=c0,A=a,B=b)=2^(-(m0+1))/[4(m0+1)]` for every m0, every
   `c0:Fin(m0+1)`, and a,b. Thus the natural indices encode the printed
   positive integer and category minus one. Write sgn(true)=1,
   sgn(false)=-1, `δ(M)=1/[M² 2^(M²+2)]`, and
   `I(u,v)={m(u)=m(v), c(u)≠c(v)}`. Put
   `s(u,v)=δ(m(u)+1)` on I and 1 otherwise,
   `a(u,v)=(sgn A(u)+sgn A(v))1_I`, and
   `q=integral s(u,v)² d(μ×μ)`. The base model has two records:
   `X_+=(1,1+s)`, `X_-=(1,1-s)` and
   `Y_±=sgn B(u)+sgn B(v)±a(u,v)`.
   The directed model's unit is `(u,r)` with law μ times Lebesgue measure
   restricted to [0,1]. If r<s use the base record indexed by t; if r>s use
   the base record indexed by `Fin.rev t` (exchange records 0 and 1); if
   r=s use base record 0 for **both** records. It has exactly two records.
   This directed model satisfies all repeated standing conditions; there
   exist common ordered-pair X,Y and injective Boolean record orientations
   representing it pointwise; `[[2,2],[2,2+2q]]` is positive definite;
   its unit-weight H_N tends to that matrix; its population coefficient is
   zero for N≥2; and its sample weighted Gram has nonzero determinant a.e.
   for each N≥2. For every N≥3 its unit-weight slope error is neither L² nor
   integrable, and the squared scaled vector errors are not UI. These are
   negations of integrability, not evaluations of divergent moments through
   real integrals. The tied-label convention is pointwise; ties have product
   probability zero under the independent uniform auxiliary coordinates.
8. **Deterministic equivalence.** For every sequence Ω_N of measurable types,
   every sequence of probability measures μ_N, every k, and every
   deterministic real k×k matrix sequence A_N,
   `A_N→0` if and only if the random matrices constant in ω with value A_N
   converge in probability to zero in the definition above.

Junk and edge conventions: real division/inversion sends 1/0 to 0; matrix inverse
over ℝ is determinant-inverse times adjugate, hence zero on a singular matrix.
For N=0 or 1 dyad sums are empty, L_N=D_N=0, and the normalized definitions
are totalized. The finite identities exclude these N; positive counts make
L_N>0 for N≥2, and population rank excludes singular population inverses.
The sample representation is explicitly conditional on rank. The consistency
clauses use totalized sample inverse but only take limits, with positive
definite limiting designs. The moment witnesses explicitly have full sample
rank (everywhere in (6), a.e. in (7)) at the relevant N. δ(0)=0 formally, but
only δ(m+1) is used. The negative powers in the rare law are **integer** powers
of positive 2; there is no real-power domain issue. `Fin.rev` is a total
permutation, not truncated subtraction on an unchecked natural. `sqrt(N)` has
a nonnegative real natural argument. All natural casts into ℝ are exact; D_N
uses subtraction in ℝ, not Nat subtraction.

Real Bochner integrals default to zero without integrability; covariance
inherits this convention. In the finite clauses bounded records on probability
spaces and finite record sets supply the needed integrability, while the UI
clause explicitly supplies L². The failure clauses expressly negate L²/L¹
instead of treating a totalized real integral as a moment. `ENNReal.ofReal`
appears in the rare atom law; its arguments are positive. `toReal ∞=0` cannot
affect the convergence definition here because every law is a probability.
The optional k=0 finite/UI/equivalence cases have empty vectors and matrices;
the intercept premise excludes k=0 in standing repeated models. Empty U
cannot carry a probability measure. No empty infimum, supremum, limsup,
liminf, logarithm, partial function, or unrestricted real power occurs.

## SAP.P018b.T21

The stub at Challenge/Part1.lean:101 asserts Defs/WholeW1.lean:577. Vectors,
matrices, dyads, endpoints, inner/outer products, coordinatewise integrals and
covariance have the finite-sum/integral meanings given in the T20 section.

A kernel K is a measure μ on measurable U and functions
`X:U×U→ℝ^k`, `Y:U×U→ℝ`. Its standing predicate asserts: μ is a probability;
X,Y are measurable; both are pointwise symmetric under swapping endpoints;
one C≥0 bounds ‖X‖ and |Y| μ×μ-a.e.; there is a coordinate j with X_j=1
everywhere; and `det Q≠0`, where `Q=integral XX' d(μ×μ)`.
Define `β=Q^(-1)integral XY d(μ×μ)`, `e(u,v)=Y(u,v)-X(u,v)'β`.
On the finite product law μ^N, let X_d and e_d evaluate these endpoint
functions, `S=sum_d X_d e_d`, and let 𝒢 be the pullback/comap of the standard
measurable space of the **entire design array** by ω↦(d↦X_d(ω)). Set
`m_d=E[e_d|𝒢]`,
`c_df=E[(e_d-m_d)(e_f-m_f)|𝒢]`, and
`C_df=E[c_df X_d X_f']`. Each conditional expectation is Mathlib condExp;
equalities under it are understood through these chosen versions.
The conditional sparse sum is `Σcond=sum_{d∩f≠∅} C_df`. The unconditional
sparse sum is `Σraw=sum_{d∩f≠∅} E[e_d e_f X_d X_f']`.
A neighbor of d is a distinct dyad f with nonempty intersection with d.

The conjunction states:

* For **every natural N≥2**, the number of dyads is `N.choose 2`; for **each
  dyad d**, its number of neighbors is `2(N-2)`; summing those numbers gives
  `N(N-1)(N-2)`; and the number of ordered overlapping pairs, including d=f,
  is `(N.choose 2)(2N-3)`. All arithmetic in this conjunct is natural.
* For **every** measurable U, every k,N, and every K satisfying the full
  standing predicate, **if N≥2**,
  `sum_d (C_dd + sum_{f in neighbors(d)} C_df)=Σcond`.
* For **every** such U,k,N,K satisfying standing, with **no N lower bound**,
  `Cov_{μ^N}(S)=Σraw`.
* The particular real-unit model with μ the normalized restriction of
  Lebesgue measure to [-1,1], `X(z,t)=(1,2+z+t)` and `Y(z,t)=(z+t)²`,
  satisfies standing and has `β=(2/3,0)`. At N=3 its conditional sparse sum
  is zero, its score covariance is
  `[[12/5,24/5],[24/5,4712/315]]`, and those two matrices are unequal.

The docstring says the neighbor expectation must contain the braces, gives the
three pair counts, distinguishes the conditional expression from score
variance, and describes the uniform nonlinear witness. It does not call the
canonical claim false.

Junk and edge conventions: Q's inverse is totalized but nonsingular by
standing. The finite sums for N=0,1 are empty; the only assertion at those N
is the correct zero score-covariance identity. Natural subtractions N-2,
N-1 and 2N-3 occur only with N≥2, where they equal ordinary nonnegative
integer arithmetic. Endpoints are min'/max' with an actual proof of
nonemptiness, so no arbitrary endpoint is selected. Conditional expectation
is zero by definition if the conditioning space is not a sub-σ-algebra, its
trimmed law is not σ-finite, or its argument is nonintegrable. Here the design
is measurable, so its comap is a sub-σ-algebra, and probability and boundedness
give finiteness and integrability; those defaults are not used. The normalized
restriction `cond volume [-1,1]` multiplies the restriction by inverse mass;
the mass is 2, so this is the genuine uniform law rather than conditioning
on a null or infinite-mass event. The Bochner covariance/mean defaults do not
apply to the bounded records/residuals. Intercept makes k positive. Empty U is
excluded by probability. There is no division by N or dyad count, logarithm,
square root, real power, `toReal`, infimum, supremum or partial function here.

## SAP.P018b.T22

The stub at Challenge/Part1.lean:112 asserts Defs/WholeW2.lean:50. For each
natural N,T, the coordinate index is the disjoint sum
`Fin N ⊕ (Fin N ⊕ (Dyad N × Fin T))`. These are respectively unit covariates,
unit effects, and observation errors. Dyads and endpoints are the two-element
finite sets and their minimum/maximum defined above.

Quantifier order: for **all naturals N,T**, if N≥2 and T≥1, then for **every
measurable probability space (Ω,μ)** and **every measurable map**
`Z:Ω→(index→ℝ)`, assume **each coordinate** has law `gaussianReal 0 1` and
the **whole indexed family** of coordinate functions is mutually independent
(`iIndepFun`). Denote the three disjoint coordinate families X_i, U_i, ν_dt.
Define `e_dt=sum_{i∈d} U_i+ν_dt`, `p_d=|X_min(d)-X_max(d)|`,
`m_d=β₀+β₁p_d`, and `Y_dt=m_d+e_dt`.

The conclusions, all on that same probability space, are:

* The pushforward law of the entire finite array `(e_dt)` is Gaussian.
  The error array and the entire covariate vector `(X_i)` are independent.
* For every d,t, e_dt is in L² and has expectation zero.
* For every d,f and t,u,
  `Cov(e_dt,e_fu)=card(d∩f)+(if d=f and t=u then 1 else 0)`.
  Thus it is 3 for the same observation, 2 for different records on the same
  dyad, 1 for distinct dyads sharing a unit, and 0 for disjoint dyads.
* For every d,t, `E[e_dt|σ(all X_i)]=0` μ-a.e.
* For **every pair of real coefficients β₀,β₁**, every d and t,
  `E[Y_dt|σ(X_min(d),X_max(d))]=m_d` μ-a.e. and, separately,
  `E[Y_dt|σ((1,p_d))]=m_d` μ-a.e.

The σ-algebras here are literally MeasurableSpace.comap of the displayed
maps into the standard finite-product Borel spaces. HasLaw includes a.e.
measurability and equality of pushforward law. The docstring's β₀=0, β₁=1,
T=1 or 2 cases are specializations of the quantified conclusion; the corrected
observation-error symbol is described as ν.

Junk and edge conventions: N≥2 and T≥1 avoid an empty observation set, though
some individual covariance cases are unavailable at small N or T. All endpoints
are genuine elements proved to exist; no default partial lookup is involved.
The Gaussian variance parameter is the nonnegative real 1, not a real converted
through a clipping convention. All means, covariances and conditional
expectations exist from finite linear combinations of finite-dimensional
Gaussian coordinates, and the absolute difference predictor is integrable.
Consequently the Bochner-integral zero default and conditional-expectation
zero defaults (incompatible σ-algebra, non-σ-finite trim, nonintegrability)
cannot give these assertions their meaning. A singleton conditioning coordinate
1 causes no problem. Natural intersection counts cast exactly into ℝ; there is
no natural subtraction, division, log, sqrt, rpow, toReal, infimum, supremum,
limsup or partial function in this statement's dependency closure.

## SAP.P018b.T23

The stub at Challenge/Part1.lean:119 asserts Defs/Part5.lean:58. A vector is
`Fin k→ℝ` and a matrix is a real k×k matrix, with
`x'β=sum_a x_a β_a` and `(xy')_ab=x_a y_b`.
Write `p(t)=1/(1+exp(-t))`,
`ℓ(x,y,β)=y x'β-log(1+exp(x'β))`, and
`s(x,y,β)=(y-p(x'β))x`.
For each a,b define
`J_ab=-deriv_{t at β_b}[s_a(x,y,update(β,b,t))]`.
Here update changes exactly one coordinate, and deriv is Mathlib's totalized
one-variable real derivative. For a finite observation type E define
`B(X,β)=sum_{d:E} p(X_d'β)(1-p(X_d'β)) X_dX_d'`.

There are three universally quantified conjuncts:

1. For **every natural k**, every real vector x, **every real y** (not just
   binary responses), and every real coefficient vector β, let p=p(x'β).
   Then `0<p<1`; for every a, the coordinate curve
   `t↦ℓ(x,y,update(β,a,t))` has derivative `s_a(x,y,β)` at β_a;
   `J=p(1-p)xx'`; J is positive semidefinite; and
   `s(x,y,β)s(x,y,β)'=(y-p)²xx'`.
2. For **every finite type E**, every k, every collection of real vectors X_d,
   every real response collection Y_d, and every β,
   `sum_d J(X_d,Y_d,β)=B(X,β)` and
   `sum_d s(X_d,Y_d,β)s(X_d,Y_d,β)'=
   sum_d (Y_d-p(X_d'β))² X_dX_d'`.
3. For **every measurable Ω**, **every type Θ** (no measurable structure on Θ
   is required), every natural k, **every probability law μ** on Ω,
   every function `ψ:Ω→Θ→ℝ^k`, and every fixed θ, assume **every coordinate**
   `ω↦ψ(ω,θ)_a` is in L²(μ). Then the matrix
   `M_ab=integral ψ(ω,θ)_a ψ(ω,θ)_b dμ` is positive semidefinite.
   Positive semidefinite means Hermitian (over ℝ, symmetric) with
   `sum_ab v_a M_ab v_b≥0` for every real vector v.

The generic matrix is a same-data outer product, with a single ω in both
factors. There are no independent copies or centering operations in its
definition. The docstring identifies these as corrected logistic formulas and
states the probability/L² assumptions on the generic assertion.

Junk and edge conventions: real division sends 1/0 to zero, but
`1+exp(-t)>0` for every finite real t. Real.log is extended by log|x| for
negative x and log 0=0, but here `1+exp(x'β)>0`. The score's derivative is
totalized to zero when it does not exist, but these coordinate curves are
smooth, so the usual derivative applies. Bochner integrals are totalized to
zero on nonintegrable functions; the probability and coordinate L² hypotheses
give integrability of **each product** by Cauchy–Schwarz. No junk product
expectations remain. For k=0, derivatives indexed by coordinates are vacuous
and the matrix assertions concern the unique empty matrix, while the sigmoid
assertion still concerns p(0)=1/2. Empty E gives ordinary empty sums, without
any division by card E. Empty Θ contributes no θ; empty Ω cannot carry the
required probability law. These edge specializations do not eliminate the
positive-dimensional nonempty cases. No other partial functions, sqrt, rpow,
toReal, infimum, supremum or asymptotic extremum occurs.

## SAP.P018b.T24

The stub at Challenge/Part1.lean:129 asserts Defs/WholeW2.lean:79. It has no
global variables or hypotheses. Its data are a literal ordered list of rational
triples (H,C,D), in rows Alliances, Power ratio, Lower democracy, Lower
dependence, International organizations, Non-contiguity, Log distance, Only
minor powers, Constant:

`[(.069,.175,.265),(.020,.047,.070),(.005,.010,.015),
(10.734,17.560,24.749),(.002,.005,.008),(.074,.181,.185),
(.026,.068,.102),(.078,.188,.344),(.211,.562,.840)]`.
Each decimal here denotes its exact rational, e.g. .069=69/1000. A triple is
represented by `ℚ × (ℚ × ℚ)`, so the field projections select H,C,D in that
order. The entire conjunction unfolds as follows:

* The list of D/H ratios in order equals
  `[265/69,7/2,3,24749/10734,4,5/2,51/13,172/39,840/211]`.
* The list of endpoint ratios `(D+1/2000)/(H-1/2000)` equals
  `[531/137,47/13,31/9,49499/21467,17/3,53/21,205/51,
  689/155,1681/421]`.
* Explicit rational equalities identify the lower-dependence ratio as
  `(24749/1000)/(10734/1000)=24749/10734` and the only-minor-powers ratio
  as `(344/1000)/(78/1000)=172/39`.
* For **every row in the list**, its D/H lies between 24749/10734 and 172/39,
  inclusive, and is <5; `H<C<D`; its D/C is between 185/181 and 86/47,
  inclusive. Another conjunct says its D/H is <10.
* For **every row** and **every pair of reals h,d**, if
  `H-1/2000≤h` and `d≤D+1/2000`, then `d/h<10`. These are one-sided
  domains; no upper bound on h or lower bound on d is imposed.
* For **every row**, as real inequalities,
  `0<H-1/2000`, `D+1/2000<10(H-1/2000)`, and
  `(D+1/2000)/(H-1/2000)≤17/3`.
* For **every pair of real numbers b,se**, if `|b|≤23/2000` and
  `15/2000≤se`, then `|b|/se≤23/15` and `23/15<41/25`.
* Independently, for **every real b,se**, if `21/2000≤|b|`, `0<se`, and
  `se≤5/2000`, then `21/5≤|b|/se` and `41/25<21/5`.
* Exact rational equalities give `.185/.181=185/181` and
  `.344/.188=86/47`. An exact real equality gives `.011/.008=11/8`, and
  the strict real inequality `11/8<41/25` is also asserted.

These are arithmetic consequences of a supplied table and displayed coefficient
and standard-error bounds. There is no formal variable for an underlying
dataset, fitted model, rounding function, or hypothesis-test procedure. The
docstring describes the ratios, rounding bounds and two separate full
one-sided domains, using the decimal 1.64 for the rational 41/25.

Junk and edge conventions: both ℚ and ℝ divide by zero using zero, but every
literal H,C is positive and every `H-1/2000` is positive. The rowwise bound
on h forces h>0. The upper-statistic hypotheses force se>0, and the
lower-statistic hypotheses explicitly require it, so no statistic uses the
zero-division convention. Casting rationals into ℝ is exact, not rounding or
truncation. Quantification over list membership is not empty: there are exactly
nine distinct rows. There are no measures, undefined expectations, empty
extrema, infimum/supremum, log/sqrt/rpow, limsup/liminf, truncated natural
subtraction, or partial-function defaults.
