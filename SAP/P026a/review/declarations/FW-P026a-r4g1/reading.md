# Blind reading

Written and saved before opening `claims.json` or `record.json`. The review reads
`closure.json`, the five Challenge docstrings/statements, and all source declarations
in their closures. Auto-generated closure declarations were also printed in
`scratch/BlindCheck.lean`: they are proofs of `NeZero`, `AtLeastTwo`, or the range
of a `Fin` index, not additional statistical hypotheses. Constructors and
projections have exactly the fields described below.

## Common expansions into finite sums

The following notation is purely an abbreviation for the Mathlib finite sums,
field arithmetic, inequalities, functions, `Bool`, `Fin`, and finite sets used in
the source. It applies to each section below.

An `AssignmentDesign Ω I R` is just two unrestricted functions, weights
`d : Ω → R` and assignments `t : Ω → I → Bool`. Here Ω and I have `Fintype`
instances and I has decidable equality. R is an ordered field; in the statements
it is ℚ for concrete tables and ℝ for universal results. This structure alone
asserts neither normalization nor positivity. Write

- `E f = ∑_{w∈Ω} d(w) f(w)` (`mean`).
- `isProbability` means every d(w) ≥ 0 and ∑w d(w) = 1.
- `Aᵃ_i(w) = 1` if t(w,i)=a and 0 otherwise (`armIndicator`).
- `pᵃ_i = E Aᵃ_i` (`inclusion`), `qᵃᵇ_ij = E(Aᵃ_i Aᵇ_j)`
  (`jointInclusion`). Positive marginals means p¹_i>0 and p⁰_i>0 for every i.
- For fixed potential outcomes x,z:I→R, `Y_i(w)=x_i` if t(w,i)=true and z_i
  otherwise (`response`).
- `S(x)=∑i x_i` (`fixedTotal`), `Δ_N(x,z)=(S(x)-S(z))/N`
  (`averageEffect`), where the natural N is cast to R.
- `Hᵃ(x)(w)=∑i Aᵃ_i(w)x_i/pᵃ_i` (`htSum`), and
  `H_N(x,z)=(H¹(x)-H⁰(z))/N` (`htContrast`).
- `Gᵃ(x,f)(w)=∑i[Aᵃ_i x_i/pᵃ_i - Aᵃ_i f_i(w)/pᵃ_i + f_i(w)]`
  (`adjustedSum`); `G_N(x,z,f)=(G¹(x,f)-G⁰(z,f))/N`
  (`adjustedContrast`). The same prediction f is used in both arms.
- `Cov(f,g)=E(fg)-(Ef)(Eg)` (`designCovariance`), `Var(f)=Cov(f,f)`
  (`designVariance`). These are algebraic sums, not Bochner integrals.
- `d_ij=E 1{t_i≠t_j}` (`disagreementProbability`). `directedSupport` is
  ∀i,j, i≠j → q¹⁰_ij>0.
- Every off-diagonal sum below is **ordered**, ∑i ∑_{j∈univ.erase i};
  it is not a sum over unordered pairs (`orderedOffDiagonalSum`).
  Let M_ab={(i,j):i≠j and qᵃᵇ_ij=0}. `unavailablePairSum D a b h`
  means ∑_{(i,j)∈M_ab} h(i,j).
- `zeroAdjustment(q)=1` if q=0, otherwise 0. Define
  `Bᵃᵇ_ij(w)=[Aᵃ_i Aᵇ_j/(qᵃᵇ_ij+1{qᵃᵇ_ij=0})]
  (qᵃᵇ_ij-pᵃ_i pᵇ_j)(Y_i/pᵃ_i)(Y_j/pᵇ_j)`
  (`estimatedPairTerm`).
- `V_N(x,z)(w)` (`printedVarianceEstimate`) is N⁻² times
  `∑i[A¹_i(Y_i/p¹_i)²+A⁰_i(Y_i/p⁰_i)²]
  +∑_{i≠j}(B¹¹_ij+B⁰⁰_ij-2B¹⁰_ij)
  +∑_{M_11}[A¹_iY_i²/(2p¹_i)+A¹_jY_j²/(2p¹_j)]
  +∑_{M_00}[A⁰_iY_i²/(2p⁰_i)+A⁰_jY_j²/(2p⁰_j)]`.
- `C(x,z)(w)` (`covarianceWithZeroOmission`) is
  `∑_{i≠j,q¹⁰_ij≠0}[A¹_iA⁰_j/q¹⁰_ij](q¹⁰_ij-p¹_i p⁰_j)
  (Y_i/p¹_i)(Y_j/p⁰_j)
  -∑i A¹_iY_i²/(2p¹_i)-∑i A⁰_iY_i²/(2p⁰_i)`.
  A zero joint is explicitly omitted, not asserted positive.
- `K(x,z)(w)=∑_{M_10}[A¹_iY_i²/p¹_i+A⁰_jY_j²/p⁰_j]`
  (`directedPairCorrection`). `C⁺=C-K/2`
  (`repairedCovarianceEstimate`), `V⁺_N=V_N+K/N²`
  (`repairedVarianceEstimate`).
- `P(x,z)=∑_{i≠j}(q¹⁰_ij-p¹_i p⁰_j)(x_i/p¹_i)(z_j/p⁰_j)
  -∑i x_i z_i` (`populationCrossCovariance`).
- `B⁺(x,z)=∑i(x_i-z_i)² + ½∑_{M_11}(x_i+x_j)²
  +½∑_{M_00}(z_i+z_j)²+∑_{M_10}(x_i-z_j)²`
  (`repairedBias`).
- `Vᵃ(x,z)(w)` (`armVarianceEstimate`) is
  `∑i Aᵃ_i(1-pᵃ_i)(Y_i/pᵃ_i)² +∑_{i≠j,qᵃᵃ_ij>0} Bᵃᵃ_ij
  +∑_{M_aa}[Aᵃ_iY_i²/(2pᵃ_i)+Aᵃ_jY_j²/(2pᵃ_j)]`.

`UnitLaw I` consists of weights on the **entire** finite type I→Bool,
nonnegativity, total weight one, and positive marginals for every i in both
arms. Its `assignmentDesign` has those weights and t(w,i)=w(i).
`ClusterLaw U C` consists of a fixed surjection c:U→C and a `UnitLaw C`.
The cluster design is that law; `totals x(k)=∑_{i∈U:c(i)=k}x_i`.
Surjectivity ensures no cluster is empty. No distributional assumptions about
fixed outcomes or covariates are built into these structures.

`finiteIndependent D f g` is
`∀u:α→R, ∀v:β→R, E[u(f) v(g)]=E[u(f)]E[v(g)]` for f:Ω→α,g:Ω→β.
On the finite probability spaces in use this expresses independence of the
whole random objects, including a function-valued vector. It is not merely
zero covariance. `fittingIndicators D J(w)` is the function j↦t(w,j) on the
subtype {j:I // j∈J}; `fittingResponses D J x z(w)` is j↦Y_j(w) on that subtype.

## SAP.P026a.T1

There are no input hypotheses: the theorem asserts a conjunction of explicit
rational computations and support certificates (`T1WholeStatement`, containing
`T1Statement`). All quantifiers below range over the displayed finite sets.

The first law has Ω=Fin 3, I=Fin 2, weights 1/3, assignments 00,01,11.
Potential outcomes are x=z=1 and N=2. It asserts probability normalization,
positive marginals, and for every i≠j positive disagreement and positive
same-arm joints. It further asserts:

- p¹=(1/3,2/3), p⁰=(2/3,1/3); every off-diagonal d,q¹¹,q⁰⁰ equals 1/3.
- q¹⁰_01=0, q¹⁰_10=1/3; for every w, A¹_0(w)A⁰_1(w)=0.
- For every w in table order H₂=(-9/4,0,9/4), V₂=(57/16,3/2,57/16),
  and C=-9/4.
- E H₂=0, Var H₂=27/8, E V₂=23/8<27/8, and their difference is -1/2.
- Cov(H¹(1),H⁰(1))=-13/4, E C=-9/4>-13/4; the difference is +1.
- Δ₂(1,1)=0. The literal-34 domain fails, and at every w the partial ratio
  of A¹_0 A⁰_1 to q¹⁰_01 is `none`.

The second law has Ω=Fin 14, I=Fin 6, all weights 1/14, and exactly all binary
strings with three ones and t₀≤t₁:
`000111,001011,001101,001110,010011,010101,010110,011001,011010,011100,
110001,110010,110100,111000`. Again x=z=1, now N=6. It asserts probability
normalization, positive marginals, exactly three treated in every state, and
for every distinct i,j positive disagreement and same-arm joints. For every
distinct i,j, q¹⁰_ij=0 iff i=0,j=1. More precisely:

- p¹=(2/7,5/7,1/2,1/2,1/2,1/2), p⁰=(5/7,2/7,1/2,1/2,1/2,1/2).
- For every i≠j, q¹¹_ij,q⁰⁰_ij≥1/14 and d_ij≥3/7. The latter equals 3/7
  iff (i,j)=(0,1) or (1,0). Each same-arm bound is attained by some i≠j.
- Partition Ω into g=0,1,2 according to (t₀,t₁)=00,01,11 (`w1SixGroup`).
  The numbers of states are (4,6,4). For every w, H₆ takes group values
  (-3/20,0,3/20), V₆ takes (-619/3600,7/54,-619/3600).
- E H₆=0, Var H₆=9/700, E V₆=-269/6300<9/700, difference -1/18.
- Cov(H¹(1),H⁰(1))=27/175, E C=202/175, difference +1; Δ₆(1,1)=0.
- Literal-34 domain fails; for every w, A¹_0A⁰_1=0 and its partial ratio
  with q¹⁰_01 is `none`.

`w1PartialRatio(x,p)` is `none` if p=0 and `some(x/p)` otherwise.
`w1Literal34Domain D` means all p¹_i,p⁰_i are nonzero and all off-diagonal
q¹⁰_ij are nonzero. The docstring describes the facts as refuting the printed
support deduction, conservativeness, and sharp-null equalities; that relation
to a paper has not yet been checked.

Junk-value audit: every actual marginal is positive; N=2 or 6. Missing joint
probabilities are real missing support. The formula V deliberately uses q+1{q=0},
so no joint denominator vanishes in V for these probability laws. C has an
explicit zero-omission branch. Literal division by zero is represented by
`none`, not by a fabricated rational. Whether V and C render the paper's
intended convention remains a claim-stage question. `Fin` numerals are in range;
auxiliary `NeZero` proofs just elaborate them. Empty types, empty extrema,
logs, roots, powers with nonintegral exponents, and extended-real conversions
do not occur. Finite sums have their ordinary empty-sum convention, but these
concrete types and groups are nonempty. No integrability default is involved.

## SAP.P026a.T2

This is a conjunction of independent universal clauses and concrete rational
certificates. In each of the first eleven universal clauses quantify first over
arbitrary finite nonempty U,C with decidable equality, then E:ClusterLaw U C,
then separation `∀c≠d,d_cd>0`, then the displayed arbitrary fixed real outcome
functions on U. Write N=|U|, X=totals x, Z=totals z. Extra assumptions/quantifiers
are stated where needed. There is no directed-support assumption.

1. For all distinct cluster indices i,j, d_ij=q¹⁰_ij+q¹⁰_ji.
2. For all distinct i,j, d_ij>0 iff q¹⁰_ij>0 or q¹⁰_ji>0.
3. For all x,z, Cov(H¹(X),H⁰(Z))=P(X,Z).
4. For all x,z,
   `N²(E V_N(X,Z)-Var H_N(X,Z)) = ∑i(X_i-Z_i)²
   +½∑M11(X_i+X_j)²+½∑M00(Z_i+Z_j)²-2∑M10 X_i Z_j`.
5. For all x,z,
   `E C⁺(X,Z)-Cov(H¹(X),H⁰(Z))
   =-½∑i(X_i-Z_i)²-½∑M10(X_i-Z_j)²`, and E C⁺≤that true covariance.
6. For all x,z, `N²(E V⁺_N-Var H_N)=B⁺(X,Z)`, and Var H_N≤E V⁺_N.
7. For all fixed c:U→ℝ, additionally assume every distinct-cluster same-arm
   q¹¹,q⁰⁰ is positive. Put Q=totals c (identical in both arms). Then
   `E V⁺_N(Q,Q)-Var H_N(Q,Q)=∑M10(Q_i-Q_j)²/N²`, and
   `E V⁺_N(Q,Q)=Var H_N(Q,Q)` iff for every i≠j with q¹⁰_ij=0, Q_i=Q_j.
8. For all x,z, then w:C→Bool with **positive weight**, pointwise
   `V⁺_N(X,Z)(w)=[V¹(X,Z)(w)+V⁰(X,Z)(w)-2C⁺(X,Z)(w)]/N²`.
9. For all x,z,r:U→ℝ, let R=totals r, X'=X-R,Z'=Z-R. Then
   `N²(E V⁺_N(X',Z')-Var G_N(X,Z,constant R))=B⁺(X',Z')`
   and Var G_N≤E V⁺_N(X',Z').
10. For all x,z, B⁺(X,Z)≥0.
11. Separately, for all finite nonempty U,C and E:ClusterLaw U C, with **no**
    separation hypothesis, for all x,z,r, totals(x-r)=totals x-totals r and
    totals(z-r)=totals z-totals r, and as functions of w,
    `G_N(X,Z,constant R)=H_N(totals(x-r),totals(z-r))`.

There are also these unconditional concrete clauses:

- In the fourteen-state six-cluster law of T1, x=z=(1,2,1,1,1,1), N=6,
  Var H₆=2759/12600, E V₆=151/1400, E V⁺₆=3109/12600>2759/12600.
  The two biases E V₆-Var H₆ and E V⁺₆-Var H₆ equal -1/9 and 1/36.
- In the three-state two-cluster law of T1, d_01>0 and q¹⁰_01=0.

All SAP definitions in these formulas are expanded in the common section. The
docstring describes a repair, exact biases, conservativeness, sharp-null equality
characterization, fixed residuals, and a strict six-cluster example.

Junk-value audit: UnitLaw supplies positive marginals and an actual probability
law. |U|>0 follows from Nonempty U, so its real cast and its square are nonzero.
The constants 2 and concrete N=6 are nonzero. Joint zeros are intentional:
V uses the explicit +1 safeguard and C explicitly omits them; repaired terms
handle their bias. For arbitrary unsupported w a zero-joint pair could be
observed, but clause 8 expressly restricts to positive-weight w and expectations
ignore zero-weight states. All cluster fibers are nonempty by surjectivity.
The statement has no partial choices, integrals, extended reals, roots, logs,
noninteger powers, infima or limits. Ordered sums can be empty for a singleton
cluster type; those sums equal 0 without making the rest of the theorem vacuous.
Finite nonempty independent Bernoulli cluster designs satisfy all universal
hypotheses, including the optional same-arm positivity for distinct clusters.

## SAP.P026a.T3

This is another conjunction. Its first clause quantifies over arbitrary finite
nonempty U,C with decidable equality, then E:ClusterLaw U C, then separation,
then **directed support** q¹⁰_ij>0 for every i≠j, then arbitrary fixed
x,z:U→ℝ. Use N,X,Z as in T2. The conclusions are:

- `E C(X,Z)-Cov(H¹(X),H⁰(Z))=-½∑i(X_i-Z_i)²` and E C≤true covariance.
- `N²(E V_N(X,Z)-Var H_N(X,Z))=∑i(X_i-Z_i)²
  +½∑M11(X_i+X_j)²+½∑M00(Z_i+Z_j)²` and Var H_N≤E V_N.
- If every cluster has X_i=Z_i and additionally every distinct-cluster q¹¹,q⁰⁰
  is positive, then E V_N=Var H_N.

The second universal clause repeats all the same type, law, separation and
directed-support assumptions, then quantifies arbitrary x,z,r:U→ℝ. For
R=totals r and X'=X-R,Z'=Z-R, Var G_N(X,Z,constant R)≤E V_N(X',Z').
Under cluster-level equality X=Z and same-arm support, equality holds.

The concrete design has Ω=Fin 6×Fin 15 and I=Fin 10, every weight 1/90.
Its first four coordinates use the six equally enumerated choices of two
ones among four, indexed by the first state coordinate. The remaining six
use the fifteen choices of two ones among six, indexed independently by
the second coordinate. It asserts probability normalization, positive marginals,
directed support, and for every i≠j q¹⁰_ij≥1/6, q¹¹_ij≥1/15,
q⁰⁰_ij≥1/6, d_ij>0. Each of the three joint-probability bounds is attained
by some ordered distinct pair.

The next universal clause, with arbitrary finite nonempty U,C, E and fixed
x,z,r and **no separation/support premises**, gives both totals-of-differences
identities and the fixed-residual generalized-contrast identity stated in T2.
Finally it asserts existence of an actual real-weight design on Fin 3 states
and Fin 2 indices with normalization, positive marginals, positive disagreement
for all distinct pairs, and failure of directed support.

Junk-value audit: positive marginals and N=|U|>0 guard all arm/ATE denominators.
Directed support means C's omission branch is never used off diagonal. V can
still encounter zero same-arm joints, handled by its explicit convention and
bounds. In the 90-state design every relevant joint is positive. The `Nat`
subtraction i.val-4 occurs only in the branch i.val≥4 and i.val<10, so it is
ordinary subtraction with value below 6; the supplied proof establishes that
range. There are no unguarded partial functions or integrability defaults.
The final existential is possible using the real version of the 00,01,11
law; it is not a contradiction among premises. The rest of the universal
hypotheses hold, for example, for independent fair cluster assignments.

## SAP.P026a.T4

There are no premises: `T4WholeStatement` asserts finite rational facts.
For the six-unit law Ω=Fin 4, I=Fin 6, weights 1/4, the assignment rows are
`010101,011010,100110,101001`. Coordinates (0,1), (2,3), (4,5) are
complementary pairs. In both examples x_i=1,z_i=0, so Y_i=A¹_i.
Define `h(u,v)=u+v-2uv` (`xorFitPolynomial`). The six predictions are
`[h(Y₂,Y₄),1-h(Y₂,Y₄),h(Y₀,Y₄),1-h(Y₀,Y₄),h(Y₀,Y₂),1-h(Y₀,Y₂)]`.
The theorem asserts:

- A probability law, positive marginals, all p¹_i=p⁰_i=1/2, exactly three
  treated per state, and qᵃᵇ_ij=1/4 for every a,b whenever floor(i/2)≠floor(j/2).
- For every w,i, f_i(w)=A¹_i(w); for every i, Cov(A¹_i,f_i)=1/4.
- For every w, G¹(1,f)=3, G⁰(0,f)=3, G₆(1,0,f)=0, H₆(1,0)=1;
  Δ₆(1,0)=1 and E G₆-Δ₆=-1.
- For all i,j, whole-object `finiteIndependent(t_i,t_j)` holds **iff**
  floor(i/2)≠floor(j/2). Thus the complete set J_i of individually independent
  coordinates is {2,3,4,5} for i<2, {0,1,4,5} for 2≤i<4, and {0,1,2,3} for i≥4.
- Let a_i=2 for i<2 and 0 otherwise, b_i=4 for i<4 and 2 otherwise.
  Both indices are in J_i; for every w,
  f_i(w)=h(Y_ai,Y_bi) for even i and 1-h(Y_ai,Y_bi) for odd i.
- For every i, Pr(t_i=true and f_i=1)=1/2 whereas
  Pr(t_i=true)Pr(f_i=1)=1/4; t_i and f_i are not independent.
- `E G₆-Δ₆=-(1/6)∑i Cov(A¹_i,f_i)(1/p¹_i+1/p⁰_i)`.

For the three-unit law Ω=Fin 4, I=Fin 3, weights 1/4, assignment rows are
`000,011,101,110`. Every pair of distinct coordinates has all four joint
probabilities 1/4. Predictions are
`[h(Y₁,Y₂),h(Y₀,Y₂),h(Y₀,Y₁)]`. The theorem asserts normalization,
positive marginals, p¹=p⁰=1/2 at every coordinate, f_i=A¹_i pointwise,
Cov(A¹_i,f_i)=1/4 for every i, G₃=0 pointwise, E G₃=0, Δ₃=1,
and bias -1. For the alternative prediction `[0,0,Y₀Y₁]` (`productFit`),
Cov(A¹_2,f_2)=-1/8, E G₃=7/6 and bias +1/6.

The docstring characterizes this as refuting passage from pairwise independence
to independence after arbitrary nonlinear fitting on several outcomes. Only
the six-unit example has fixed treatment count; the three-unit example does
not. The complete fitting sets and their permitted-input certificates are
explicitly stated for the six-unit example.

Junk-value audit: N is 6 or 3, and every p is 1/2. No missing denominator is
used. Natural division i.val/2 and remainder i.val%2 identify the intended
complementary pair and parity; neither is a real division. Every vector lookup
uses a valid `Fin` index. Empty fitting sets are absent in these witnesses.
All means and covariances are genuine finite moments. No logarithm, square
root, infimum, limit, extended-real coercion, or default partial-function
value occurs. The counterexamples are fully constructed, not conclusions
assumed as hypotheses; whether they obey the paper's fitting permissions
requires the next stage.

## SAP.P026a.T5

This conjunction contains the six clauses of `T5Statement` and four further
clauses. All weights/outcomes are real. Unless stated otherwise, first quantify
over any finite nonempty I with decidable equality, then E:UnitLaw I.

1. For any type Θ, i:I, finite J⊆I, fixed y1,y0:I→ℝ, deterministic
   G:(J→ℝ)→Θ and P:Θ→ℝ, if t_i is independent of the **whole vector**
   fittingIndicators J, then t_i is independent of G(fittingResponses J y1 y0),
   is independent of P of that parameter, and Cov(A¹_i,P(G(...)))=0.
2. With the same quantifier order, the same conclusions follow if t_i is
   instead independent of the whole fittingResponses vector itself.
3. For any fixed x,z:I→ℝ, J:I→Finset I, and maps
   G_i:(J_i→ℝ)→ℝ, assume **for every i** independence of t_i and the whole
   assignment vector on J_i. Put f_i(w)=G_i(Y restricted to J_i).
   Then E G¹(x,f)=S(x), E G⁰(z,f)=S(z), E G_|I|(x,z,f)=Δ_|I|(x,z).
4. For i, J, x,z, fixed real a and b:J→ℝ, assume for every j∈J
   independence of t_i and t_j individually. Then
   `Cov(A¹_i,a+∑j b_jY_j)=∑j b_j(x_j-z_j)Cov(A¹_i,A¹_j)`
   and the left side is zero.
5. Without needing Nonempty I, for every E with `independentAssignments`
   and every i:I, t_i is independent of the whole vector on univ.erase i.
   `independentAssignments` means: for **every** family F_i:Bool→ℝ,
   `E ∏i F_i(t_i)=∏i E F_i(t_i)`.
6. Without needing Nonempty I, for any additional finite B with decidable
   equality, E, c:I→B, and `independentBlocks E c`, each t_i is independent
   of the vector on {j:c(j)≠c(i)}. The block condition means: for every
   family F_b taking the whole Boolean vector on fiber c⁻¹(b) to ℝ,
   `E ∏b F_b(t restricted to c⁻¹(b))=∏b E F_b(t restricted to c⁻¹(b))`.
7. A strengthened version of clause 3 allows, separately for every i,
   **either** whole assignment-vector independence **or** whole response-vector
   independence. The same three unbiasedness conclusions hold, with the
   disjunction chosen per unit, not a single global choice.
8. For any Θ,i,J,x,z,G,P, define
   `F(t)=P(G(j↦if t_j then x_j else z_j))` on the whole fitting assignment
   vector. For every allocation w, P(G(fittingResponses(w))) equals
   F(fittingIndicators(w)). Moreover assignment-vector independence implies
   independence of t_i and F(fittingIndicators), and zero covariance with A¹_i.
   This is the full expansion of `w1OutcomeMap`.
9. For any Θ,i,j,x,z,G:ℝ→Θ,P:Θ→ℝ, independence of t_i and t_j implies
   independence of t_i with G(Y_j), with P(G(Y_j)), and zero covariance
   with the latter. There is no i≠j premise: the positive-marginal law makes
   the i=j independence premise impossible, which does not affect other cases.
10. There exist a design on Ω=Fin 4,I=Fin 3, a finite J⊆Fin 3, and
    G:(J→ℝ)→ℝ with normalization, positive marginals, and individual
    independence of t₀ and every t_j (j∈J), but
    `Cov(A¹_0,G(fittingResponses J 1 0))≠0`. Thus the nonlinear fitting
    warning is a genuine existential assertion, not a universal premise.

All function arrows from J above mean functions from its membership subtype.
The fitting sets and maps are fixed before w is drawn. Parameters and any fixed
covariates are allowed inside the deterministic G and P. No assertion permits
assignment-dependent fitting sets or additional unmodeled fitting randomness.
The docstring describes whole-vector independence, scalar propagation,
additive predictions, leave-one-out fits under mutual independence, and
other-block fits under independence of entire block vectors.

Junk-value audit: UnitLaw supplies every marginal strictly positive; Nonempty I
protects the ATE denominator where used. Clauses 5 and 6 have no division by |I|
and safely allow an empty I (their i-quantifier then has no instances). Finite
sets J may be empty: their function space is a singleton and any deterministic
prediction from it is constant, so independence and zero covariance are
meaningful, not fabricated values. Empty sums/products are 0/1. Empty block
fibers similarly give constant vectors. No `sInf`, `sSup`, limsup/liminf,
log/sqrt/rpow, Bochner integral, infinity-toReal, or default choice occurs.
Arbitrary codomain Θ may be empty, in which case no fitting G exists because
the real-vector domain is inhabited; this standard empty-type specialization
does not make the positive, nonempty specializations vacuous. Independence
here is a finite test-function identity and entails ordinary independence on
the finite image, so no nonmeasurable-function counterexample is in play.
The nontrivial nonlinear existential can be realized by the real XOR law with
J={1,2}, G(v)=v₁+v₂-2v₁v₂. Fair mutually independent unit assignments give
nonempty instances of all independence premises in the universal clauses.
