# Blind reading

Saved at step 1, before opening `claims.json` or `record.json`. Sources read:
the three target docstrings and declarations in `Challenge/Part1.lean`, every
source declaration listed in `closure.json`, and the generated constructors,
projections, and auxiliary proofs printed in `scratch/ClosureCheck.out`.
The auxiliary proofs attached to numerals merely certify `Nat.AtLeastTwo` for
numeral syntax. The two auxiliary proofs for `independentDesign` establish
nonnegative weights and total mass one. They introduce no hypotheses.

## SAP.P037a.T11

The docstring describes independent retained-block totals, finite unbiasedness
and variance identities, bounds, consistency, Gaussian limits, contrasts, and
fitted estimates under regularity conditions. The theorem is a conjunction of
16 universally quantified propositions, not one implication sharing all its
hypotheses. Here is their full mathematical content.

### Objects and notation, unfolded

A `Design Ω`, for a finite type Ω, is a real function d on Ω with d(w) ≥ 0 for
every w and Σ_w d(w) = 1. Write E_d X = Σ_w d(w)X(w), and
Var_d X = E_d(X²) − (E_d X)². These are finite weighted sums.

A `RetainedRow B` specifies, for each block b in {0,…,B−1}, natural numbers
n_b (students) and a_b (assignments), a design d_b on {0,…,a_b−1}, a Boolean
exposure e_b(z,i), and fixed real arrays y_bi, g_bi, π_bi. Its structure fields
require π_bi = Σ_z d_b(z)1{e_b(z,i)} and π_bi > 0, for every student. A
Boolean in an `if` tests equality to true. No independence among students
inside a block is required. Neither outcomes nor g depend on the assignment.

Let N = Σ_b n_b. A row assignment w chooses one z_b for each block. Its law
is exactly P(w) = Π_b d_b(w_b). In particular block independence is built into
the law used in the theorem. For any predicate A, `rowProbability r A` is
Σ_w P(w)1{A(w)}. The separately named `independentDesign r.law` has the same
weights P. More generally `independentDesign` constructs this product law
for any finite family of finite designs.

The individual contribution is C(I,π,y,g) = g + (I/π)(y−g). Put
T_b(z) = Σ_i C(1{e_b(z,i)},π_bi,y_bi,g_bi),
μ̂(w) = (Σ_b T_b(w_b))/N, μ = (Σ_b Σ_i y_bi)/N, and
V = Σ_b Var_{d_b} T_b. These respectively unfold `blockTotal`, `oracleMean`,
`potentialMean`, and `totalBlockVariance`.

For a sequence r_B with B+1 blocks, `BlockBounds r m c η K` means precisely:
m is natural; c,η,K are real; c>0, η>0, K≥0; for every B≥0,
N_B≥c(B+1); and for every b, n_Bb≤m and, for every student i,
π_Bbi≥η, |y_Bbi|≤K, |g_Bbi|≤K. Constants are uniform in B,b,i.
Below write A = K+2K/η and D=mA.

A `PairedExposure r` supplies a second Boolean exposure e'_b(z,i), fixed
y'_bi,g'_bi,π'_bi on the very same blocks, students, assignments and designs.
It requires π'_bi = E_{d_b}1{e'_b(z,i)} > 0. Define
T'_b(z)=Σ_i C(1{e'_b(z,i)},π'_bi,y'_bi,g'_bi), H_b=T_b−T'_b,
Δ=(Σ_b Σ_i(y_bi−y'_bi))/N, and Δ̂(w)=(Σ_b H_b(w_b))/N.
These unfold `contrastBlockTotal`, `populationContrast`, and
`oracleContrast`. The two exposures need not be disjoint or independent.

For a natural number q, `Covariates r q` is an arbitrary fixed real array
x_bik, k∈{0,…,q−1}. For a real vector β and a real array p_bi, define
F(β,p,w) = (1/N)Σ_b Σ_i C(1{e_b(w_b,i)},p_bi,y_bi,Σ_k x_bik β_k).
This is `fittedMean`. `fittedCoefficient r x p w` is G(p,w)⁻¹v(p,w), where
G_kl = Σ_b Σ_i (1{e_b(w_b,i)}/p_bi)x_bik x_bil and
v_k = Σ_b Σ_i (1{e_b(w_b,i)}/p_bi)x_bik y_bi.
Multiplication means finite matrix-vector multiplication. The deterministic
normalized `covariateGram` and `covariateRhs` are respectively
Q_B,kl=(Σ_b Σ_i x_Bbik x_Bbil)/N_B and
v_B,k=(Σ_b Σ_i x_Bbik y_Bbi)/N_B.

### The sixteen conjuncts and their quantifiers

1. `individualUnbiased`: for every finite Ω, design d, real function I on Ω,
   and real π,y,g, if π≠0 and E_d I=π, then E_d C(I,π,y,g)=y. Here I need
   not be an indicator and π need not be positive.
2. `individualBound`: for all real I,π,y,g,K,η, if I=0 or I=1, η>0,
   π≥η, |y|≤K and |g|≤K, then |C(I,π,y,g)|≤K+2K/η.
3. `blockUnbiased`: for every natural B, row r and b∈Fin B,
   E_{d_b}T_b=Σ_i y_bi, with only the row structure's conditions.
4. `oracleUnbiasedVariance`: for every B and row r with N>0,
   E_P μ̂=μ and Var_P μ̂=V/N².
5. `blockIndependence`: for every B, row r and family of arbitrary real
   functions f_b:ℝ→ℝ, E_P Π_b f_b(T_b(w_b)) = Π_b E_{d_b} f_b(T_b).
6. `oracleFiniteBounds`: for every sequence r_B, natural m, real c,η,K
   satisfying `BlockBounds`, every B and every real ε>0:
   |T_Bb(z)|≤D for all b,z; Var T_Bb≤D² for all b;
   V_B/N_B²≤D²/[c²(B+1)]; and
   P_B(ε<|μ̂_B−μ_B|)≤D²/[c²(B+1)ε²].
7. `oracleConsistency`: for every sequence and constants satisfying the
   same bounds and for every ε>0, P_B(ε<|μ̂_B−μ_B|)→0 as natural B→∞.
   This is convergence in probability on possibly different finite spaces.
8. `oracleNormality`: universally quantify the same sequence and constants,
   and a real σ²>0; additionally require V_B≥σ²(B+1) for every B. Then:
   (a) for every B and ε>0 such that 2D<ε√(σ²(B+1)),
   Σ_b E_{d_Bb}[U_Bb² 1{ε√V_B<|U_Bb|}]=0, where
   U_Bb=T_Bb−E T_Bb; and (b) for every real x,
   P_B(N_B(μ̂_B−μ_B)/√V_B≤x)→Φ(x). Here Φ(x) is the probability of
   (−∞,x] under Mathlib's Gaussian measure with mean 0 and variance 1.
9. `centeredBlockBound`: for every B,row r,m∈ℕ,η,K∈ℝ, assuming η>0,
   K≥0, all n_b≤m and all π_bi≥η, |y_bi|≤K, |g_bi|≤K,
   every b,z satisfies |T_b(z)−E T_b|≤2D. N>0 is not assumed here.
10. `centeredTotalIdentity`: for every B,row r with N>0 and every w,
    Σ_b(T_b(w_b)−E T_b)=N(μ̂(w)−μ).
11. `contrastFinite`: for every B,row r with N>0, second exposure s,
    natural m and real η,K, assume η>0, K≥0, n_b≤m, and the bounds
    π≥η, |y|,|g|≤K for each of the two exposures. Then
    E_P Δ̂=Δ; Var_P Δ̂=(Σ_b Var H_b)/N²;
    |H_b(z)|≤2D for all b,z; and Var H_b≤(2D)² for all b.
12. `contrastLimits`: for every sequence r_B, second exposure sequence s_B,
    m,c,η,K satisfying `BlockBounds` and the same bounds for the second
    exposure, (a) for every ε>0, P_B(ε<|Δ̂_B−Δ_B|)→0; and (b) for every
    real v>0 with W_B=Σ_b Var H_Bb≥v(B+1) for every B, and every real x,
    P_B(N_B(Δ̂_B−Δ_B)/√W_B≤x)→Φ(x).
13. `contrastRate`: universally quantify the sequence, second exposures,
    and constants with the same two-exposure bounds. For every B and ε>0,
    Var_P Δ̂_B≤(2D)²/[c²(B+1)] and
    P_B(ε<|Δ̂_B−Δ_B|)≤(2D)²/[c²(B+1)ε²].
14. `contrastLindeberg`: universally quantify the same data, and v>0 with
    W_B≥v(B+1) for every B. For every B and ε>0 with
    4D<ε√(v(B+1)),
    Σ_b E[(H_Bb−E H_Bb)² 1{ε√W_B<|H_Bb−E H_Bb|}]=0.
15. `fittedSubtractions`: for every B,q,row r with N>0,covariates x,
    real vectors βhat,βstar, real array p, and assignment w, assume
    p_bi>0 for all b,i. Then
    F(βhat,π,w)−F(βstar,π,w)
    =Σ_k [(Σ_bi (1−1{e_b(w_b,i)}/π_bi)x_bik)/N](βhat_k−βstar_k),
    and
    F(βhat,p,w)−F(βhat,π,w)
    =(1/N)Σ_bi 1{e_b(w_b,i)}(y_bi−Σ_k x_bik βhat_k)(p_bi⁻¹−π_bi⁻¹).
16. `fittedLimits`: for every fixed natural q, sequence r_B, covariates x_B,
    arrays pHat_B(w)_bi (arbitrary functions of the row assignment), natural
    m, real c,η,K,L, real q×q matrix Q and real q-vector v, assume:
    `BlockBounds`; |x_Bbik|≤L for all indices; Q_B,kl→Q_kl and v_B,k→v_k
    for all k,l; for every real vector a≠0, Σ_k a_k(Qa)_k>0;
    pHat_B(w)_bi>0 for every B,w,b,i; for every ε>0,
    P_B(∃b,i: ε<√(B+1)|pHat_B(w)_bi−π_Bbi|)→0; and for every B,b,i,
    g_Bbi=Σ_k x_Bbik (Q⁻¹v)_k. After these assumptions define
    βstar=Q⁻¹v, βhat_B(w)=G(pHat_B(w),w)⁻¹v(pHat_B(w),w), and
    μhat_B(w)=F(βhat_B(w),pHat_B(w),w). The conclusions are:
    for every ε>0, P_B(∃k: ε<|βhat_B(w)_k−βstar_k|)→0;
    for every ε>0, P_B(ε<√(B+1)|μhat_B−μ̂_B|)→0;
    for every ε>0, P_B(ε<|μhat_B−μ_B|)→0;
    and for every real σ²>0 with V_B≥σ²(B+1) for all B, and every real z,
    P_B(N_B(μhat_B−μ_B)/√V_B≤z)→Φ(z).

Every arrow to zero or Φ above is `Filter.Tendsto` from `atTop` on natural
B to the ordinary real neighborhood filter. None is a `limsup` or a
totalized limit operator.

### Junk-value and boundary conventions

Real division is total and division by zero is zero. The individual identity
assumes π≠0; row fields ensure π>0; uniform bounds ensure η>0; normalizations
using N explicitly assume N>0 or follow from N_B≥c(B+1)>0; p in the fitted
identities and pHat in the limits are strictly positive; c² and ε² appearing
in bounds are positive. The definitions of means on N=0 would return zero,
but no conclusion interpreting a population mean uses that case.

`Real.sqrt` returns zero on nonpositive inputs. V and W are nonnegative
finite variances, and every normalizing square root used for Gaussian limits
has a strictly positive lower bound. Threshold square roots likewise have
positive σ² or v and B+1>0. The √(B+1) factor is positive.

Mathlib matrix inverse is the ordinary inverse when the determinant is a
unit and is the zero matrix otherwise. Thus a singular empirical G gives
βhat=0; it is not, at that assignment, a general least-squares minimizer.
No finite-sample minimization conclusion is stated. The population Q in the
limit assumptions is positive definite (and is symmetric as a limit of Gram
matrices), so for q>0 its inverse is the ordinary inverse. The empirical
singular-case convention remains part of the estimator definition and must
be assessed against the intended estimator.

The Gaussian's variance is the nonnegative real number 1. Its probabilities
are finite (at most 1), so `ENNReal.toReal` never turns ∞ into zero here.
There are no Bochner integrals in the SAP closure: expectations are finite
sums, so no nonintegrability convention is used. There are no logs, real
powers, infima or suprema, partial-function defaults, or unbounded-sequence
`limsup`/`liminf` operations.

Empty finite sums are zero and empty finite products are one. A `Design` on
an empty Ω cannot exist, since its total would be 0=1. Accordingly every
assignment space of an actual block has at least one element. Individual
blocks may have no students. A row with B=0 exists but has N=0 and so cannot
satisfy an N>0 premise. The asymptotic sequence always has B+1 blocks and
positive N; m=0 cannot satisfy all `BlockBounds`. q=0 is permitted and gives
an empty coefficient vector and zero fitted regressions; its positive
definiteness condition has no nonzero vectors to test. This is a legitimate
zero-covariate special case rather than evidence that q>0 cases are empty.
Natural indices and counts are embedded exactly in ℝ; all subtraction in
T11's formulas is real subtraction. No natural truncation is involved.

## SAP.P037a.T12

The theorem conjoins four propositions about the following total function
E:ℕ→ℕ (`eligibleCount`):

* E(n)=40 if n≤200;
* E(n)=64 if n>200 and n≥550;
* otherwise E(n)=4[10+⌊(6(n−200)+175)/350⌋], where the floor describes
  natural-number division and the subtraction is natural subtraction.

In the third branch 200<n<550, so n−200 is ordinary nonnegative integer
subtraction. In that branch E(n) is nearest-multiple-of-four rounding of
40+24(n−200)/350, with a formal half-up convention.

The complete conclusions, including all quantifiers, are:

1. For every pair of integers n,k, 350k ≠ 3500+6(n−200)−175.
   This says the interpolation in units of four never hits a half integer
   at any integer school size. These subtractions are in ℤ, not ℕ.
2. For every natural n, 40≤E(n)≤64 and 4 divides E(n); and for every pair
   of naturals n≤n', E(n)≤E(n').
3. For every natural n, E(n)=64 iff n≥521; for every natural n≥550,
   E(n)=64. The two real interpolation endpoint identities are
   40+24(200−200)/350=40 and 40+24(550−200)/350=64.
   Also E(100)=40, E(200)=40, E(375)=52.
4. E(100)/100=2/5, E(200)/200=1/5, E(375)/375=52/375,
   E(550)/550=64/550, E(715)/715=64/715. Here E and denominators are
   cast to ℝ before division.

The docstring calls this a corrected rule, describes these same conclusions,
and says the examples refute the interpretation that every school below 550
has exactly 64 eligible students; the literal upper bound of at most 64 is
preserved. The theorem itself is an arithmetic conjunction and does not
contain an existential random experiment or a factual assertion that any
particular school was sampled under this rule.

Junk conventions: natural subtraction is truncated at zero but is used only
in the branch n>200. Natural division is floor division with fixed positive
denominator 350. There is therefore no zero-denominator or negative-size
artifact in the rule. The half-up tie convention cannot affect any integer
n by conclusion 1. The real divisions all have fixed positive denominators.
The rule assigns 40 even at n=0 or n<40; it does not assert that a sample of
that size can be selected from such a school. No general E(n)/n assertion
at n=0 is present. All other totalization issues listed in the task (log,
sqrt, powers, integration, `toReal`, extrema, limits, empty index sums,
partial-function defaults) are absent. Auxiliary numeral proofs are harmless.

## SAP.P037a.T13

`fittedEffect(t,b,c)` is just t+bc for real arguments. It imposes no model,
regression, or data-fitting conditions by itself. `reduction(m,a)` is
(m−a)/m in ℝ. The theorem is the conjunction of three propositions:

1. Exact arithmetic: 0.04+(−0.85)·0.2=−0.13, and
   (0.2−0.08)/0.2=0.6.
2. For every real t, then b, then m, assume separately
   0.035≤t≤0.045, −0.855≤b≤−0.845, 0.222≤m≤0.223. Write d=t+0.2b.
   Then all of the following hold:
   −0.136≤d≤−0.124;
   0.086≤m+d≤0.099;
   it is not the case that 0.075≤m+d≤0.085;
   the fixed number 0.095 belongs to [0.086,0.099];
   124/223≤−d/m≤68/111;
   the fixed number 0.57 belongs to [124/223,68/111];
   and the fixed number 0.6 belongs to [124/223,68/111].
   Membership of these fixed numbers in the bound intervals does not assert
   that each is the prediction for every permissible t,b,m.
3. For every real t,b, if 0.035≤t≤0.045 and −0.855≤b≤−0.845, then
   −0.136≤t+0.2b≤−0.124. This repeats the effect interval without m.

All displayed decimals above are exact rational constants, not floating
point quantities. The docstring describes arithmetic consequences of the
printed coefficients and explicit coefficient/control intervals. It does
not claim that the model coefficients or observed control level have been
estimated inside Lean.

Junk conventions: real division by zero would yield zero in `reduction`,
but its use here has control 1/5. The variable denominator m in the interval
clause is at least 222/1000>0. Every other denominator is a fixed positive
integer interpreted in ℝ. Subtraction and negative coefficients are real
arithmetic, with no natural truncation. There are no square roots, logs,
real powers, integrals, `toReal`, extrema, limits, partial functions, or
empty index types in the T13 statement. Auxiliary numeral proofs are
ordinary arithmetic typeclass certificates.
