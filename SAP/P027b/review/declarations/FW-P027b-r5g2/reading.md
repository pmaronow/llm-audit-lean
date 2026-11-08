# Blind reading

This file was written before opening `claims.json` or `record.json`. The source
statements, docstrings, and every entry in `closure.json` were read. The 56
generated `_proof_` entries were also inspected by Lean in `scratch/Blind.lean`:
they certify numeral instances, the positivity/normalization of phase weights,
the positivity of the four row parameters, and the zero/addition/scalar closure
properties of the stated subspaces. None adds a substantive hypothesis. The
constructors and projections of `Design` and `PhaseDecomposition` have exactly
the fields described below.

## SAP.P027b.T19

The theorem asserts the conjunction of eight propositions. They are conclusions,
not assumptions supplied to the theorem.

### Basic finite design and statistics, fully expanded

A `Design U Ω` has finite types U and Ω, real weights w(ω) ≥ 0 with
Σω w(ω) = 1, and a Boolean selection rule s(ω,k). Its expectation is the finite
sum E_D f = Σω w(ω)f(ω). Write I_k(ω) = 1 if s(ω,k) is true and 0 otherwise,
π_k = Σω w(ω)I_k(ω), π_kl = Σω w(ω)I_k(ω)I_l(ω), and
Δ_kl = π_kl − π_kπ_l. Its variance is
Σω w(ω)(f(ω) − Σν w(ν)f(ν))².

The HT total is t(y,ω) = Σk I_k(ω)y_k/π_k, and its mean is t(y,ω)/|U|.
The HT variance estimate is the ordered double sum

    h(y,ω) = Σk Σl [if π_kl > 0 then
      I_k(ω)I_l(ω)(Δ_kl/π_kl)(y_k/π_k)(y_l/π_l) else 0].

For Z = {(k,l) : k ≠ l and π_kl = 0}, the quadratic correction is

    q(y,ω) = Σ(k,l)∈Z [I_k(ω)y_k²/(2π_k) + I_l(ω)y_l²/(2π_l)].

The corrected total-variance estimate is c₂(y,ω) = h(y,ω)+q(y,ω).
All pairs in both formulas are ordered. The WR mean-variance estimate with
integer parameter m is

    w(y,ω) = [Σk I_k(ω)(y_k/(π_k/m) − t(y,ω))²]
             / [|U|² m (m−1)],

where m−1 in this denominator is subtraction in the reals.

### The particular periodic design

For natural r > 0 and m ≥ 2, let G = Fin r × Fin 2, U = Σg:G Fin m, and Ω = G.
There are q = 2r groups and N = mq units. A single group g is selected with
p_g = 1/(6r) when its second coordinate is 0, and p_g = 5/(6r) otherwise.
All m units of that group are selected. `oneDraw` selects exactly the drawn
group; `liftDesign` preserves its weights and selects every unit whose group is
selected. Thus `phaseOriginal` is this explicit finite probability experiment.
`phaseSize` is x_k = 2 in the first class and 10 in the second class.

For a real vector z on U, put Y_g = Σj z_(g,j), Q_g = Σj z_(g,j)²,
Q = Σk z_k². The four periodic statistics are

    V(z) = Var_D(t(z,·)/N),
    H(z) = E_D[h(z,·)/N²],
    C(z) = E_D[c₂(z,·)/N²],
    W(z) = E_D[w(z,·)].

Define R(q) = 5(q−1)/(9q−5), c(q) = 6q/(9q−5), and
T(z) = C(z) − (1+R(2r))H(z). The square norm means Σk z_k².

### First conjunct: fixed populations

For every r,m as above, and then every z:U→ℝ with Σk z_k = 0, all of the following
hold (the quantifiers precede the centering hypothesis):

    V = (Σg Y_g²/p_g)/N²;
    H = V − (Σg Y_g²)/N²;
    0 ≤ (Σg Y_g²)/N²;
    C − H = (N−m)Q/N²;
    W = [m Σg Q_g/p_g − N²V]/[N²(m−1)].

### Second conjunct: outcome model moments

For every type Ξ with a measurable space, every probability measure μ on Ξ,
then every r>0, m≥2, β,σ²∈ℝ with σ²≥0, and every family of errors
ε_k:Ξ→ℝ satisfying the following conditions: each ε_k is integrable with
integral 0; every ε_k ε_l is integrable with integral σ² if k=l and 0 otherwise.
Here and throughout, `outcomeE` means the real Bochner integral against μ.

Let u_k(ξ)=βx_k+ε_k(ξ), z_k(ξ)=u_k(ξ)−N⁻¹Σl u_l(ξ), and
Y_g(ξ)=Σj z_(g,j)(ξ). Put

    L = 16m²β² + mσ²(1−1/q),
    B(ξ) = Σg Y_g(ξ)²/N²,
    V̄ = ∫V(z(ξ))dμ, H̄ = ∫H(z(ξ))dμ,
    C̄ = ∫C(z(ξ))dμ, W̄ = ∫W(z(ξ))dμ,
    Q̄ = ∫Σk z_k(ξ)²dμ.

The conclusions, simultaneously, are

    for every g, ∫Y_g²dμ = L;
    ∫B dμ = 16β²/q + σ²(N−m)/N²;
    V̄ = (9q/5)∫B dμ;
    H̄ = V̄−∫B dμ;
    if V̄>0, then (H̄−V̄)/V̄ = −5/(9q);
    Q̄ = 16Nβ²+(N−1)σ²;
    C̄ = H̄+(N−m)Q̄/N²;
    W̄ = (9/5)σ²/m.

Also, for every real ρ, if σ²=900(1−ρ²) and
β²=900ρ²(N−1)/(16N), then Q̄=900(N−1) and the tuple (V̄,H̄,C̄,W̄)
equals the following *explicit arithmetic* tuple (`periodicModelPredictions`):
set q=N/m, s=900(1−ρ²), b=900ρ²(N−1)/(16N), B=16b/q+s(N−m)/N²,
v=(9q/5)B, h=v−B, c=h+(N−m)(16Nb+(N−1)s)/N², and w=(9/5)s/m;
the tuple is (v,h,c,w). No independence assumption is needed for this
moment-only conjunct beyond the displayed cross moments.

### Third conjunct: deterministic decomposition

For every r>0,m≥2 and centered z, define real vector subspaces as follows:

* centered space: vectors with total sum zero;
* within space: vectors with sum zero separately in each group;
* signal space: the real linear span of the single vector k↦x_k−6;
* low space: vectors constant inside each group, zero on the second class, with
  total sum zero;
* high space: vectors constant inside each group, zero on the first class, with
  total sum zero.

The dimensions are respectively N−1, N−2r, 1, r−1, r−1. The four component spaces
(within,signal,low,high, in that index order Fin 4) are pairwise orthogonal for
the inner product Σk v_kw_k. A `PhaseDecomposition` is four real vectors
(w,s,l,h), satisfying: each group sum of w is zero; s_k=b(x_k−6) for some real b;
l_k=v_g for a group vector v of group-sum zero, supported on the first class;
h has the corresponding representation supported on the second class; and
z=w+s+l+h pointwise. Such a decomposition exists, and any two have identical
four component vectors. For every such decomposition,

    T(z) = (N−m)/N² [||w||²+c(2r)(||h||²−||l||²)],
    −(N−m)c(2r)||l||²/N² ≤ T(z).

For every real β, T(β(x−6)+z)=T(z). `Nonempty` of a decomposition asserts
existence of actual vectors, not an assumed conclusion.

### Fourth conjunct: Gaussian distribution and expectation

For every measurable Ξ and probability μ, r>0,m≥2, real β,σ² with σ²>0,
and errors ε_k which are μ-a.e. measurable, individually have pushforward law
N(0,σ²), and are jointly independent under μ, form z as above. Set
a=(N−m)σ²/N² and c=c(2r). There exist three real random variables X₀,X₁,X₂
on the *same* Ξ, independent under μ, with respective laws
χ²_(N−2r), χ²_(r−1), χ²_(r−1), and

    T(z(ξ)) = a[X₀(ξ)+c(X₁(ξ)−X₂(ξ))] for μ-almost every ξ.

Moreover ∫T(z)dμ = a(N−2r)>0. `chiSquaredLaw d` is concretely the
pushforward of d independent standard real Gaussians by v↦Σj v_j².
`GaussianNoise` uses Mathlib's `gaussianReal 0 σ².toNNReal`, with σ² its
variance parameter, and `iIndepFun` for independence of the whole finite family.

### Fifth conjunct: lower tail

For every measurable Ξ, probability μ, natural r>0,m≥2,K>0, real β,σ²,ℓ with
σ²>0 and ℓ>0, and errors indexed by i∈Fin K and k∈U such that *for each i*
the k-indexed family is independent N(0,σ²), form z_i and

    a=(N−m)σ²/N², c=c(2r), k=ac, d=(r:ℝ)−1,
    Tbar(ξ)=K⁻¹Σi T(z_i(ξ)),
    P=(μ{ξ:Tbar(ξ)≤−ℓ}).toReal,
    J=floor(ℓ/(4k))∈ℤ, h=ceil(d/2)∈ℤ.

Then P≤exp(−ℓ/(4k))2^(d/2); if h<J, this bound is at most
2^(−((J:ℝ)−(h:ℝ))). The statement imposes no independence between distinct
i-indexed populations and asserts no improvement of the bound with K.

### Sixth through eighth conjuncts: the four printed rows

The constants indexed in the following order are exact rationals:

| row | r | m | printed H | printed C | printed contrast t | exponent e |
|---|---:|---:|---:|---:|---:|---:|
| 0 | 2 | 30 | 1412.15 | 2029.28 | −102561/1550 | 189 |
| 1 | 10 | 30 | 1564.34 | 2396.58 | −29703/1750 | 213 |
| 2 | 2 | 60 | 1430.59 | 2032.07 | −281297/3100 | 522 |
| 3 | 10 | 60 | 1562.38 | 2395.86 | −25671/1750 | 371 |

For every measurable Ξ, probability μ, then row∈Fin 4, natural K>0, real β,
and errors ε_(i,k) such that each population's errors are independent
N(0,17.91), let Hbar=K⁻¹Σi H(z_i) and Cbar=K⁻¹Σi C(z_i), with the row's r,m.
Then

    μ{|Hbar−printed H|≤0.005 and |Cbar−printed C|≤0.005}.toReal ≤ (2^e)⁻¹.

Again there is no condition on dependence between populations. The arithmetic
predictions at (N,m,ρ)=(120,30,.99),(600,30,.99),(240,60,.99),(1200,60,.99)
are, in that order,

    (1575.3366,1356.53985,2025.91485,1.0746),
    (1586.1366,1542.07725,2395.65225,1.0746),
    (1581.5493,1361.889675,2034.077175,0.5373),
    (1586.9493,1542.867375,2397.154875,0.5373).

Also −5/(9·4)=−5/36 and −5/(9·20)=−1/36. For each row,
printed C−(1+R(2r))printed H=t;
.005(2+R(2r)) is 77/6200 for r=2 and 89/7000 otherwise;
(2^e)⁻¹ is at most respectively 10^−56,10^−64,10^−157,10^−111.
Finally set ℓ=−t−.005(2+R(2r)),
k=[(N−m)17.91/N²]c(2r). For every row ℓ,k>0,
R(2r)=15/31 for r=2 and 19/35 otherwise,
floor(ℓ/(4k))−ceil(((r:ℝ)−1)/2)=e as an integer, and for *all* real H,C,
closeness to the respective printed numbers by at most .005 implies
C−(1+R(2r))H≤−ℓ.

### Junk-value and boundary audit

Real division is total, with x/0=0. The primitive statistics permit meaningless
zero inclusion probabilities on arbitrary designs; here every unit has the
strictly positive probability p_g. Joint-zero divisions in h are skipped by its
conditional. N>0, m>1, q=2r≥2, 9q−5>0, and k>0 in the tail assertions, so all
displayed relevant denominators are nonzero. The formula-only prediction
function is total at invalid arbitrary real inputs, but this statement uses
positive N,m and only calibrates the function at valid values.

Natural subtraction is truncated in dimensions and chi-square degrees
(N−1,N−2r,r−1); r>0,m≥2 put them in their intended nonnegative ranges. At r=1,
the two parity spaces and χ²₀ are genuinely zero dimensional; the product over
Fin 0 has one empty vector and its square sum is zero, giving point mass at zero.
No unintended empty population or sample occurs. Ω cannot be empty for any
`Design`, since its weights sum to 1. Natural and integer casts here are exact;
`PeriodicTail` uses real r−1 and real J−h in its real power, whereas the row
certificate subtracts two integers. Floor and ceiling are the ordinary total
integer functions on finite reals.

Real powers on base 2 are the usual positive-base powers. Squaring elsewhere is
natural exponentiation; negative integer powers of 10 are reciprocal powers and
have positive base. There are no problematic powers, logs, or square roots in
the SAP arithmetic. Gaussian construction internally uses its standard
zero-variance Dirac convention; σ².toNNReal replaces negative inputs by zero,
but positive variance is explicitly required whenever `GaussianNoise` is used
here. The model-moment conjunct allows σ²=0 without asserting a nondegenerate law.

Real Bochner integrals are zero for a nonintegrable function. This does not
change these meanings: the moment conjunct explicitly assumes all needed first
and pair moments, which give integrability of the finite quadratic statistics;
the Gaussian conjuncts imply these moments. A pushforward by a function that is
not a.e. measurable can default to the zero measure, but ε is a.e. measurable,
and the polynomial chi-square pushforward is measurable. The asserted X laws
are probability laws, so cannot be a zero-measure pushforward. Measures of sets
are outer measures if the sets are not measurable; all events here are formed
from a.e. measurable finite quadratic statistics. Their measures are ≤1, so
ENNReal.toReal never sees ∞ (whose toReal would be 0). The usual completed/a.e.
interpretation suffices for these probabilities. No sInf/sSup, liminf/limsup,
default choice of partial functions, or limit operation occurs.

The docstring describes exact expectations, moments, diagonalization, Gaussian
laws and probability bounds; it does not call the result a deterministic
exclusion or a refutation. Its mention of an accepted claim is not used in this
blind reading.

## SAP.P027b.T20

This is a conjunction of a universal theorem and an existential example.
First quantify over finite types U and Ω, then a finite probability design D
(nonnegative real weights summing to 1, arbitrary Boolean selections), assume
π_k=Σω w(ω)I_k(ω)>0 for every k, and then quantify over every y:U→ℝ.
Define π_kl=Σω w(ω)I_k(ω)I_l(ω), Δ_kl=π_kl−π_kπ_l,
t(y,ω)=Σk I_k(ω)y_k/π_k,
h(y,ω)=ΣkΣl [if π_kl>0 then
I_k I_l (Δ_kl/π_kl)(y_k/π_k)(y_l/π_l) else 0], and
A(y)=ΣkΣl [if k≠l and π_kl=0 then y_ky_l else 0].
Expectations and variances are the weighted finite sums defined in the T19
section. The conclusions are

    E_D h(y,·)=Var_D t(y,·)+A(y),

and, if either every y_k≥0 or every y_k≤0, both A(y)≥0 and
E_D h−Var_D t≥0.

Second, there exist a design D on population Fin 3 and sample space Fin 2,
and two outcome vectors yPos,yNeg on that *same* design, such that every π_k>0,
A(yPos)>0, A(yNeg)<0, E_D h(yPos)−Var_D t(yPos)>0, and
E_D h(yNeg)−Var_D t(yNeg)<0. The statement does not prescribe the witness design
or vectors; it requires actual bias of each sign. The docstring matches these
parts literally.

The only potentially junk operation is real division: the π_k denominators
are positive, and h evaluates its π_kl division only in the positive branch.
Its zero branch is the explicit omission of zero-probability pairs. Everything
is a finite real sum, so no integrability or extended-real conventions occur.
U may be empty in the universal part, producing valid zero sums; Ω cannot be
empty because Σωw(ω)=1. The existential types are nonempty. There are no
truncated subtractions, real powers, logarithms, square roots, extrema, limits,
or partial-function defaults. Casts of the finite sizes are exact.

## SAP.P027b.T21

Quantify first over finite U,Ω and design D as just defined; assume every π_k>0.
Then quantify over arbitrary y:U→ℝ and arbitrary ordered-pair exponent functions
a,b:U→U→ℝ. Assume that for every ordered pair k≠l with π_kl=0,

    a_kl>0, b_kl>0, and (a_kl)⁻¹+(b_kl)⁻¹=1.

This is the full unfolding of Mathlib `Real.HolderConjugate`, equivalently both
finite exponents exceed 1 and their reciprocals sum to 1. Nothing is required
of a,b at other pairs. Let Z be precisely these ordered distinct zero-inclusion
pairs, and use t,h,A,E_D,Var_D exactly as expanded in T20. Define

    Astar=Σ(k,l)∈Z [|y_k|^(a_kl)/a_kl + |y_l|^(b_kl)/b_kl],
    Ahat(ω)=Σ(k,l)∈Z [I_k(ω)|y_k|^(a_kl)/(a_kl π_k)
                      +I_l(ω)|y_l|^(b_kl)/(b_kl π_l)],
    hC(ω)=h(y,ω)+Ahat(ω).

Powers here are real powers (`Real.rpow`), and the theorem asserts all five
conclusions: A≤Astar, −A≤Astar, E_D Ahat=Astar,
E_D hC=Var_D t+A+Astar, and Var_D t≤E_D hC. No sign condition on y is assumed.
The docstring's unbiased correction, both bounds, exact expectation, and
conservativeness correspond to these five assertions.

Every used π and exponent denominator is positive; the zero-joint branch of h
is skipped. Real powers have nonnegative bases |y_k|; a zero base with a positive
exponent gives 0, and no 0^0 or negative exponent at a zero base is used. Unused
pairs' exponents can be arbitrary without entering any evaluated summand. Real
division or rpow defaults outside these safe conditions do not affect the
statement. Finite weighted sums avoid Bochner and toReal defaults. Empty U gives
legitimate empty sums, Ω cannot be empty, and there are no other listed junk
operations.

## SAP.P027b.T22

Quantify over finite U,Ω, then D, assume π_k>0 for every k, then quantify over
y and real ordered-pair functions a,b. Use exactly the finite sums t,h,Ahat,hC
expanded in T20 and T21; no additional primitive notion occurs. Assume, in this
order, for every pair in Z={(k,l):k≠l and π_kl=0}:

1. a_kl,b_kl>0 and a_kl⁻¹+b_kl⁻¹=1;
2. |y_k|^(a_kl)=|y_l|^(b_kl);
3. (−y_k)y_l=|y_k||y_l|.

The last condition says their product is nonpositive, including zero. The
conclusion is E_D hC=Var_D t. Only sufficiency is asserted; there is no converse
or existence claim. The equality hypotheses are algebraic equality cases of
Young's inequality and of the sign bound, rather than an explicit premise that
the desired expectation already equals the variance. The docstring describes
these two additional equality conditions.

All junk-value conclusions for T21 apply independently here: the inclusion and
exponent denominators are positive, all real-power bases are absolute values,
and all used exponents are positive. For zero y the equality hypotheses can
hold with positive exponents in their ordinary meaning. Empty Z makes the pair
hypotheses vacuous, legitimately leaving the usual HT unbiasedness result;
there are also nonempty-Z instances with opposite nonzero outcomes. Empty U
gives zero statistics, Ω cannot be empty. No undefined expectations, extended
reals, limits, extrema, or other defaults occur.

## SAP.P027b.T23

For every finite U,Ω, every design D (weights ≥0 summing to 1 and Boolean
selections), assume π_k>0 for every k, and then for every y:U→ℝ, assert equality
of functions Ω→ℝ,

    h(y,·)+Σ(k,l)∈Z[I_k(·)y_k²/(2π_k)+I_l(·)y_l²/(2π_l)]
      = h(y,·)+Σ(k,l)∈Z[I_k(·)|y_k|^2/(2π_k)+I_l(·)|y_l|^2/(2π_l)],

where on the right the exponent 2 is a real exponent and the functions a,b are
both identically 2; the left uses natural squaring. The symbols Z,h,π,I and the
finite expectation and variance expand exactly as in T20. Also assert that the
finite expectation of the left-hand estimator is at least the finite design
variance of t(y,·)=Σk I_k(·)y_k/π_k. The function equality quantifies over every
sample, including sample-space points of probability zero. The theorem states
conservativeness in expectation, not pointwise nonnegativity of the estimate.
The docstring correctly describes the specialization and conservativeness at
the level of this blind reading.

All used denominators π_k and 2π_k are positive, and the π_kl division in h is
guarded. Absolute-value bases with real exponent 2 have their ordinary square
meaning, including at zero. Finite expectations have no existence issue.
Empty U is permitted and unproblematic; Ω is necessarily nonempty. No toReal,
integral, truncated subtraction, unsafe real-power domain, extremum, limit,
logarithm, square root, or default partial value is used.
