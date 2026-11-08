# Blind reading

This file was written before opening `claims.json` or `record.json`. It reads
the five Challenge declarations and the union of all 168 declarations listed
in their closures. Source definitions were read with line numbers. Generated
numeral proofs and pattern-match/equality machinery were also inspected using
`scratch/BlindInspect.lean` and its printed output. The generated proofs certify
ordinary numeral size/nonzero facts, not statistical hypotheses.

## Common mathematical notation, completely unfolded

All unit indices are the finite type `Fin n`, identified with integers
0,...,n-1. All scalar arrays take real values. A subset is a `Finset (Fin n)`.
Write U={0,...,n-1}, D(n,m)={S⊆U: |S|=m}, and Sᶜ=U\S. There is no
unmentioned distribution: E_m f=(sum over S in D(n,m) of f(S))/|D(n,m)|,
V_m f=E_m[(f-E_m f)²], and Pr_m(E)=|{S∈D(n,m):E(S)}|/|D(n,m)|.
These are ordinary finite real sums and divisions.

For A⊆U define M_A(a)=(sum over i∈A of a_i)/|A|,
M(a)=M_U(a), a°_i=a_i-M(a),
C_A(a,b)=M_A(ab)-M_A(a)M_A(b), and C(a,b)=C_U(a,b).
These unfold `mean`, `popMean`, `centered`, `sampleCov`, and `popCov`.
`Arm` has exactly two constructors. For t=treated let A_t(S)=S and s_t=m;
for t=control let A_t(S)=Sᶜ and s_t=n-m (natural subtraction).

Define the real allocation coefficients

    A(n,s)=2(n-s)/(s(n-1)),
    B(n,s)=2(n-s)n/(s³(n-1)),
    α(n,s)=s(n-s)/(n(n-1)),
    ℓ(n,s)=s(s-1)(n-s)(n-s-1)/(n(n-1)(n-2)(n-3)).

All subtractions in these four expressions are real subtractions, including
expressions whose operands originate as natural numbers. They are `W1A`,
`W1B`, `W1Alpha`, and `W1Ell`. Set

    Q_s(a,b)=A(n,s) M[(ab-M(ab))²]+B(n,s) M(a²)M(b²).

This is exactly `covarianceBound`, not a proposition or an assumed bound.

A `Population n d` is just three arrays x:Fin n→Fin d→ℝ and
yT,yC:Fin n→ℝ, with no constraints in its constructor. For a vector z in
ℝ^d, z·w=sum over k<d of z_k w_k. Define

    x̄_A,k=M_A(i↦x_i,k), G_kl=M(i↦x_i,k x_i,l),
    h_i=sum over k<d of x_i,k²,
    κ=sSup {h_i/n:i<n},
    L_A,kl=M_A(i↦x_i,k x_i,l)-x̄_A,k x̄_A,l,
    Lhat(S)=I_d-(m/n)x̄_S x̄_Sᵀ-((n-m)/n)x̄_Sᶜ x̄_Sᶜᵀ.

`standardized` means exactly x̄_U=0 and G=I_d. `interactedRegular P m`
means det(L_S)≠0 and det(L_Sᶜ)≠0 for every S∈D(n,m).
`noninteractedRegular P m` means det(Lhat(S))≠0 for every S∈D(n,m).
The determinant is Mathlib's determinant of a finite real matrix. No inverse
is used in these predicates. `pT n m` is (m:ℝ)/(n:ℝ) and `pC n m`
is ((n:ℝ)-(m:ℝ))/(n:ℝ). `scalarPopulation a yT yC r` has d=1
and x_i,0=r a_i, with the supplied outcomes.

Further definitions used by T5 are

    Cov_h(y)=M(hy)-M(h)M(y),
    ν3(A,y)_k=-x̄_A,k M_A(y-M(y)),
    T(n,s)=(n-s)(n-2s)/((n-1)(n-2)s²),
    Ccoef(n,m)=T(n,n-m).

These are `leverageCov`, `armNu3`, `NTTT`, and `NCCC`; subtraction inside
T is real, whereas the argument n-m in Ccoef is natural subtraction.
`firstVariance P A` is C_A(x_·,0,x_·,0).

General totalization conventions: real a/0=0; sums over empty finite sets
and coordinate types are zero. Accordingly M_∅=0, and E_m, V_m, and Pr_m
are zero if D(n,m) is empty. This would not be a probability distribution.
For n=0, population means and Gram entries are zero; the range defining κ
is empty and real sSup gives its default zero. For n>0 the range is finite,
nonempty, and bounded, so κ is an actual maximum. Real square root is zero
at negative inputs. Empty-dimensional matrices have determinant one and
identity equal to the unique empty matrix. There are no Bochner integrals,
extended-real conversions, real logarithms, real powers, infima, limsup,
liminf, or partially defined array lookups in these closures. Vector literals
are total functions on their indicated `Fin` types. Numeral casts are exact.

## SAP.P005a.T1

The Challenge statement is `T1WholeStatement`, a conjunction with no external
hypotheses and no existentially hidden data. The fixed arrays, in label order,
are a=(0,-3,-1,2,-4,-3) and b=(2,1,3,-3,1,1), n=6, m=4.
The first conjunct, `T1Statement`, asserts 4≤6, 1≤4<6, |D(6,4)|=15,
M(a)=-3/2, M(b)=5/6, C(a,b)=-23/12,
E_4 C_S(a,b)=-69/40, V_4 C_S(a,b)=16607/4800,
Q_4(a,b)=3829/1440, and Q_4(a,b)<V_4 C_S(a,b).

The remaining simultaneous conclusions are:

* M(ab)=-19/6, E_4 C_S(a,b)=[(4-1)6/(4(6-1))]C(a,b),
  A(6,4)=1/5, B(6,4)=3/40.
* M[(ab-M(ab))²]=113/36, M(a²)=13/2, M(b²)=25/6.
  The two summands of Q_4 are 113/180 and 65/32 respectively, and Q_4
  is also explicitly asserted to be their sum.
* V_4 C_S(a,b)-Q_4(a,b)=11531/14400>0.
* For every subset S of these six units, if S is nonempty, then for every
  real c,e, C_S(a+c,b+e)=C_S(a,b). Separately, for every real c,e the
  variances of these two statistics under D(6,4) coincide.
* For every S∈D(6,4), C_S(a°,b°)=C_S(a,b).
  Q_4(a°,b°)=835/128, V_4 C_S(a,b)≤Q_4(a°,b°), and
  Q_4(a°,b°)≠Q_4(a,b).

The docstring describes a six-unit counterexample to the uncentered bound,
with location invariance and a valid centered bound. The actual statement
contains this particular counterexample and its numerical details; the shift
invariance assertions are restricted to these fixed arrays.

Junk-value check: all numerical denominators are nonzero; n=6,m=4 gives 15
assignments and nonempty arms. The arbitrary subset in the shift statement
has an explicit nonempty hypothesis. The centered bound divides by ordinary
positive integers. No default convention changes any substantive assertion.

## SAP.P005a.T2

The statement is a conjunction of four universal assertions, with no global
data. First: for every natural n,m, every proof of n≥4, 0<m and m<n,
then every arm t and every two arrays a,b:Fin n→ℝ, both

    E_m C_A_t(S)(a,b) = (s_t-1)n/(s_t(n-1)) C(a,b),
    V_m C_A_t(S)(a,b) ≤ Q_s_t(a°,b°).

Second: for every natural n, every subset S⊆Fin n, if S is nonempty,
then every a,b:Fin n→ℝ and c,e:ℝ satisfy
C_S(a-c,b-e)=C_S(a,b). This quantifier allows n below four whenever a
nonempty subset exists.

Third: for every n,m with n≥4 and 0<m<n, then every t,a,b, set u=a°,
v=b°, s=s_t. It asserts sum_i u_i=sum_i v_i=0,
M(uv)=C(a,b), C_A_t(S)(a,b)=C_A_t(S)(u,v) for every S∈D(n,m), and

    V_m M_A_t(S)(uv)=(n-s)/(s(n-1)) M[(uv-M(uv))²].

It also asserts all of `W1ProductFacts`, which unfolds as follows. Put
A0=sum_i u_i², B0=sum_i v_i², G0=sum_i u_i v_i,
H0=sum_i u_i² v_i², Z(S)=(sum_{i∈A_t(S)}u_i)(sum_{i∈A_t(S)}v_i),
α=α(n,s), ℓ=ℓ(n,s). Then simultaneously

    E_m Z=αG0,
    V_m Z=(α-6ℓ)H0+ℓA0B0+(2ℓ-α²)G0²,
    V_m Z≤αA0B0,
    V_m[M_A_t(S)(u) M_A_t(S)(v)]=(V_m Z)/s⁴,
    V_m[M_A_t(S)(u) M_A_t(S)(v)]
       ≤(n-s)n/(s³(n-1)) M(u²)M(v²).

The third universal assertion finally says that if M(a)=0 and then M(b)=0,
the variance is bounded by the uncentered expression Q_s(a,b) itself.
Fourth: for every n,m with n≥4 and 0<m<n, and then every pair of arbitrary
functions U,V from subsets of Fin n to ℝ,
V_m(S↦U(S)-V(S))≤2V_m U+2V_m V. No independence hypothesis appears.

The docstring describes the expectation, repaired centered bound, invariance,
exact centered-product moments, and recovery under zero population means.
The formal minimum size is four, including in the general variance inequality.

Junk-value check: s_t≥1 and n-s_t≥1, and n≥4 makes n-1,n-2,n-3 all
nonzero. Thus α and ℓ, including their boundary-arm numerators, have their
ordinary values even when s=1 or s=n-1. Natural n-m is not truncated because
m<n. The only general subset assertion excludes the empty subset. All sums
are finite; there is no integrability assumption or hidden empty-design case.

## SAP.P005a.T3

This is another hypothesis-free conjunction about fixed data. Let n=16,m=8,
d=1, r=sqrt(8/71), a=(8,-8,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1),
x_i,0=r a_i, y_i=1/64 for i<2 and y_i=1 otherwise; yT=y and yC=0.
All Population and regularity notions here are the finite real matrix notions
defined above. The statement asserts standardization, both every-assignment
regularities, M(y²)≤1, M(yC²)=0, 1/4<m/n<3/4, |D(16,8)|=12870,
κ=32/71, and h_i y_i=8/71 for every i.

Writing V=V_8 C_S(h,y), it asserts

    V=1678565511/8259174400,
    Q_8(h,y)=117645319/619438080 < V,
    A(16,8)M(h²y²)+B(16,8)M(y²)M(h²)=334349/1744896 < V.

In addition:

* M(y²)=28673/32768 and m/n=1/2.
* For every i<16, at most seven labels j have x_j,0=x_i,0. For every
  S∈D(16,8), C_S(x,x)>0 and C_Sᶜ(x,x)>0.
* As functions on Fin 16, h_i=512/71 for i<2, and h_i=8/71 otherwise.
  M(h)=1 and M[(hy-M(hy))²]=0.
* Define K(S)=|S∩{0,1}|. Pr_8(K=0)=7/30, Pr_8(K=1)=8/15,
  Pr_8(K=2)=7/30. For every S∈D(16,8), K(S)≤2 and C_S(h,y) equals
  0, -27783/36352, or -11907/9088 according as K is 0, 1, or 2.
* V-Q_8(h,y)=329883773/24777523200>0. V minus the other failed
  expression is 287940733/24777523200>0.
* The quantity `W1ThirdBound`, fully unfolded as
  A(16,8)16²κ²M(y²)+B(16,8)M(y²)M(h)16κ, equals 60758087/9678720,
  and V is at most this quantity.
* Q_8(h-1,y°)=5550293259/13214679040, and V≤Q_8(h-1,y°).

The docstring calls this a standardized regular counterexample to two finite
bounds and records the third-expression and centered-bound comparisons.
There is no statement about failure of the third or asymptotic bound.

Junk-value check: sqrt has strictly positive argument; n=16,m=8 gives
nonempty finite design and two arms of size eight. κ is an actual finite
maximum. Regularity is asserted as nonzero determinants, with stronger
scalar positivity also included, so no singular-inverse interpretation is
involved. Every listed rational denominator is positive. The piecewise
definition at labels 0 and 1 is an ordinary decidable case split.

## SAP.P005a.T4

The statement has three universal conjuncts. First: for every n,d,m:ℕ and
Population P of those dimensions, assume n≥4, 0<m<n, and standardized P;
then for every t:Arm and K:ℝ assume M(y²)≤K, with y=yT for treated and
y=yC for control. Put s=s_t, h_i=sum_k x_i,k², κ=max_i h_i/n,
u_i=h_i-d, v_i=y_i-M(y), and

    R(P,s,K)=A(n,s)n²κ²K+B(n,s)nκdK.

All conclusions below hold simultaneously:

    M(h)=d;
    for every i, 0≤h_i≤nκ and |u_i|≤nκ; d≤nκ;
    M(u²)=M(h²)-d²; M(u²)≤M(h²)≤nκd;
    M(v²)=M(y²)-M(y)²; M(v²)≤K;
    M[(uv-M(uv))²]≤M(u²v²)≤n²κ²K;
    V_m C_A_t(S)(h,y)≤Q_s(u,v)≤R(P,s,K).

Second: for every n,m with n≥4 and 0<m<n, then every t and real p,
if 0<p<s_t/n then A(n,s_t)≤2/(p(n-1)) and
B(n,s_t)≤2/(p³n(n-1)).

Third: for every two functions d,m:ℕ→ℕ, every dependent sequence
P_n:Population n (d n), then every K,lo,hi:ℝ, assume all of
`W1SequenceAssumptions`, namely 0≤K, 0<lo<hi<1; for every n≥2,
d_n≤n, 0<m_n<n, M(yT_n²)≤K, M(yC_n²)≤K,
M(x_·,k²)≤K for every k<d_n, and lo<m_n/n<hi; and eventually,
for every sufficiently large n, x̄_U=0 and G=I_(d_n).
Then for every t:Arm, define

    V_n=V_(m_n)[S↦C_A_t(S)(h_n,y_n)],
    R_n=A(n,s_t)n²κ_n²K+B(n,s_t)nκ_nd_nK,
    r_n=nκ_n²+κ_nd_n/n.

There exists a real C≥0 such that eventually
0≤R_n≤Cr_n and 0≤V_n≤R_n. Also R=O(r) and V=O(r).
For every n≥2, V_(m_n)[S↦C_A_t(S)(h_n,y_n)/n]=V_n/n².
Finally that divided-statistic variance is O(κ_n²/n+κ_nd_n/n³).
`IsBigO atTop f g` is Mathlib's condition that there exists a real constant
c such that eventually ‖f_n‖≤c‖g_n‖ (for these real values, absolute values).
`∀ᶠ n in atTop` means there exists a natural threshold after which all
indices satisfy the property. Constants may depend on the input sequence,
moment/allocation constants, and arm; they precede the eventual index.

The docstring explicitly allows dimension zero, including in a sequence,
and describes the repaired chain and both deterministic asymptotic orders.

Junk-value check: finite-clause denominators and design are nonzero as in T2.
Although K is not separately assumed nonnegative in the finite clause,
M(y²)≤K forces K≥0 since n≥4. The sequence assumptions impose no conditions
at n=0,1. Those entries can involve empty designs, division by zero, and empty
suprema but are ignored by atTop; the exact variance scaling clause starts
at n=2. For every relevant index κ has a genuine finite nonempty maximum.
Dimension zero means h=κ=0 and all coordinate sums/matrix equations have
their mathematically ordinary empty-dimensional meanings; a zero Big-O
comparison then requires eventually zero variance, not a positive default
rate. Nothing uses the n-2 or n-3 denominators at n=2,3 in this target.

## SAP.P005a.T5

The statement is a hypothesis-free conjunction about n=6,m=2,d=1 and
x=(-8/5,-1,0,3/5,4/5,6/5), yT_i=x_i², yC_i=2x_i²+3.
It asserts standardization, every-assignment interacted regularity,
M(yT²)≤28, M(yC²)≤28, 1/4<m/n<3/4, and |D(6,2)|=15.
It also asserts Cov_h(yT)=434/625 and Cov_h(yC)=868/625.

Let J_C=E_2[x̄_Sᶜ·ν3(Sᶜ,yC)] and J_T=E_2[x̄_S·ν3(S,yT)],
with the ordinary finite dot products and ν3(A,y)_k=-x̄_A,k M_A(y-M(y)).
The core assertion is

    J_C-J_T=217/2500,
    Ccoef(6,2)Cov_h(yC)-T(6,2)Cov_h(yT)=-217/2500,
    J_C-J_T ≠ Ccoef(6,2)Cov_h(yC)-T(6,2)Cov_h(yT).

The additional simultaneous conclusions are M(yT²)=1059/625,
M(yC²)=17361/625, M(x²)=1, the elementary numerical inequality 1≤28,
m/n=1/3, and injectivity of x as a function on the six labels. For every
S∈D(6,2), C_S(x,x)>0 and C_Sᶜ(x,x)>0. For every i, h_i=x_i²;
M(h)=1, M(yT)=1, M(yC)=5, T(6,2)=1/10,
Ccoef(6,2)=-1/80, J_C=217/12500, J_T=-217/3125, and
-Ccoef(6,2)Cov_h(yC)+T(6,2)Cov_h(yT)=217/2500.

The docstring describes the inequality as refuting the printed third bias
component and says reversing the printed signs gives its actual value.
The theorem establishes the mismatch for this specific Population, not a
universal third-moment identity.

Junk-value check: n=6,m=2 and control size four are positive, the design has
15 assignments, and n-1,n-2 and both squared arm sizes are nonzero. The
natural subtraction in Ccoef(6,2) is exactly four. All rational denominators
are positive. The injective covariates and the explicitly positive arm
variances exclude degenerate regressions. There is no inverse or limiting
operation in the asserted bias-component calculation.
