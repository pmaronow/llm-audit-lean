# Blind reading of the Lean statements

Saved before opening `claims.json` or `record.json`. This reading uses only
`SAP/P033/Defs.lean`, all four Defs parts, the Challenge files, and the Mathlib
sources cited below. The challenge contains the fifteen closed theorems
`SAP.P033.T1` through `SAP.P033.T15`. There are no theorem parameters or
hypotheses outside the propositions described here. Each numbered paragraph
below describes conjuncts, not assumptions of the overall theorem.

## Mathematical conventions and complete dictionary

All scalars below are real unless declared natural. `Fin n` means the integers
0 through n-1. Sums over a `Fin` type include all its elements. Finite means,
variances, and covariances use the uniform distribution: for a finite set Ω,
EΩ X = (Σω Xω)/|Ω|, VΩ X = EΩ[(X-EΩ X)²], and
CovΩ(X,Y) = EΩ[(X-EΩ X)(Y-EΩ Y)]. The definition permits an empty Ω, in which
case these expressions are zero by Lean's division convention; the specific
sign spaces below are nonempty.

For a vector y of length n, m(y) = Σy/n,
s²(y) = Σ(y-m(y))²/(n-1), and s(y) = √s²(y). This is the sample variance,
distinct from VΩ. A square root is the nonnegative real square root (zero on
negative arguments). Real division is totalized, with x/0 = 0. Thus denominator
conditions must be checked in the individual statements.

N(m,v) denotes `gaussianReal m v`: v is the **variance**, not the standard
deviation. For v>0 it has density exp(-(x-m)²/(2v))/√(2πv); for v=0 it is the
Dirac measure at m. Write Φ(x)=Pr[N(0,1)≤x], φ its density,
Q(p)=inf{x : p≤Φ(x)}, z=Q(39/40), and
P(a)=Φ(a-z)+Φ(-a-z). Infima here are real conditional infima, not extended-real
quantiles; use outside (0,1) needs care.

For a measure μ and statistic T, C(μ,T,θ,H) is the real value of
μ{ω : θ∈[Tω-H,Tω+H]}. `μ.real A` is `(μ A).toReal`, which is zero for an
infinite measure value. In these assertions measures are probability laws or
are constructed from normalized densities. `HasLaw T ν μ` means T is μ-almost
everywhere measurable and μ pushed forward by T equals ν. `MemLp T 2 μ`
means almost-everywhere strong measurability and a finite second moment.
`variance` is the real value of ∫⁻|T-EμT|², and is zero for infinite extended
variance; `covariance` is the Bochner integral of the centered product. Bochner
integrals are zero for nonintegrable functions, so integrability remains a
substantive check. Interval integrals are oriented Lebesgue integrals, equal
to the integral over (a,b] when a≤b. All displayed local windows have a<b.
`Measure.pi` is the finite product law, so coordinates are independent.
`iIndepFun` means joint independence. Statements with arbitrary probability
spaces quantify over the type Ω, its measurable space, the measure μ, and a
proof μ(Ω)=1, in that order.

The eight-observation design is indexed by (side,i)∈{0,1}×{0,1,2,3}. Put
x=(1/5,2/5,3/5,4/5), K_i=1-x_i, μ0(t)=2+t, μ1(t)=6+t,
a=(6/5,3/10,-1/5,-3/10), r=(50/7,-125/14,-25/7,75/14),
B2=-21/125, d=B2 r, and b=a-d. Define
G_k[p,q]=Σi K_i x_i^(p+q), for p,q=0,...,k;
T_w(Y)=Σi w_i(Y_1i-Y_0i). L(ν1,ν0) is the product of eight independent
unit-variance normals with means ν0(-x_i) on side 0 and ν1(x_i) on side 1.
Write L1=L(μ1,μ0), s_a=√83/5, s_b=√410/5. The fixed data Y* have
side-0 vector (19/10,3/2,8/5,1) and side-1 vector
(63/10,63/10,34/5,33/5).

Put q4(t)=20(1-5t)(1-5t/2)(1-5t/3)(1-5t/4), ν1=μ1+q4,
and L2=L(ν1,μ0). For N studies and S⊆Fin N, L_NS is the product with law
L2 at j∈S and L1 otherwise, and θ_Sj is 24 at j∈S and 4 otherwise.
`rdEffect ν1 ν0 c` means ν1(c)-ν0(c).

For m observations define
e_i(y)=√((m-1)/m)[y_i-(Σj y_j-y_i)/(m-1)]. A cluster score variance is
Vhat_f(score)=f Σg score_g², for **any real** multiplier f. For C cells with
sizes m_c, owner map o:Fin C→Fin G, weights ell_c and data y_ci, the nested
score at g is Σc:o(c)=g ell_c Σi e_i(y_c).

In the ten-cluster example running values are (-5,-4,-3,-2,-1,1,2,3,4,5),
the kernel is 1-|x|/6, and the one-side Gram matrix is
H_k[p,q]=Σj=0..4 5(1-(j+1)/6)(j+1)^(p+q).
The two vectors are A=(1/5,1/5,0,-2/5,-1,1,2/5,0,-1/5,-1/5) and
D=(-2/5,1/5,4/5,2/5,-2,2,-2/5,-4/5,-1/5,2/5).
On the uniform space of ten independent Boolean bits, ε_g is +1 for true
and -1 for false, Y_gi=ε_g for five i, and T_A=Σ A_g ε_g
(likewise T_D). In the noisy model there are sixty independent Boolean bits:
ten cluster bits and fifty individual bits, with Y_gi=ε_g+η_gi,
barY_g=Σi Y_gi/5, and T_w=Σg w_g barY_g.

For n observations per side, u_nj=(j+1)/(n+1), k_nj=1-u_nj,
M_np=Σj k_nj u_nj^p, Δ_n=M_n0 M_n2-M_n1²,
w_nj=k_nj(M_n2-M_n1 u_nj)/Δ_n, and v_n=2Σj w_nj².
The pure estimator is Σj w_nj(ε_1j-ε_0j). The noisy estimator replaces each
sign with the average of five outcomes ε_sj+η_sji. Both use the full uniform
Boolean space of the displayed coordinates. The cluster plug-in statistic is
U(a,Z)=G/(G-1) Σg a_g²(Z_g-m(Z))².

The count example has two eligible cells with baseline counts (5,45), two
ineligible cells with baseline (10,40), and 100 individuals per cell. All
individual indices start at zero. Potential outcome Y_e,t,c,i is 1 if
i<baseline_e,c+5t and 0 otherwise. Treatment D_e,i is 1 if e=true and i<50,
and 0 otherwise. Observed outcomes choose the potential outcome at D_e,i.
W(yE,yI,dE,dI)=(yE-yI)/(dE-dI), and B(p)=p(1-p).
The stored standard error is s*=154987506828555/10^16.

For the caliper statements c=49/25, A_f(h)=∫c^(c+h) f,
B_f(h)=∫(c-h)^c f, and p_f(h)=A_f(h)/(A_f(h)+B_f(h)).
Tail(n,k,p)=Σj=k..n choose(n,j)p^j(1-p)^(n-j); if k>n the sum is empty.
L_M,f is the product of M copies of Lebesgue measure with density
max(f,0), implemented using `ENNReal.ofReal`. N_h(X) counts coordinates
in [c-h,c+h], and K_h(X) counts those in [c,c+h]. The two intervals overlap
at c; densities give that singleton zero mass. Let f1(x)=x/8 on [0,4]
and zero elsewhere, and fm(x)=(m+1)x^m/4^(m+1) on [0,4], zero elsewhere.
Fθ(x)=Φ(x-θ)-Φ(-x-θ), and
pθ(h)=[Fθ(c+h)-Fθ(c)]/[Fθ(c+h)-Fθ(c-h)].

For finite sets L,R, rho(L,R)=|L∪R|/(|L|+|R|). Funnel coordinates are
F(β,se,s0)=(|β|/s0,se/s0). The upper-endpoint imputation is
u(β,U,q)=(U-β)/q, the width imputation is w(L,U,q)=(U-L)/(2q),
t(β,se)=|β|/se, and the reconstructed p-value is
2Φ(-t(β,w(L,U,q))). Binary sample variance as a function of real n,k is
[k(1-k/n)²+(n-k)(k/n)²]/(n-1).

For bias assertions let Lθ,b=N(θ+b,1),
C_b(H)=Φ(H-b)-Φ(-H-b), H_B=inf{H≥0:C_B(H)≥19/20},
PP(t,H)=2Φ(-z|t|/H), and AP(B,t)=Φ(B-|t|)+Φ(-B-|t|).
Valid(B,P) says: for every real b with |b|≤B, then every real α with
0<α<1, Pr_N(b,1)[P(t)≤α]≤α. This is a null-law calibration assertion;
measurability and [0,1] range are not added to this predicate by definition.

Mathlib definitions checked: `Probability/Distributions/Gaussian/Real.lean`
(49,222), `Probability/HasLaw.lean` (39), `Probability/Moments/Variance.lean`
(56,64), `Probability/Moments/Covariance.lean` (44),
`MeasureTheory/Measure/MeasureSpaceDef.lean` (102),
`MeasureTheory/Measure/Map.lean` (99), `MeasureTheory/Measure/WithDensity.lean`
(39), `MeasureTheory/Constructions/Pi.lean` (210),
`MeasureTheory/Integral/Bochner/Basic.lean` (158),
`MeasureTheory/Integral/IntervalIntegral/Basic.lean` (659),
`MeasureTheory/Function/LpSeminorm/Defs.lean` (152),
`MeasureTheory/Function/L1Space/Integrable.lean` (59),
`Probability/Independence/Basic.lean` (136),
`Order/Monotone/Defs.lean` (74,99),
`Analysis/Asymptotics/Defs.lean` (169), and
`Analysis/Calculus/ContDiff/Defs.lean` (472).
Strict monotonicity has the usual ordered-pair quantifiers. The smoothness
parameter used here is the embedded ∞ of ℕ∞, meaning C-infinity, rather than
the extra analytic order ω. Little-o as h→0+ means that for every ε>0 the
absolute remainder is at most εh for all sufficiently small positive h.

## SAP.P033.T1

This closed assertion conjoins the following facts about the fixed model.

* μ0 and μ1 are continuous, and their cutoff difference is 4. Under L1,
  E T_a=E T_b=4, Var T_a=83/25, Var T_b=82/5, s_a=√Var T_a,
  s_b=√Var T_b, and (T_a-4)/s_a and (T_b-4)/s_b each have law N(0,1).
* C(L1,T_a,4,z s_a)=C(L1,T_b,4,z s_b)=19/20. With z replaced by
  49/25, each coverage is 2Φ(49/25)-1. Also 0<s_a<s_b,
  T_a(Y*)=T_b(Y*)=4, and t(T_b(Y*),s_b)<49/25<t(T_a(Y*),s_a).
* G1=[[2,4/5],[4/5,2/5]] with determinant 4/25;
  G2=[[2,4/5,2/5],[4/5,2/5,146/625],[2/5,146/625,94/625]]
  with determinant 168/390625. For every i,
  a_i=K_i(5/2-5x_i),
  r_i=K_i(125/2-14375x_i/42+15625x_i²/42), and
  b_i=K_i(13-125x_i/2+125x_i²/2).
* The moments Σ(a,a x,a x²)=(1,0,-21/125),
  Σ(r,r x,r x²)=(0,0,1), Σ(b,b x,b x²)=(1,0,0).
  Twice the squared coefficient norms of a,b are 83/25,82/5;
  Σd²=243/50, Σa d=-21/25, and
  83/50+243/50-2(-21/25)=41/5.
* The side-0/side-1 fitted values at Y* are 211/100,611/100 for a
  and 52/25,152/25 for b. Their differences are 4.
  16/(83/25)=400/83, 16/(82/5)=40/41, and
  40/41<(49/25)²<400/83.
* Row vectors (5/2,-5), (125/2,-14375/42,15625/42),
  (13,-125/2,125/2), multiplied by G1,G2,G2 respectively, are
  (1,0),(0,0,1),(1,0,0). Equivalently each equality is quantified over
  every column index of the relevant matrix.
* d=(-6/5,3/2,3/5,-9/10), b=(12/5,-6/5,-4/5,3/5),
  Var(T_b)/Var(T_a)=410/83, and 1<410/83.

The coefficient norm and inner-product facts are deterministic; this statement
does not separately assert the corresponding one-side random-variable
variance/covariance equalities.

## SAP.P033.T2

* For every probability space, A,B:Ω→R and τ,σA,σB,c in that order,
  if σA>0,σB>0,c>0, A has law N(τ,σA²), and B has law N(τ,σB²),
  then C(μ,A,τ,cσA)=C(μ,B,τ,cσB)=2Φ(c)-1. Independence is not assumed.
* L2=L1. For every measurable space E and F from the eight-coordinate data
  space to E, if F is measurable, the two pushed-forward laws agree.
  E_L2 T_a-(ν1(0)-μ0(0))=-20. For every κ>0, the event
  24∈[T_a-κs_a,T_a+κs_a] is contained in
  {(T_a-4)/s_a≥20/s_a-κ}.
* (20/s_a)²=10000/83, (5+49/25)²=30276/625<10000/83,
  0<z<5, and 10<20/s_a. The L2 coverage of 24 is ≤1/25 at both
  half-lengths (49/25)s_a and z s_a. L1 coverage of 4 at the first is
  ≥1776/2401>1/25, and at the second is exactly 19/20.
* For every natural N≥1, all L_NS are equal. For every S⊆Fin N exactly
  |S| individual studies have coverage ≤1/25, and exactly N-|S| have
  coverage 19/20, with their respective θ_Sj and half-length z s_a.
  For that N there is no single measurable data function F to the naturals
  such that, **for every S**, F(Y)=|S| almost surely under L_NS.
* For every probability space and L,betahat:Ω→R, if both are in L², then
  Var(L-betahat)=Var L+Var betahat-2Cov(L,betahat).
* For every x, q4(x)=20-625x/3+4375x²/6-3125x³/3+3125x⁴/6.
  ν1 is continuous; q4(x_i)=0 for every i, q4(0)=20,
  ν1(0)-μ0(0)=24, and ν1(x_i)=μ1(x_i) for every i.
  μ0,μ1 are continuous, E_L2 T_a=4, and (T_a-4)/s_a has law N(0,1)
  under L2. Pr_N(0,1)[|x|≥5]≤1/25.
* For every N≥1, then every S, then every measurable space E and measurable
  F from the entire N-study data to E, its L_NS and L_N,empty laws agree.
  Finally 41/5=83/50+243/50+42/25.

No differentiability beyond continuity of the conditional mean functions is
asserted, although a polynomial expression is specified.

## SAP.P033.T3

* The constant zero function is continuous; for every g,i, E Y_gi=0;
  its two-side cutoff difference is zero, and every Y_gi∈[-1,1].
  E T_A=E T_D=0, V T_A=62/25, V T_D=10.
* For every real f and every ten-bit configuration, both estimated
  variances using score_g=(A_g/5)Σi e_i(Y_g) or (D_g/5)Σi e_i(Y_g)
  are zero. There are 1024 configurations, 912 with T_A≠0 and 968 with
  T_D≠0, leaving 112 and 56 respectively with zero estimates.
* In the sixty-bit noisy space, for every g,i,j,
  Cov(Y_gi,Y_gj)=1+1_{i=j}. For every nonzero real vector v of length 5,
  Σv_i²+(Σv_i)²>0. For every g, V barY_g=6/5;
  V T_A=372/125 and V T_D=12. For every f and every noisy configuration,
  the same residual-based score variances are zero. In fact, for every
  noisy configuration and g, each of those two scores itself is zero.
* H1=[[25/2,175/6],[175/6,175/2]], det H1=4375/18;
  H2=[[25/2,175/6,175/2],[175/6,175/2,1855/6],
  [175/2,1855/6,2415/2]], det H2=61250/9.
  ΣA²=62/25, ΣD²=10, (6/5)(62/25)=372/125, (6/5)10=12.
  Every residual in the pure model is zero.
* For every g, kernel_g=(1/6,1/3,1/2,2/3,5/6,5/6,2/3,1/2,1/3,1/6)_g.
  Row (9/25,-3/25) times H1 is (1,0), and
  (37/25,-6/5,1/5) times H2 is (1,0,0), with every column quantified.
  For each j=0,...,4, A_(j+5)=5(1-(j+1)/6)(9/25-3(j+1)/25),
  D_(j+5)=5(1-(j+1)/6)(37/25-6(j+1)/5+(j+1)²/5).
* For every real f, the intervals T_A±z√Vhat and T_D±z√Vhat cover zero
  on exactly 112 and 56 of the 1024 pure-model configurations, respectively.

## SAP.P033.T4

* For every natural m≥2, then every y:Fin m→R, each residual equals
  √(m/(m-1))(y_i-Σy/m), and Σi e_i(y)=0.
* For every C,G, every size function m with m_c≥4 for every cell, then
  every owner map, every ell, every dependent array y_ci, and every real f,
  all nested scores vanish and Vhat_f of those scores is zero. No
  surjectivity, randomness, or within-cell constancy is required.
* For each n≥3, M_n0=n/2, M_n1=n(n+2)/(6(n+1)),
  M_n2=n(n+2)/(12(n+1)),
  Δ_n=n²(n+2)(n-1)/(72(n+1)²)>0,
  w_nj=6(n-j)(n-1-2j)/(n(n-1)(n+1)) for every j, and
  Σj(n-j)²(n-1-2j)²=n(n-1)(n+1)(4n²+5n-1)/30.
  v_n=12(4n²+5n-1)/(5n(n-1)(n+1))>0. The pure and noisy estimators
  have mean zero and variances v_n and (6/5)v_n. For every real f and
  every array y_(side,j),i with five individuals per cell,
  fΣg[(w_(n,g.2)/5)Σi e_i(y_g)]²=0.
* As the natural n tends to infinity, n v_n tends to 48/5.
* For every G≥2, probability space, vector of random variables Z_g,
  weights a_g, and real mean,vZ, if every Z_g is L², the Z_g are jointly
  independent, all E Z_g=mean, and all Var Z_g=vZ, then for every g,
  E(Z_g-m(Z))²=(1-1/G)vZ; E U(a,Z)=vZΣa_g²; and
  Var(Σa_g Z_g)=vZΣa_g².
* For every finite Ω (not explicitly assumed nonempty) and Z_g:Ω→R for
  ten g, if for every g, EΩ(Z_g-m(Z))²=9/10, then EΩ U(A,Z)=62/25
  and EΩ U(D,Z)=10. The premise itself excludes empty Ω.
* In the specific pure and noisy models the expected plug-in estimates are
  respectively (62/25,10) and (372/125,12).
  The remaining equalities are 1/6-1/36=5/36,
  11/72-1/36=1/8, 5/48-1/36=11/144, 1/13-1/26=1/26,
  and 1/26-1/26=0 (all real subtractions).

The design specified in Lean uses normalized u_nj; there is no separate
physical bandwidth variable in this proposition.

## SAP.P033.T5

* For every eligibility, treatment, cell, and individual, potential outcomes
  are binary. For every eligibility and individual, treatment is binary.
  For every individual D_false≤D_true; the treatment counts are 0 and 50.
  For every cell, the eligible untreated potential-outcome count is its
  baseline and the sum of individual treatment effects is 5. For every cell,
  eligible observed counts are (10,50) and ineligible observed counts (10,40).
* (5+45)/200=(10+40)/200; W(30,25,50,0)=1/10;
  (10+40)/200=1/4; B(1/4)=3/16; (1/10)²/B(1/4)=4/75.
  s²(10,50)=800, s²(10,40)=450,
  (1/10)²/s²(10,50)=1/80000≠4/75.
* W(60,50,100,0)=1/10, (20+80)/400=1/4,
  s²(20,100)=3200, (1/10)²/s²(20,100)=1/320000=(1/80000)/4.
* For every yE,yI,dE,dI,sd,scale in that order, if scale>0, dE≠dI,
  and sd>0, then scaling all four count arguments preserves W, and
  dividing the scaled W by scale·sd gives (W/sd)/scale.
* For each n≥2, then every y, then every scale>0, s(scale·y)=scale·s(y).

## SAP.P033.T6

* For every probability space, then Y and p, if Y is measurable, is binary
  almost surely, and Pr[Y=1]=p, then Var Y=p(1-p)=1/4-(p-1/2)²≤1/4
  and √Var Y≤1/2.
* For every N≥2 and binary vector Y of length N,
  s²(Y)=N/(N-1)m(Y)(1-m(Y))≤N/(4(N-1)), and
  (1/10)s(Y)≤(1/20)√(N/(N-1)). For every p∈[0,1],
  (1/10)√B(p)≤1/20. For every p,q∈[0,1], |p-q|≤1.
* 1<1229/500 and P(0)=1/20. For every a>0, P is differentiable at a
  with derivative φ(a-z)-φ(a+z)>0, and
  P(a)<Φ(a-z)+1/40. P is strictly increasing on [0,∞).
* For every τ with |τ|≤1/20,
  P(|τ|/s*)≤P(1/(20s*))<19/20. The latter upper power lies strictly
  between 8972619/10^7 and 8972620/10^7.
* There exist, jointly, σ60,σ80,σ95 with
  P(.1σ60/s*)=.6, P(.1σ80/s*)=.8, P(.1σ95/s*)=.95,
  σ60∈(3430295,3430296)/10^7,
  σ80∈(4342101,4342102)/10^7,
  σ95∈(5587016,5587017)/10^7, and σ95>1/2.
* For every N≥31731, (1/2)√(N/(N-1))≤5000079/10^7,
  P((1/20)√(N/(N-1))/s*)≤8972711/10^7<19/20
  (the last strict bound is asserted directly for the power).
* ((15/4)-1)/36=11/144 and ((11/4)-1)/10=7/40.
  For all β,se,σ with σ>0,se>0, (|β|/σ)/(se/σ)=|β|/se.

## SAP.P033.T7

* ∫0^4 x/8 dx=1. For each r in the finite set {1/10,3/20,1/5}, let
  h=cr. Then 0<h<c, f1 is strictly positive throughout [c-h,c+h],
  A_f1=(2ch+h²)/16, B_f1=(2ch-h²)/16, p_f1=1/2+r/4,
  and f1 is C-infinity on the open window.
* For h=c/10,3c/20,c/5 the probabilities are 21/40,43/80,11/20.
  At c/5, A=26411/250000 and B=21609/250000. Window endpoints for
  these three widths are (441/250,539/250), (833/500,1127/500),
  (196/125,294/125).
* For each natural k≤19, Tail(19,k,1/2)≤1/20 iff k≥14.
  For every M≥19, let μ=L_M,f1; **if** μ{N_(c/5)=19}>0, then
  Prμ[Tail(19,K_(c/5),1/2)≤1/20 | N_(c/5)=19]
  =Tail(19,14,11/20)>1/20, where conditional probability is explicitly
  an intersection probability divided by μ{N=19}.
* Tail(12,9,1/2)=299/4096,
  Tail(12,9,21/40)=336637329302285487/3355443200000000000;
  Tail(15,11,1/2)=1941/32768,
  Tail(15,11,43/80)=3589476431322242287677900507/35184372088832000000000000000;
  Tail(19,14,1/2)=2083/65536,
  Tail(19,14,11/20)=50930691593528557166389/655360000000000000000000.
* For every natural m≥1 the polynomial density integrates to 1 on [0,4].
  For every 0<h<c it is strictly positive on the closed window, C-infinity
  on the open window, and
  p_fm(h)=[(c+h)^(m+1)-c^(m+1)]/[(c+h)^(m+1)-(c-h)^(m+1)].
  For every fixed 0<h<c, this probability tends to 1 as natural m→∞.
  p_f9(49/125)=4609141/5401600.
* For every θ,x with x≥0, Pr_N(θ,1)[|t|≤x]=Fθ(x). For every θ,
  C(N(θ,1),id,θ,z)=19/20.
  p_(7/2)(49/125)∈[644747758104,644747758105]/10^12,
  Tail(19,14,p_(7/2)(49/125))∈[280413461677,280413461678]/10^12,
  and p_0(49/125)∈[318944499071,318944499072]/10^12.
* Tail(19,13,1/2)=10949/131072>1/20,
  Tail(19,14,1/2)<1/20, and L_19,f1{N_(c/5)=19}>0.

## SAP.P033.T8

First quantify over f:R→R, proofs f≥0 everywhere, f(x)=0 for x<0,
Lebesgue integrability, and ∫R f=1. Under these hypotheses:

* For every 0<h<c with A_f(h)+B_f(h)>0, then every naturals M,n with
  L_M,f{N_h=n}>0, the conditional mass Pr[K_h=j|N_h=n] is
  choose(n,j)p_f(h)^j(1-p_f(h))^(n-j) for every natural j≤n,
  and Pr[K_h≥k|N_h=n]=Tail(n,k,p_f(h)) for every natural k≤n.
* For such h, p_f(h)=1/2 iff A_f(h)=B_f(h). If f(c+u)=f(c-u)
  for every 0<u<h, these masses are equal. If f is nonincreasing on
  the closed window, A≤B, p≤1/2, and for every k≤n the tail at p
  is ≤the tail at 1/2. If f is nondecreasing, all three inequalities reverse.
* Still for such h, for every a,L with a>0, f≥a on the closed window,
  and |f(x)-f(y)|≤L|x-y| for every pair of points there,
  |A-B|≤Lh², A+B≥2ha,
  |p-1/2|=|A-B|/(2(A+B))≤Lh/(4a).
* For all naturals n,k with k≤n, Tail(n,k,p) is nondecreasing on p∈[0,1].
  If f is continuous at c and f(c)>0, p_f(h)→1/2 as h→0+.
  For every f' with f differentiable at c with derivative f' and f(c)>0,
  p_f(h)-1/2-h f'/(4f(c))=o(h) as h→0+.
* The three fair-binomial tails at (12,9),(15,11),(19,14) equal
  299/4096,1941/32768,2083/65536.

Separately, with **no assumptions on f**, for every natural M, h≥0, and
every X:Fin M→R, K_h(X)≤N_h(X).

## SAP.P033.T9

* For every probability space, T,τ,s with s>0 and T having law N(τ/s,1),
  Pr[z<|T|]=P(|τ|/s). P(0)=1/20. For every a>0 the derivative of P
  at a is φ(a-z)-φ(a+z)>0. P is strictly increasing on [0,∞).
* For every a,b≥0, if 1/20<P(a)<1 and P(a)=P(b), then a=b.
* For every type with decidable equality and every nonempty finite sets L,R,
  |L|+|R|=|L∪R|+|L∩R|, 1/2≤rho(L,R)≤1,
  and rho(L,R)<1 iff L∩R is nonempty.
* For every τ,s,rho with τ≠0,s>0,0<rho<1,
  P(|τ|/s)<P(|τ|/(s√rho)).
* The four cluster ratios are 57/(23+46)=19/23,
  185/(98+101)=185/199, 278/(202+226)=139/214,
  204/(133+130)=204/263. Each lies strictly between zero and one.
  The corresponding integer overlaps are 12,14,150,59, using natural
  subtraction (in these examples the minuends are larger).
* The real table arithmetic is 31/48-1/36=89/144,
  113/144-1/36=109/144, 31/48-1/36=89/144 (repeated),
  61/104-1/26=57/104, 81/104-1/26=77/104,
  61/104-1/26=57/104 (repeated).

## SAP.P033.T10

The following are closed numerical assertions: 0≤1/2≤2 and 1/2≤4/5;
(1/2)/(1/2)=1<49/25; (1/2)/(49/25)=25/98<1/2;
m(0,2,4)=2, s²(0,2,4)=4, s(0,2,4)=2;
F(1,1/2,2)=(1/2,1/4), F(1,1/2,4)=(1/4,1/8), these points differ,
and their x/y ratios are both 2. Finally (25/49)(1/2)=25/98<1/2.
There is no universal classification rule or data-dependent hypothesis here.

## SAP.P033.T11

* For all β,se,s with s≠0,se≠0, (β/s)/(se/s)=β/se.
  For all x,y,zeta with y≠0,zeta≠0,
  x/y=zeta iff y=x/zeta. For all x,y,zeta with y>0,zeta>0,
  zeta≤x/y iff y≤x/zeta, and y≤x/zeta iff zeta·y≤x.
* 1/(49/25)=25/49<1<49/25. For every v≥0, √v=v iff v=0 or v=1.
* For every naturals n,k with n≥2 and k≤n, the binary variance expression
  equals k(n-k)/(n(n-1)), with real subtraction in that expression.
  For every n≥2, every binary vector y of length n, then every natural k
  such that Σy=k, s²(y)=k(n-k)/(n(n-1)).
* Binary variance at (n,k)=(568,82) is 123/994, and this number lies
  strictly between (351770457441169/10^15-10^-14)² and
  (351770457441169/10^15+10^-14)².
  Also z>0 and 51021/10^5<1/z<51022/10^5.

## SAP.P033.T12

* There exists a unique positive H with C_1(H)=19/20; H_1>0 and
  C_1(H_1)=19/20; H_1∈(264614554821530,264614554821540)/10^14.
  For every θ,b with |b|≤1,
  C(Lθ,b,id,θ,H_1)=C_b(H_1)≥19/20, with equality iff |b|=1.
* z∈(195996398454000,195996398454010)/10^14,
  Q(.9)∈(128155156554460,128155156554470)/10^14.
  Let C=H_1 Q(.9)/z. Then
  C∈(173022157382648,173022157382677)/10^14,
  {t:PP(t,H_1)≤1/5}={t:C≤|t|}, and the probability of that set under
  N(1,1) equals Φ(1-C)+Φ(-1-C). That probability lies strictly in
  (23579196727091,23579196727101)/10^14.
* There exists a unique positive H with C_(1/2)(H)=19/20;
  H_(1/2)>0, C_(1/2)(H_(1/2))=19/20,
  H_(1/2)∈(218147744232810,218147744232820)/10^14. The probability
  Pr_N(1/2,1)[PP(t,H_(1/2))≤1/5] lies strictly in
  (20414905632765,20414905632774)/10^14.
* Valid(1,PP(·,H_1)) is false, and Valid(1/2,PP(·,H_(1/2))) is false.

No second all-θ/all-b interval-coverage clause is asserted for bound 1/2;
only its unique-root, half-length, and overrejection assertions are present.

## SAP.P033.T13

* For every t and h>0, |t|/(h/z)=z|t|/h;
  PP(t,h)<1/20 iff h<|t| iff 0∉[t-h,t+h], and
  PP(t,h)≤1/20 iff h≤|t|.
* For every B≥0 there exists a unique positive H with C_B(H)=19/20,
  H_B>0, and C_B(H_B)=19/20. For every b with |b|≤B,
  Pr_N(b,1)[PP(t,H_B)<1/20]=1-C_b(H_B)≤1/20,
  with equality iff |b|=B.
* H_0=z. For every t, PP(t,H_0)=2Φ(-|t|). For every 0<α<1,
  Pr_N(0,1)[PP(t,H_0)≤α]=α.
  Pr_N(1,1)[PP(t,H_1)≤1/5]>1/5.
* For every B≥0, AP(B,0)=1, AP(B,·) is continuous on R, strictly
  decreasing on [0,∞), tends to zero as t→+∞, and is Valid(B,AP(B,·)).
  For every b,α with |b|=B and 0<α<1, its rejection probability is exactly
  α. For every t, AP(B,t)≤1/20 iff H_B≤|t|, and iff PP(t,H_B)≤1/20.

## SAP.P033.T14

* For every q>0, with β=-3/20,L=-213/1000,U=-101/1000,
  u=49/(1000q), w=7/(125q), and w/u=8/7.
  U-β=49/1000 and U-L=14/125. At q=49/25,
  u=1/40, t(β,u)=6, w=1/35, t(β,w)=21/4.
  (L+U)/2-β=-7/1000.
* For every q>0, with β=79/1000,L=27/1000,U=132/1000,
  t(β,w)/q=158/105 and t(β,u)/q=79/53.
  These are strictly between 27/18 and 28/18, and between 26/18 and 27/18,
  respectively.

## SAP.P033.T15

* For every α,β,L,U in that order, assuming L<U and
  Q(1-α/2)>0, let q=Q(1-α/2). The width imputation equals
  (U-L)/(2q), its t statistic is |β| divided by that imputation, and its
  reconstructed p-value is 2Φ of the negative t statistic. There is no
  explicit range assumption on α; there is an explicit positive-quantile
  assumption.
* Q(1-(1/10)/2)=Q(19/20) and Q(1-(1/20)/2)=z.
* For every β,L,U,q with L<U and q>0,
  2q(w-u)=2β-(L+U); w=u iff β=(L+U)/2;
  u<w iff (L+U)/2<β; w<u iff β<(L+U)/2.
* For every β,q,s with q>0,s>0, both width and upper imputations of
  [β-qs,β+qs] equal s.
* For every q>0, width for [-213/1000,-101/1000] is 7/(125q),
  and its t statistic at β=-3/20 is 75q/28. At q=49/25 these are
  1/35 and 21/4.
