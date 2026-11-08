# Blind reading (saved before opening claims.json or record.json)

Read the five Challenge docstrings and statements, every source definition in
their closures, and all 146 distinct generated auxiliary proof declarations
listed by closure.json. The latter were printed in
`scratch/ClosureProofs.out`; they certify numeral instances, finite-index bounds,
nonnegativity of squares, and a measure typeclass. They add no statistical
assumptions. The initial print command had an unsupported pretty-printer option;
the corrected print file compiled successfully. No Solution files were read.

All five declarations are closed propositions: there is no outer data parameter
or hypothesis. Each asserts a conjunction about specified data, together with
some universally quantified conditional facts. The hypotheses of those internal
facts are described below. Indexing by `Fin n` means the integers 0 through n-1.
All divisions displayed below are real divisions unless explicitly counts.

Shared Mathlib meanings used below: `HasLaw T ν μ` asserts almost-everywhere
measurability and pushforward law ν; `MemLp T 2 μ` asserts almost-everywhere strong
measurability and finite second absolute moment. Expectations are Bochner
integrals. Mathlib variance is the extended integral of the squared centered
norm, converted to a real using `ENNReal.toReal`; covariance is the Bochner
integral of the product of the two centered variables. A measure's `.real A`
means `(μ A).toReal`. Finite product measures mean independent coordinates.
`IsUnit` of a real square matrix means invertibility. Matrix inverse in the WLS
definitions is the Mathlib totalized inverse. `ContDiff ℝ ∞` means smoothness of
every finite order. `Tendsto ... atTop (𝓝 a)` is an ordinary sequence limit.

## SAP.P033.T1

The docstring describes a pointwise eight-score Gaussian sharp RD witness,
without uniformity over a smoothness class. Here is the complete mathematical
content of `T1WholeStatement`, including its constituent certificates.

Put d=(1/5,2/5,3/5,4/5), K_i=1-d_i, μ0(x)=2+x, μ1(x)=6+x,
and θ=μ1(0)-μ0(0)=4. Let P be the independent eight-coordinate normal law on
Y:{0,1}×{0,1,2,3}→R, with variance 1 in each coordinate and means
μ0(-d_i) on side 0 and μ1(d_i) on side 1. Define

* l=(6/5,3/10,-1/5,-3/10), q=(50/7,-125/14,-25/7,75/14),
  b=-21/125, β_i=b q_i, a_i=l_i-β_i;
* T_w(Y)=Σ_i w_i(Y_(1,i)-Y_(0,i)), and S_(s,w)(Y)=Σ_i w_iY_(s,i);
* s_l=√83/5, s_a=√410/5, Φ(x)=N(0,1)((-∞,x]),
  z=inf{x:39/40≤Φ(x)};
* C(P,T,θ,H)=P{Y:θ∈[T(Y)-H,T(Y)+H]}.

It asserts continuity of μ0,μ1, E_P T_l=E_P T_a=4,
Var_P T_l=83/25, Var_P T_a=82/5, s_l=√Var_P T_l,
s_a=√Var_P T_a, and that (T_l-4)/s_l and (T_a-4)/s_a both have law N(0,1).
Both C(P,T_w,4,z s_w) equal 19/20, and both
C(P,T_w,4,(49/25)s_w) equal 2Φ(49/25)-1. It asserts 0<s_l<s_a.
For the fixed responses Y0=(19/10,3/2,8/5,1) and
Y1=(63/10,63/10,34/5,33/5), both estimates equal 4 and
|T_a|/s_a<49/25<|T_l|/s_l.

For degree p, define G_p(r,t)=Σ_i K_i d_i^(r+t), r,t∈Fin(p+1).
The deterministic certificate asserts
G_1=[[2,4/5],[4/5,2/5]], det G_1=4/25,
G_2=[[2,4/5,2/5],[4/5,2/5,146/625],[2/5,146/625,94/625]],
det G_2=168/390625. For every i it asserts
l_i=K_i(5/2-5d_i),
q_i=K_i(125/2-(14375/42)d_i+(15625/42)d_i²), and
a_i=K_i(13-(125/2)d_i+(125/2)d_i²).
The row vectors (5/2,-5), (125/2,-14375/42,15625/42), and
(13,-125/2,125/2), multiplied by their respective G_1,G_2,G_2,
give the intercept, quadratic-coefficient, and intercept unit rows respectively
(universally over the column index). Thus these are actual WLS coefficient rows.
The sums of l_i d_i^k for k=0,1,2 are (1,0,b), those of q are (0,0,1),
and those of a are (1,0,0). It asserts
2Σl_i²=83/25, 2Σa_i²=82/5, Σβ_i²=243/50,
Σl_iβ_i=-21/25, and 83/50+243/50-2(-21/25)=41/5.
The four fitted observed side means, linear then corrected, are
(211/100,611/100) and (52/25,152/25). It also states
16/(83/25)=400/83, 16/(82/5)=40/41, and
40/41<(49/25)²<400/83.
Further conjuncts identify β=(-6/5,3/2,3/5,-9/10),
a=(12/5,-6/5,-4/5,3/5), and the estimator variance ratio as 410/83>1.

The population construction uses a scalar score law equal to Lebesgue measure
restricted to (-1,1), divided by its mass 2. Eight independent such scores and
eight independent N(0,1) errors have their product joint law. Treatment is
the Boolean decision x≥0; potential outcomes are (6 if treated, 2 otherwise)+x+e.
The score and joint laws are asserted probability measures. For every Boolean
treatment and every real x, the potential outcome as a function of e is
integrable and its expectation is μ1(x) or μ0(x). Evaluating responses at the
fixed scores -d_i,d_i pushes the independent error law to P. This is an
explicitly specified response map, not event-mass conditioning.
Both T_l,T_a are in L²(P). For every side s∈Fin 2,
S_(s,l),S_(s,β),S_(s,a) are in L²(P), their variances are
83/50,243/50,41/5 respectively, and Cov(S_(s,l),S_(s,β))=-21/25.
The quantile set is asserted nonempty and bounded below, Φ(z)=39/40, z>0.

Junk conventions: real division by zero is 0, √x is 0 for x≤0,
real infimum is totalized for empty/unbounded sets, infinite measure mass and
infinite variance convert to 0, and a nonintegrable Bochner integral is 0.
Here denominators are positive constants, standard deviations are positive,
the quantile has explicit existence/boundedness/value certificates, Gaussian
linear functions have finite moments (explicit L² conjuncts), and every
probability is finite. The conditioning normalizer is 2. Thus these conventions
do not supply the asserted inference. Indices are nonempty; exponents are
natural powers, all casts preserve the displayed rational values. There are no
logs, real powers, truncated subtractions, limsups, or partial-function defaults.

## SAP.P033.T2

Use d,K,μ0,μ1,l,s_l,Φ,z,T_l,C from T1, with their explicit meanings above.
Define r(x)=20(1-5x)(1-(5/2)x)(1-(5/3)x)(1-(5/4)x),
μ2(x)=6+x+r(x), and P2 as the independent eight-coordinate normals with
side-0 means 2-d_i and side-1 means μ2(d_i), all variances 1.
No premise is imposed on this particular witness.

First, universally in a type Ω, measurable structure, probability μ,
real-valued functions A,B and real τ,σA,σB,c, if σA>0,σB>0,c>0,
and A,B have respective laws N(τ,σA²),N(τ,σB²), both intervals
[A±cσA],[B±cσB] cover τ with probability 2Φ(c)-1. No independence
between A and B is assumed or needed. Universes permit arbitrary such spaces.

For the witness the theorem asserts P2=P. Universally over a measurable target
space E and F:(eight-response space)→E, measurability of F implies equality of
its pushforward laws under P2 and P. It asserts E_P2 T_l-24=-20.
For every real κ>0, the event 24∈[T_l±κs_l] is a subset of
{20/s_l-κ≤(T_l-4)/s_l}. It asserts (20/s_l)²=10000/83,
(5+49/25)²=30276/625<10000/83, 0<z<5, and 10<20/s_l.
Coverage under P2 of 24 with either half-length (49/25)s_l or z s_l is
at most 1/25. Coverage under P of 4 with the former is at least
1776/2401>1/25 and with the latter is 19/20.

For each natural N≥1 and each subset S⊆Fin N, let Q_(N,S) be the product
of P2 at indices in S and P elsewhere, with θ_j=24 on S and 4 elsewhere.
For every such N, all Q_(N,S)=Q_(N,empty). For each S exactly |S|
studies have individual z s_l coverage ≤1/25 and exactly N-|S| have
coverage 19/20. There is no measurable function F from the N study response
arrays to natural numbers which, for every S, equals |S| almost surely under
Q_(N,S). The quantifier order is ¬∃F, measurable F and ∀S, almost sure
correct count; it does not deny identification when S is supplied to F.
Additionally for every measurable target E and F on the N-study array,
measurable F implies equality of its pushforward law for every S and empty S.

For every probability space and real functions L,B in L², it asserts
Var(L-B)=Var L+Var B-2Cov(L,B). This is a separate general identity,
without a hypothesis that its two variables are independent.

The remaining conjuncts assert
r(x)=20-(625/3)x+(4375/6)x²-(3125/3)x³+(3125/6)x⁴ for every real x;
continuity of μ2,μ0,μ1; r(d_i)=0 and μ2(d_i)=μ1(d_i) for every i;
r(0)=20 and μ2(0)-μ0(0)=24; E_P2 T_l=4;
(T_l-4)/s_l has law N(0,1) under P2;
N(0,1){|x|≥5}≤1/25; and 41/5=83/50+243/50+42/25.
All four functions μ0,μ1,r,μ2 are C∞. T_l is L²(P2), Φ(5)≥49/50,
5<20/s_l-49/25, ((T_l-4)/s_l)² is integrable with expectation 1,
C(P,T_l,4,(49/25)s_l)=2Φ(49/25)-1, and
1-(25/49)²=1776/2401. The same nonempty/bounded quantile and exact z
certificates as T1 are included.

Junk conventions: those for Gaussian measures, integrals, variance, quantile,
division and square root are as in T1. L² premises exclude infinite moments in
the general variance identity; normal laws supply finite moments in the
coverage formula. Every standard deviation divisor is positive. The count
N-|S| is natural truncated subtraction, but |S|≤N, so no underflow occurs.
N≥1 rules out the vacuous count-identification experiment. Empty S is allowed
and essential; it is a legitimate model, not an empty sample. Arbitrary target
types and measurable maps do not add an impossible premise. No other partial,
logarithmic, real-power, or limsup convention occurs. The statement establishes
different coverage of different target parameters under equal conditional data
laws; it does not assert a general failure of bias correction or uniformity.

## SAP.P033.T3

The randomness is uniform counting on all maps ω:Fin 10→Bool. A Boolean
sign is +1 for true and -1 for false, so this is ten independent fair signs.
Finite mean of a function is its sum divided by the cardinality of its domain;
finite variance and covariance use centered sums with this same denominator.
Clusters have five records. Scores are (-5,-4,-3,-2,-1,1,2,3,4,5),
triangular weights 1-|x|/6, and Y_(g,i)=sign(ω_g).
Let a=(1/5,1/5,0,-2/5,-1,1,2/5,0,-1/5,-1/5),
b=(-2/5,1/5,4/5,2/5,-2,2,-2/5,-4/5,-1/5,2/5).
T_w=Σ_g w_g sign(ω_g). For m records define
R_i(y)=√((m-1)/m)[y_i-(Σ_j y_j-y_i)/(m-1)].
For a real multiplier f the variance estimator here is fΣ_g score_g²,
where score_g=(w_g/5)Σ_i R_i(Y_g).

The assertion includes continuity of the constant zero mean, mean zero for
every coordinate Y_(g,i), cutoff effect 0-0=0, and Y_(g,i)∈[-1,1] for
every ω,g,i. Both T_a,T_b have finite means 0 and variances 62/25,10.
For every real f and every ω both variance estimates are zero. The sample
space has cardinality 1024: T_a is nonzero on 912 and zero on 112 outcomes;
T_b is nonzero on 968 and zero on 56 outcomes. For every real f the
intervals [T_w±z√(estimated variance)] contain 0 on exactly 112 and 56
outcomes respectively. Here z is the same infimum-defined normal critical
value as above; all half-lengths are identically zero.

For the noisy extension the uniform domain is maps
ω:(Fin 10 ⊕ (Fin 10×Fin 5))→Bool, so all ten cluster signs and fifty
record signs are independent fair signs. Y_(g,i)=sign(ω_inl(g))+
sign(ω_inr(g,i)); Z_g=Σ_iY_(g,i)/5; T_w=Σ_g w_g Z_g.
For all g,i,j the within-cluster covariance is 1+1_(i=j).
For every nonzero real vector v∈R^5,
Σ_i v_i²+(Σ_i v_i)²>0. Each Z_g has variance 6/5 and estimator
variances are 372/125 and 12. For every f,ω the two variance estimates
are zero; separately every individual cluster score is asserted zero.

The WLS certificates use per-side G_p(r,s)=Σ_(j=0)^4
5(1-(j+1)/6)(j+1)^(r+s). They assert
G_1=[[25/2,175/6],[175/6,175/2]], det=4375/18;
G_2=[[25/2,175/6,175/2],[175/6,175/2,1855/6],
[175/2,1855/6,2415/2]], det=61250/9;
Σ_g a_g²=62/25, Σ_g b_g²=10, (6/5)(62/25)=372/125,
(6/5)10=12, and R_i(Y_g)=0 in the pure sign model.
The kernel vector is (1/6,1/3,1/2,2/3,5/6,5/6,2/3,1/2,1/3,1/6).
The rows (9/25,-3/25) and (37/25,-6/5,1/5) times G_1,G_2
are their intercept unit rows. For every j∈Fin 5, a_(j+5) and b_(j+5)
equal 5K_(j+5) times the corresponding row polynomial at j+1.

Junk conventions: all finite-mean domains used here are nonempty (sizes
2^10 and 2^60); no division by an empty cardinality occurs. m=5 makes
the residual denominators and square-root arguments positive. Estimated
variance is algebraically zero for all f, even negative f; its square root is
therefore the ordinary √0. This is cancellation, not a negative-variance
square-root artifact. The real quantile is totalized in principle, but zero
interval widths make its value irrelevant to these counts, and its defining
normal probability level is legitimate. All finite moments exist. Fin indices
are bounded by types; no other junk-value operations occur.

## SAP.P033.T4

This is a conjunction of general residual identities, a normalized shrinking
grid model, a physical WLS realization, general cluster plug-in identities,
the ten-cluster examples, and exact rational arithmetic.

For every natural m≥2, every vector y∈R^m, and every i,
the residual R_i from T3 equals √(m/(m-1))(y_i-Σ_j y_j/m),
and Σ_iR_i=0. Next, for all naturals C,G, cell-size map m:Fin C→Nat
with every m_c≥4, owner:Fin C→Fin G, real weights ell_c,
outcomes y_c∈R^(m_c), and real multiplier f, every cluster score
Σ_(c:owner(c)=g) ell_cΣ_iR_i(y_c) is 0, and f times the sum
of their squares is 0. No stochastic premise is used in this cancellation.

For every natural n≥3 set d_j=(j+1)/(n+1), K_j=1-d_j,
M_k=Σ_(j∈Fin n)K_j d_j^k,
D=M_0M_2-M_1², l_j=K_j(M_2-M_1d_j)/D,
V_n=2Σ_j l_j². The theorem asserts
M_0=n/2, M_1=n(n+2)/(6(n+1)), M_2=n(n+2)/(12(n+1)),
D=n²(n+2)(n-1)/(72(n+1)²)>0,
l_j=6(n-j)(n-1-2j)/(n(n-1)(n+1)),
Σ_j(n-j)²(n-1-2j)²=n(n-1)(n+1)(4n²+5n-1)/30,
V_n=12(4n²+5n-1)/(5n(n-1)(n+1))>0.
The difference of two independently signed sides weighted by l has finite
mean 0 and variance V_n. With independent cluster and five record signs
added as in T3, each cluster averaged before fitting, its finite mean is 0
and variance (6/5)V_n. For every real f and every array of five real
outcomes per cluster, fΣ_(side,j)[(l_j/5)Σ_iR_i(y_(side,j))]²=0.
Finally n V_n tends to 48/5 as natural n tends to infinity.

For every G≥2, probability space (Ω,μ), maps Z_g:Ω→R, weights a_g,
and real mean,varZ, assume: every Z_g is L², the family is independent,
every expectation is mean, and every variance is varZ. Write
barZ=Σ_gZ_g/G, P_a(Z)=G/(G-1) Σ_g a_g²(Z_g-barZ)².
Then for each g, E(Z_g-barZ)²=(1-1/G)varZ,
E P_a=varZΣ_g a_g², and Var(Σ_g a_gZ_g)=varZΣ_g a_g².
For every finite type Ω and functions Z:Fin 10→Ω→R, if each
finite mean of (Z_g-barZ)² is 9/10, the finite means of P_a and P_b
for the T3 weight vectors are 62/25 and 10. The pure-sign examples
have these plug-in expectations; the noisy examples have expectations
372/125 and 12. This last conditional fact does not assume independence,
because it assumes the exact centered second moments needed by the algebra.
Arithmetic conjuncts are 1/6-1/36=5/36, 11/72-1/36=1/8,
5/48-1/36=11/144, 1/13-1/26=1/26, and 1/26-1/26=0.

The physical realization has n(n+1) clusters per side, five records per
cluster, physical distances x_j=(j+1)/(n(n+1)), h_n=1/n,
and weights W_j=max(0,1-|x_j/h_n|). The embedding of active indices
maps j∈Fin n to the same integer in Fin(n(n+1)); padding a vector assigns
it to j<n and assigns 0 to every outer index. Define record WLS of degree p
by G^(-1) times the moment vector, with
G_(r,s)=Σ_(j,i) W_j x_j^(r+s), RHS_r=Σ_(j,i)W_j x_j^r y_(j,i).
Normalized WLS uses d_j,K_j and the cluster means of the n active clusters.
Cluster means are always Σ_i y_(j,i)/5.
Define physical intercept weights L_j=W_j(M'_2-M'_1x_j)/
(M'_0M'_2-(M'_1)²), where M'_k=Σ_j W_jx_j^k, and
B=Σ_j L_jx_j². Corrected physical intercept equals the fitted linear
intercept minus B times the fitted quadratic coefficient; normalized corrected
intercept uses the analogous normalized bias moment. The physical RD
estimator is Σ_j L_j(barY_(1,j)-barY_(0,j)). Its sign and noisy
models use the independent uniform Boolean coordinates on the full grid,
exactly as in the normalized model.

h_n tends to 0 and the constant zero mean is C∞. For every n≥3:
h_n>0; x_j/h_n=(j+1)/(n+1) for every full index;
W_j>0 iff j<n, exactly n weights are positive, and active W_j=K_j.
For every real function F on full indices, Σ_jW_jF_j equals its active
sum Σ_(j∈Fin n)K_jF_j. For every active a and every full F,
Σ_j padded(a)_jF_j equals Σ_(j∈Fin n)a_jF_j.
For p=1 or p=2 both normalized and physical record Gram matrices are
units. For every such p, every full outcome array y, and every coefficient
index r∈Fin(p+1), h_n^r fitPhysical_(p,r)(y) equals
fitNormalized_(p,r)(active cluster means).
For every y the physical linear intercept is Σ_j L_j barY_j;
for every full j, L_j is the padded normalized l_j;
B=h_n²Σ_(j∈Fin n)l_jd_j². For every y the physical corrected intercept
equals both the normalized corrected intercept of active means and the
physical quadratic fitted intercept. The full-grid sign/noisy RD estimators
have finite means 0 and variances V_n,(6/5)V_n. For every real f,
every real cluster weight vector ell, and every real full record array y,
fΣ_g[(ell_g/5)Σ_iR_i(y_g)]²=0.

Junk conventions: the residual, normalized grid, physical distance, bandwidth,
intercept, matrix-inverse, and plug-in definitions are total even at small n,m,G.
All substantive uses have m≥2 (nested cells ≥4, examples 5), n≥3, G≥2,
positive D, and nonsingular matrices. Thus the zero defaults of real inverse
and singular matrix inverse never establish a fit. The limit includes n=0,1,2,
where some definitions return junk values; changing finitely many terms cannot
affect the asserted limit. Subtractions in moment and plug-in formulas are
real subtractions after casts, not natural truncation. C,G may be zero in the
general nested-cell identity: empty cells/clusters just make that valid sum
identity empty. In the separate arbitrary-Fintype conditional identity, Ω can
be empty, but its second-moment premise would then be 0=9/10 and impossible;
there are nonempty sign-model instances. Other finite-mean uses are nonempty.
All random moments are either finite sums or have L² hypotheses. No logs,
real powers, conditional-law divisions, limsup defaults, or partial lookups occur.

## SAP.P033.T5

Let cells be Fin 2, individuals Fin 100, eligibility and treatment Booleans.
For an integer k, binaryIndicator(k,i) is 1 if i<k, 0 otherwise.
Untreated baseline counts are e=(5,45) for eligible and u=(10,40) for
ineligible. The potential outcome at eligibility E, treatment T, cell c,
individual i is binaryIndicator(baseline_(E,c)+(5 if T else 0),i).
Actual treatment is binaryIndicator(50,i) when eligible and zero otherwise.
Observed outcome chooses the treated potential exactly when actual treatment
equals 1, otherwise the untreated potential.

The assertion is: for all E,T,c,i the potential outcome is 0 or 1;
for all E,i actual treatment is 0 or 1; and for every i treatment under
ineligibility is at most treatment under eligibility. Treatment counts are
50 and 0. For every cell the eligible untreated count is e_c and the sum
of eligible potential treatment effects is 5. For every cell observed counts
are (10,50) if eligible and (10,40) if ineligible. The two untreated total
rates agree: (5+45)/200=(10+40)/200.

Define W(yE,yI,dE,dI)=(yE-yI)/(dE-dI), mean(y)=Σ_i y_i/n,
S²(y)=Σ_i(y_i-mean(y))²/(n-1), S(y)=√S²(y), and
binary population variance at p to be p(1-p).
Then W(30,25,50,0)=1/10, (10+40)/200=1/4,
(1/4)(1-1/4)=3/16, (1/10)²/(3/16)=4/75.
S²(10,50)=800, S²(10,40)=450,
(1/10)²/S²(10,50)=1/80000≠4/75.
After doubling counts, W(60,50,100,0)=1/10,
(20+80)/400=1/4, S²(20,100)=3200, and
(1/10)²/3200=1/320000=(1/80000)/4.

For every real yE,yI,dE,dI,sd,scale, if scale>0, dE≠dI and sd>0,
W(scale*yE,scale*yI,scale*dE,scale*dI)=W(yE,yI,dE,dI), and
that scaled Wald ratio divided by scale*sd equals
(W(yE,yI,dE,dI)/sd)/scale. Separately, for every natural n≥2,
every vector y∈R^n, and every real scale>0,
S(scale*y)=scale*S(y). No nonconstant-sample premise is imposed on this
last equality, which remains meaningful for S=0.

Junk conventions: real division by zero and square roots of negative numbers
are totalized. The numerical Wald denominator is 50 (100 when doubled),
the population variance is 3/16>0, the count variances are 800,450,3200,
and numerical sample sizes are 2, so these divisions are meaningful. General
standardized ratios assume positive sd and distinct treatment counts. General
sampleSD scaling assumes n≥2 and scale>0, so its variance is nonnegative;
constant samples legitimately have zero SD without any division by it.
The binary indicator also has a defined saturation for k>n and empty values
for k=0; all witness thresholds here are between 5 and 50, inside Fin 100.
Natural count addition does not overflow; n-1 in sample variance is real
subtraction after coercion. No probability integration, sInf, logs, real powers,
limsup, or partial-function defaults occur in this statement.
