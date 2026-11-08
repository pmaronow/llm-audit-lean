# Blind reading

Saved before opening either `claims.json` or `record.json`. Sources inspected: the five Challenge declarations and every entry of their `closure.json` closures. Generated declarations were inspected using `scratch/ClosurePrint.lean`; their complete printed types and bodies are in `scratch/ClosurePrint.log`. Numeral auxiliaries prove `Nat.AtLeastTwo` or `NeZero`; the generated matcher exhausts `Fin 5`. They add no hypotheses to the mathematical claims. `scratch/BlindScope.lean` checks the scope of the Gaussian clause by definitional equality.

Notation below is mathematical shorthand for the explicit Mathlib finite sums, real arithmetic, matrix multiplication/inverse/transpose, measurable pushforwards, and Bochner integrals. No shorthand below is an additional hypothesis.

## SAP.P039.T1

Source: `SAP/P039/Challenge/Part1.lean:9`, `SAP/P039/Defs/Part1.lean:10–63`.

A growth history is any function h : N -> R. The domain includes all natural numbers; only h(1),...,h(16) are used. For a real d define

- N(d,h) = h(16)/3 + sum_{q=2}^{15} d^(16-q) h(q).
- D(d) = 1/3 + sum_{q=2}^{15} d^(16-q).
- I(d,h) = N(d,h)/D(d).
- Nd(d,h) = h(16)/3 + sum_{q=1}^{15} d^(16-q) h(q).
- Dd(d) = 1/3 + sum_{q=1}^{15} d^(16-q).
- Id(d,h) = Nd(d,h)/Dd(d).
- e(q) = 1 if q=1 and 0 otherwise, including q=0 and q>16.

The actual finite sums use k in {0,...,13} or {0,...,14}, with q=15-k and exponent k+1.

The theorem is a conjunction of four assertions:

1. For every real d, if d>=0, then D(d)>0 and Dd(d)>0. For every h,h', if h(q)=h'(q) for every natural q with 2<=q<=16, then N(d,h)=N(d,h') and I(d,h)=I(d,h'). For every h, Nd(d,h)-N(d,h)=d^15 h(1). Also Dd(d)-D(d)=d^15.
2. The fixed number d=1/2 lies strictly between 0 and 1. e(1)=1 and e(q)=0 for 2<=q<=16. N(1/2,e)=I(1/2,e)=0, Nd(1/2,e)=1/32768, Dd(1/2)=131069/98304, and Id(1/2,e)=3/131069>0, hence it differs from I(1/2,e).
3. The fixed number d=9/10 lies strictly between 0 and 1. N(9/10,e)=I(9/10,e)=0. Nd(9/10,e)=205891132094649/10^15, Dd(9/10)=22440939433444477/(3*10^15), and Id(9/10,e)=617673396283947/22440939433444477>0, hence it differs from I(9/10,e).
4. (1/2)^15=1/32768, 1/3+32767/32768=131069/98304, and (9/10)^15=205891132094649/10^15.

There are no external hypotheses on the two concrete witnesses. Universal d is only constrained by d>=0, without an upper bound. The docstring describes an implemented Q2–16 predictor versus a Q1–16 description, with the two witnesses.

Junk conventions: real division uses 0 inverse = 0, but every asserted ratio has a positive denominator. `15-k` is natural truncated subtraction, but k<=14, so it is ordinary subtraction here and never reaches 0. All powers are natural powers. No 0^0 occurs in N or D, as exponents are positive. No empty index types, integrals, extrema, logarithms, roots, or non-finite conversions occur. Values of h outside 1–16 are irrelevant.

## SAP.P039.T2

Source: `SAP/P039/Challenge/Part1.lean:14`, `SAP/P039/Defs/Part1.lean:10–29,65–87`.

Use exactly the six unfolded functions N,D,I,Nd,Dd,Id above; growth histories again have type N -> R.

First, for every real d and every history h, if d>=0, all of the following hold:

- D(d)>=1/3, D(d)>0, and Dd(d)>0.
- For every history h', agreement on every natural q with 2<=q<=16 implies N(d,h)=N(d,h') and I(d,h)=I(d,h').
- Nd(d,h)=N(d,h)+d^15 h(1) and Dd(d)=D(d)+d^15.
- Id(d,h)-I(d,h)=d^15 (h(1)-I(d,h))/Dd(d).
- Id(d,h)=I(d,h) if and only if d=0 or h(1)=I(d,h).

Second, for every history h, D(0)=1/3, I(0,h)=h(16), D(1)=43/3, and

I(1,h)=(3/43)*(h(16)/3 + sum_{q=2}^{15} h(q)).

The same conjunction states the real natural-power conventions 0^0=1, 1^k=1 for every natural k, and 0^k=0 for every k>=1. The docstring describes this as the corrected predictor, its exact relation to the described one, and both endpoints.

Junk conventions: all divisions in the asserted formulas have positive denominators. The finite sums and the natural subtraction have exactly the safe ranges explained for T1. The explicit 0^0=1 is the usual total natural-power convention; no growth term receives a zero exponent at d=0. The casts of natural indices and constants introduce no loss or truncation. There are no measure, extrema, or root conventions in this statement.

## SAP.P039.T3

Source: `SAP/P039/Challenge/Part1.lean:19`, `SAP/P039/Defs/Part2.lean:15–85`, `SAP/P039/Defs/Part3.lean:10–95`, `SAP/P039/Defs/WholeW1.lean:11–62`.

### All regression and distribution definitions unfolded

A vector of length n is a function Fin n -> R and a matrix of size n by p is a function Fin n -> Fin p -> R. Write v.w=sum_i v_i w_i and ||v||²=sum_i v_i². For a matrix A and response y,

- Full rank means the map b -> A b is injective.
- beta_A(y)=(A^T A)^(-1) A^T y.
- e_A(y)=y-A beta_A(y); SSE_A(y)=||e_A(y)||².
- SE²_A(y,j)=SSE_A(y)/(real(n)-real(p)) * ((A^T A)^(-1))_{jj}.
- t_A(y,j)=beta_A(y)_j/sqrt(SE²_A(y,j)).
- t²_A(y,j)=beta_A(y)_j²/SE²_A(y,j). This is defined as a quotient, not by squaring t, although the two agree on the tested data.
- A vector b is least squares if for every vector b' of length p, ||y-Ab||²<=||y-Ab'||².
- L(x) has columns the constant vector 1 and x.
- [Z,x] appends x as the final column of Z.
- P_Z=Z(Z^T Z)^(-1) Z^T; M_Z=I-P_Z.

The data, all in R^6, are u=(1,-1,0,0,0,0), v=(0,0,1,-1,0,0), w=(0,0,0,0,1,-1), y=(1,-1,3/2,-3/2,1,-1), Z=[1,u]. Set r=e_Z(y).

Let G_m be the product probability measure of m independent real Gaussian variables of mean 0 and variance 1. Chi²_nu is the pushforward of G_nu by z -> sum_i z_i². Student_nu is the pushforward of G_(nu+1) by

z -> z_0 / sqrt((sum_{i!=0} z_i²)/real(nu)).

For positive nu this is the normal divided by the square root of an independent chi-square divided by nu. Its two-sided tail at t is the real conversion of its measure of {s : t<=|s|}. The two analytic functions are

F4(t)=1-(3/2)z+(1/2)z³, z=t/sqrt(4+t²),

F3(t)=1-(2/pi)*(atan(q)+q/(1+q²)), q=t/sqrt(3).

### Exact finite assertions

The theorem first conjoins all of these fixed-data assertions:

- Z^T Z=diag(6,2); Z has full rank; r=(0,0,3/2,-3/2,1,-1); SSE_Z(y)=13/2; M_Z is symmetric and idempotent, has rank 4, and M_Z y=r. Also r=(3/2)v+w.
- Each of the four designs in the following table has full rank. The displayed beta is least squares and is the unique least-squares vector. The residual, SSE, SE² of the final slope, and t² of that slope are as follows.

| Design and response | beta | residual | SSE | SE² | t² |
|---|---|---|---|---|---|
| L(v), r | (0,3/2) | w | 2 | 1/4 | 9 |
| [Z,v], y | (0,1,3/2) | w | 2 | 1/3 | 27/4 |
| L(u+v), r | (0,3/4) | (-3/4,3/4,3/4,-3/4,1,-1) | 17/4 | 17/64 | 36/17 |
| [Z,u+v], y | (0,-1/2,3/2) | w | 2 | 1/3 | 27/4 |

- (u+v).M_Z(u+v)=2, ||u+v||²=4, and 3/4=(3/2)*2/4.
- t_L(v)(r,1)=3 and t_[Z,v](y,2)=3 sqrt(3)/2. F4 of the former is below 1/20; F3 of the latter is above 1/20.
- F4(3)=1-45/(13 sqrt(13))<1/20. F3(3 sqrt(3)/2)=1/2-(2/pi)*(atan(1/5)+6/13)>1/20.
- The unequal t² values 9 and 27/4 and the unequal correlated-regressor slopes 3/4 and 3/2 are asserted explicitly, with the same full-rank conditions repeated as conclusions.

### Gaussian assertions and tails

For every sigma : R_{>=0}, if sigma>0, then for every gamma in R², let mu be the product law of six independent N(0,sigma²) coordinates epsilon. Let

S(epsilon)=t_L(v)(e_Z(Z gamma+epsilon),1),

U(epsilon)=v.epsilon/(sigma sqrt(2)),

V(epsilon)=SSE_[Z,v](Z gamma+epsilon)/sigma².

Then (U,V) has joint law N(0,1) product Chi²_3; for every epsilon (including zero-SSE inputs) S=U/sqrt(V/4); S has law sqrt(4/3) times Student_3. Its second moment is 4, the second moment of Student_3 is 3, and that of Student_4 is 2. The law of S differs from Student_4. All three squared functions are explicitly asserted integrable under their respective measures.

For every real threshold t, if t>=0, the actual Student_4 and Student_3 tails equal F4(t) and F3(t), respectively. Further fixed assertions are

- 900²=810000, 247²*13=793117<810000, and 247 sqrt(13)<900.
- (3 sqrt(3)/2)/sqrt(3)=3/2, atan(3/2)=pi/4+atan(1/5), atan(1/5)<1/5, and 3<pi.
- 1/2-(2/3)*(1/5+6/13)=23/390; F3(3 sqrt(3)/2)>23/390>1/20.
- The actual Student tails at the two statistics satisfy the same exact formulas and bounds. The actual Student_4 tail at 3 lies in [0.03985,0.03995); the actual Student_3 tail at 3 sqrt(3)/2 lies in [0.08045,0.08055).

This is a closed conjunction apart from the positive sigma, arbitrary gamma, and nonnegative-threshold universals. The docstring describes concrete counterexamples to equivalence of two procedures, Gaussian null laws, actual reference probabilities, and totalization on zero SSE.

Junk conventions: Mathlib matrix inverse is total (over R a singular matrix has inverse zero), but all concrete Gram matrices here are nonsingular. `Real.sqrt` equals zero on nonpositive inputs; all fixed SE² values are positive. Statistical ratios return zero on a zero denominator. The Student pushforward and S are thus assigned zero on zero chi-square/SSE; at positive degrees of freedom and positive sigma these sets have Gaussian probability zero, so this does not change a law or integral. The identity S=U/sqrt(V/4) deliberately covers them using the same totalization. Student_0 would be degenerate by division by zero, but is never used. Chi²_0 has an empty sum, but is never used. Bochner integrals return zero for nonintegrable functions, but each squared moment used here has an explicit Integrable conclusion and is truly finite. Pushforward `Measure.map` uses an arbitrary Dirac value on non-AE-measurable maps of a nonzero measure in this Mathlib version; all maps here are Borel functions of finite real vectors, so that branch is excluded. `ENNReal.toReal` sends infinity to zero, but all tail measures are bounded by 1. Radicals in F4 and F3 are strictly positive and 1+q²>0; atan is total without an undefined branch. Natural degrees of freedom are fixed positive constants. No log, real rpow, extrema, limsup, or empty observation set occurs. The isolated `studentMixtureDensity._proof_1` in the closure is only a numeral proof; the density definition itself is not used by this statement.

## SAP.P039.T4

Source: `SAP/P039/Challenge/Part1.lean:28`, `SAP/P039/Defs/Part2.lean:15–89`, `SAP/P039/Defs/Part3.lean:97–164`, `SAP/P039/Defs/WholeW1.lean:94–125`.

Use the fully expanded finite-vector OLS functions, P_Z, M_Z, L(x), [Z,x], and Student laws just defined. For a probability measure mu and a vector random variable epsilon, its covariance matrix has entries

Cov_mu(epsilon)_{ij}=integral (epsilon_i-integral epsilon_i dmu)*(epsilon_j-integral epsilon_j dmu) dmu.

T4 is the conjunction of the next three universally quantified assertions.

### Deterministic regression algebra

For every natural n,k, every real n by k matrix Z, and every x,y in R^n: if the map c -> Zc is injective, some c in R^k satisfies Zc=1, no c satisfies Zc=x, and k+1<n, the following hold. Define

P=Z(Z^T Z)^(-1)Z^T, M=I-P, r=My,

xbar=(sum_i x_i)/real(n), xc=x-xbar*1,

sm=x.Mx, sc=||xc||², c=x.r,

a=c/sc, b=c/sm, sr=||r||²-c²/sc, sf=||r||²-c²/sm.

Every following clause is a conclusion, not an extra premise:

- P^T=P, P²=P, M^T=M, M²=M, MZ=0; sum_i r_i=0; M xc=Mx; xc.r=c; c=x.My.
- sc=sm+||P xc||²; 0<sm<=sc; sm=sc iff P xc=0; P xc=0 iff xc is orthogonal to each column of Z.
- beta_L(x)(r)=(-a*xbar,a), and this vector minimizes squared error over all real 2-vectors. SSE_L(x)(r)=sr.
- There is exactly one real (k+1)-vector minimizing the full-model squared error. Its last OLS coefficient is b, and SSE_[Z,x](y)=sf.
- a=b*sm/sc; a>0 iff b>0; a<0 iff b<0; |a|<=|b|; a=b iff b=0 or P xc=0; sf<=sr.
- SE²_L(x)(r,1)=sr/((real(n)-2)*sc) and SE²_[Z,x](y,k)=sf/((real(n)-real(k)-1)*sm).
- If sf>0, then t²_L(x)(r,1)=(real(n)-2)*c²/(sc*||r||²-c²), t²_[Z,x](y,k)=(real(n)-real(k)-1)*c²/(sm*||r||²-c²), and the former divided by real(n)-2 is at most the latter divided by real(n)-real(k)-1.
- Within that sf>0 implication, if P xc=0, then a=b, the two full residual vectors coincide, and t_L(x)(r,1)=sqrt((real(n)-2)/(real(n)-real(k)-1))*t_[Z,x](y,k). If also k>=2 and the full t is nonzero, its absolute value is strictly smaller than that of the residual-line t.

The quantifier order is n,k,Z,x,y, then the four structural hypotheses, then all conclusions. There is no assumption y has positive SSE until the stated subclause.

### Covariance

For every measurable space Omega (universe Type), every probability measure mu, every n,k,Z,x,gamma,epsilon : Omega -> R^n, and real sigma, assume sigma>0; the same full-rank, intercept, x-outside-span and k+1<n conditions; every coordinate epsilon_i is integrable; every product epsilon_i epsilon_j is integrable; every coordinate mean is zero; and Cov_mu(epsilon)=sigma² I.

Let r(omega)=M(Z gamma+epsilon(omega)). Then for every omega, r(omega)=M epsilon(omega); Cov_mu(r)=sigma² M; rank(M)=n-k; rank(Cov_mu(r))=n-k; and Cov_mu(r) differs from sigma² I. The noise coordinates need not be independent or Gaussian for this assertion.

### Gaussian null

For every measurable space Omega (Type), every probability measure mu, n,k,Z,x,gamma,epsilon, and sigma : R_{>=0}, assume sigma>0; Z is injective and contains 1 in its column span; x is outside that span; k+1<n; epsilon is measurable; and its pushforward law is the product of n independent N(0,sigma²) coordinates. Set Y=Z gamma+epsilon, tf=t_[Z,x](Y,k), tr=t_L(x)(M Y,1), and nu=n-k-1 (natural subtraction).

The conclusions are law(tf)=Student_nu, full-model SSE>0 almost surely, and residual-line SSE>0 almost surely. Additionally, if P xc=0, then law(tr) is the pushforward of Student_nu by t -> sqrt((real(n)-2)/(real(n)-real(k)-1))*t; if k>=2 this law differs from Student_(n-2). There is no lower bound nu>2: nu=1 and nu=2 are included. The orthogonality implication does not put the full t law or positive-SSE facts into the hypotheses; the scope is checked in `scratch/BlindScope.lean`.

The docstring describes precisely linear OLS, projection and attenuation, covariance, Gaussian laws, and exclusion of an empirical nonlinear application.

Junk conventions: all matrix inverses are total but the hypotheses make every relevant Gram matrix invertible, including that of L(x). The intercept condition plus k+1<n implies k>=1 and n>=3; thus neither observation nor coefficient index types can be empty and n, n-2, n-k-1 are positive. The natural differences n-k and n-k-1 therefore agree with ordinary integer subtraction and their real casts. The conclusion sm>0 and sc>=sm excludes zero or negative slope denominators. Residual errors and SE² are nonnegative; only t identities have sf>0 guards. At arbitrary perfect fits, the definitions t=0 and t²=0 at zero SE are still total but no unguarded deterministic inference uses them. In the Gaussian clause zero SSE is null and the positive degrees of freedom exclude Student_0. Covariance's inner and outer Bochner integrals have finite first/second moments supplied in the hypotheses, and linear residuals inherit this. The Gaussian clause makes no moment assertion at nu=1,2 and so does not use nonexistent variances or means of a Student statistic. Measurability prevents the totalized nonmeasurable pushforward branch; Gaussian sigma² is strictly positive. The only roots here have nonnegative arguments (positive where inverted); no logarithm, real-power, infinite conversion, sInf/sSup, or limsup convention is used. Covariance rank can be stated without explicitly requesting independence. sigma as a positive NNReal in the Gaussian clause represents exactly all positive real scales.

## SAP.P039.T5

Source: `SAP/P039/Challenge/Part1.lean:39`, `SAP/P039/Defs/Part4.lean:14,19–101,110–115,138–169`.

The measure index j has type Fin 5, i.e. exactly 0,1,2,3,4. Each E_j is a finite set of natural election years. E_0=E_2={1948,1952,1956,1960,1964,1968,1972,1976,1980,1984,1988,1992,1996,2000,2004,2008,2012}; E_1=E_3={1972,1976,1980,1984,1988,1992,1996,2000,2004,2008,2012}; E_4={1960,1964,1968,1972,1984,1996,2004,2008}.

The function X(j,t) is the exact rational lookup table below. Every terminating decimal is exact, not a real approximation. A dash means t is outside E_j and the total function returns the placeholder zero. Every natural t not in any displayed row also returns zero.

| Year | X(0,t) | X(1,t) | X(2,t) | X(3,t) | X(4,t) |
|---|---|---|---|---|---|
| 1948 | 0.186449401704861 | — | 0.239968577629729 | — | — |
| 1952 | 0.068356278600414 | — | 0.0879775359846345 | — | — |
| 1956 | -0.039661945232703 | — | -0.051046667334368 | — | — |
| 1960 | -0.041319840049504 | — | -0.0531804508563835 | — | -0.068 |
| 1964 | -0.24728138844441 | — | -0.318262019168295 | — | -0.22 |
| 1968 | 0.170508105389464 | — | 0.219451428379582 | — | 0.116 |
| 1972 | -0.365450440554801 | -0.51177218671487 | -0.455834850869706 | -0.60215659702977 | -0.041 |
| 1976 | 0.044642638216102 | -0.231688492759438 | 0.0508461944446885 | -0.22548493653085 | — |
| 1980 | -0.498138285011637 | -0.171462108121506 | -0.621023999873778 | -0.294347822983647 | — |
| 1984 | 0.235890938802093 | -0.0356144375420135 | 0.27380029103004 | 0.00229491468593002 | 0.0385 |
| 1988 | 0.153129340875841 | -0.296507211564452 | 0.173195729075055 | -0.276440823365235 | — |
| 1992 | 0.133646079679683 | -0.061530236247573 | 0.192515613229452 | -0.00266070269781005 | — |
| 1996 | -0.104467146002477 | 0.336875932107128 | -0.14605008654561 | 0.295292991563994 | 0.0415 |
| 2000 | -0.0859714651726795 | 0.237764496391801 | -0.169644956461836 | 0.154091005102645 | — |
| 2004 | 0.048727587431465 | -0.340268001872056 | 0.249490683526865 | -0.139504905776655 | 0.052 |
| 2008 | -0.061819369305165 | -0.30311773910617 | -0.119001518922825 | -0.36029988872383 | -0.0045 |
| 2012 | 0.0294616125544001 | 0.33154260332366 | 0.0403303265691201 | 0.34241131733838 | — |

The prescribed signed-winner function is W=(1984,1996,1984,2012,1968). The prescribed maximum-score vector is m=(0.235890938802093,0.336875932107128,0.27380029103004,0.34241131733838,0.116).

The statement is a conjunction of the following four groups, with no external hypotheses:

1. 1972 and 1980 both belong to E_1 and E_3. |X(1,1972)|-|X(1,1980)|=85077519648341/250000000000000, and |X(3,1972)|-|X(3,1980)|=307808774046123/1000000000000000. Both differences are strictly positive, expressed also as the two strict magnitude comparisons.
2. 1980 and 1984 both belong to E_2. X(2,1980)<0<X(2,1984). (-2.23)*X(2,1984)=-1526436622492473/2500000000000000<0 and differs from 1.38. For every natural t in E_2, X(2,t)<=X(2,1984).
3. For every j : Fin 5, W_j belongs to E_j, X(j,W_j)>0, and for every natural t in E_j distinct from W_j, X(j,t)<X(j,W_j). Thus these are unique signed maxima, not definitions that force maximization.
4. For every j : Fin 5, X(j,W_j)=m_j.

The universal order in the maxima clause is j, then membership/positivity conclusions, then t, its membership and inequality to W_j, then the strict comparison. The docstring says the two voter-centered comparisons refute the 1980 selection and that all five signed maxima are positive, with a negative worked product. It does not describe an arbitrary coefficient rule; the only coefficient used by this statement is the fixed real -2.23.

Junk conventions: all rational denominators are fixed positive integers; all decimal casts are exact rationals. The only partial-looking definition is the year lookup, whose default is zero outside E_j. Every optimization quantifier is guarded by t in E_j, and every explicit year used is asserted in E_j, so this default cannot affect the result. Fin 5 is nonempty and has exactly five elements; the generated matcher has no reachable default case. Each election set is nonempty and the theorem asserts an attained unique maximum by comparisons rather than by sSup/sInf. No subtraction is on naturals in the statement, and there are no measure, integral, root, power, limit, or infinity conventions here. The generated `modelElections._proof_1` appearing in the closure is only a NeZero proof for Fin 5, not an extra sampling definition or restriction.
