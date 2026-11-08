# Blind mathematical reading

This file was written from `SAP/P010/Defs.lean`, all six `Defs/Part*.lean`
files, and `Challenge.lean` / `Challenge/Part1.lean`, before opening
`claims.json` or `record.json`. No Solution or Comparator was inspected.
The mathematical abbreviations below are expansions of definitions, not
additional hypotheses. Arm labels are zero-based.

## Shared objects and exact conventions

For natural numbers K,d, a population state is
ω=((Y_a)_a,(S_a)_a,Z,X) in
R^{Fin K} × Bool^{Fin K} × Fin K × R^{Fin d}, with the usual finite
product Borel measurable spaces. `true` means pass. The observed variables
are Y=Y_Z and S=S_Z. Write B_a={Z=a}, P={S=true}, P_a={S_a=true},
A=intersection_a P_a, C={all S_a are equal}, and
O_a={S_b=true for every b≠a}. Consistency Y=Y_a and S=S_a on B_a is
built into the coordinates.

For a measure μ and real f, write
M_μ(f;E)=(integral_E f dμ)/(μ(E)).toReal. This is exactly `meanOn`.
It is an ordinary event conditional mean only when 0<μ(E)<infinity and
f is integrable on E. A nonintegrable integrand has Bochner integral zero;
real division by zero is zero; ENNReal.toReal(infinity)=0. No existence
of an ordinary expectation is implicit in M. All real integrals below
have this totalized Bochner convention.

p_a=`passRate μ a`=μ(P∩B_a).toReal / μ(B_a).toReal.
`randomAssignment μ` means, in this order, (i) for every a the pair
(Y_a,S_a) is independent of Z, and (ii) μ(B_a)>0 for every a.
It does NOT require the whole vector ((Y_a)_a,(S_a)_a) to be independent
of Z. `positivePassRates` means p_a>0 for every a.
`populationAssumptions` means μ is a probability measure, randomAssignment,
and positivePassRates. A probability measure has μ(universe)=1.
`covariateRandomAssignment` replaces the independent pair with
(Y_a,S_a,X), still separately for every a, and also requires every arm
to have positive mass. `covariateBalance` means: for each b in Bool,
if μ(S=b)>0, then X and Z are independent under
μ(·∩{S=b})/μ(S=b). It imposes nothing on a zero-mass status.
All independence statements use factorization on every pair of measurable
events in the respective generated sigma algebras.

The conditional law L_μ(f|E) is μ(E)^{-1} times the pushforward of μ|E
by f, with inverse and scalar multiplication in ENNReal.
F_a=`passerDistribution μ a`=L_μ(Y|P∩B_a).
r_a=`trimmingRatio μ a`=sum_{b≠a}(1-p_b)/p_a.
The potential counterpart is
r_a^pot=sum_{b≠a} μ(S_b=false).toReal / μ(P_a).toReal.

For a real measure F and real u, the quantile is the EXTENDED real
Q_F(u)=inf{x in [-infinity,+infinity]: u≤F({y:y≤x}).toReal}.
The set infimum uses the complete order on EReal, including inf(empty)
=+infinity. For a probability measure Q_F(0)=-infinity; Q_F(1) may
be +infinity. The real quantile q_F(u)=Q_F(u).toReal sends both infinities
to zero. In the probability cases here, for 0<u<1 the quantile is finite.
`noAtoms F` is F({x})=0 for every real x.
`fullRealSupport μ f` is μ(l<f<u)>0 for every real l<u.
`allMoments μ f` is integrability of |f|^n for every natural n, including 0.

The real trimmed endpoints are
L_a=M_μ(Y;P∩B_a∩{Y≤Q_{F_a}(1-r_a)}) and
U_a=M_μ(Y;P∩B_a∩{Q_{F_a}(r_a)≤Y}).
Comparisons with quantiles are in EReal. The upper-tail mean is
T_F(p)=M_F(id;{y:Q_F(p)≤y}).
The essential endpoints e_a^-,e_a^+ are the essential infimum and
supremum of the extended-real identity y↦(y:EReal) under F_a.
They are formed in a complete lattice, so infinite values are meaningful.
The corrected endpoint pair is (L_a,U_a) embedded in EReal if r_a<1,
and (e_a^-,e_a^+) otherwise.

ν is compatible with μ if ν satisfies populationAssumptions, ν(A)>0,
and the pushforward laws of (Y,S,Z) under ν and μ agree. Covariates and
the joint potential vectors are not in this observable law.
C_a(μ) is the set of real numbers M_ν(Y_a;A) for such compatible ν.
No separate integrability condition occurs in this set definition.
Its extended version is just its image in EReal, not a closure and not
a set enlarged by ±infinity. `IsGLB` and `IsLUB` assert actual greatest
lower bounds / least upper bounds of that embedded set; they do not
assert attainment.

A tail coupling of F and p is a probability measure γ on R×Bool whose
first marginal is F and for which γ(second=false).toReal=p.

### Empirical definitions

The three arms are 90–90, 90–70, 90–45. Let n=(544,538,533),
f=(35,182,40), N_a=n_a-f_a, preference counts c=(61,162,327),
and approval counts h=(192,188,324). These are constants supplied by
the file, not quantities tied to a raw dataset by a hypothesis.
Let δ_a=f_a/n_a in Q, t_a=sum_{b≠a}δ_b/(1-δ_a),
k_a^-=max(0,ceil(N_a(1-t_a))-1), and
k_a^+=N_a truncated-minus max(0,floor(N_at_a)).
For counts o_a the endpoint pair is
(max(0,k_a^- - max(0,N_a-o_a))/k_a^-,
 min(k_a^+,o_a)/k_a^+) in Q, and I_a(o) is the closed real interval
with those endpoints. Every subtraction of naturals is truncated at 0;
the ceil-minus-one is first an integer subtraction, then clamped at 0.
The lower truncation in the numerator is the usual count of retained
ones in the bottom tail, rather than signed subtraction.
Let H=1-sum_a δ_a. The fractional preference pair is
(max(0,(c_a/n_a-sum_{b≠a}δ_b)/H), min(1,(c_a/n_a)/H)).

### Density and finite-cell definitions

e(π,f_R,f_O)=π f_R/[π f_R+(1-π)f_O].
o(p)=p/(1-p), v(p)=(1-p)/p, and sigmoid(η)=exp(η)/(1+exp(η)).
N(f,w)(x)=f(x)w(x)/sum_u f(u)w(u) on Fin n.
The density version is D_ν(f,w)(x)=f(x)w(x)/integral f w dν.
The original cell distribution is f_O=(3/4,1/4), replication
f_R=(1/4,3/4), and cell e_x=e(1/2,f_R(x),f_O(x)).

### Explicit population constructions

`finitePopulation` is the finite sum of masses times Dirac measures
at the supplied states. `fairArmDistribution` assigns 1/2 to each of 0,1.
`stratumPopulation(s0,s1;F0,F1)` draws independent Y_0~F0, Y_1~F1,
and fair Z, fixes (S_0,S_1)=(s0,s1), and uses d=0.
E is the exponential law with density exp(-x) on x>0.
Lap(r) has density ENNReal.ofReal((r/2)exp(-r|x|)); it is used here
only with r=1,2. The reflected E is the law of -E.

`missingPassingPopulation upper` has strata (true,true), (true,false),
(false,true) with probabilities 1/4,1/4,1/2. In the first stratum Y_0
has E if upper=true and -E otherwise; in the second it has the opposite
law. In the third Y_0 has Lap(2). Y_1 has Lap(1) in every stratum;
within strata outcomes and fair Z are independent.

B is the Beta(3,3) law with density 30x²(1-x)² on (0,1).
Hvy has density 5/[2(1+|x|)^6] on R.
`commonOutcomePopulation(s;F)` draws Y_0=Y_1~F, fixes S_0=S_1=s,
and draws fair independent Z.
`boundedPasserPopulation` is 1/3 commonOutcome(true;B) plus
2/3 commonOutcome(false;Hvy).
For 0<t<1, `betaEndpointPopulation(t,upper)` uses
E_t=(0,t) if upper=false and (1-t,1) otherwise, q=B(E_t),
F=B|E_t/q and G=B|((0,1)\E_t)/(1-q). Its four stratum components
(checks; outcome laws; mass) are
(TT;F,F;q/3), (TF;G,Hvy;(1-q)/3),
(FT;Hvy,G;(1-q)/3), (FF;Hvy,Hvy;(1+q)/3).

`normalCommonPopulation` is 4/5 commonOutcome(true;N(0,1)) plus
1/5 commonOutcome(false;N(0,1)). Here Gaussian's second argument is
the variance. With variance 0 Mathlib defines it as a Dirac measure.

The four-state `jointDependencePopulation` assigns mass 1/4 each to
(Y_0,Y_1,S_0,S_1,Z)=(0,0,T,T,0),(1,1,T,T,0),
(0,1,T,T,1),(1,0,T,T,1), with no covariates.
For `selectionPopulation(q)`, use three equally likely subject types
(Y_0,Y_1,S_0,S_1)=(1,1,F,T),(0,0,T,F),(0,0,T,T), X=0;
independently Z=0 with probability q and Z=1 with probability 1-q.
In the literal definition masses are passed through ENNReal.ofReal;
T16 only uses 0<q<1.

For `simulationPopulation(p0,p1,ρ,λ,σ)`, set
a=p0*p1+ρ sqrt(p0(1-p0)p1(1-p1)). The check strata FF,TF,FT,TT
have masses ENNReal.ofReal(1-p0-p1+a), ofReal(p0-a), ofReal(p1-a),
ofReal(a), respectively. In each, independently draw ε~N(0,σ²)
and fair Z, and set Y_0=Y_1=λ(1_{S_1}-1_{S_0})+ε.
`checkCorrelation` is [μ(P_0∩P_1)-μ(P_0)μ(P_1)]/
sqrt(μ(P_0)(1-μ(P_0))μ(P_1)(1-μ(P_1))), using toReal masses.
The effect interval width W(μ)=(U_1-L_0)-(L_1-U_0).
N_w=`normalMixture w`=(1-w)N(0,1)+w N(-1,1) with ofReal
weights. Its lower and upper means are its bottom 3/4 mean and
top 3/4 mean, denoted m_w^- and m_w^+.

## Theorems, in file order

All unnamed quantifiers range over the objects just defined. Conjunctions
below are assertions together, not hypotheses. Each theorem proves the
corresponding `TnStatement`.

### T1

There are no hypotheses or free parameters. I_0(c) and I_1(c) are
disjoint; I_0(c) and I_2(c) are disjoint; it is false that for every
ordered pair a,b in Fin 3 some real x belongs to both I_a(c),I_b(c);
and there is no real x belonging to I_a(c) for every a in Fin 3.

### T2

No hypotheses. For every arm, N=(509,356,493),
t=(32239072/72978893,10871635/51611456,31403827/72143648),
k^-=(284,281,278), k^+=(285,282,279). Preference endpoints are
[(0,61/285),(87/281,27/47),(56/139,1)]; approval endpoints are
[(0,64/95),(113/281,2/3),(109/278,1)].
For every a, every natural j, then hypotheses 1≤j and j≤N_a,
j/N_a<1-t_a iff j≤k_a^-, and j/N_a>t_a iff N_a-k_a^+<j.
The point 1/2 belongs to every approval interval and to preference
intervals 1 and 2. The preference upper endpoint of arm 0 is strictly
below both other lower endpoints. Their respective gaps are
7654/80085 and 7481/39615, each positive. H=40739821/77997088>0.
The fractional preference pairs for all three arms are
[(0,8745997/40739821),
 (12614477/40739821,23486112/40739821),
 (16448045/40739821,1)]. The lower endpoints of arms 1 and 2
minus arm 0's upper endpoint equal 3868480/40739821 and
7702048/40739821 respectively, each positive.

### T3

For every Bool upper, let μ be the specified missingPassingPopulation.
Then populationAssumptions hold, μ(A)=1/4, the observed Y law is
atomless, Y has full real support and every absolute moment,
p_0=1/2,p_1=3/4,r_0=1/2, F_0=Lap(1), and Q_{F_0}(1/2)=0.
M_μ(Y;{Y≤0}∩B_0)=-3/4 and M_μ(Y;{0≤Y}∩B_0)=3/4,
where neither event requires passing. M_μ(Y_0;A) is +1 for
upper=true and -1 otherwise. It is false that this last mean lies
between those two non-passing-conditioned means. Corrected endpoints
are L_0=-1,U_0=1. Finally the two populations, with upper=false,true,
have identical pushforward laws of (Y,S,Z).

### T4

For all natural K,d, then μ, assume populationAssumptions; choose
a in Fin K; assume μ(A)>0, F_a atomless, Y integrable under
μ restricted to P∩B_a, and r_a<1, in that order. Then
L_a≤M_μ(Y_a;A)≤U_a; each endpoint belongs to C_a(μ);
every real m in C_a(μ) satisfies L_a≤m≤U_a;
p_a(1-r_a)=H:=1-sum_b(1-p_b); and r_a<1 iff H>0.
If r_a=0 both endpoints equal M_μ(Y;P∩B_a).
Also L_a=(p_a/H) integral_0^{H/p_a} q_{F_a}(u) du and
U_a=(p_a/H) integral_{1-H/p_a}^1 q_{F_a}(u) du.
These are Mathlib oriented interval integrals for Lebesgue measure;
here the hypotheses order the limits and give H/p_a in (0,1].

### T5

No hypotheses. For the specified boundedPasserPopulation μ,
populationAssumptions hold; μ(A)=1/3; Y's law is atomless and has
full real support; integrals of Y, Y², |Y|³ are 1/6,13/63,19/84;
|Y|³ is integrable. For every real R≥1, the masses of {Y>R}
and {Y<-R}, converted to reals, are both 1/[3(1+R)^5].
For each a in Fin 2, p_a=1/3, r_a=2, every m in C_a(μ)
satisfies 0<m<1, and the embedded compatible set has GLB 0 and
LUB 1; it does not have GLB -infinity or LUB +infinity.
For every real t with 0<t<1, B((0,t))=10t³-15t⁴+6t⁵;
both betaEndpointPopulation(t,false) and (...,true) are compatible;
for every a their always-passer means are respectively
b(t)=t(15/2-12t+5t²)/(10-15t+6t²) and 1-b(t), with 0<b(t)<t.

### T6

For all K,d, μ satisfying populationAssumptions, a, μ(A)>0,
atomless observed law μ.map Y, integrability of Y on P∩B_a,
and 1≤r_a, in that order: 1≤r_a iff sum_b p_b≤K-1;
e_a^-≤M_μ(Y_a;A)≤e_a^+ in EReal. For every real l such
that e_a^-=l, l<M_μ(Y_a;A); for every real u such that
e_a^+=u, M_μ(Y_a;A)<u. The extended compatible set has
GLB e_a^- and LUB e_a^+. Any finite essential endpoint is not
in C_a(μ). The set has simultaneously GLB -infinity and LUB
+infinity iff, for every real M, F_a((-infinity,M))>0 and,
separately for every real M, F_a((M,infinity))>0.

### T7

No hypotheses. The given four-state μ satisfies populationAssumptions,
μ(C)=1 and μ(A)=1, but the pair ((Y_0,Y_1),S) is not
independent of Z. Specifically μ(Y_0=0,Y_1=0,S=true,Z=0)=1/4,
whereas μ(Y_0=0,Y_1=0,S=true)μ(Z=0)=1/8.
The selected observed mean is 1/2 in each arm, and
M_μ(Y_0-Y_1;A)=0.

### T8

For all K,d, μ satisfying populationAssumptions and μ(C)=1,
then a in Fin K with Y_a integrable on the entire population:
S=S_a almost surely; (Y_a,S) is independent of Z; for every t,
p_t=μ(P).toReal>0; P=A up to a μ-null set; and
M_μ(Y;P∩B_a)=M_μ(Y_a;P∩B_a)=M_μ(Y_a;P)=M_μ(Y_a;A).

### T9

For each ρ in the two-element set {1/4,1/2}, use
μ_ρ=simulationPopulation(4/5,4/5,ρ,1,1).
It satisfies populationAssumptions, μ_ρ(A)>0, atomless full-support
observed Y, actual check correlation ρ, p_0=p_1=4/5 and
r_0=r_1=1/4. The A masses at the two correlations are 17/25,18/25.
Their arm-0 passer laws are N_{3/20},N_{1/10}, and their arm-1
laws are respectively the reflections of those laws.
The two mixture means are -3/20,-1/10 and the centered second
moments are 451/400,109/100. The widths are respectively
2(m_{3/20}^+-m_{3/20}^-) and 2(m_{1/10}^+-m_{1/10}^-).
The first width belongs to
[1798577298898/10^12,1798577299027/10^12], the second to
[1767983385194/10^12,1767983385319/10^12], and their difference
is greater than 30593913580/10^12. There are no free design
parameters outside the initial two-element universal quantifier.

### T10

For all real p0,p1,ρ,λ,σ, in that order, assume
0<p0<1, 0<p1<1, σ≥0, and, setting
a=p0*p1+ρ sqrt(p0(1-p0)p1(1-p1)), assume in file order
0≤1-p0-p1+a, a≤p0, a≤p1, 0≤a.
Then all of the following hold:

* For every natural K,d, every μ,ν satisfying populationAssumptions,
  every arm i, if the whole pass-rate functions agree and the arm-i
  passer laws agree, their corrected endpoint pairs for i agree.
* Let w0=1-a/p0, w1=1-a/p1, and let μ be the simulation population.
  It satisfies populationAssumptions, μ(A).toReal=a, actual check
  correlation ρ and pass rates p0,p1. Its passer laws are
  (1-w0)N(0,σ²)+w0 N(-λ,σ²) in arm 0 and
  (1-w1)N(0,σ²)+w1 N(λ,σ²) in arm 1.
  Its selected means are -λw0 and λw1.
* If λ≠0, then for every real ρ'≠ρ, both real algebraic formulas
  -λ[1-(p0*p1+ρ' sqrt(p0(1-p0)p1(1-p1)))/p0] and
  λ[1-(p0*p1+ρ' sqrt(p0(1-p0)p1(1-p1)))/p1]
  differ from their counterparts with ρ. No admissibility hypothesis
  is imposed on ρ' in this clause; it compares formulas.
* The two fixed widths from T9 are unequal.

### T11

No hypotheses. sigmoid(log(1/3))=1/4 and
sigmoid(log(1/3)+log(9))=3/4.
For every q0,q1 in R, then hypotheses 0<q0<1,0<q1<1,
the log likelihood log(q0)+3log(1-q0)+3log(q1)+log(1-q1)
is at most its value at (1/4,3/4), with equality iff
q0=1/4 and q1=3/4.
For each of the two cells f_O,f_R are positive and 0<e_x<1.
The propensities are 1/4,3/4, their odds 1/3,3, their
f_R-weighted masses 1/12,9/4, and the total 7/3.
The normalized odds-weighted mass of cell 1 is 27/28,
which differs from its original mass 1/4. In every cell,
normalized reverse-odds weighting of f_R equals f_O.

### T12

For every type Ω and measurable space on it, then every measure ν,
real π and real functions f_R,f_O, assume in order
0<π<1, f_R>0 ν-a.e., f_O>0 ν-a.e., integrability of f_R
and f_O, and integral f_R=integral f_O=1.
Writing e_x=e(π,f_R(x),f_O(x)), conclude:
ν-a.e., 0<e_x<1,
o(e_x)=[π/(1-π)] f_R/f_O, and
f_O/f_R=[π/(1-π)]v(e_x).
The integral of f_R v(e) is (1-π)/π; D_ν(f_R,v(e))=f_O
ν-a.e.; for every positive real c, D_ν(f_R,c v(e))=f_O
ν-a.e. Finally, IF f_R²/f_O is integrable, its integral J is
strictly positive, D_ν(f_R,o(e))=(f_R²/f_O)/J ν-a.e., and
D_ν(f_R,o(e))=f_O ν-a.e. iff f_R=f_O ν-a.e.
Nothing is asserted in the last clause for a nonintegrable
squared-density ratio, and no nonnegative infinite integral appears.

### T13

No hypotheses. The specified normalCommonPopulation μ satisfies
populationAssumptions, μ(A)=4/5, and atomless full-support observed Y.
Each arm has pass rate 4/5 and passer law N(0,1).
For arm 0 both trimming shares equal 1/4;
M_μ(Y_0;A)=M_μ(Y_0;O_0∩P_0)=0.
For q=q_{N(0,1)}(3/4), M_μ(Y_0;Y_0≤q)=-φ(q)/(3/4)<0,
so it is false that the always-passer mean is at most that lower-tail
mean. The corrected U_0=φ(q_{N(0,1)}(1/4))/(3/4)>0,
where φ is the usual standard normal density.

### T14

For all K,d, then a probability measure μ, arm a, μ(A)>0,
atomless F=L_μ(Y_a|P_a), and integrability of Y_a on P_a:
for every real p, if 0≤p<1, then (i) every tail coupling γ of
F,p has M_γ(first;second=true)≤T_F(p), and (ii) the explicit
pushforward of F under y↦(y,indicator[Q_F(p)≤y]) is such a
coupling and attains equality. For every real p,q with
0≤p≤q<1, T_F(p)≤T_F(q).
Also μ(O_a^c∩P_a).toReal/μ(P_a).toReal≤r_a^pot, and if
r_a^pot<1, M_μ(Y_a;A)≤T_F(r_a^pot).
Neither random assignment nor positive passing in every arm is a
hypothesis of this theorem.

### T15

For all K,d, μ satisfying populationAssumptions, arm a,
μ(A)>0, atomless observed law μ.map Y, and integrability
of Y on P∩B_a, in that order:
L_μ(Y_a|P_a)=F_a; for every b, μ(P_b).toReal=p_b;
r_a^pot=r_a; T_{L_μ(Y_a|P_a)}(r_a)=U_a.
If r_a<1, then M_μ(Y_a;A)=M_μ(Y_a;O_a∩P_a)
and this mean is at most U_a. The tail-mean equality itself is
not guarded by r_a<1.

### T16

For every real q, then hypotheses q>0 and q<1, the specified
selectionPopulation(q) satisfies populationAssumptions,
covariateRandomAssignment, covariateBalance, μ(A)=1/3,
p_a=2/3 for every a, and independence of S and Z.
Y_1-Y_0=0 almost surely; the integral of 1_{S_1}-1_{S_0}
is zero. The mean of Y_1-Y_0 on A, on {S_0=T,S_1=F},
and on {S_0=F,S_1=T} is zero in each case.
Selected observed arm means are 0 and 1/2; their arm-1-minus-arm-0
difference is 1/2, and 1/2≠0.

### T17

For all K,d, μ, then hypotheses that μ is a probability measure
and randomAssignment holds: for every a, p_a=μ(P_a).toReal;
positivePassRates holds iff μ(P_a)>0 for every a.

### T18

For all K,d, μ satisfying populationAssumptions, μ(C)=1,
then arms a,b, with Y_a and Y_b integrable on the whole population:
M_μ(Y;P∩B_a)-M_μ(Y;P∩B_b)=M_μ(Y_a-Y_b;A).

### T19

For all K,d, probability μ satisfying randomAssignment, then
arms a,b with Y_a,Y_b integrable on the whole population:
M_μ(Y;B_a)=integral Y_a dμ,
M_μ(Y;B_b)=integral Y_b dμ, and their difference is
integral (Y_a-Y_b) dμ. No positive pass-rate or common-check
hypothesis is imposed.

### T20

For all K,d, probability μ satisfying randomAssignment and
μ(C)=1, S and Z are independent. No outcome integrability
or positive pass-rate hypothesis is imposed.

### T21

There exists a measure μ on Population(2,1) satisfying
populationAssumptions, independence of observed S and Z,
μ(A)>0, and
M_μ(Y;P∩B_1)-M_μ(Y;P∩B_0)≠M_μ(Y_1-Y_0;A).
There is NO integrability condition on any of these three restricted
integrands, and NO explicit witness is named in this statement.
The quantifier is existential over an entire measure, not over a
parameter of a previously supplied family.

### T22

For all K,d, probability μ satisfying covariateRandomAssignment
and μ(C)=1, covariateBalance holds (the two status-conditional
independences for positive-mass statuses). No positive pass rates
or outcome integrability is imposed.

### T23

There exists a measure μ on Population(2,1) such that μ is a
probability measure, every pass rate is positive,
covariateRandomAssignment and covariateBalance hold, and
μ(A∩{X=0})>0. Its selected arm-1-minus-arm-0 contrast restricted
also to X=0 differs from M_μ(Y_1-Y_0;A∩{X=0}).
There is NO integrability condition for any of these three event
integrands, no named witness and no requirement of positive variance
or multiple support points for X. The all-zero one-coordinate
covariate is permitted.

## Mathlib definitions checked

The definitions were followed to the installed Mathlib sources under
`/home/ubuntu/sal/deps/mathlib/Mathlib/`:

* `Probability/Independence/Basic.lean:94–146` and the corresponding
  `Kernel/Indep*.lean` definitions: independent generated sigma algebras
  and event factorization (not vector independence inferred from marginals).
* `MeasureTheory/Measure/Typeclasses/Probability.lean:64`: total mass one.
* `MeasureTheory/Function/L1Space/Integrable.lean:59`: a.e. strong
  measurability and finite integral of the norm.
* `MeasureTheory/Integral/Bochner/Basic.lean:158,204`: integral equals
  zero without integrability; set integral is integral under restriction.
* `MeasureTheory/Measure/Restrict.lean:43–72`: restriction gives
  intersection masses on measurable sets.
* `MeasureTheory/Measure/Map.lean:99`: pushforward for a.e. measurable
  maps; otherwise an arbitrary Dirac mass for nonzero source measure
  (zero source stays zero). All population coordinate maps, stratum maps,
  sign reflections and threshold maps used here are measurable, so the
  fallback is not their intended reading.
* `MeasureTheory/Function/EssSup.lean:46,51`: essSup and essInf are
  filter limsup/liminf for the a.e. filter. Their EReal codomain is a
  complete lattice, avoiding a conditional-completeness default.
* `Data/EReal/Basic.lean:220`: both infinities convert to real zero.
* `Probability/Distributions/Gaussian/Real.lean:222`: normal law of
  specified mean and variance; variance zero gives a Dirac law.

Ordinary Fin sums, natural truncated subtraction, integer floor/ceiling,
closed/open real intervals, ENNReal inverse/ofReal, finite measure sums,
product measures and density measures have their usual Mathlib meanings.
No proof of a Challenge stub was used as evidence for this reading.
