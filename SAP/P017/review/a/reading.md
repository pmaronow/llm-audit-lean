# Blind reading of the P017 Challenge

This file was written from `SAP/P017/Defs*.lean`, `SAP/P017/Defs/*.lean`,
`SAP/P017/Challenge*.lean`, `SAP/P017/Challenge/*.lean`, and the relevant Mathlib
definitions, before opening either `claims.json` or `record.json`. Names in the
Challenge are theorem stubs whose propositions are the corresponding
`TnStatement` definitions. No Solution or Comparator was read.

## Conventions and fully expanded common definitions

All functions called effects, estimates, weights, and remainders are real valued.
An arbitrary sample space has its stated sigma algebra; real spaces have their
Borel sigma algebra and products/functions have the product sigma algebra.
Unless a section explicitly says otherwise, G and P are probability measures,
meaning their mass on the whole space is exactly one. E_G denotes the Bochner
integral against G. In Mathlib that integral is defined to be zero for a
nonintegrable function. Integrable means almost everywhere strongly measurable
and finite integral of the absolute value; I do not silently add integrability
when the proposition does not state or imply it.

For measurable integrable tau:Omega->R, put mu=E_G tau. Its effect support S is
the closed topological support of the pushforward G.map tau: x belongs to S iff
every open neighborhood of x has positive pushforward mass. It is not the
pointwise range of tau. Let a=inf{x:x in S} and b=sup{x:x in S}, with these infimum
and supremum taken after embedding R into the complete extended real line
[-infinity,+infinity]. Empty infimum/supremum would be +infinity/-infinity.
The radius c is max(0,min(b-mu,mu-a)) in [0,+infinity]; specifically this uses
EReal.toENNReal, which sends negative values and -infinity to zero and
+infinity to +infinity. Subtraction here is in EReal, with mu always finite.

C_d(x)=min(mu+d,max(mu-d,x)) for finite real d. C_c(x) uses this formula
with d=c.toReal when c is finite, and C_infinity(x)=x. The infinite branch is
explicit: it does not substitute infinity.toReal=0. R_d(x)=x-C_d(x).
I_c(x) means ENNReal.ofReal(|x-mu|)<=c, equivalently |x-mu|<=c for finite
nonnegative c, and always true for c=infinity.

A weight w:Omega->R is admissible iff it is measurable, is nonnegative at
EVERY point, E_G|w| is finite, E_G w>0, and w*tau is integrable. Its weighted
mean is E_G(w*tau)/E_G w. Rep(t) means there EXISTS such an admissible w with
weighted mean t. The admissible denominator is finite and strictly positive.
An atom at t means G{tau=t}>0. IOA(t) means either a<t<b, or (t=a or t=b)
and t is an atom. Bounds comparing finite values with a or b use EReal.

For any measure Q and set A, pr(Q,A)=(Q(A)).toReal. This is the real value of
the outer measure even when A is not measurable; infinite outer measure would
be sent to zero. For probability Q it is always finite, so this conversion
does not erase an infinite value. All pr expressions below use probability
measures. Almost everywhere equalities are with respect to the indicated Q.

Write q_n=sqrt(n) for n:N. For a sequence V_n and deterministic real sequence
h_n, LittleOp(Q,V,h) means: for EVERY eta>0,
pr(Q,{|V_n|>eta*h_n})->0 as n->infinity. Positivity of h is not built into the
definition; it is separately required where stated. BIP(Q,V) means: for EVERY
epsilon>0 there EXISTS M>0 such that EVENTUALLY in n,
pr(Q,{|V_n|>M})<epsilon. Cons(Q,hat,mu) means: for EVERY b>0,
pr(Q,{|hat_n-mu|>b})->0.

RN(Q,hat,mu) means there EXISTS variance v in the nonnegative reals with v>0
such that q_n*(hat_n-mu) converges in distribution to N(0,v). Mathlib's
TendstoInDistribution includes almost everywhere measurability of EVERY
scaled variable, and convergence of their pushforward probability laws in
the weak topology. N(m,v)=gaussianReal m v, with v a variance, not a standard
deviation; v=0 would give the Dirac mass at m, but RN excludes that case.

NR(Q,hat,Z,e,mu,v) means, for EVERY n>=1: Z_n is measurable and has law
N(0,v); e_n is measurable and e_n^2 is integrable; and
q_n*(hat_n-mu)=Z_n+e_n almost everywhere. It does NOT require independence of
Z_n and e_n, independence across n, or measurability of hat unless separately
specified. SR(Q,e) means q_n*E_Q(e_n^2)->0. SM(Q,V) means n*E_Q(V_n^2)->0.
These limit definitions alone do not assert integrability.

Phi(x)=N(0,1)((-infinity,x]). Write

    T(n,d,s)=2 integral_{x>d} x^2 * [sqrt(n)/(s*sqrt(2*pi))]
                       * exp(-x^2*n/(2*s^2)) dx.

This is a Lebesgue integral on R restricted to the open upper tail. The
statements using its normal-density interpretation require n>=1,d>0,s>0.

For a probability G, G^N=iidSamples G is the countably infinite product of
copies of G, on sequences indexed by N; Mathlib infinitePi takes this product
branch because each factor is a probability measure. For a sequence s,
bar X_n(s)=(sum_{0<=i<n} X(s_i))/n, and
L_n(O,s)=(1/n)*sum_{0<=i<n} dirac_{O(s_i)} is the empirical observed measure.
The scalar in the latter is in [0,infinity]. Every fixed-sample assertion
using these constructions below is for n>=1. Their values at n=0 use Lean's
total arithmetic and are irrelevant to the stated limits.

## Concrete populations, including all SAP construction definitions

The IPW population is (U,B,D) with independent U uniform on (0,1), B fair on
{-1,1}, D fair on {0,1}. A fair pair (a,b) is (dirac_a+dirac_b)/2. The uniform
law is Lebesgue measure restricted to (0,1). Potential outcomes are Y0=B,
Y1=B+U, effect tau=Y1-Y0=U. The observed data map is
O=(D,D*Y1+(1-D)*Y0), and the IPW summand is
X=2*D*Yobs-2*(1-D)*Yobs. A_b(n) is the set of ALL sample sequences such that
for every i<n, B_i=b and D_i=0. No conditions on U_i are added in A_b(n).

The normal population is (A,B) with independent A~N(0,1) and B fair on
{-1,1}; Y0=0,Y1=B,tau=B. On its IID sample space put M_n=bar A_n,
H_n=M_n+1/n, D_n=M_n-C_1(H_n) with mu=0,
Z_n=q_n*M_n, and e_n=1/q_n (constant in the sample). Thus D_n is an
intermediate error relative to M_n, not H_n-C_1(H_n).

The slow population is (A,Q,T,D), independently distributed as follows:
A~N(0,1), Q uniform on [0,1),
T~(1/4)dirac_{-1}+(1/4)dirac_1+(1/4)Lebesgue|[-1,1],
and D fair on {0,1}. The continuous part has mass 1/2, so the total is one.
Y0=0,Y1=T,tau=T. The observed data map is (A,Q,D,D*T).
On IID samples define U_n=fract(sum_{i<n} Q_i), where fract(x)=x-floor(x);
F_n=1 if U_n<p_n and F_n=0 otherwise; M_n=bar A_n;
B_n=C_{1/2}(M_n) with mu=0; H_n=B_n+10*F_n; and
e_n=q_n*(B_n-M_n+10*F_n). Here H_n=rareEstimator p and
e_n=rareRemainder p. The special slow sequence is
p*_n=1/(1+floor(log_2 n)) for n>=1; Nat.log 2 0=0 defines p*_0=1.
All of these formulas are defined on the entire sequence space, not merely
on its full-measure population-supported subset.

## SAP.P017.T1

This is an unconditional conjunction about the IPW construction:

* tau is measurable and integrable; mu=1/2; S=[0,1]; c=1/2>0;
  both endpoint atoms have probability zero; almost surely 0<tau<1 and |X|<4.
* E X=1/2, E X^2=14/3, E(X-1/2)^2=53/12.
* For EVERY n>=1, E bar X_n=1/2 and
  E(bar X_n-1/2)^2=53/(12*n). The whole sequence
  q_n*(bar X_n-1/2) converges in distribution to N(0,53/12).
* For EVERY real weight w, if w is measurable, pointwise nonnegative,
  integrable, and E w>0, then 0<E(w*tau)/E w<1. This clause does not
  separately assume w*tau integrable.
* For EVERY n>=1, pr(A_{-1}(n))=pr(A_1(n))=(1/4)^n>0 and the two events
  are disjoint. For EVERY s in A_{-1}(n), all first n summands equal 2,
  bar X_n=2, C_c(bar X_n)=1, L_n(O,s)=dirac_(0,-1), and the clipped
  value is not Rep. For EVERY s in A_1(n), all summands equal -2,
  bar X_n=-2, C_c(bar X_n)=0, L_n(O,s)=dirac_(0,1), and the clipped
  value is not Rep.

## SAP.P017.T2

For EVERY measurable space Omega, probability G, and measurable integrable
tau:Omega->R, the following conjunction holds:

* For EVERY real t, Rep(t) iff t is an atom OR both G{tau<t}>0 and
  G{t<tau}>0.
* For EVERY real t with a<t<b, Rep(t). For EVERY real t equal to either
  extended support endpoint, Rep(t) iff t is an atom. For EVERY real t
  with t<a or b<t, not Rep(t).
* For EVERY real t that is an atom, there EXISTS an admissible w with
  E w=1 and weighted mean t.

There is no prescribed formula or bound for either the atom weight or the
interior weight, and no normalized interior witness is explicitly required.
There is no positive-radius assumption in T2.

## SAP.P017.T3

For EVERY pair of measurable spaces Omega,Xi, probability G, measurable
integrable tau, with c>0, probability P on Xi, and sequence hat of measurable
estimates (measurable for EVERY n, including zero), all of these hold:

* For EVERY real x, a<=C_c(x)<=b and Rep(C_c(x)) iff IOA(C_c(x)).
* For EVERY real x with ENNReal.ofReal(|x-mu|)<c, Rep(C_c(x)).
* IF c=infinity OR every clipping endpoint t=mu-c.toReal or mu+c.toReal
  that also equals a or b has positive tau atom mass, THEN for EVERY real x,
  Rep(C_c(x)). The atom condition is conditional on coinciding with a support
  endpoint; it does not require atoms at clipping endpoints in the support
  interior.
* IF RN(P,hat,mu), THEN pr{|hat_n-mu|<c}->1 and
  pr{Rep(C_c(hat_n))}->1. The first event uses the strict ENNReal inequality.
* For EVERY real x strictly inside that radius, C_c(x)=x.

The RN hypothesis is inside an implication and is required only for the two
probability limits. No separate finite-valued-effect case or explicit
comparison of mu+-c against a,b is included.

## SAP.P017.T4

For EVERY measurable space Omega, probability G, measurable integrable tau,
and c>0, the following conjunction holds:

* There EXISTS real d>0 with ofReal(d)<c.
* For EVERY such real d: for EVERY x, Rep(C_d(x)),
  |C_d(x)-mu|<=|x-mu|, and C_d(x)=x iff |x-mu|<=d.
* Still for EVERY such d, for EVERY measurable space Xi, probability P,
  and arbitrary real function hat on Xi: for EVERY eta>0 and h>0,
  pr{|hat-C_d(hat)|>eta*h}<=pr{|hat-mu|>d}. If hat is measurable and
  max(sup supp(P.map hat)-mu,mu-inf supp(P.map hat))<=d in EReal,
  then pr{hat=C_d(hat)}=1. Measurability is not required for the first
  outer-measure inequality.
* Still for EVERY such d, for EVERY real c'>d there EXISTS real x with
  |x-mu|<=c', C_{c'}(x)=x, and C_d(x)!=x.
* If c is finite, c.toReal/2>0 and ofReal(c.toReal/2)<c. If c=infinity,
  EVERY real d>0 satisfies ofReal(d)<c.
* For EVERY real t, the interior, endpoint-atom, and exterior Rep statements
  from T2 hold.
* Under the same infinite-radius-or-endpoint-atom condition as T3,
  for EVERY x, Rep(C_c(x)).

## SAP.P017.T5

Unconditionally, for the normal construction:

* tau is measurable and integrable, mu=0, S={-1,1}, c=1;
  RN(P,H,0), NR(P,H,Z,e,0,1), and LittleOp(P,q_n/n,1), with
  P=normalPopulation^N.
* For EVERY n>=1, M_n has law N(0,1/n). For EVERY sample s,
  D_n equals M_n+1 if M_n<-1-1/n; otherwise it equals -1/n if
  M_n<=1-1/n; otherwise it equals M_n-1. For EVERY s,
  D_n=0 iff M_n=1. Consequently pr{D_n!=0}=1.
* For EVERY n>=1, pr{|M_n|>1}=2*Phi(-q_n)<1, and that tail is <=1/n.
* For EVERY n>=2 and EVERY sample s with |M_n|<=1/2,
  D_n=-1/n and H_n-C_1(H_n)=0. Moreover
  pr{|M_n|<=1/2}>=1-4/n and
  pr{|D_n|/(1/n)>=1/2}>=1-4/n.
* LittleOp(P,n*D_n+1,1), but NOT LittleOp(P,D_n,1/n).

All n-dependent divisions in these finite assertions have positive n.

## SAP.P017.T6

Unconditionally, again for the normal construction:

* tau is measurable integrable with mu=0,S={-1,1},c=1;
  NR(P,H,Z,e,0,1), SR(P,e), and for EVERY n>=1, E e_n^2=1/n.
* For EVERY sample with |M_25|<=1/2, C_1(H_25)=H_25 and
  D_25^2=1/625. That event has probability >=21/25, so
  E D_25^2>=21/15625.
* T(25,1,1)=E[1_{|M_25|>1}*M_25^2]
  <=E M_25^6=15/15625. Thus
  E D_25^2-T(25,1,1)>=6/15625>0.
* For EVERY sample in the same central event,
  -23/50<=H_25<=27/50.
* SM(P,H_n-C_1(H_n)) AND SM(P,D).

## SAP.P017.T7

For EVERY measurable Omega,Xi, probability G, measurable integrable tau with
c>0, probability P, and real estimate sequence hat satisfying RN(P,hat,mu):

* BIP(P,q_n*(hat_n-mu)) and Cons(P,hat,mu).
* For EVERY deterministic sequence h:N->R with h_n>0 for EVERY n,
  LittleOp(P,hat_n-C_c(hat_n),h).
* If c=infinity, for EVERY n and EVERY sample point,
  hat_n-C_c(hat_n)=0.
* For EVERY n and EVERY point, I_c(hat_n) implies the same zero equality.
* For EVERY n, eta>0, h>0, the event
  {|hat_n-C_c(hat_n)|>eta*h} is contained in {not I_c(hat_n)},
  and its probability is at most that of the latter event.
* pr{not I_c(hat_n)}->0, and
  LittleOp(P,q_n*(hat_n-C_c(hat_n)),1).

RN is an outer hypothesis for the entire conjunction. The theorem does not
separately quantify a merely consistent estimator. Measurability of hat is
not an additional hypothesis here; RN supplies AE measurability of its
scaled variables.

## SAP.P017.T8

This is a conjunction of FOUR separately quantified assertions.

First, for EVERY measurable Xi, probability P, sequences hat,Z,e,
mu,c:R, v>=0, with c>0,v>0, with EVERY hat_n measurable and
NR(P,hat,Z,e,mu,v), and then for EVERY n>=1, set
tilde=mu+Z_n/q_n. All of these hold:

* For EVERY real x,y, |C_c(x)-C_c(y)|<=|x-y| and
  |R_c(x)-R_c(y)|<=|x-y|.
* Almost surely |R_c(hat_n)|<=|R_c(tilde)|+|e_n|/q_n.
* E R_c(hat_n)^2<=2*E R_c(tilde)^2+2*E e_n^2/n.
* For EVERY real x, R_c(x)^2=max(|x-mu|-c,0)^2
  <=1_{|x-mu|>c}*(x-mu)^2<=(x-mu)^4/c^2.
* E(tilde-mu)^4=3*v^2/n^2, and
  E R_c(hat_n)^2<=6*v^2/(c^2*n^2)+2*E e_n^2/n.
* Almost surely |tilde-C_c(hat_n)|<=|R_c(tilde)|+|e_n|/q_n;
  E(tilde-C_c(hat_n))^2<=6*v^2/(c^2*n^2)+2*E e_n^2/n.
* E R_c(tilde)^2<=E[1_{|tilde-mu|>c}*(tilde-mu)^2]
  =T(n,c,sqrt(v)).

Second, universally over a fresh measurable Xi, probability P, hat,Z,e,
mu,c,v, under exactly the same hypotheses plus SR(P,e):
SM(P,R_c(hat_n)) AND SM(P,mu+Z_n/q_n-C_c(hat_n)).

Third, for EVERY real mu,c,x,y, with NO positivity hypotheses,
|x-C_c(y)|<=|R_c(x)|+|C_c(x)-C_c(y)|.

Fourth, for EVERY measurable Xi, ANY measure P (not necessarily finite or a
probability), ANY sequence hat and ANY real mu: for EVERY real x,y,
x-C_infinity(x)=0 and y-C_infinity(x)=y-x; also
SM(P,hat_n-C_infinity(hat_n)). No integrability hypothesis is present or
needed for that identically zero integrand.

## SAP.P017.T9

The proposition is the NEGATION of a universal assertion. That assertion
quantifies, in order: measurable spaces Omega,D,Xi (in Type, not arbitrary
universe levels); probability G; measurable integrable tau with c>0;
measurable observation map O:Omega->D; probability P on Xi; measurable
data:Xi->(N->Omega); estimate sequence hat; an arbitrary
H:N->Measure(D)->R; a factorization hypothesis saying for EVERY n>=1 and
EVERY s in Xi, hat_n(s)=H(n,L_n(O,data(s))); and RN(P,hat,mu).
It then asserts for EVERY n>=1 and EVERY s, Rep(C_c(hat_n(s))).
T9 says that this whole universal assertion fails, equivalently there exist
such spaces, measures, functions and satisfied hypotheses and some positive
n and sample point at which that representation fails.

The negated universal imposes NO law connecting data under P with G^N,
no independence/IID condition, no measurability of H, no measurability of hat
beyond RN, and no requirement that the bad sample point have positive
probability. Those conditions must not be supplied implicitly in the reading.

## SAP.P017.T10

This conjunction has THREE separately quantified parts.

First: for EVERY measurable Omega,Xi, probability G, measurable integrable
tau, probability P, and measurable hat:Xi->R, assuming

    max(sup supp(P.map hat)-mu, mu-inf supp(P.map hat)) <= c

in EReal, it concludes: supp(P.map hat) is contained in {x:I_c(x)};
pr{I_c(hat)}=1; the sets {hat=C_c(hat)} and {I_c(hat)} are equal;
pr{hat=C_c(hat)}=1; AND
(pr{I_c(hat)}=0 implies pr{hat=C_c(hat)}=0).
In particular, this last implication is STILL under the support-bound
hypothesis, under which its antecedent contradicts the preceding probability
one conclusion. The event equality is also only asserted under that hypothesis.

Second: for EVERY measurable Omega, probability G, measurable integrable
tau with S=R, c=infinity and for EVERY real x, C_c(x)=x.

Third: for EVERY measurable Omega,Xi, probability G, measurable integrable
tau with S=[0,infinity), probability P, measurable hat, and
pr{hat<0}>0, it concludes c=ofReal(mu); the support-bound inequality in the
first part fails; pr{hat=C_c(hat)}<=1-pr{hat<0}<1.
There is no positive-radius hypothesis in any of these three parts.

## SAP.P017.T11

For EVERY n>=1 and then EVERY real c>0,sigma>0,

    T(n,c,sigma)
      = c*sigma*sqrt(2/pi)*exp(-c^2*n/(2*sigma^2))/sqrt(n)
        + 2*sigma^2*Phi(-c*sqrt(n)/sigma)/n.

Separately, for EVERY real c>0,sigma>0, n*T(n,c,sigma)->0 AND
for EVERY real k>0, n^k*T(n,c,sigma)->0. The limits are n->infinity over N.
No truncated-random-variable expectation or alternative density/CDF
standardization formula is explicitly included.

## SAP.P017.T12

There are FOUR top-level conjuncts.

First, for EVERY sequence p:N->R such that for EVERY n>=1,
0<p_n<=1, and p_n->0, the slow construction satisfies:

* tau measurable integrable, mu=0,S=[-1,1],c=1; RN(P,H,0), where
  P=slowPopulation^N and H=rareEstimator p.
* For EVERY n>=1, U_n has uniform [0,1) law, pr{F_n=1}=p_n,
  F_n and M_n are independent, and q_n*M_n has law N(0,1).
* For EVERY such n and EVERY sample, q_n*H_n=q_n*M_n+e_n.
  For EVERY delta>0, pr{|e_n|>delta}<=4/n+p_n.
* For EVERY such n, the THREE sets {H_n not in S}, {|H_n|>1}, and
  {H_n!=C_1(H_n)} all equal {F_n=1}. The last event has probability
  p_n, and pr{H_n in S}=1-p_n.
* For EVERY such n and EVERY sample, F_n=0 implies H_n=B_n and
  H_n-C_1(H_n)=0; F_n=1 implies 19/2<=H_n<=21/2,
  C_1(H_n)=1, and H_n-C_1(H_n)=B_n+9.
* For EVERY n>=1,
  (289/4)*p_n<=E(H_n-C_1(H_n))^2<=(361/4)*p_n.
* For EVERY n>=4, E e_n^2>=100*(n-4)*p_n; here n-4 is REAL
  subtraction after casting n, not truncated natural subtraction.
* LittleOp(P,e,1) AND LittleOp(P,q_n*(H_n-C_1(H_n)),1).

Second, for the particular p* above, it asserts ALL of the following:

* 0<p*_n<=1 for EVERY n>=1, p*_n->0, RN(P,rareEstimator p*,0),
  and the same measurability, integrability, mu,S,c facts about tau.
* For EVERY n>=1, pr{H_n!=C_1(H_n)}=p*_n;
  p*_1000=1/10, p*_(10^12)=1/40, and for EVERY k:N,
  p*_(2^k)=1/(k+1).
* For EVERY real alpha>0, (2^k)^alpha*p*_(2^k)->+infinity as
  k->infinity. For EVERY real alpha>0 there do NOT exist C>0 with
  eventually p*_n<=C/n^alpha.
* NOT SR(P,rareRemainder p*).
* For EVERY sequence r:N->R with r_n>0 for EVERY n>=1 and r_n->0,
  there EXISTS p with 0<p_n<=1 for EVERY n>=1 and p_n->0,
  RN(P,rareEstimator p,0), the exact error probability p_n for EVERY
  n>=1, and p_n/r_n->+infinity. There is no required formula for this p.

Third, for EVERY p (with no positivity or limit hypothesis), EVERY n>=1,
and EVERY sample: -1/2<=B_n<=1/2; if F_n=1 then
17/2<=H_n-C_1(H_n)<=19/2; and if |M_n|<=1/2 and F_n=0,
then e_n=0.

Fourth, there does NOT exist C>0 such that eventually
p*_n<=C*(2*Phi(-sqrt(n))).

## SAP.P017.T13

This is a conjunction of THREE separately quantified parts.

First: for EVERY measurable Omega,Xi, probability G, measurable integrable
tau with c>0, probability P, sequence hat with EVERY hat_n measurable,
and RN(P,hat,mu), the events {I_c(hat_n)} and {hat_n=C_c(hat_n)}
are equal for EVERY n, and pr{I_c(hat_n)}->1.

Second: for EVERY p with 0<p_n<=1 for EVERY n>=1 and p_n->0, the slow
construction has measurable integrable tau, mu=0,S=[-1,1],c=1,
RN(P,rareEstimator p,0); and for EVERY n>=1,
pr{|H_n|>1}=p_n and pr{H_n!=C_1(H_n)}=p_n.

Third: for EVERY measurable Xi, probability P, measurable functions
tilde,u:Xi->R, real mu,c,sigma with c>0,sigma>0, and n>=1, IF
tilde has law N(mu,sigma^2/n), THEN

    pr{|tilde+u-mu|>c}
       <= 2*Phi(-c*sqrt(n)/(2*sigma)) + pr{|u|>c/2}.

There is no independence hypothesis and no moment hypothesis on u.

## SAP.P017.T14

For EVERY measurable Omega,Xi, probability G, measurable integrable tau
with c>0, probability P, and sequence hat satisfying RN(P,hat,mu),
LittleOp(P,q_n*(hat_n-C_c(hat_n)),1). Explicitly, for EVERY eta>0,
pr{sqrt(n)*|hat_n-C_c(hat_n)|>eta}->0. No additional measurability of
hat, finite-radius hypothesis, or IID sampling hypothesis is imposed.

## SAP.P017.T15

For EVERY measurable Omega,Xi, probability G, measurable integrable tau
with c>0, probability P, sequences hat,Z,e with EVERY hat_n measurable,
variance v>=0 with v>0, NR(P,hat,Z,e,mu,v), and SR(P,e),
SM(P,hat_n-C_c(hat_n)), i.e. n*E(hat_n-C_c(hat_n))^2->0.
The order is G,tau and positive radius; P,hat,Z,e and measurability;
v and positivity; the decomposition; then the remainder limit. Independence,
finite c, and an additional RN hypothesis are not required.

## SAP.P017.T16

For EVERY measurable Omega,Xi, probability G, measurable integrable tau,
probability P, and sequence hat satisfying RN(P,hat,mu), BOTH
BIP(P,q_n*(C_c(hat_n)-mu)) AND, for EVERY n and EVERY point,
|C_c(hat_n)-mu|<=|hat_n-mu|. In expanded BIP quantifiers: for EVERY
epsilon>0 there EXISTS M>0 such that EVENTUALLY in n,
pr{|sqrt(n)*(C_c(hat_n)-mu)|>M}<epsilon. No positivity or finiteness
assumption on c is made, so zero and infinite radius are included.

## Mathlib endpoints inspected

The semantic endpoints used above were inspected in:
`MeasureTheory/Measure/Support.lean` (support and neighborhood characterization),
`MeasureTheory/Measure/Map.lean` (pushforward and its fallback),
`MeasureTheory/Measure/MeasureSpaceDef.lean` (Measure.real),
`MeasureTheory/Function/L1Space/Integrable.lean` and
`HasFiniteIntegral.lean` (integrability),
`MeasureTheory/Integral/Bochner/Basic.lean` (the total Bochner integral),
`MeasureTheory/Function/ConvergenceInDistribution.lean` (weak convergence and
AE measurability), `Probability/Distributions/Gaussian/Real.lean` (variance
parameter and zero-variance branch), `Probability/ProductMeasure.lean`
(infinitePi), `Data/EReal/Basic.lean` (toENNReal),
`Probability/Independence/Basic.lean` (IndepFun),
`Algebra/Order/Floor/Defs.lean` (fract), and `Data/Nat/Log.lean` (floor log).
For an AE nonmeasurable map Mathlib has a fallback pushforward; every support
map used here is explicitly measurable or concrete measurable, so that branch
does not supply a support conclusion. The negated T9 specifies measurable data
but does not say its law is the IID population law.
