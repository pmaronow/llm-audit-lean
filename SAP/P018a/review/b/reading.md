# Blind mathematical readings

Saved at stage 1, before opening either `claims.json` or `record.json`.
Sources: all five `Defs/Part*.lean`, `Defs.lean`, both `Challenge/Part*.lean`,
and `Challenge.lean`. Each challenge theorem is exactly the proposition named
`TnStatement`; the docstrings are not additional hypotheses or conclusions.

## Dictionary and Mathlib semantics

All vectors are real functions on `{0,...,k-1}`, and matrices are real square
matrices on the same index set. `outer(x,y)=xy^T`, `dot(x,y)=sum_a x_a y_a`,
and `sandwich(P,M)=PMP` (there is no transpose on the last factor).
Vector norms are maximum absolute coordinate norms. The scoped elementwise
matrix norm is the maximum absolute entry norm. Positive semidefinite means
symmetric with nonnegative quadratic form, and positive definite means
symmetric with strictly positive quadratic form on every nonzero vector.
The finite-dimensional reading follows Mathlib's finitely supported-vector
definitions in `LinearAlgebra/Matrix/PosDef.lean:60,162`.

`A^-1` is Mathlib's nonsingular matrix inverse: `det(A)^-1 adj(A)` over the
reals, and the zero matrix if singular (`NonsingularInverse.lean:166-176`).
Scalar division is total, with `1/0=0`; natural numbers are cast to reals
before every subtraction in `D_N=N(N-1)/2`. Real square root is zero on
nonpositive arguments. These conventions also apply on exceptional samples.

For any finite observation type E, unit type V, memberships s_d, and scores
q_d, define

* `B(X)=sum_d X_d X_d^T`, `bhat=B(X)^-1 sum_d X_d Y_d`, and
  `rhat_d=Y_d-X_d^T bhat`.
* `M_s(q)=sum_{d,f:s_d intersect s_f nonempty} q_d q_f^T`;
  this is an ordered double sum including the diagonal.
* `u_i(q)=sum_{d:i in s_d} q_d`, `M_diag(q)=sum_d q_d q_d^T`, and
  `Vhat_s(X,Y)=B(X)^-1 M_s(X_d rhat_d) B(X)^-1`.

Dyads `Dyd_N` are exactly all two-element subsets of `{0,...,N-1}`;
`firstUnit` is their minimum and `secondUnit` their maximum. `overlap(d,f)`
means nonempty intersection and includes d=f; `neighbors(d)` excludes d.
For N<2 the dyad type is empty. Otherwise its size is D_N.

A kernel K consists of a measure mu on a measurable space U and functions
X:U x U -> R^k, Y:U x U -> R. Its sample law P_N is the finite product
mu^N (`MeasureTheory/Constructions/Pi.lean:210`); samples are N unit draws,
not D_N independently drawn dyads. Write

`Q=E_mu^2[XX^T]`, `beta=Q^-1 E_mu^2[XY]`,
`e(u,v)=Y(u,v)-X(u,v)^T beta`, `q(u,v)=X(u,v)e(u,v)`,
`X_d=X(U_min(d),U_max(d))`, `Y_d=Y(U_min(d),U_max(d))`,
`e_d=e(U_min(d),U_max(d))`, `S_N=sum_d X_d e_d`,
`H=E_mu^2[qq^T]`, `h(u)=E_v q(u,v)`, `Gamma=E_u[h(u)h(u)^T]`,
`V_N=(N/D_N^2)Q^-1 Cov_P_N(S_N)Q^-1`, and
`V_star=4 Q^-1 Gamma Q^-1`.
Expectations of vectors/matrices are coordinatewise Bochner integrals.
`Cov(f,g)_{ab}=integral (f_a-E f_a)(g_b-E g_b)` and `varMat(f)=Cov(f,f)`
(`Probability/Moments/Covariance.lean:44`). Scalar `variance` is the
extended nonnegative second centered moment followed by `toReal`
(`Variance.lean:58-64`), which returns zero at infinity. Bochner integrals
return zero when nonintegrable (`Integral/Bochner/Basic.lean:158,204`).
These are the literal definitions; uses below need finite moments to have
their ordinary probabilistic meanings.

`Standing(K)` means, jointly: mu is a probability measure; X and Y are
measurable on U x U; for every u,v they are symmetric under swapping u,v;
there exists one C>=0 with ||X||<=C and |Y|<=C mu^2-almost everywhere;
there exists a coordinate j<k that equals 1 for every u,v; and det Q !=0.
In particular k>=1. `SampleRank(K)` means there exists N0 such that for
every N>=N0, det B(X) !=0 P_N-almost surely.
`Proposition1Extra(K)` means: one C>=0 bounds all fitted residuals in
absolute value, for every N, almost surely simultaneously over its dyads;
every Q_ab is nonzero; every entry of E[X(U0,U1)X(U0,U2)^T] is nonzero;
and eventually for every N all E[rhat_d^2] are nonzero and all
E[rhat_d rhat_f] for f in neighbors(d) are nonzero.

Let G_X be the sigma algebra pulled back from the entire design map.
`m_d=E[e_d|G_X]`, `c_df=E[(e_d-m_d)(e_f-m_f)|G_X]`,
`C_df=E[c_df X_d X_f^T]`,
`Sigma_print=sum_{d,f overlap} C_df`, and
`Sigma_corr=E[M_members(X_d e_d)]`.
These conditional expectations use Mathlib `condExp`: zero if the proposed
sigma algebra is not a subalgebra, the trimmed measure is not sigma finite,
or the integrand is nonintegrable (`ConditionalExpectation/Basic.lean:94ff`).

`f_N ->p 0` abbreviates exactly: for every real epsilon>0,
`(P_N{epsilon<=||f_N||}).toReal -> 0` as N tends to infinity. The definition
itself does not demand measurability or probability measures.
`f_N => nu` means every f_N is almost everywhere measurable, nu is a
probability measure, and for every bounded continuous real g,
`E_P_N[g(f_N)] -> integral g dnu`. `Normal(V)` means a probability law nu
with V positive semidefinite whose pushforward by every linear form c^T x
is `gaussianReal(0,(c^T V c).toNNReal)`. Mathlib's Gaussian parameter is
variance, and zero variance gives a Dirac measure (`Gaussian/Real.lean:222`).
`HasLaw` and `IdentDistrib` include almost everywhere measurability and
equality of pushforward measures (`HasLaw.lean:39`, `IdentDistrib.lean:71`).
`IndepFun` and `iIndepFun` are independence of the pulled-back sigma algebras
(`Independence/Basic.lean:136,144`). `MemLp f 2` requires almost everywhere
strong measurability and finite second absolute moment
(`Function/LpSeminorm/Defs.lean:152`).

Weighted single-record notation, with fixed real weights w_d:
`B_w=sum w_d X_d X_d^T`, `bhat_w=B_w^-1 sum w_d X_d Y_d`,
`Q_w=D_N^-1 E B_w`, `beta_w=(E B_w)^-1 E sum w_d X_d Y_d`,
`S_w=sum w_d X_d(Y_d-X_d^T beta_w)`,
`Vhat_w=B_w^-1 M_members(w_d X_d(Y_d-X_d^T bhat_w)) B_w^-1`,
`V_w=(N/D_N^2) Q_w^-1 Cov(S_w) Q_w^-1`.

A repeated kernel R has a unit measure mu, natural counts T_Nd, and
measurable-space functions X_Ndt(u,v),Y_Ndt(u,v); its law is again mu^N.
Write `L_N=sum_d T_Nd`, `B_R=sum_dt X_dt X_dt^T`,
`H_R=L_N^-1 E B_R`, `beta_R=(E B_R)^-1 E sum_dt X_dt Y_dt`,
`bhat_R=B_R^-1 sum_dt X_dt Y_dt`,
`q_d(b)=sum_t X_dt(Y_dt-X_dt^T b)`,
`Vhat_R=B_R^-1 M_members(q_d(bhat_R)) B_R^-1`,
`V_R=(N/L_N^2) H_R^-1 Cov(sum_d q_d(beta_R)) H_R^-1`.
All record functions use the lower endpoint as first argument.
`RepeatedStanding(R)` requires a probability measure, T_Nd>0 for every
N>=2 and d, measurable X_Ndt,Y_Ndt for every N,d,t, one nonnegative
almost everywhere uniform bound over all N,d,t, and one intercept coordinate
equal to 1 everywhere. It does not assert symmetry or rank.
`RepeatedAtSize(R,N)` requires probability, positive counts, measurability,
and one common almost everywhere bound only at this N, with no intercept.

For record weights w_dt, add w_dt to every Gram and XY summand and every
block score summand. The weighted population coefficient uses expected
weighted Gram and XY; the weighted sample coefficient uses the sample ones.
Write these as B_Rw, beta_Rw, bhat_Rw, q_dw(b). Their normalization is
`H_Rw=D_N^-1 E B_Rw`, covariance estimator
`Vhat_Rw=B_Rw^-1 M_members(q_dw(bhat_Rw)) B_Rw^-1`, and target
`V_Rw=(N/D_N^2)H_Rw^-1 Cov(sum_d q_dw(beta_Rw))H_Rw^-1`.

## SAP.P018a.T1

No external hypotheses. Fix U uniform on [-1,1], defined by normalizing
Lebesgue measure on that interval, and X(z,t)=(1,2+z+t), Y(z,t)=(z+t)^2.
The following are all asserted:

* Standing holds; for every N>=3 the sample Gram is nonsingular almost surely.
* Q=[[1,2],[2,14/3]], det Q=2/3, beta=(2/3,0),
  H=[[28/45,56/45],[56/45,3448/945]],
  Gamma=[[4/45,8/45],[8/45,632/945]], and Gamma is positive definite.
* For every N>=3, every d,f has c_df=0 almost surely, Sigma_print=0,
  Cov(S_N)=D_N H+N(N-1)(N-2)Gamma !=0.
  At N=3 this covariance is [[12/5,24/5],[24/5,4712/315]].
* V_N tends to V_*=[[3664/315,-592/105],[-592/105,296/105]], which is
  positive definite. There exists one Normal(V_*) law nu such that
  sqrt(N)(bhat-beta) => nu. Also N Vhat-V_* ->p 0.
* For every real z,t in [-1,1], 0<=2+z+t<=4, 0<=(z+t)^2<=4, and
  -2/3<=(z+t)^2-2/3<=10/3.
* E[XY]=(2/3,4/3), det Gamma=1184/42525, det V_*=4736/4725.

## SAP.P018a.T2

For every measurable space U, natural dimension k, and kernel K,
Standing(K) implies all of the following. E[q]=0. For every N>=2,
E[X_d e_d]=0 for every d; E[X_d e_d e_f X_f^T]=0 for every disjoint d,f;
Cov(S_N)=Sigma_corr. Define, separately at each such N,
`M=Cov(sum_d X_d m_d)`. Then

* Cov(S_N)=sum_all d,f C_df+M; M is positive semidefinite;
  Cov(S_N)=sum_all C_df if and only if M=0.
* Cov(S_N)-Sigma_print=M+sum_disjoint d,f C_df.
* Sigma_corr=D_N H+N(N-1)(N-2)Gamma.

Gamma is positive semidefinite and V_N tends to V_star. Additionally, for
every N>=2, Sigma_corr equals the overlap sum of
E[E[e_d e_f|G_X]X_d X_f^T]; and if every m_d=0 almost surely, then
Cov(sum_d X_d m_d)=0. There is no conditional-mean-zero assumption in
Standing or in the main covariance conclusion.

## SAP.P018a.T3

An unconditional conjunction of five example packages:

1. On independent fair Boolean signs, X=1 and Y(b,c)=sign(b)+sign(c),
   where true maps to 1 and false to -1. Standing, SampleRank,
   Proposition1Extra and beta=0 hold. For every N>=4, V_N=[[4]],
   E[meat(fitted scores)]=[[(N-1)(N-2)(N-3)]], and
   E[Vhat_00]=4(N-2)(N-3)/(N^2(N-1)). E[Vhat_00]-4 tends to -4,
   while N Vhat-[[4]] ->p 0.
2. For every N, under the Dirac law on Unit, E[1-1]=0 and Var(N*1)=0;
   nevertheless N*1-1 does not tend to 0, either deterministically or in
   the above inProbability sense.
3. Let nu_N=N^-1 delta_N+(1-N^-1)delta_1, with nonnegative coefficients
   supplied by ENNReal.ofReal (at N=0 the literal definition is delta_1).
   Each nu_N for N>=1 is a probability; x-1 ->p 0 under nu_N;
   E_nu_N x=2-N^-1 and Var_nu_N(x)=N-3+3/N-1/N^2 for every N>=1.
   The means tend to 2, and the variances tend to +infinity.
4. For eight independent fair signs define r_ij=u_i+u_j-(sum_l u_l)/4.
   The finite uniform average over all 2^8 sign vectors is used, with
   Cov_F(f,g)=average(fg)-average(f)average(g). Then
   Cov_F(r_01 r_02,r_34 r_35)=7/16,
   Cov_F((u0+u1)(u0+u2),(u3+u4)(u3+u5))=0, and
   Cov_F(r_01 r_02,r_03 r_04)=-1/16.
5. With density t^-2 on t>=1 relative to Lebesgue measure, take
   X(u,v)=(1,exp(-u)+exp(-v)), Y=0. Standing holds and
   (D_N^-1 B)^-1-Q^-1 ->p 0. There exists N0>=3 such that for every
   N>=N0, B is nonsingular almost surely, and for every integer m>=1,
   exp(2m)/(4m^N) is at most the extended integral of
   ||(D_N^-1 B)^-1||_op; that integral equals infinity.
   Here ||A||_op is literally sup{sqrt(sum_a (Ax)_a^2):sum_a x_a^2<=1},
   a bounded, nonempty set for each finite real matrix.

## SAP.P018a.T4

Conjunction of three universally quantified results, with separate binders:

1. Every measurable U, natural k, kernel K with Standing(K) satisfies
   N Vhat-V_N ->p 0. Neither SampleRank nor Proposition1Extra is assumed.
2. Every probability space (Omega,mu), real Z in L2(mu), every V in R and
   every c>0 satisfy
   mu{|Z-V|>c} <= c^-2(Var(Z)+(E Z-V)^2).
3. For every sequence of measurable spaces Omega_N and probability laws
   mu_N, every real array Z_N in L2(mu_N) for all N, and every fixed real
   V, if E Z_N-V ->0 and Var(Z_N)->0, then for every real c>0,
   mu_N{|Z_N-V|>c}->0.

## SAP.P018a.T5

Define Z1=[[1,0,0],[1,0,0],[0,1,0]],
Z2=[[0,1,0],[0,0,1],[0,0,1]],
C(tau,sigma)=tau(Z1+Z2)(Z1+Z2)^T+sigma I and
W(t1,t2,sigma)=t1 Z1 Z1^T+t2 Z2 Z2^T+sigma I.
For every real t1,t2,sigma,
C(1,1)=[[3,1,1],[1,3,1],[1,1,3]],
W=[[t1+t2+sigma,t1,0],[t1,t1+t2+sigma,t2],[0,t2,t1+t2+sigma]],
and C(1,1)!=W(t1,t2,sigma).

For F=[[1,1],[1,3],[1,2]],
Winv=(1/21)[[8,-3,1],[-3,9,-3],[1,-3,8]],
R=(1/16)[[71,-27],[-27,15]],
L=[[19/16,-13/16,5/8],[-7/16,9/16,-1/8]], the identities
Winv W(1,1,1)=I, R(F^T Winv F)=I, R F^T Winv=L, LF=I,
L C(1,1)L^T=(1/64)[[379,-135],[-135,67]] hold. The ratio of R_00
to the latter matrix's 00 entry is 284/379<1.

Finally, for every probability space, every natural N>=1, every family
a_i of independent N(0,1) real random variables, every natural D,
every yc:Omega->R^D and estimate:R^D->R, assume
estimate(y+c 1)=estimate(y)+c for all y,c, independence of yc and
abar=sum_i a_i/N, measurability of estimate, and finite second moments
both of estimate(yc) and estimate(yc+2 abar 1). Then
Var(estimate(yc+2 abar 1))=Var(estimate(yc))+4/N>=4/N.
Neither a distributional specification of yc nor derivation of its
independence is included.

## SAP.P018a.T6

For every N>=2, let Z1_di=1{min(d)=i} and Z2_di=1{max(d)=i}.
For every d,f the entries of Z1 Z1^T, Z2 Z2^T, Z1 Z2^T, Z2 Z1^T
are respectively the equality indicators for their lower/lower,
upper/upper, lower/upper, upper/lower endpoints; the entry of
(Z1+Z2)(Z1+Z2)^T is |d intersect f|.
For every real tau,sigma the latter shared covariance expands to
tau(Z1Z1^T+Z2Z2^T+Z1Z2^T+Z2Z1^T)+sigma I. If also N>=3,
then for every tau>0, every sigma, and every t1,t2,s in R, it differs
from t1 Z1 Z1^T+t2 Z2 Z2^T+s I.

Separately, for every probability space, natural m,N, deterministic real
m by N matrix Z, random vectors a in R^N and nu in R^m whose coordinates
are in L2, assume independence of a and nu. For every tau,sigma with
Cov(a)=tau I and Cov(nu)=sigma I,
Cov(Za+nu)=tau ZZ^T+sigma I.

Separately, for every natural m,k, real symmetric m by m matrix C and
m by k matrix F with det C and det(F^T C^-1 F) units (equivalently
nonzero reals), set G=F^T C^-1 F and L=G^-1 F^T C^-1.
Then LF=I and L C L^T=G^-1. Positivity of C is not a hypothesis.

## SAP.P018a.T7

No external hypotheses. Let each unit be a pair of independent fair signs
(Z,W), X_ij=(1,1+Z_i Z_j), Y_ij=W_i+W_j. Standing and
Proposition1Extra hold, Q=[[1,1],[1,2]], beta=0,
Gamma=[[1,1],[1,1]], V_star=[[4,0],[0,0]]. For every N>=3,
V_N=[[4N/(N-1),-4/(N-1)],[-4/(N-1),4/(N-1)]].
P_N{Vhat_11<0}->1-exp(-1/2), and N Vhat-V_star ->p 0.

In the separately specified eight-unit deterministic sample, all 28
unordered pairs are listed lexicographically; unit signs are
Z=(1,1,-1,-1,1,1,-1,-1), W=(1,-1,1,-1,1,-1,1,-1).
Then B=[[28,24],[24,48]], det B=768, bhat=0,
Vhat=[[3/8,-1/48],[-1/48,-13/288]], with negative 11 entry.
There is no SampleRank assertion, second-order weak limit, or assertion
about any studentized slope in this proposition.

## SAP.P018a.T8

For every measurable U, natural k, and K satisfying Standing:
there exists one Normal(V_star) law nu with sqrt(N)(bhat-beta)=>nu;
V_N->V_star; N Vhat-V_star ->p 0.
For every c in R^k with c^T V_star c>0:

* If eventually for every N, c^T Vhat c>0 almost surely, then
  (c^T(bhat-beta))/sqrt(c^T Vhat c) => N(0,1).
* Without that additional assumption,
  P_N{c^T Vhat c<=0}->0.

Also, for every such c and then every real alpha with 0<alpha<1,
P_N{c^T Vhat c>=0 and |c^T(bhat-beta)|<=z_(1-alpha/2)
sqrt(c^T Vhat c)} ->1-alpha.
Here z_p=inf{z in R:p<=P(N(0,1)<=z)} using the real infimum;
the invoked p lies strictly between 1/2 and 1. The pivot's weakLimit
requires measurability for every N, including exceptional early N, and
its literal expression still uses total real square root and division.

## SAP.P018a.T9

No external hypotheses. For the scalar sign kernel of T3, assign
w_{ij}=2^(-(i+j+2)) for zero-based i<j. For every N>=2, all weights
are positive and <=1/8, and Var(bhat_w)>=9/16. This variance tends to
36/35. For every N>=8,
P_N{|N Vhat_w-N Var(bhat_w)|>=N/2}>=1/256.
There does not exist a deterministic real sequence V_N such that
N Var(bhat_w)-V_N->0 and N Vhat_w-V_N ->p 0 simultaneously.

For every N>=2 the joint law of (bhat_w,Vhat_w) equals that of
(bhat_R,Vhat_R) for the repeated scalar sign model with
T_N,{i,j}=2^(i+j+2), X_dt=1, Y_dt=sign_i+sign_j. This asserts equality
in distribution, not pointwise equality on the same labeled unit sample.

## SAP.P018a.T10

Conjunction of the following four results:

1. For every measurable U, natural k and repeated kernel R, assume
   RepeatedStanding, the existence of common functions fX_t(u,v),
   fY_t(u,v) such that for every N,d,t,u,v the record kernels equal
   fX_(t.val),fY_(t.val), and a natural T0 bounding all T_Nd.
   For every positive definite H, assume H_R,N->H and
   (N/L_N^2) M_members(E[q_d(beta_R,N)])->0.
   Then N Vhat_R-V_R ->p 0.
2. For every K with Standing, every deterministic array w_Nd and real
   scale sequence a_N>0, assume one real C with
   0<w_Nd/a_N<=C for all N,d. For every positive definite H, assume
   Q_(w/a),N->H. Then N Vhat_w-V_w ->p 0. There is no overlap-mean
   hypothesis in this second assertion.
3. For every measurable U, natural k,N, arbitrary repeated kernel R,
   arbitrary real record weights w_dt, real scale a>0, N>=2, and then
   every sample omega with det B_Rw(omega)!=0 and det H_Rw!=0,
   bhat_R,aw(omega)=bhat_Rw(omega),
   Vhat_R,aw(omega)=Vhat_Rw(omega), and V_R,aw=V_Rw.
   RepeatedStanding is not assumed in this algebraic assertion.
4. The weights in T9 are positive and <=1/8 for every N>=2 and d;
   the scalar sign kernel satisfies Standing and SampleRank; and
   there is no deterministic V_N making both the scaled estimator
   variance and the scaled weighted sandwich converge to it as in T9.

## SAP.P018a.T11

For the scalar sign kernel, every N>=3 has N Var(bhat)=4;
4/D_N->0; N Vhat_00-4 ->p 0. For every N>=3,
N(2N-2)/D_N^2=4/D_N,
N[N(N-1)^2]/D_N^2=4,
and N(2N-2)/D_N^2 !=4.
No formula identifies 4/D_N with conditional covariance or a printed
target beyond these scalar expressions.

## SAP.P018a.T12

Conjunction of four results, each with fresh universal binders:

1. For every measurable U, natural k,N and repeated R with
   RepeatedAtSize(R,N), N>=2, L_N>0 and det H_R!=0, set
   S=sum_d q_d(beta_R). Then E S=0, E[L_N^-1 B_R]=H_R,
   V_R=Cov(H_R^-1 ((sqrt(N)/L_N)S)), and almost surely, if
   det B_R(omega)!=0, then
   sqrt(N)(bhat_R-beta_R)=(L_N^-1 B_R)^-1 ((sqrt(N)/L_N)S).
2. For every measurable U, natural k,N and repeated R with
   RepeatedAtSize(R,N), N>=2, every real record-weight array w with
   det H_Rw!=0, set S=sum_d q_dw(beta_Rw). Then E S=0,
   E[D_N^-1 B_Rw]=H_Rw, V_Rw=Cov(H_Rw^-1 ((sqrt(N)/D_N)S)),
   and almost surely, if det B_Rw!=0, then
   sqrt(N)(bhat_Rw-beta_Rw)=(D_N^-1 B_Rw)^-1 ((sqrt(N)/D_N)S).
   Weight positivity is not required.
3. Every K with Standing and every N>=2 satisfies V_singleRecord(K)=V_N
   and V_(w identically 1)=V_N, where singleRecord gives each dyad
   exactly one record with the original K functions.
4. For every R (no probabilistic standing assumptions), N>=2, L_N>0,
   and det E B_R!=0,
   V_R=(N/D_N^2)(D_N^-1 E B_R)^-1
   Cov(sum_d q_d(beta_R))(D_N^-1 E B_R)^-1.

## SAP.P018a.T13

No external hypotheses. Use the six dyads (01,02,03,12,13,23),
X_d=(1,x_d) with x=(0,2,5,5,1,1), Y=(1,1,1,0,0,0),
r=(1/2,1/2,1/2,-1/2,-1/2,-1/2).
For general X,Y,b define p_d=1/(1+exp(-X_d^T b)),
q_d=X_d(Y_d-p_d), A=sum_d p_d(1-p_d)X_dX_d^T,
L(b)=sum_d[Y_d X_d^T b-log(1+exp(X_d^T b))],
P=sum_overlap r_d r_f X_d X_d^T, and
V_log=A^-1 M_members(q) A^-1.

The statement asserts all of the following exact witness facts:

* Every Y_d is binary. For every b in R^2, L(b)<=L(0); for every b,
  L(b)=L(0) implies b=0.
* At b=0, p_d=1/2, Y_d-p_d=r_d, and q_d=X_d r_d for every d.
* sum_d X_d r_d=0. A=(1/4)sum_d X_d X_d^T=
  H_l=[[3/2,7/2],[7/2,14]], det A=det H_l=35/4,
  A^-1=J=[[8/5,-2/5],[-2/5,6/35]], and J H_l=I.
  det(sample Gram)=140.
* P=H_l and M_members(q)=[[3/2,7/2],[7/2,27/2]].
  J H_l J=J, whereas J M_members(q) J=
  C=[[38/25,-64/175],[-64/175,192/1225]].
  Thus the printed sandwich equals J, V_log=C, and they differ;
  both J and C are positive definite.
* M_members(q)=sum_i u_i(q)u_i(q)^T-M_diag(q).
  The printed sandwich minus V_log is
  [[2/25,-6/175],[-6/175,18/1225]].
* For each dyad d, the sum of r_f over its distinct overlapping
  neighbors f is zero.

Several equations are repeated with the explicit H_l,J names; each is
included above. Strict concavity of the entire function L is not asserted.

## SAP.P018a.T14

For every finite V,E with decidable equality, every membership map
s:E->finite subsets of V with exactly two members for each d and
injective as a map, then for every natural k, real arrays X_d in R^k,
Y_d in R, and b in R^k, assume all Y_d are binary and det A(X,b)!=0.
Define r_d=Y_d-expit(X_d^T b), q_d=X_d r_d. Then for every d,f,
q_d q_f^T=r_d r_f X_d X_f^T;
M_s(q)=sum_i u_i(q)u_i(q)^T-M_diag(q);
M_s(q) and A^-1 M_s(q) A^-1 are symmetric; and
the printed middle factor equals
sum_d [r_d sum_{f:s_d intersect s_f nonempty}r_f]X_d X_d^T.
No fitting, score-centering, or maximization assumption on b is imposed.
In a separate unconditional conjunct, the explicit six-dyad witness of
T13 has printed middle factor different from M_s(X_d r_d).
