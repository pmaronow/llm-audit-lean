# Blind reading

This file was written from `SAP/P018a/Defs{,/Part1,/Part2,/Part3,/Part4,/Part5}.lean`, the Challenge files, and the Mathlib definitions they use, before opening either `claims.json` or `record.json`. The audited theorems are the fourteen Challenge stubs `SAP.P018a.T1` through `SAP.P018a.T14`. They have no hypotheses outside their respective `TnStatement` definitions. All limits below are as the natural number N tends to infinity.

## Common objects and exact conventions

`Vec k` is R^k indexed by `Fin k = {0,...,k-1}`; `Mat k` is the real k by k matrices. `dot x y = sum_a x_a y_a`, `outer x y = xy'`, and `score x r = rx`. The vector norm is the finite supremum norm and the matrix norm used for probability convergence is the maximum absolute entry. `sandwich P M` means PMP, without a transpose on its last factor. Positive (semi)definiteness includes symmetry and the usual strictly positive (nonnegative) real quadratic form; Mathlib states it using finitely supported vectors, equivalent here to all vectors.

`Dyad N` consists of all two-element subsets of `Fin N`, with no duplicates. `members d` is that subset; `members_card` proves its size is two. `firstUnit d` and `secondUnit d` are its least and greatest elements. `overlap d f` means their intersection is nonempty, including d=f. `neighbors d` means the other dyads that overlap d. Write D_N = N(N-1)/2 in real arithmetic (`Dreal`); subtraction here is real subtraction. The dyad type is empty for N=0,1.

For finite observations E with unit subsets s_d and vectors q_d, define

* B_s(q) = sum over **ordered** (d,f) with s_d intersect s_f nonempty of q_d q_f'. This is `meat`.
* U_i(q) = sum_{d:i in s_d} q_d (`unitScore`).
* B_0(q) = sum_d q_d q_d' (`dyadMeat`).
* G(X)=sum_d X_d X_d' (`sampleGram`), b_hat=G(X)^{-1} sum_d X_d Y_d (`sampleOLS`), r_hat_d=Y_d-X_d'b_hat (`fittedResidual`), and V_hat=G^{-1}B_s(X r_hat)G^{-1} (`sampleVariance`).

**Totalization matters to the literal reading.** Mathlib's matrix inverse is the ordinary inverse when its determinant is nonzero and the zero matrix otherwise (`LinearAlgebra/Matrix/NonsingularInverse.lean:169`). Thus the estimator and sandwich above are defined even on singular samples. Real scalar division also has 1/0=0. A Bochner integral is zero if its integrand is not integrable (`MeasureTheory/Integral/Bochner/Basic.lean:158`). Expectations of vectors and matrices here are coordinatewise real Bochner integrals (`meanVec`, `meanMat`). `covMat(f,g)_{ab}` is E[(f_a-E f_a)(g_b-E g_b)] and `varMat(f)=covMat(f,f)`. The separately used scalar `ProbabilityTheory.variance Z` is the extended integral E[|Z-EZ|^2] followed by `ENNReal.toReal`, which gives zero at infinity. `MemLp Z 2` requires almost-everywhere strong measurability and finite second moment. Where ordinary covariance or variance is written below, it is this literal definition; integrability is not an implicit extra hypothesis.

`inProbability mu f` says: **for every real epsilon>0**, the real-valued measure mu_N{omega: epsilon <= ||f_N(omega)||} tends to zero. It does not itself require measurable f or probability source measures. `weakLimit mu f nu` says: every f_N is a.e. measurable; nu is a probability measure; and **for every bounded continuous real function g** on the target, E_mu_N[g(f_N)] tends to E_nu[g]. `centeredNormalLaw nu V` says V is positive semidefinite, nu is a probability measure on R^k, and **for every c in R^k** its pushforward by x -> c'x is the real Gaussian with mean zero and variance max(c'Vc,0). Zero variance is a Dirac mass. The semidefinite condition makes the max harmless. All a.e. qualifiers use the displayed measure, not a pointwise convention.

A `Kernel U k` is an arbitrary measurable-space type U, a measure mu on U, and functions X:U x U -> R^k, Y:U x U -> R. `unitSampleLaw K N` is mu^{otimes N}. For a sample omega, X_d=X(omega_i,omega_j), Y_d=Y(omega_i,omega_j) for i=min d, j=max d. Define

* Q=E_{mu x mu}[XX'] (`populationGram`), beta=Q^{-1}E[XY] (`populationBeta`), e(u,v)=Y(u,v)-X(u,v)'beta (`populationResidual`), and h(u,v)=X(u,v)e(u,v) (`populationScore`). `epsilon K omega d` is e at that pair; S_N=sum_d X_d e_d is `scoreSum`.
* H=E[h(U,V)h(U,V)'] (`scoreH`), g(u)=E_V[h(u,V)] (`projection`), Gamma=E[g(U)g(U)'] (`projectionGamma`).
* V_N=(N/D_N^2) Q^{-1} Var(S_N) Q^{-1} (`trueTarget`); V_star=4Q^{-1}Gamma Q^{-1} (`limitingTarget`). `coefficientError` is b_hat-beta.
* The sigma algebra A_X (`designSigma`) is the pullback sigma algebra of the **whole** design omega -> (X_d)_d. m_d=E[e_d|A_X] (`conditionalResidualMean`), c_df=E[(e_d-m_d)(e_f-m_f)|A_X] (`conditionalResidualCov`), and C_df=E[c_df X_d X_f'] (`conditionalTerm`). `printedSigma` is sum_{d overlaps f} C_df. `correctedSigma` is E[B_members(Xe)]. Conditional expectation is Mathlib's real conditional expectation; it becomes zero if the sigma algebra is not a sub-sigma algebra, the trimmed measure is not sigma-finite, or the integrand is not integrable. Under `Standing` the intended finite-measure/integrability conditions hold.

`Standing K` is exactly the conjunction of: (1) mu is a probability measure; (2) X and Y are jointly measurable on U x U; (3) **for every u,v** both X(u,v)=X(v,u) and Y(u,v)=Y(v,u); (4) **there exists a real C>=0** such that ||X||<=C and |Y|<=C for mu x mu almost every pair; (5) **there exists j in Fin k** such that X(u,v)_j=1 for every u,v; (6) det Q != 0. Thus the intercept condition forces k>0. `SampleRank K` adds: there exists N0 such that **every N>=N0** has det G !=0 almost surely. It is not part of `Standing`.

`Proposition1Extra K` is exactly: (1) there exists C>=0 such that **for every N**, almost every sample has |r_hat_d|<=C **for all dyads d**; (2) **for all coordinates a,b**, Q_ab !=0; (3) for all a,b, the (a,b) entry of E[X(U0,U1)X(U0,U2)'] under three independent unit draws is nonzero; (4) **eventually for all N**, E[r_hat_d^2] !=0 for every d and E[r_hat_d r_hat_f] !=0 for every d and every f in `neighbors d`. It does not assert rank or positivity of the last cross moments.

For deterministic dyad weights w, let G_w=sum_d w_d X_d X_d', b_hat_w=G_w^{-1}sum_d w_d X_dY_d (`weightedGram`, `weightedOLS`), Q_w=D_N^{-1}E G_w, beta_w=(E G_w)^{-1}E sum_d w_d X_dY_d, S_w=sum_d w_d X_d(Y_d-X_d'beta_w). `weightedVariance` is G_w^{-1}B_members(wX(Y-X'b_hat_w))G_w^{-1}; `weightedTarget` is (N/D_N^2)Q_w^{-1}Var(S_w)Q_w^{-1}.

A `RepeatedKernel U k` has measure mu, nonnegative integer record counts T(N,d), and record functions X(N,d,t,u,v), Y(N,d,t,u,v) for t=0,...,T(N,d)-1. Its sample law (`repeatedLaw`) is again mu^{otimes N}; the observed records (`repeatedX`, `repeatedY`) use the least/greatest unit of the dyad. Write L_N=sum_d T(N,d) (`repeatedL`), G_R=sum_{d,t} X_dt X_dt' (`repeatedGram`), H_R=L_N^{-1}E G_R (`repeatedH`), beta_R=(E G_R)^{-1}E sum_{d,t}X_dtY_dt (`repeatedBeta`), b_hat_R=G_R^{-1}sum_{d,t}X_dtY_dt (`repeatedOLS`), and q_d(b)=sum_t X_dt(Y_dt-X_dt'b) (`repeatedBlockScore`). The repeated sandwich is G_R^{-1}B_members(q(b_hat_R))G_R^{-1}; its target is (N/L_N^2)H_R^{-1}Var(sum_d q_d(beta_R))H_R^{-1}.

`RepeatedStanding R` means: mu is probability; for **every N>=2 and every d**, T(N,d)>0; every X(N,d,t,.,.) and Y(N,d,t,.,.) is jointly measurable; one C>=0 bounds both their norm/absolute value almost everywhere, **uniformly in N,d,t**; and there exists one intercept coordinate j with X(N,d,t,u,v)_j=1 for all indices and all u,v. It assumes neither symmetry, rank, bounded record counts, nor a common kernel across dyads. `RepeatedAtSize R N` assumes probability, positive T(N,d) for all d, measurability for all d,t, and one a.e. bound for all d,t **at this N**; it has no intercept or rank assumption.

For deterministic real record weights w_dt, `recordWeightedGram`=sum_{d,t}w_dt X_dtX_dt', `recordWeightedXY`=sum_{d,t}w_dt X_dtY_dt; `recordWeightedOLS` uses their sample ratio; `recordWeightedBeta` uses the ratio of their expectations. `recordWeightedBlockScore` is sum_t w_dt X_dt(Y_dt-X_dt'b). `recordWeightedH`=D_N^{-1}E G_w; `recordWeightedVariance`=G_w^{-1}B_members(q_w(b_hat_w))G_w^{-1}; `recordWeightedTarget`=(N/D_N^2)H_w^{-1}Var(sum_d q_w(beta_w))H_w^{-1}. `singleRecord K` sets all T=1 and uses K's functions.

The logistic definitions are p(x,b)=1/(1+exp(-x'b)) (`expit`), q_d=X_d(Y_d-p_d) (`logisticScore`), A=sum_d p_d(1-p_d)X_dX_d' (`logisticBread`), and A^{-1}B_s(q)A^{-1} (`logisticVariance`). The distinct `printedLogisticMeat` is sum_{d overlaps f} r_dr_f X_dX_d', with **X_d in both factors**. `logLikelihood x y b`=yx'b-log(1+exp(x'b)).

## Named fixed examples

* Nonlinear example: mu is normalized Lebesgue measure on [-1,1] (`uniformUnitLaw`); X(z,t)=(1,2+z+t), Y(z,t)=(z+t)^2 (`nonlinearKernel`). The named matrices are Q0=[[1,2],[2,14/3]], H0=[[28/45,56/45],[56/45,3448/945]], Gamma0=[[4/45,8/45],[8/45,632/945]], and V0=[[3664/315,-592/105],[-592/105,296/105]].
* Sign example: `fairLaw` is uniform probability on Bool; `signValue` is +1 on true, -1 on false. `signKernel` has X=1 and Y(u,v)=s(u)+s(v). `fairAverage N f` is the average of f over all 2^N real sign vectors, recursively using equal weights for +1 and -1. `signResidual4(u,d)`=sum_{i in sixMembers d}u_i-(sum_i u_i)/2. `signResidual8(u,i,j)`=u_i+u_j-(sum_l u_l)/4 and `fairCov8(f,g)`=fairAverage_8(fg)-fairAverage_8(f)fairAverage_8(g).
* `concentratedWeight {i,j}`=2^{-(i+j+2)}. `concentratedRepeated` has T(N,{i,j})=2^{i+j+2}, with every record X=1, Y=s_i+s_j.
* `inverseSpikeLaw N` has mass ofReal(1/N) at N and mass ofReal(1-1/N) at 1, so it is the intended probability mixture for N>=1 (and a Dirac at 1 for N=0). `paretoUnitLaw` has Lebesgue density 1_{t>=1}/t^2; `inverseKernel` has this unit law, X(u,v)=(1,exp(-u)+exp(-v)), Y=0. `euclideanSq x`=sum_a x_a^2. `matrixOperatorNorm M` is the supremum of sqrt(sum_a (Mx)_a^2) over sum_a x_a^2<=1; the set is nonempty and bounded for every finite real matrix.
* `signPairKernel` has independent fair signs (z,w) per unit, X=(1,1+z_iz_j), Y=w_i+w_j. `eightMembers` lists all 28 dyads in lexicographic order on eight units. For its deterministic example, z=(1,1,-1,-1,1,1,-1,-1), w=(1,-1,1,-1,1,-1,1,-1), `degeneracyX`=(1,1+product_{i in d}z_i), `degeneracyY`=sum_{i in d}w_i.
* `sixMembers` lists (01,02,03,12,13,23). For logistic data, X_d=(1,x_d) with x=(0,2,5,5,1,1), Y=(1,1,1,0,0,0), r=(1/2,1/2,1/2,-1/2,-1/2,-1/2). `logitH`=[[3/2,7/2],[7/2,14]] and `logitHinv`=[[8/5,-2/5],[-2/5,6/35]].
* `endpointZ1 N` and `endpointZ2 N` are the 0/1 incidence matrices for the least/greatest unit in each dyad. `sharedCov N tau sigma`=tau(Z1+Z2)(Z1+Z2)'+sigma I. `twoRoleCov N t1 t2 sigma`=t1 Z1Z1'+t2 Z2Z2'+sigma I. The fixed versions use Z1=[[1,0,0],[1,0,0],[0,1,0]], Z2=[[0,1,0],[0,0,1],[0,0,1]], the dyads 01,02,12. `glsF`=[[1,1],[1,3],[1,2]], `glsWinv`=(1/21)[[8,-3,1],[-3,9,-3],[1,-3,8]], `glsR`=(1/16)[[71,-27],[-27,15]], `glsL`=[[19/16,-13/16,5/8],[-7/16,9/16,-1/8]].
* `normalQuantile p`=inf{z real : p <= P(G<=z)}, G standard normal. Its uses in T8 have 1/2<p<1, where this is the ordinary quantile. `HasLaw` includes a.e. measurability and equality of pushforward measures; `IdentDistrib` includes a.e. measurability of both maps and equality of their pushforwards. `IndepFun` and `iIndepFun` mean independence of the pulled-back sigma algebras, not an unmentioned Gaussian representation.

## T1 — `SAP.P018a.T1`

This is an unconditional conjunction about the nonlinear example:

1. It satisfies `Standing`; **for every N>=3**, its sample Gram is nonsingular almost surely. Its population Q=Q0, det Q0=2/3, beta=(2/3,0), H=H0 and Gamma=Gamma0, and Gamma0 is positive definite.
2. **For every N>=3**, for all dyads d,f, c_df=0 almost surely; printedSigma=0; Var(S_N)=D_N H0+N(N-1)(N-2)Gamma0, and this variance matrix is nonzero. At N=3 it is [[12/5,24/5],[24/5,4712/315]].
3. V_N tends to V0; V0 is positive definite. **There exists a probability law nu on R^2** with centered normal law of covariance V0 such that sqrt(N)(b_hat-beta) converges weakly to nu. N V_hat-V0 tends to zero in probability.
4. **For every real z,t**, if both belong to [-1,1], then 0<=2+z+t<=4, 0<=(z+t)^2<=4, and -2/3<=(z+t)^2-2/3<=10/3. E[XY]=(2/3,4/3). det Gamma0=1184/42525 and det V0=4736/4725.

## T2 — `SAP.P018a.T2`

**For every measurable-space type U, every natural k, and every Kernel K**, assume `Standing K`. Then all the following hold:

1. E[h(U,V)]=0. **For every N>=2**, every dyad score is centered; for **every ordered pair of disjoint dyads** E[(X_de_d)(X_fe_f)']=0; and Var(S_N)=correctedSigma.
2. At each such N define M=Var(sum_d X_d m_d). Then Var(S_N)=sum_{all d,f} C_df+M; M is positive semidefinite; Var(S_N)=sum_{all d,f}C_df **if and only if** M=0; and Var(S_N)-printedSigma=M+sum_{disjoint d,f}C_df.
3. For every such N, correctedSigma=D_N H+N(N-1)(N-2)Gamma. Gamma is positive semidefinite and V_N tends to V_star.
4. **For every N>=2**, correctedSigma also equals sum_{overlapping d,f} E[E[e_de_f|A_X] X_dX_f']. If **every d** has m_d=0 a.s. at this N, then Var(sum_d X_dm_d)=0.

The theorem does not separately identify sum X_dm_d as E[S_N|A_X], nor the first double sum as E[Var(S_N|A_X)].

## T3 — `SAP.P018a.T3`

This is an unconditional conjunction of five examples:

1. The sign kernel satisfies `Standing`, `SampleRank`, and `Proposition1Extra`, and beta=0. **For every N>=4**, V_N=[[4]], E[B(X r_hat)]=[[(N-1)(N-2)(N-3)]], and E[(V_hat)00]=4(N-2)(N-3)/(N^2(N-1)). E[(V_hat)00]-4 tends to -4, while N V_hat-[[4]] tends to zero in probability.
2. **For every natural N**, on the one-point Dirac probability space E[1-1]=0 and Var(N*1)=0. Nevertheless N*1-1 does not tend to zero, either deterministically or in the defined probability sense.
3. **For every N>=1**, inverseSpikeLaw is probability, its mean is 2-1/N, and its variance is N-3+3/N-1/N^2. Under these laws x-1 tends to zero in probability, the mean tends to 2, and the variance tends to positive infinity.
4. Under eight independent fair signs, Cov(r01 r02,r34 r35)=7/16 for r_ij=u_i+u_j-sum(u)/4; Cov((u0+u1)(u0+u2),(u3+u4)(u3+u5))=0; and Cov(r01 r02,r03 r04)=-1/16. These are direct finite expectations, without a separate assertion that the r's are OLS residuals.
5. The inverse kernel satisfies `Standing`; (G/D_N)^{-1}-Q^{-1} tends to zero in probability. **There exists N0>=3 such that for every N>=N0**, sample G is nonsingular almost surely; **for every natural m>=1**, exp(2m)/(4m^N) is a lower bound for the extended expectation of the Euclidean operator norm of (G/D_N)^{-1}; and that extended expectation is infinity. No assertion of this last rank or moment bound is made for every N>=3.

## T4 — `SAP.P018a.T4`

Three separate universal assertions:

1. **For every U,k,K**, `Standing K` implies N V_hat-V_N tends to zero in probability under mu^{otimes N}. There is no `SampleRank` or `Proposition1Extra` premise.
2. **For every probability space (Omega,mu) and Z:Omega->R**, assume `MemLp Z 2`. **For every real V and c>0**, P(c<|Z-V|) <= c^{-2}(Var(Z)+(EZ-V)^2).
3. **For every family of measurable spaces Omega_N, probability measures mu_N and Z_N:Omega_N->R**, assume every Z_N has finite second moment. **For every real constant V**, if EZ_N-V tends to zero and Var(Z_N) tends to zero, then **for every real c>0**, P(c<|Z_N-V|) tends to zero.

## T5 — `SAP.P018a.T5`

1. **For every real t1,t2,sigma**, sharedCov3(1,1)=[[3,1,1],[1,3,1],[1,1,3]], twoRoleCov3(t1,t2,sigma)=[[t1+t2+sigma,t1,0],[t1,t1+t2+sigma,t2],[0,t2,t1+t2+sigma]], and they differ. Parameters are not required to be nonnegative.
2. The fixed matrices satisfy W_inv twoRoleCov3(1,1,1)=I, R(F'W_inv F)=I, RF'W_inv=L, LF=I, L sharedCov3(1,1)L'=(1/64)[[379,-135],[-135,67]], and R00/(L sharedCov3(1,1)L')00=284/379<1.
3. **For every probability space, every natural N>=1, and functions a_i**, assume the a_i are jointly independent and each has standard normal law. **For every natural D, yc:Omega->R^D, and estimate:R^D->R**, assume estimate(y+c*1)=estimate(y)+c for **all y,c**; yc is independent of A_bar=sum_i a_i/N; estimate is measurable; estimate(yc) has finite second moment; and estimate(yc+2 A_bar*1) has finite second moment. Then Var(estimate(yc+2 A_bar*1))=Var(estimate(yc))+4/N, hence is >=4/N. The independence and moments are hypotheses; the theorem does not produce yc from a model.

## T6 — `SAP.P018a.T6`

1. **For every N>=2 and every dyad pair d,f**, (Z1Z1')df=1_{min d=min f}, (Z2Z2')df=1_{max d=max f}, (Z1Z2')df=1_{min d=max f}, (Z2Z1')df=1_{max d=min f}, and ((Z1+Z2)(Z1+Z2)')df=|d intersect f|. **For every real tau,sigma**, sharedCov equals tau times the sum of these four incidence products plus sigma I. If additionally N>=3, then **for all real tau>0 and sigma and all real t1,t2,s**, sharedCov(N,tau,sigma) differs from twoRoleCov(N,t1,t2,s).
2. **For every probability space, natural m,N, deterministic real m by N matrix Z, and random vectors a in R^N and nu in R^m**, assume each coordinate has finite second moment and a is independent of nu. **For every real tau,sigma**, if Var(a)=tau I and Var(nu)=sigma I, then Var(Za+nu)=tau ZZ'+sigma I. Zero mean is not required.
3. **For every natural m,k, symmetric real m by m matrix C and real m by k matrix F**, assume det C is a unit (over R: nonzero) and det(F'C^{-1}F) is a unit. Set G=F'C^{-1}F and L=G^{-1}F'C^{-1}. Then LF=I and LCL'=G^{-1}. No positive definiteness or probabilistic interpretation is a premise of this algebraic clause.

## T7 — `SAP.P018a.T7`

Unconditionally the sign-pair kernel satisfies `Standing` and `Proposition1Extra`; Q=[[1,1],[1,2]], beta=0, Gamma=[[1,1],[1,1]], and V_star=[[4,0],[0,0]]. **For every N>=3**, V_N=[[4N/(N-1),-4/(N-1)],[-4/(N-1),4/(N-1)]]. The probability that (V_hat)11<0 tends to 1-exp(-1/2). N V_hat-[[4,0],[0,0]] tends to zero in probability. No `SampleRank` assertion is included.

For the explicit eight-unit data: G=[[28,24],[24,48]], det G=768, b_hat=0, V_hat=[[3/8,-1/48],[-1/48,-13/288]], and its slope entry is negative. This is a fixed finite example; its positive-probability occurrence in the random sample is not a separate conjunct.

## T8 — `SAP.P018a.T8`

**For every U,k,K**, assume `Standing K`. Then:

1. **There exists a law nu** that is centered normal with covariance V_star, allowing singular V_star, and sqrt(N)(b_hat-beta) converges weakly to nu. V_N tends to V_star and N V_hat-V_star tends to zero in probability.
2. **For every c in R^k with c'V_star c>0**: if **eventually for every N**, c'V_hat c>0 almost surely, then c'(b_hat-beta)/sqrt(c'V_hat c) converges weakly to the standard normal. Regardless of that added positivity premise, P(c'V_hat c<=0) tends to zero.
3. **For every c with c'V_star c>0 and then every real alpha with 0<alpha<1**, the probability of the conjunction c'V_hat c>=0 and |c'(b_hat-beta)|<=q_{1-alpha/2} sqrt(c'V_hat c) tends to 1-alpha. This coverage clause does not have the extra eventual a.s. positivity premise. The displayed quotient in the pivot is still a total real function at every N, including exceptional invalid samples.

## T9 — `SAP.P018a.T9`

Unconditional assertions for the concentrated-weight sign example:

1. **For every N>=2 and every d**, 0<w_d<=1/8. For every such N, Var((b_hat_w)0)>=9/16, and this variance tends to 36/35.
2. **For every N>=8**, the probability of |N(V_hat_w)00-N Var((b_hat_w)0)|>=N/2 is at least 1/256.
3. **There does not exist a deterministic real sequence V(N)** such that both N Var((b_hat_w)0)-V(N) tends to zero and N(V_hat_w)00-V(N) tends to zero in probability.
4. **For every N>=2**, the pair (b_hat_w,V_hat_w) under the sign sample law has the same joint distribution as (b_hat_R,V_hat_R) for `concentratedRepeated` under its sample law. This is distributional, not equality using the same ordered signs.

## T10 — `SAP.P018a.T10`

Five conjoined clauses:

1. **For every U,k,R**, assume `RepeatedStanding R`; assume **there exist functions fX(t,u,v), fY(t,u,v)**, defined for every natural record index t, such that all R's X(N,d,t,u,v),Y(N,d,t,u,v) equal these functions at t.val, for **all N,d,t,u,v**; assume **there exists natural T0** with T(N,d)<=T0 for all N,d. **For every positive definite H**, assume H_R(N)->H and (N/L_N^2)B_members(d -> E[q_d(beta_R(N))])->0. Then N V_hat_R-target_R tends to zero in probability. The overlap condition is on dyadwise means, not the (automatically centered) total score.
2. **For every U,k,K with Standing K, every family of deterministic real weights w(N,d) and real sequence a(N)**, assume a(N)>0 for all N and **there exists real C** with 0<w(N,d)/a(N)<=C for all N,d. **For every positive definite H**, assume Q_{w/a}(N)->H. Then N V_hat_w-target_w tends to zero in probability. The common symmetric single-record K is required; these are not arbitrary directed or varying record kernels.
3. **For every U,k,N,R, deterministic real record weights w and real a>0**, assume N>=2. **For every sample omega**, if det G_w(omega)!=0 and det H_w!=0, then b_hat_{aw}(omega)=b_hat_w(omega), V_hat_{aw}(omega)=V_hat_w(omega), and target_{aw}=target_w. This clause has no `RepeatedStanding`/measurability/positivity-of-weights premise.
4. **For every N>=2 and dyad d**, the concentrated weights are in (0,1/8].
5. The sign kernel satisfies `Standing` and `SampleRank`; there is no deterministic sequence V(N) having both convergences in T9(3).

## T11 — `SAP.P018a.T11`

Unconditionally in the unweighted sign example: **for every N>=3**, N Var((b_hat)0)=4; 4/D_N tends to zero; N(V_hat)00-4 tends to zero in probability. **For every N>=3**, also N(2N-2)/D_N^2=4/D_N, N[N(N-1)^2]/D_N^2=4, and N(2N-2)/D_N^2!=4. These last statements are scalar algebra, without a separate identification of their numerators as covariance expressions.

## T12 — `SAP.P018a.T12`

Four independent universal clauses:

1. **For every U,k,N,R**, assume `RepeatedAtSize R N`, N>=2, L_N>0, and det H_R!=0. Set S=sum_d q_d(beta_R). Then ES=0; E[L_N^{-1}G_R]=H_R; target_R=Var(H_R^{-1}[(sqrt(N)/L_N)S]); and **for almost every sample**, if det G_R!=0, then sqrt(N)(b_hat_R-beta_R)=(G_R/L_N)^{-1}[(sqrt(N)/L_N)S]. The last implication is inside the a.e. quantifier.
2. **For every U,k,N,R**, assume `RepeatedAtSize R N` and N>=2. **For every deterministic real record-weight array w**, assume det H_w!=0. Put S_w=sum_d q_{w,d}(beta_w). Then ES_w=0; E[G_w/D_N]=H_w; target_w=Var(H_w^{-1}[(sqrt(N)/D_N)S_w]); and **a.e. on nonsingular samples** sqrt(N)(b_hat_w-beta_w)=(G_w/D_N)^{-1}[(sqrt(N)/D_N)S_w]. The weights need not be positive.
3. **For every U,k,N,K**, `Standing K` and N>=2 imply target_{singleRecord K}=V_N and target_{w=1}=V_N.
4. **For every U,k,N,R**, assume N>=2, L_N>0, and det(E G_R)!=0. Then target_R also equals (N/D_N^2)(D_N^{-1}E G_R)^{-1} Var(sum_d q_d(beta_R))(D_N^{-1}E G_R)^{-1}. This is an algebraic renormalization; it assumes no `RepeatedAtSize` and no integrability beyond what the totalized definitions provide.

## T13 — `SAP.P018a.T13`

Unconditional statements about the six logistic observations:

1. Every Y is binary. **For every beta in R^2**, sum_d logLikelihood(X_d,Y_d,beta)<=its value at zero; if equality holds, beta=0. Thus zero is the unique global maximizer. det A(0)=35/4.
2. The printed sandwich is [[8/5,-2/5],[-2/5,6/35]], the score-product sandwich is [[38/25,-64/175],[-64/175,192/1225]], and they differ. Both are positive definite.
3. sum_d X_dr_d=0; sum_d (1/4)X_dX_d'=logitH; det logitH=35/4; logitHinv logitH=I; printed meat=logitH; score meat=[[3/2,7/2],[7/2,27/2]]; the two sandwiches using logitHinv have the values in (2) and differ.
4. **For every d**, logisticScore(X_d,Y_d,0)=X_dr_d. Its meat equals sum_{i=0}^3 U_i(q)U_i(q)'-B_0(q). Printed covariance minus corrected covariance=[[2/25,-6/175],[-6/175,18/1225]].
5. **For every d**, p_d(0)=1/2 and Y_d-p_d(0)=r_d; A(0)=logitH and A(0)^{-1}=logitHinv; det G(X)=140; and **for every d**, sum_{f!=d, f overlaps d} r_f=0. Strict concavity of the entire likelihood is not a conjunct.

## T14 — `SAP.P018a.T14`

**For every finite types V,E with decidable equality and every s:E->finite subsets of V**, assume every s_d has size two and s is injective. **For every natural k, X:E->R^k, Y:E->R, and beta in R^k**, assume every Y_d is zero or one and det A(X,beta)!=0. Define r_d=Y_d-p_d and q_d=X_dr_d. Then:

1. **For every d,f**, q_dq_f'=r_dr_f X_dX_f'.
2. B_s(q)=sum_i U_i(q)U_i(q)'-B_0(q).
3. B_s(q) and A^{-1}B_s(q)A^{-1} are symmetric.
4. Printed meat=sum_d [r_d sum_{f overlaps d}r_f] X_dX_d'.

Independently of those universal premises, the six-observation printed meat differs from its score-product meat. No fitted-score equation is assumed in the universal clause; beta is arbitrary subject to nonsingular bread.
