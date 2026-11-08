# Blind reading of the Challenge

This file was written from `SAP/P041/Defs.lean`, all fourteen Defs parts, and the Challenge files, before opening `claims.json` or `record.json`. The twelve Challenge theorems have no explicit parameters or hypotheses: each asserts the closed proposition `TnStatement` described below. The Challenge proofs are `sorry`; this reading concerns their statements.

## Definitions and Mathlib meanings

All unqualified arithmetic below is real arithmetic, except explicitly natural-number counts, binomial coefficients, ranks, and integer rounding targets. Decimal literals are exact rationals. Real division is totalized, with division by zero equal to zero. Natural subtraction is truncated. None of the definitions themselves imposes probability, nonsingularity, or positivity assumptions.

For real q, write A(q) = -2 log(q)/12, B(q) = -3 log(q)/12, E(h,t) = exp(-ht), and D(q) = E(A(q),12)-E(B(q),12). Mathlib's `Real.log` is the ordinary logarithm on positive arguments, log|q| on negative arguments, and zero at zero. Real powers on positive bases are exp(t log q); the natural powers appearing elsewhere are ordinary integer powers. `binomialCountProbability n k p` is choose(n,k) p^k (1-p)^(n-k), with natural n-k. Write O(nP,nN,rP,rN) = (1-rP/nP)-(1-rN/nN).

Write R(a,b)=100(a/b-1), Q(a,b)=100|a-b|/((a+b)/2), and W(x,k) for k-1/2 <= x < k+1/2, where k is an integer. Thus ties are rounded upward. Write I(v,x) for v-0.0005 <= x <= v+0.0005; both endpoints are included. `withinPrintedPrecision x v` means |x-v| <= 0.0005.

Write e(h,s)=s/h, Z(h,s)=h log(h)/s, and P(z)=2 Phi(-|z|), where Phi is the CDF of the genuine Gaussian probability measure with mean zero and variance one. `gaussianReal`'s second argument is a nonnegative variance. Mathlib's `cdf` agrees with the real probability of (-infinity,x] for a probability measure, and `gaussianReal 0 1` has an `IsProbabilityMeasure` instance. Thus no arbitrary nonprobability-CDF convention is involved. Let J(h,s) be the closed interval [exp(log h-(49/25)e(h,s)), exp(log h+(49/25)e(h,s))]. Let ZB(hF,sF,hA,sA)=(log hF-log hA)/sqrt(e(hF,sF)^2+e(hA,sA)^2). The tier function is 3 if P(z)<.01, otherwise 2 if P(z)<.05, otherwise 1 if P(z)<.10, otherwise 0. `Real.sqrt` is the nonnegative square root on nonnegative inputs and is zero on negative inputs.

For a natural m, U_m is the finite set {0,...,2m-1}, represented by `Fin (2*m)`. B_m is the finite set of all m-element subsets of U_m (`Finset.univ.powersetCard m`). Mathlib's `mem_powersetCard` says exactly subsethood and cardinality m, and its cardinality is choose(2m,m). For any subset z of ranks in `Fin n`, Y_z(r) is one if there exists an earlier rank s<r outside z, and zero otherwise. For z subset U_m and an arbitrary real-valued rank function y, C_m(z,y)=(sum over r in z of y(r))/m-(sum over r in U_m\z of y(r))/m. The function does not itself require |z|=m. For a function f on subsets of U_m, E_m[f]=(sum over z in B_m of f(z))/|B_m|, a uniform finite average. K(z) is the number of ranks r such that every s<=r belongs to z, hence the length of the initial cited run. L_m(k) is the fraction of B_m for which K(z)=k. The independent-citation expression is the uniform average over all 16 subsets z of `Fin 4` of (1/4) sum over ranks r of (2 if r in z, otherwise -2)Y_z(r).

For a finite real matrix X with observation rows and coefficient columns and vector y, beta_X(y)=(X^T X)^(-1) X^T y; u_X(y)=y-X beta_X(y); M_X(u)_{jl}=sum_i u_i^2 X_ij X_il; H_X(y)=n/(n-k) (X^T X)^(-1) M_X(u_X(y)) (X^T X)^(-1). In H, n-k is subtraction after casting the two cardinalities to reals, not natural subtraction. Mathlib's square-matrix inverse is the ordinary inverse when its determinant is a unit and zero otherwise. Over R, unit determinant means nonzero determinant. Matrix-vector multiplication and dot products are ordinary finite sums, and `1-S`, signs, and vector subtraction are pointwise. `Pi.single j0 1` is the coordinate vector with a one at j0 and zeros elsewhere.

The fixed positive-study Gram matrix G_P has rows (300,150,100,100), (150,150,50,50), (100,50,100,0), (100,50,0,100). The fixed citation design X_C has rows (1,0,0), (1,1,0), (1,0,1), (1,1,1). Its four supplied survivor counts are a=(12,25,23,42). The citation Gram G_C has rows (200,100,100), (100,100,50), (100,50,100). The supplied inverse B_C has rows (3/200,-1/100,-1/100), (-1/100,1/50,0), (-1/100,0,1/50). The supplied coefficient vector b_C is (21/100,8/25,7/25). For real n,a,f, `binaryCellSSR` is a(1-f)^2+(n-a)f^2.

`survivalIndicator none h` is one; for `some t` it is one exactly when h<t and zero otherwise (removal at the horizon counts as nonsurvival). `removalIndicator` is its complement. Neither indicator is used by any target proposition. Arm difference F(nT,nB,sT,sB)=sT/nT-sB/nB. Tenure L(C,Y)=C-Y. The year hazard is h0 exp(bY+aT+gTY+w). The tenure hazard is h0 exp(Cb) exp(-bL+(a+Cg)T-gTL+w). The illustrative relative hazard is exp(log(132/125) T(Y-2009)). These functions themselves place no positivity or treatment-domain restriction on their arguments.

Sources followed: Mathlib `Data/Finset/Powerset.lean` (`powersetCard`, membership and cardinality), `Probability/CDF.lean` (`cdf`, `cdf_eq_real`), `Probability/Distributions/Gaussian/Real.lean` (`gaussianReal`, its probability-measure instance), `LinearAlgebra/Matrix/NonsingularInverse.lean` (inverse instance and `nonsing_inv_apply_not_isUnit`), `Data/Matrix/Mul.lean` (dot product and matrix-vector product), `Analysis/SpecialFunctions/Log/Basic.lean`, and `Analysis/SpecialFunctions/Pow/Real.lean`. Square-root conventions are those of the imported Mathlib real square root.

## SAP.P041.T1

This is the conjunction of three groups, with no common hypothesis.

1. For every real q, if 0<q and then q<1, A(q)>0, B(q)>0, A(q)/B(q)=2/3, B(q)/A(q)=3/2, 2/3 is not one, E(A(q),12)=q^2, E(B(q),12)=q^3, and D(q)=q^2(1-q).
2. For every real q and then real t, if 0<q, q<1, and 0<=t, E(A(q),t)=q^(t/6) and E(B(q),t)=q^(t/4).
3. At q=4/5 the two twelve-hour survivals are 16/25 and 64/125, and D=16/125. At q=99/100 they are 9801/10000 and 970299/1000000, and D=9801/1000000. The first D minus the second is 118199/1000000 and is positive. Their quotient is 128000/9801 and exceeds 13. Both A/B ratios equal 2/3, which differs from one. The corresponding removal probabilities, in order B(4/5), A(4/5), B(99/100), A(99/100), are 61/125, 9/25, 29701/1000000, 199/10000; each is strictly between zero and one. The binomial expressions at (n,k,p)=(150,75,61/125), (150,52,9/25), (76,1,29701/1000000), (75,3,199/10000) are all strictly positive.

## SAP.P041.T2

Seven independent conjuncts are asserted.

1. For all real h,s, first assuming I(.691,h) and then I(.318,s), .80<|Z(h,s)|<.81 and |Z(h,s)|<1.
2. For all real hF,sF,hA,sA, assuming in that order I(.691,hF), I(.318,sF), I(.629,hA), I(.091,sA), |log hF-log hA|<.21 e(hF,sF), .21 e(hF,sF)<(49/25)e(hF,sF), |log hF|<(49/25)e(hF,sF), and both 1 and hA belong to J(hF,sF).
3. For all h,s with I(.691,h), I(.318,s), the lower endpoint of J lies strictly between .279 and .282 and its upper endpoint lies strictly between 1.700 and 1.706.
4. For all hF,sF,hA,sA under the four intervals in group 2, .18<ZB<.21.
5. At the supplied central entries, |P(Z(.691,.318))-.42|<=.005 and |P(ZB(.691,.318,.629,.091))-.845|<=.0005.
6. O(150,150,52,75)=23/150 and O(75,76,3,1)=-51/1900; their difference is 1027/5700 and positive. O(150,150,82,101)=19/150 and O(75,76,7,3)=-307/5700; their difference is 343/1900 and positive.
7. There exist real qA, then real qF, with 0<qA<1 and 0<qF<1, A(qA)/B(qA)=A(qF)/B(qF)=2/3, the latter ratio not one, D(qF)>0, and 13 D(qF)<D(qA). The witnesses need not be the specific q values of T1.

## SAP.P041.T3

The first group is unconditional arithmetic: R(75/150,52/150)=575/13, R(92/150,69/150)=100/3, R(62/100,32/100)=375/4. Subtracting 36,29,64 respectively gives 107/13,13/3,119/4, each greater than 1/2. Each corresponding W assertion at 36,29,64 is false individually; the same three R values satisfy W at 44,33,94 respectively. Q(75,52)=4600/127, Q(92,69)=200/7, Q(62,32)=3000/47, and those satisfy W at 36,29,64.

Second, for every real a then real b, assuming 0<b and then b<a, R(a,b)-Q(a,b)=100(a-b)^2/[b(a+b)] and this difference is strictly positive. Third, those differences at (75,52), (92,69), (62,32) equal 13225/1651,100/21,5625/188 respectively.

## SAP.P041.T4

An unconditional conjunction: the three R values in T3 equal 575/13,100/3,375/4, satisfy W at 44,33,94 respectively, and the first two are within .005 of 44.23 and 33.33. The third equals 93.75 exactly. R(76/150,52/150)=600/13, satisfies W at 46, and is within .005 of 46.15. The three Q values are 4600/127,200/7,3000/47 and satisfy W at 36,29,64. The 76 count is simply an additional fixed arithmetic case; no premise selects a real-data convention.

## SAP.P041.T5

The conjunction has the following groups.

1. For every natural n (implicit), subsets z,z' of `Fin n`, and rank r, agreement of z and z' on every earlier s<r implies Y_z(r)=Y_z'(r).
2. For every natural m with 1<=m, and then every subset z of U_m (not necessarily balanced), C_m(z,0)=0. For every m with 1<=m, E_m[C_m(z,0)]=0.
3. B_2 is exactly the six subsets {2,3},{1,3},{1,2},{0,3},{0,2},{0,1}. In that order the Y vectors are (0,1,1,1), (0,1,1,1), (0,1,1,1), (0,0,1,1), (0,0,1,1), (0,0,0,1). The cited means are 1,1,1,1/2,1/2,0; all uncited means are 1/2; the contrasts are 1/2,1/2,1/2,0,0,-1/2. Each row asserts equality of the whole Y function and both means as well as the contrast.
4. The six contrasts are asserted again individually. Their balanced average is 1/6 and is nonzero. The corresponding average for zero outcomes is zero.
5. For every m>=1: for every natural k with k<=m, L_m(k)=choose(2m-k-1,m-1)/choose(2m,m); E_m[K]=m/(m+1); for every z in B_m, the cited Y sum is m-K(z) and the uncited Y sum is m-1; the average cited mean is m/(m+1); E_m[C_m(z,Y_z)]=1/[m(m+1)] and is strictly positive. Subtractions in the binomial coefficient are natural subtraction; m>=1 and k<=m are part of this group.
6. For every m>=1 and then every z in B_m, the uncited mean is (m-1)/m (here subtraction in the real expression is real subtraction).
7. At m=50, E_50[K]=50/51, the average cited mean is 50/51, every balanced uncited mean is 49/50, and the average contrast is 1/2550 and nonzero.
8. E_2[C_2(z,(0,0,1,1))]=0 for this fixed rank-outcome vector. The independent-citation expression defined above is zero.

## SAP.P041.T6

1. For every natural m, assuming 1<=m, and then every function g:U_m x Bool -> R, E_m[C_m(z,r -> g(r,1_{r in z}))]=(sum_r [g(r,true)-g(r,false)])/(2m).
2. For every m>=1 and then every fixed rank function c:U_m -> R, E_m[C_m(z,c)]=0.
3. For every g:`Fin 4` x Bool -> R the formula in group 1 is also stated at m=2 with denominator 4.
4. For every m>=1: for every subsets z,z' of U_m and every rank r, agreement of memberships at every s different from r implies Y_z(r)-Y_z'(r)=0; the average zero-outcome contrast is zero; the average scrutiny contrast is 1/[m(m+1)] and positive. The own-coordinate comparison is over all subsets, not only balanced subsets.
5. At m=2 the scrutiny average is 1/6, the zero-outcome average is zero, and the all-subset own-coordinate invariance of group 4 is restated on four ranks.
6. The fixed outcome vector (0,0,1,1) has zero balanced average contrast at m=2, and the scrutiny average at m=50 is 1/2550.

## SAP.P041.T7

All statements are fixed finite matrix/arithmetic assertions, with no assumptions.

1. The four rows of X_C each weighted by 50 give Gram G_C; sum_i a_i X_C(i,.)=(102,67,65); G_C B_C=B_C G_C=identity; B_C(102,67,65)=b_C. Coefficient index 1 equals .320 and equals one half of [(25-12)/50+(42-23)/50]. Also G_C^(-1)=B_C.
2. The fitted values at the four rows are (21/100,53/100,49/100,81/100). Their binary residual sums of squares are 1833/200,2509/200,2493/200,1353/200, whose sum is 2047/50. For every cell i, (row 1 of B_C dotted with X_C(i,.))^2=1/10000. Multiplying the weighted sum of these squared influences and cell residual sums of squares by 200/197 gives variance 2047/492500.
3. .320/.645=64/129<1. The variance lies between .0635^2 (inclusive) and .0645^2 (exclusive), and its square root between .0635 (inclusive) and .0645 (exclusive). .645^2=16641/40000 differs from that variance. (.32)^2/variance=50432/2047>24, and 2.61^2<24. The corrected ratio .32/sqrt(variance) is greater than 4.89 and greater than 2.61.
4. The four signed influences themselves are (-1/100,1/100,-1/100,1/100).

## SAP.P041.T8

1. For all real h,s, under I(.670,h), I(.095,s), |Z|>2.80. Separately, for all h,s under I(.480,h), I(.174,s), 2.01<|Z|<2.04; under I(.274,h), I(.162,s), 2.18<|Z|<2.20; and under I(.316,h), I(.149,s), 2.43<|Z|<2.46. In each universal statement, the h interval precedes the s interval as hypotheses.
2. Under the same four pairs of interval assumptions, respectively: P(Z)<.01 and tier=3; .01<P(Z)<.05 and tier=2; .01<P(Z)<.05 and tier=2; .01<P(Z)<.05 and tier=2.
3. For every real p1,p2,p3,p4, assuming in order p1<.01, .01<p2<.05, .01<p3<.05, .01<p4<.05, the conclusion is p1<.05, p2<.10, p3<.10, and not p4<.01. This last group does not assume the p values are probabilities.

## SAP.P041.T9

Five conjuncts:

1. For every natural n,k, intercept coordinate j0 in `Fin k`, real n-by-k matrix X, and arbitrary real vector S of length n, assume in order k<n, det(X^T X) is a unit, and X(i,j0)=1 for every i. Then beta_X(1-S)=e_j0-beta_X(S), u_X(1-S)=-u_X(S), the two residual meats agree, H_X(1-S)=H_X(S), and for every coefficient j the square roots of the corresponding diagonal covariances agree. S need not be binary. The existence of j0 forces k>=1 and k<n forces n>=2.
2. For every n, n-by-4 X, real length-n S, and real sT,sB,w2,w4, assume in order det(X^T X) a unit, X^T X=G_P, X^T S=(sT+sB,sT,w2,w4). Then coefficient index 1 is sT/150-sB/150.
3. For every n, n-by-3 X, real S, and real sT,sB,w4, assume a unit determinant, Gram G_C, and X^T S=(sT+sB,sT,w4). Then coefficient 1 is sT/100-sB/100.
4. For every n, n-by-2 X, real S, and real sT,sB, assume a unit determinant, Gram with rows (151,75),(75,75), and X^T S=(sT+sB,sT). Then coefficient 1 is sT/75-sB/76.
5. The following supplied count differences are exact: F(150,150,105,88)=17/150; F(150,150,98,75)=23/150; F(150,150,90,68)=11/75; F(150,150,68,49)=19/150; F(100,100,67,35)=8/25; F(100,100,63,26)=37/100; F(100,100,58,19)=39/100; F(100,100,34,11)=23/100; F(75,76,72,75)=-51/1900; F(75,76,68,73)=-307/5700. For every member (x,v) of the finite set pairing these ten exact values with (.113,.153,.147,.127,.320,.370,.390,.230,-.027,-.054) in that order, x is nonzero, |x-v|<=.0005, and |-x-v|>.0005. This arithmetic is not connected to an actual observation vector by a premise.

## SAP.P041.T10

1. For every real h0,a,b,g,C,L,T,w, b(C-L)+aT+gT(C-L)+w = Cb-bL+(a+Cg)T-gTL+w and the tenure hazard equals the year hazard evaluated at Y=C-L. h0 and T are unrestricted real numbers.
2. For every real a,g,C,L, exp(-g)=1/exp(g), exp((a+Cg)-g(L+1))=exp((a+Cg)-gL)/exp(g), and for every real r>0, r<1 iff 1<1/r, and 1<r iff 1/r<1.
3. For every r in [.9885,.9895], 1.0106<1/r<1.0117 and 1<1/r. For every r in [.9805,.9815], 1.0188<1/r<1.0199 and 1<1/r. For every r in [1.0555,1.0565], .9465<1/r<.9475 and 1/r<1. For every r in [1.0035,1.0045], .9955<1/r<.9966 and 1/r<1. Each universal has a lower-bound hypothesis followed by an upper-bound hypothesis.
4. For every real g,V,s, assuming V>0 and then s=exp(g)sqrt(V), (1/exp(g))sqrt(V)=s/(exp(g))^2 and (-g)^2/V=g^2/V.
5. L(2014,2009)=5 and L(2014,2008)=6. The illustrative relative hazard equals one at (T,Y)=(0,2009),(0,2008),(1,2009), and equals 125/132 at (1,2008). Also 132/125>1, 125/132<1, and their product is one.

## SAP.P041.T11

For every real h,s under I(.691,h), I(.318,s), .4205<=P(Z)<=.4232. Under I(.775,h), I(.503,s), .6936<=P(Z)<=.6954. Under I(.627,h), I(.406,s), .4700<=P(Z)<=.4720. Each interval pair forms a separate universally quantified implication with h and then s as variables and hypotheses. At those three exact central pairs, respectively, |Z| is within .00005 of .8032,.3927,.7209 and P(Z) is within .00005 of .4219,.6945,.4710. Separately, for all h,s in each of the same three rounding rectangles, |Z|<1. There is no subgroup, mechanism, or data-identification assertion.

## SAP.P041.T12

The first unconditional conjunction gives Q(75,52)=4600/127, Q(92,69)=200/7, Q(62,32)=3000/47, W of those values at 36,29,64 respectively, and the three strict inequalities 52/150<75/150, 69/150<92/150, 32/100<62/100. The second conjunct negates the conjunction W(R(75/150,52/150),36) AND W(R(92/150,69/150),29) AND W(R(62/100,32/100),64). It asserts at least one of those three directional rounding assertions fails, not that all three fail, and contains none of the three exact directional R values.
