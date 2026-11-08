# Blind reading of SAP.P041

This file was written before opening `claims.json` or `record.json`. It reads the twelve theorem types in `SAP/P041/Challenge/Part1.lean`, expanding their definitions in `SAP/P041/Defs/Part1.lean` through `Part14.lean`. Each theorem is a closed proposition; there are no ambient mathematical hypotheses. The Challenge bodies are `sorry`, so this reading does not treat them as evidence of truth.

## Conventions and complete supporting definitions

All decimal literals below are exact rational real numbers. Natural and integer values used in real arithmetic are coerced to the reals. `Fin n` is the ordered set of integers 0 through n−1; `Finset` is a finite set without multiplicity; its sums and cardinalities have their usual finite meanings. Vectors displayed with brackets and matrices with rows have zero-based coordinates. Matrix and vector operations are ordinary finite sums. Real division is totalized with division by zero equal to zero, so domain restrictions must be checked separately.

Write, for real q, h and t:

- H+(q)=−2 log(q)/12, H−(q)=−3 log(q)/12;
- S(h,t)=exp(−ht), D(q)=S(H+(q),12)−S(H−(q),12);
- B(n,k,p)=choose(n,k) p^k (1−p)^(n−k), for natural n,k (the subtraction in the exponent is natural subtraction);
- O(nP,nN,rP,rN)=(1−rP/nP)−(1−rN/nN), with all four arguments real;
- R(a,b)=100(a/b−1), the directional percentage increase;
- A(a,b)=100|a−b|/((a+b)/2), the symmetric percentage difference;
- Round(x,k) means k−1/2 ≤ x < k+1/2, for integer k;
- E(h,s)=s/h, W(h,s)=h log(h)/s;
- P(z)=2 Phi(−|z|), where Phi is the cumulative distribution function of the real Gaussian distribution with mean 0 and variance 1;
- I(v,x) means v−0.0005 ≤ x ≤ v+0.0005 (both endpoints included);
- CI(h,s) is the closed real interval [exp(log h−(49/25)E(h,s)), exp(log h+(49/25)E(h,s))];
- Z(hF,sF,hA,sA)=(log hF−log hA)/sqrt(E(hF,sF)^2+E(hA,sA)^2);
- Tier(z) is 3 if P(z)<0.01; otherwise 2 if P(z)<0.05; otherwise 1 if P(z)<0.10; otherwise 0.

For each natural m let U_m={0,…,2m−1} and let Bal(m) be the set of all m-element subsets of U_m. For any real function f on subsets, Avg_m(f)=sum over z in Bal(m) of f(z), divided by |Bal(m)|. This is a uniform finite average, not a measure-theoretic expectation or an asserted stochastic experiment. For z a subset of {0,…,n−1}, let Q(z,r)=1 if there exists s<r outside z, and 0 otherwise. For a real vector Y indexed by U_m, C_m(z,Y)=(sum over r in z of Y(r))/m−(sum over r in U_m\z of Y(r))/m. This definition accepts arbitrary subsets z, even unbalanced ones. Let K(z) be the number of r for which every s≤r belongs to z: it is the length of the initial segment contained in z. Let L(m,k)=|{z in Bal(m):K(z)=k}|/|Bal(m)|. Finally J is (1/16) times the sum over all 16 subsets z of {0,1,2,3} of (1/4)sum_r [(2 if r belongs to z, else −2) Q(z,r)].

For any finite real design X with n rows and k columns and response y, set G=X^T X, beta(X,y)=G^−1 X^T y, u(X,y)=y−X beta(X,y), M(X,u)_{jl}=sum_i u_i^2 X_{ij} X_{il}, and H(X,y)=[n/(n−k)] G^−1 M(X,u(X,y)) G^−1. The factor n−k here is subtraction in the reals, not truncated natural subtraction. The inverse is Mathlib's nonsingular matrix inverse: adjugate divided by determinant, equal to the usual inverse when the determinant is nonzero, and equal to zero for a singular real matrix. `IsUnit det` for a real determinant means the determinant is nonzero. `Pi.single j0 1` is the coordinate vector e_j0. Real square root is the nonnegative square root, totalized as zero on negative arguments.

The fixed matrices and vectors are:

```
G_P = [300 150 100 100; 150 150 50 50;
       100 50 100 0; 100 50 0 100]
X_c = [1 0 0; 1 1 0; 1 0 1; 1 1 1]
a_c = [12,25,23,42]
G_c = [200 100 100; 100 100 50; 100 50 100]
G_c_inv = [3/200 -1/100 -1/100;
           -1/100 1/50 0; -1/100 0 1/50]
b_c = [21/100,8/25,7/25]
SSR(n,a,f) = a(1-f)^2 + (n-a)f^2.
```

The remaining supplied definitions are: survivalIndicator(None,h)=1 and survivalIndicator(Some t,h)=1 if h<t, else 0; removalIndicator=1−survivalIndicator. Thus removal at exactly the horizon counts as removed. Arm(nT,nB,sT,sB)=sT/nT−sB/nB. Prec(x,v) means |x−v|≤0.0005. Tenure(C,Y)=C−Y. Year(h0,b,a,g,Y,T,w)=h0 exp(bY+aT+gTY+w). Ten(h0,b,a,g,C,L,T,w)=h0 exp(Cb) exp(−bL+(a+Cg)T−gTL+w). Ill(T,Y)=exp(log(132/125) T(Y−2009)). The survival/removal indicator definitions are not referenced by any of the twelve theorem types.

Mathlib definitions followed: `Probability/CDF.lean` defines `cdf` and proves `cdf_eq_real`, its value on a probability measure being the measure of (−infinity,x]; `Probability/Distributions/Gaussian/Real.lean` defines `gaussianReal` by Gaussian density for nonzero variance and supplies its probability-measure instance. At variance 1 the density is exp(−x²/2)/sqrt(2 pi). `Analysis/SpecialFunctions/Pow/Real.lean` defines real powers; for positive base q, q^t=exp(log(q)t). `Analysis/SpecialFunctions/Log/Basic.lean` supplies the real logarithm (with log 0=0 and log of a negative number equal to log of its absolute value). `Analysis/Real/Sqrt.lean` supplies the totalized square root described above. `LinearAlgebra/Matrix/NonsingularInverse.lean` supplies the matrix inverse and its inverse laws under `IsUnit det`. `Data/Matrix/Mul.lean` supplies the finite dot product and matrix-vector product. `Data/Finset/Powerset.lean` defines `powersetCard`; membership is exactly subset containment and prescribed cardinality, and its cardinality is a binomial coefficient. No integral of an arbitrary supplied function, limsup, or infinite-index average occurs.

## SAP.P041.T1

The conclusion is the conjunction of these three independent clauses, in this order.

1. For every real q, assuming 0<q and then q<1: H+(q)>0 and H−(q)>0; H+(q)/H−(q)=2/3; H−(q)/H+(q)=3/2; 2/3 differs from 1; S(H+(q),12)=q²; S(H−(q),12)=q³; D(q)=q²(1−q).
2. For every real q and then real t, assuming 0<q, q<1 and t≥0, in that order: S(H+(q),t)=q^(t/6) and S(H−(q),t)=q^(t/4), with real exponents.
3. At q=4/5 the two twelve-hour survivals are respectively 16/25 and 64/125 and D=16/125. At q=99/100 they are 9801/10000 and 970299/1000000 and D=9801/1000000. The first D minus the second is 118199/1000000>0. Their ratio is 128000/9801>13. Both H+/H− ratios are 2/3≠1. The removal probabilities, in order negative/positive at 4/5 and negative/positive at 99/100, are 61/125, 9/25, 29701/1000000, 199/10000. Each lies strictly between 0 and 1. The four expressions B(150,75,61/125), B(150,52,9/25), B(76,1,29701/1000000), B(75,3,199/10000) are strictly positive.

There is no hypothesis specifying observed data, and no assertion here that any jointly sampled dataset has a particular probability, or that an empirical mechanism is identified.

## SAP.P041.T2

The conclusion is the conjunction of seven clauses.

1. For every real h,s, assuming I(0.691,h) and I(0.318,s), 0.80<|W(h,s)|<0.81 and |W(h,s)|<1.
2. For every real hF,sF,hA,sA, assuming in that order I(0.691,hF), I(0.318,sF), I(0.629,hA), I(0.091,sA): |log hF−log hA|<0.21 E(hF,sF); 0.21 E(hF,sF)<(49/25)E(hF,sF); |log hF|<(49/25)E(hF,sF); both 1 and hA belong to CI(hF,sF).
3. For every real h,s under the hypotheses of clause 1, the lower endpoint of CI(h,s) is strictly between 0.279 and 0.282 and its upper endpoint is strictly between 1.700 and 1.706.
4. For every real hF,sF,hA,sA under the hypotheses of clause 2, 0.18<Z(hF,sF,hA,sA)<0.21.
5. At the central values, |P(W(0.691,0.318))−0.42|≤0.005 and |P(Z(0.691,0.318,0.629,0.091))−0.845|≤0.0005.
6. O(150,150,52,75)=23/150; O(75,76,3,1)=−51/1900; their difference is 1027/5700>0. O(150,150,82,101)=19/150; O(75,76,7,3)=−307/5700; their difference is 343/1900>0.
7. There exist real qA and then qF such that 0<qA<1, 0<qF<1, H+(qA)/H−(qA)=2/3, H+(qF)/H−(qF)=2/3, the latter ratio differs from 1, D(qF)>0 and 13 D(qF)<D(qA).

There is no quantified empirical causal model or conclusion about mechanisms, cited external comparisons, or political inactivity.

## SAP.P041.T3

Three clauses are conjoined.

1. R(75/150,52/150)=575/13, R(92/150,69/150)=100/3 and R(62/100,32/100)=375/4. Their respective differences from 36,29,64 are 107/13,13/3,119/4, each greater than 1/2. Each of the three corresponding Round assertions at 36,29,64 is false individually. The same directional increases satisfy Round at 44,33,94 respectively. A(75,52)=4600/127, A(92,69)=200/7 and A(62,32)=3000/47, and these symmetric differences satisfy Round at 36,29,64 respectively.
2. For every real a and then real b, assuming b>0 and then b<a: R(a,b)−A(a,b)=100(a−b)²/[b(a+b)] and this difference is strictly positive.
3. The directional-minus-symmetric gaps at (75,52),(92,69),(62,32) equal respectively 13225/1651,100/21,5625/188.

## SAP.P041.T4

A single unconditional conjunction: R(75/150,52/150)=575/13, rounds to 44, and differs from 44.23 by at most 0.005. R(92/150,69/150)=100/3, rounds to 33 and differs from 33.33 by at most 0.005. R(62/100,32/100)=375/4=93.75 and rounds to 94. The separate variant R(76/150,52/150)=600/13 rounds to 46 and differs from 46.15 by at most 0.005. The three symmetric values at (75,52),(92,69),(62,32) are respectively 4600/127,200/7,3000/47 and round to 36,29,64.

No data-consistency or conditional-update proposition connects the variant to the other fixed values; all four directional computations are present as separate arithmetic assertions.

## SAP.P041.T5

The following nine clauses are conjoined, with their displayed local quantifiers.

1. For every natural n (implicit), subsets z,z' of Fin n and rank r, if for every s<r membership in z and z' is equivalent, then Q(z,r)=Q(z',r).
2. For every natural m with m≥1 and then every subset z of U_m, C_m(z,zero vector)=0.
3. For every natural m with m≥1, Avg_m(z↦C_m(z,zero vector))=0.
4. Bal(2) consists exactly of the six subsets in the following table. In each row Q(z,·) equals the displayed vector; its mean over z, its mean over the complement, and C_2 are the last three columns.

| z | Q(z,·) | cited mean | uncited mean | contrast |
|---|---|---|---|---|
| {2,3} | [0,1,1,1] | 1 | 1/2 | 1/2 |
| {1,3} | [0,1,1,1] | 1 | 1/2 | 1/2 |
| {1,2} | [0,1,1,1] | 1 | 1/2 | 1/2 |
| {0,3} | [0,0,1,1] | 1/2 | 1/2 | 0 |
| {0,2} | [0,0,1,1] | 1/2 | 1/2 | 0 |
| {0,1} | [0,0,0,1] | 0 | 1/2 | −1/2 |

5. The six individual contrasts equal those in the table; their uniform average is 1/6, differs from zero, and the corresponding average using the zero vector is zero.
6. For every natural m≥1: for every natural k≤m, L(m,k)=choose(2m−k−1,m−1)/choose(2m,m); Avg_m(K)=m/(m+1). For every z in Bal(m), sum over cited r of Q(z,r) is m−K(z), and sum over uncited r is m−1. The average cited mean is m/(m+1); Avg_m(z↦C_m(z,Q(z,·)))=1/[m(m+1)]>0. In the binomial coefficients the subtractions are natural subtraction; under k≤m and m≥1 their intended nonnegative values are defined without truncation changing them.
7. For every natural m≥1 and then every z in Bal(m), its uncited mean equals (m−1)/m.
8. At m=50, Avg_50(K)=50/51, the average cited mean is 50/51, every balanced assignment has uncited mean 49/50, and the average contrast is 1/2550≠0.
9. Avg_2(z↦C_2(z,[0,0,1,1]))=0 and J=0.

The protocol is encoded by Q and the two alternative fixed outcome vectors; there is no variable for physical clock time.

## SAP.P041.T6

The following six clauses are conjoined.

1. For every natural m, assuming m≥1, and then every function g:U_m×Bool→R, Avg_m of C_m(z,r↦g(r,1_{r∈z})) equals (1/(2m))sum_r [g(r,true)−g(r,false)]. No other response dependence is permitted in this clause; g is otherwise arbitrary.
2. For every natural m≥1 and then every real vector c on U_m, Avg_m(z↦C_m(z,c))=0.
3. For every function g on Fin 4×Bool, the equality in clause 1 holds with m=2 and denominator 4, without an additional hypothesis.
4. For every natural m≥1, first: for all subsets z,z' of U_m and then all r, if for every s≠r the membership of s agrees between z and z', Q(z,r)−Q(z',r)=0. These subsets are not required to be balanced. Also the average zero-outcome contrast is zero, whereas Avg_m(z↦C_m(z,Q(z,·)))=1/[m(m+1)]>0.
5. At m=2 the scrutiny average is 1/6, the zero-outcome average is zero, and the all-subsets own-membership invariance assertion of clause 4 holds for Fin 4.
6. The average contrast at m=2 for fixed outcomes [0,0,1,1] is zero, and the scrutiny average at m=50 is 1/2550.

## SAP.P041.T7

This theorem has no input hypotheses. It conjoins these exact finite computations.

1. sum_i 50 X_c(i,j)X_c(i,l)=G_c(j,l); sum_i a_c(i)X_c(i,j)=[102,67,65]_j. Both G_c G_c_inv and G_c_inv G_c equal the identity. G_c_inv[102,67,65]=b_c. b_c(1)=0.320=(1/2)[(25−12)/50+(42−23)/50]. Also G_c^−1=G_c_inv.
2. X_c b_c=[21/100,53/100,49/100,81/100]. The four SSR values for n=50, survivor counts [12,25,23,42] and those fitted values are respectively 1833/200,2509/200,2493/200,1353/200. Their sum is 2047/50. For every cell i in Fin 4, the square of row 1 of G_c_inv dotted with X_c(i,·) equals 1/10000. The expression (200/197)sum_i SSR_i [G_c_inv(1,·) dot X_c(i,·)]² equals 2047/492500.
3. 0.320/0.645=64/129<1. The variance 2047/492500 belongs to [0.0635²,0.0645²), and its square root belongs to [0.0635,0.0645). The square of 0.645 equals 16641/40000, which is different from that variance. (8/25)² divided by the variance equals 50432/2047>24; 2.61²<24. The corrected ratio (8/25)/sqrt(2047/492500) exceeds both 4.89 and 2.61.
4. The four unsquared row weights are exactly [−1/100,1/100,−1/100,1/100].

The displayed variance expression is the cell-compressed HC1 arithmetic; the theorem does not itself quantify an expanded 200-row design or invoke `hc1Covariance`. It states no probability tail, p value, critical value, or significance-star conclusion.

## SAP.P041.T8

Three clauses are conjoined.

1. For all real h,s with I(0.670,h) then I(0.095,s), |W(h,s)|>2.80. Independently, for all real h,s with I(0.480,h), I(0.174,s), 2.01<|W|<2.04. For the rectangle centered at (0.274,0.162), 2.18<|W|<2.20. For the rectangle centered at (0.316,0.149), 2.43<|W|<2.46. The quantifiers and two hypotheses restart at each rectangle.
2. Over the first rectangle P(W)<0.01 and Tier(W)=3. Over each of the other three rectangles 0.01<P(W)<0.05 and Tier(W)=2. Each assertion separately quantifies all real h,s with the corresponding two interval hypotheses.
3. For every real p1,p2,p3,p4, assuming in that order p1<0.01, 0.01<p2<0.05, 0.01<p3<0.05 and 0.01<p4<0.05: p1<0.05, p2<0.10, p3<0.10 and not(p4<0.01). In particular there is no positivity hypothesis on p1.

## SAP.P041.T9

Five independent clauses are conjoined.

1. For every natural n, natural k, j0 in Fin k, real n-by-k matrix X and real response vector S, assuming in order k<n, det(X^T X) is a unit, and X(i,j0)=1 for every row i: beta(X,1−S)=e_j0−beta(X,S); u(X,1−S)=−u(X,S); M(X,u(X,1−S))=M(X,u(X,S)); H(X,1−S)=H(X,S); for every column j, the square roots of their diagonal entries at (j,j) agree. S need not be binary. The existence of j0 requires k≥1, and k<n then gives n≥2.
2. For every natural n, n-by-4 real matrix X, real response S, and reals sT,sB,w2,w4, assuming in order det(X^T X) is a unit, X^T X=G_P, and X^T S=[sT+sB,sT,w2,w4]: beta(X,S)(1)=sT/150−sB/150. There is no separate intercept, binary-column, binary-response, or row-count assumption in this clause.
3. For every natural n, n-by-3 real matrix X, response S and reals sT,sB,w4, assuming in order det(X^T X) is a unit, X^T X=G_c and X^T S=[sT+sB,sT,w4]: beta(X,S)(1)=sT/100−sB/100.
4. For every natural n, n-by-2 real matrix X, response S and reals sT,sB, assuming in order det(X^T X) is a unit, X^T X=[151 75;75 75], and X^T S=[sT+sB,sT]: beta(X,S)(1)=sT/75−sB/76.
5. The following ten unconditional Arm values hold, followed by the rounding assertions in the last paragraph.

| nT,nB | sT,sB | exact Arm | printed v |
|---|---|---|---|
| 150,150 | 105,88 | 17/150 | 0.113 |
| 150,150 | 98,75 | 23/150 | 0.153 |
| 150,150 | 90,68 | 11/75 | 0.147 |
| 150,150 | 68,49 | 19/150 | 0.127 |
| 100,100 | 67,35 | 8/25 | 0.320 |
| 100,100 | 63,26 | 37/100 | 0.370 |
| 100,100 | 58,19 | 39/100 | 0.390 |
| 100,100 | 34,11 | 23/100 | 0.230 |
| 75,76 | 72,75 | −51/1900 | −0.027 |
| 75,76 | 68,73 | −307/5700 | −0.054 |

For every pair (x,v) in precisely the finite set of ten last-two-column pairs, x≠0, Prec(x,v), and not Prec(−x,v). No assertion extracts these values or sufficient statistics from an external dataset.

## SAP.P041.T10

Five clauses are conjoined.

1. For every real h0,a,b,g,C,L,T,w, in that order, b(C−L)+aT+gT(C−L)+w=Cb−bL+(a+Cg)T−gTL+w, and Ten(h0,b,a,g,C,L,T,w)=Year(h0,b,a,g,C−L,T,w). No positivity or binary-treatment assumptions occur here; it is an algebraic identity even for arbitrary real h0,T.
2. For every real a,g,C,L, exp(−g)=1/exp(g) and exp((a+Cg)−g(L+1))=exp((a+Cg)−gL)/exp(g). Also, for every real r>0, r<1 iff 1<1/r, and 1<r iff 1/r<1. This last universal assertion is nested inside the quantifiers a,g,C,L but does not depend on them.
3. Four independent universal statements about real r: if r lies in [0.9885,0.9895], then 1.0106<1/r<1.0117 and 1/r>1; if r lies in [0.9805,0.9815], then 1.0188<1/r<1.0199 and 1/r>1; if r lies in [1.0555,1.0565], then 0.9465<1/r<0.9475 and 1/r<1; if r lies in [1.0035,1.0045], then 0.9955<1/r<0.9966 and 1/r<1. Each interval hypothesis is supplied as a lower bound followed by an upper bound.
4. For every real g,V,s, assuming V>0 and then s=exp(g)sqrt(V): (1/exp(g))sqrt(V)=s/(exp(g))² and (−g)²/V=g²/V.
5. Tenure(2014,2009)=5; Tenure(2014,2008)=6; Ill(0,2009)=Ill(0,2008)=Ill(1,2009)=1; Ill(1,2008)=125/132; 132/125>1; 125/132<1; and their product equals 1.

No partial-likelihood maximizer, statistical fitting procedure, or p-value equality is quantified.

## SAP.P041.T11

The conclusion conjoins two clauses.

1. For every real h,s with I(0.691,h) then I(0.318,s), 0.4205≤P(W(h,s))≤0.4232. Independently, for all real h,s in the rectangle centered at (0.775,0.503), 0.6936≤P(W)≤0.6954. Independently, for all real h,s in the rectangle centered at (0.627,0.406), 0.4700≤P(W)≤0.4720. At the three exact centers, |W| differs from respectively 0.8032,0.3927,0.7209 by at most 0.00005, and P(W) differs from respectively 0.4219,0.6945,0.4710 by at most 0.00005.
2. On each of the three rectangles, separately universally quantifying h,s with its two interval hypotheses, |W(h,s)|<1.

There is no asserted rounding of the second p value to 0.70, and no comparison to a separate active-senator group, inference about a mechanism, or counterexample to an inference in this theorem.

## SAP.P041.T12

The conclusion is the conjunction of:

1. A(75,52)=4600/127, A(92,69)=200/7, A(62,32)=3000/47; these satisfy Round at 36,29,64 respectively; and 52/150<75/150, 69/150<92/150, 32/100<62/100.
2. It is false that all three assertions Round(R(75/150,52/150),36), Round(R(92/150,69/150),29), Round(R(62/100,32/100),64) hold together.

Clause 2 is one negated conjunction, not a conjunction of the three separate negations, and supplies no exact directional-percentage value. No input hypothesis or assertion about a Cox hazard ratio, empirical p value, or inferential conclusion occurs.
