# Blind reading of SAP.P026a

This file was written from `Defs.lean`, every `Defs/Part*.lean`, and the Challenge files, before opening `claims.json` or `record.json`. The statements below are readings, not endorsements. All theorems are in namespace `SAP.P026a`, and `Tk` asserts exactly `TkStatement`.

## Meaning of the underlying notation

`Fin n` is the set of integers from 0 through n-1; displayed vectors list coordinates starting at 0. `Bool` has the two values false (control, written 0 below) and true (treatment, written 1). Finite sums and products are Mathlib `Finset.sum` and `Finset.prod` over `Finset.univ`; `univ.erase i` excludes i, and `univ.filter p` keeps precisely the indices satisfying p. Thus off-diagonal sums below are over **ordered** pairs. `Fintype.card` is the actual finite cardinality. Finset subtypes used for fitting vectors contain precisely the members of that set. Function equality is equality at every argument.

The relevant Mathlib endpoints are `Algebra/BigOperators/Group/Finset/Defs.lean` (sum/product), `Data/Fintype/Defs.lean` (univ), `Data/Fintype/Card.lean` (card), `Data/Finset/Erase.lean`, `Data/Finset/Filter.lean`, and `Data/Fin/VecNotation.lean` (vector notation). The arithmetic is ordinary rational arithmetic in the explicit designs, and real arithmetic in the universally quantified laws. The generic helper definitions allow any linearly ordered field. Field division is total: Mathlib `Algebra/GroupWithZero/Basic.lean`, `div_zero`, gives a/0=0. Support hypotheses and explicit branches must therefore be read separately from the quotient notation. There are no measure integrals, infinite sums, limits, or limsups here.

For a finite outcome space Ω and finite index set I, an `AssignmentDesign` D is just weights p(w) and binary assignments T_i(w); it has no probability axioms by itself. Define

* E_D f = sum_w p(w) f(w) (`mean`).
* A_ai(w) = 1 if T_i(w)=a, and 0 otherwise (`armIndicator`).
* pi_ai = E_D A_ai (`inclusion`), and pi_abij = E_D(A_ai A_bj) (`jointInclusion`).
* `isProbability` means every p(w)>=0 and sum_w p(w)=1. `hasPositiveMarginals` means pi_1i>0 and pi_0i>0 for every i.
* Y_i(w)=x_i if T_i(w)=1, otherwise z_i (`response D x z`). All potential-outcome vectors are fixed functions.
* H_a(y)(w)=sum_i A_ai(w)y_i/pi_ai (`htSum`), H_N(x,z)=(H_1(x)-H_0(z))/N (`htContrast`), and tau_N(x,z)=(sum_i x_i-sum_i z_i)/N (`averageEffect`). Here a natural number denominator is cast into the field.
* G_a(y,f)(w)=sum_i [A_ai y_i/pi_ai-A_ai f_i(w)/pi_ai+f_i(w)] (`adjustedSum`); G_N(x,z,f)=(G_1(x,f)-G_0(z,f))/N (`adjustedContrast`).
* Cov_D(f,g)=E_D(fg)-E_D f E_D g; Var_D(f)=Cov_D(f,f). These are the definitions even for designs that are not probability laws.
* d_ij=E_D 1[T_i!=T_j] (`disagreementProbability`). Directed support means pi_10ij>0 for all distinct i,j. Write O(F)=sum_{i!=j} F_ij, and Z_ab(F)=sum_{i!=j, pi_abij=0} F_ij (`unavailablePairSum`).

To expand every estimator, put q_abij=pi_abij+1[pi_abij=0], and

    Q_abij(w) = (A_ai A_bj/q_abij)
                 (pi_abij-pi_ai*pi_bj)(Y_i/pi_ai)(Y_j/pi_bj).

This is `estimatedPairTerm`; in particular its replacement denominator is 1 when the joint probability is zero. The following are all definitions, not additional assumptions:

    V_N(w) = {sum_i [A_1i(Y_i/pi_1i)^2+A_0i(Y_i/pi_0i)^2]
              + O(Q_11+Q_00-2Q_10)
              + Z_11((A_1i Y_i^2/pi_1i+A_1j Y_j^2/pi_1j)/2)
              + Z_00((A_0i Y_i^2/pi_0i+A_0j Y_j^2/pi_0j)/2)}/N^2.

`V_N` is `printedVarianceEstimate D N x z`. Define

    C0(w) = O(if pi_10ij=0 then 0 else
                (A_1i A_0j/pi_10ij)(pi_10ij-pi_1i*pi_0j)
                  (Y_i/pi_1i)(Y_j/pi_0j))
            -sum_i A_1i Y_i^2/(2pi_1i)-sum_i A_0i Y_i^2/(2pi_0i),
    Delta(w) = Z_10(A_1i Y_i^2/pi_1i+A_0j Y_j^2/pi_0j),
    Cstar = C0-Delta/2,
    Vstar_N = V_N+Delta/N^2.

These respectively expand `covarianceWithZeroOmission`, `directedPairCorrection`, `repairedCovarianceEstimate`, and `repairedVarianceEstimate`. C0 is explicitly a continuation omitting zero directed joints; it is not a partial-valued undefined expression.

For fixed vectors y,x,z, the population and arm-estimator definitions are

    W_a(y) = sum_i pi_ai(1-pi_ai)(y_i/pi_ai)^2
              +O((pi_aaij-pi_ai*pi_aj)(y_i/pi_ai)(y_j/pi_aj)),
    K(x,z) = O((pi_10ij-pi_1i*pi_0j)(x_i/pi_1i)(z_j/pi_0j))-sum_i x_i z_i,
    L(x,z) = O((pi_10ij-pi_1i*pi_0j)(x_i/pi_1i)(z_j/pi_0j))
              -sum_i x_i^2/2-sum_i z_i^2/2,
    B_a(y) = sum_i pi_ai(1-pi_ai)(y_i/pi_ai)^2
              +sum_{i!=j, pi_aaij>0}
                   (pi_aaij-pi_ai*pi_aj)(y_i/pi_ai)(y_j/pi_aj)
              +Z_aa((y_i^2+y_j^2)/2),
    U_a(w) = sum_i A_ai(1-pi_ai)(Y_i/pi_ai)^2
              +sum_{i!=j, pi_aaij>0} Q_aaij(w)
              +Z_aa((A_ai Y_i^2/pi_ai+A_aj Y_j^2/pi_aj)/2),
    F_a(w) = sum_i A_ai(1-pi_ai)(Y_i/pi_ai)^2
              +O((A_ai A_aj/pi_aaij)(pi_aaij-pi_ai*pi_aj)
                    (Y_i/pi_ai)(Y_j/pi_aj)),
    S(x,z) = sum_{i,j: pi_10ij!=0}
                    (pi_10ij-pi_1i*pi_0j)(x_i/pi_1i)(z_j/pi_0j)
              -sum_{i,j: pi_10ij=0} x_i z_j,
    R(x,z) = sum_i(x_i-z_i)^2
              +Z_11((x_i+x_j)^2)/2+Z_00((z_i+z_j)^2)/2
              +Z_10((x_i-z_j)^2).

Their Lean names are, in order, `armPopulationVariance`, `populationCrossCovariance`, `populationCovarianceBound`, `armPopulationBound`, `armVarianceEstimate`, `fullSupportArmEstimate`, `splitPopulationCovariance`, `repairedBias`. The S sums include the diagonal. In U_a and F_a the observed outcomes are from x,z. Finally `appendixDisplay` is

    Apx(w) = sum_i A_1i(1-pi_1i)(Y_i/pi_1i)^2
               +sum_{i!=j, pi_11ij>0} Q_11ij(w)
               -sum_i A_1i Y_i^2/(2pi_1i)-sum_i A_0i Y_i^2/(2pi_0i).

`UnitLaw I` is a real probability law on **all** binary vectors w:I->Bool, with nonnegative normalized weights and positive marginals in both arms for every i. Zero weights are allowed. Its design uses T_i(w)=w_i. `ClusterLaw U C` is a fixed surjection c:U->C together with a `UnitLaw C`. Its cluster design uses cluster assignments directly; its unit design uses T_i(w)=w_{c(i)}. Its total of y in cluster k is ybar_k=sum_{i:c(i)=k} y_i. `fiberTotal` is the same fiber sum for a specified map without requiring surjectivity.

For general-valued finite random variables f,g, `finiteIndependent D f g` means, for **every** pair of functions u from the range type of f to the scalar field and v from the range type of g to that field,

    E_D[u(f) v(g)] = E_D[u(f)] E_D[v(g)].

`fittingResponses D J x z` is the full vector (Y_j)_{j in J}; `fittingIndicators D J` is the full binary vector (T_j)_{j in J}. `independentAssignments` means product expectation factors for all families F_i:Bool->R. `independentBlocks D c` means the analogous factorization for all families of functions of each full within-block assignment vector, with blocks indexed by a finite type B (empty fibers allowed).

## Explicit designs and the numerical population

All following laws are rational-valued and uniform on the displayed list, whose row order matters for pointwise output vectors.

* A=`asymmetricPairLaw`: Ω=Fin 3, I=Fin 2, rows 00, 01, 11, each of weight 1/3.
* B=`asymmetricSixLaw`: Ω=Fin 14, I=Fin 6, rows
  000111, 001011, 001101, 001110, 010011, 010101, 010110,
  011001, 011010, 011100, 110001, 110010, 110100, 111000,
  each of weight 1/14.
* X6=`xorSixLaw`: Ω=Fin 4, I=Fin 6, rows
  010101, 011010, 100110, 101001, each of weight 1/4.
* X3=`xorThreeLaw`: Ω=Fin 4, I=Fin 3, rows 000, 011, 101, 110, each of weight 1/4.
* D4=`twoOfFourLaw`: Ω=Fin 6, I=Fin 4, rows
  1100, 1010, 1001, 0110, 0101, 0011, each of weight 1/6.

Let P(u,v)=u+v-2uv (`xorFitPolynomial`). With outcomes x=1,z=0, `xorSixFit` is

    (P(Y_2,Y_4),1-P(Y_2,Y_4),P(Y_0,Y_4),1-P(Y_0,Y_4),
     P(Y_0,Y_2),1-P(Y_0,Y_2)).

`xorThreeFit` is (P(Y_1,Y_2),P(Y_0,Y_2),P(Y_0,Y_1)); `productFit` is (0,0,Y_0 Y_1).

The numerical law D=`paperTableDesign` has 10 clusters and 90 equally weighted assignments: independently choose two of clusters 0..3 and two of clusters 4..9. The first choice has D4's row order; the second enumerates lexicographically the 15 pairs (0,1),(0,2),...,(4,5) within six positions (`paperTwoOfSix`). There are 16 units with

    c = (0,0,1,1,2,3,4,4,4,5,5,6,6,7,8,9),
    y = (1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0),
    X = (4,0,4,1,4,2,4,1,2,5,4,1,4,2,2,3).

The unit design lifts each cluster's assignment to its units. The specified prediction f_i (`paperTableLinearPrediction`) is 1/4+X_i/8 on i<6, and 70/93+X_i/31 on i>=6. `paperTableLinearResidual` is e_k=sum_{i:c(i)=k}(y_i-f_i). No least-squares characterization is part of the definition.

For each w, write within-block centered vectors Xc_i=X_i-5/2 and yc_i=y_i-5/6 on i<6, Xc_i=X_i-14/5 and yc_i=y_i-3/5 otherwise. Let Tc_i(w)=A_1i(w)-the mean treatment indicator over the unit's block (6 or 10 units, respectively). Then

    r_i(w)=Tc_i(w)-[sum_j Xc_j Tc_j(w)/sum_j Xc_j^2] Xc_i,
    beta(w)=sum_i r_i(w)yc_i/sum_i r_i(w)^2.

These are `paperFeTreatmentResidual` and `paperFeEstimate`. The additionally defined `paperFeXCoefficient` is sum_i Xc_i(yc_i-beta Tc_i)/sum_i Xc_i^2, and `paperFeFitted` is the block y mean plus beta Tc_i plus that X coefficient times Xc_i. The statements do not otherwise use these last two definitions.

`paperTableClusterY` is q=(2,2,1,0,2,2,2,0,0,0); `paperTablePriorResidual` is t=(1,1,1/2,-1/2,1/2,1,1,-1/2,-1/2,-1/2). `appendixNullOutcomes` is (1,2,4,7).

`roundsToThree(v,r)` means r-1/2000<=v<r+1/2000. `sdRoundsToThree(v,r)` means (r-1/2000)^2<=v<(r+1/2000)^2; it does not take a square root or itself require r>=0. The numerical uses have positive r.

## T1

This is a closed conjunction about A and B; there are no input hypotheses.

For A it asserts all of:

1. A is a probability law with positive marginals.
2. For every i,j in Fin 2, if i!=j then d_ij>0, pi_11ij>0, and pi_00ij>0.
3. pi_1001=0 and pi_1010=1/3. For every w, A_10(w)A_01(w)=0.
4. With x=z=(1,1) and N=2, H_N has values (-9/4,0,9/4), and V_N has values (57/16,3/2,57/16), in row order, for every w.
5. E H_N=0, Var(H_N)=27/8, E V_N=23/8, and 23/8<27/8.
6. Cov(H_1(x),H_0(z))=-13/4, E C0=-9/4, and -13/4<-9/4.

For B it asserts:

1. B is a probability law with positive marginals; for every w, exactly three indices are treated.
2. For every distinct i,j in Fin 6, d_ij>0, pi_11ij>0, pi_00ij>0, and pi_10ij=0 iff (i=0 and j=1).
3. With x=z=1 and N=6, Var(H_N)=9/700, E V_N=-269/6300, and -269/6300<9/700.
4. Cov(H_1(1),H_0(1))=27/175 and E C0=202/175.

## T2

Each of the following universal clauses starts afresh: for every finite nonempty U and C (with decidable equality), every E:ClusterLaw U C, then a hypothesis `hseparated` that d_cd>0 for every distinct c,d. Write n=|U| and xbar,zbar,rbar for E's cluster totals. There is no directed-support or same-arm-support hypothesis unless stated in the individual clause.

1. After E and hseparated, for every i,j:C and proof i!=j, d_ij=pi_10ij+pi_10ji.
2. With the same quantifier order, d_ij>0 iff (pi_10ij>0 or pi_10ji>0).
3. After E,hseparated, for all x,z:U->R, Cov(H_1(xbar),H_0(zbar))=K(xbar,zbar).
4. For all x,z after those premises,

       n^2(E V_n-Var H_n)=sum_i(xbar_i-zbar_i)^2
          +Z_11((xbar_i+xbar_j)^2)/2+Z_00((zbar_i+zbar_j)^2)/2
          -2Z_10(xbar_i zbar_j).

5. For all x,z after those premises,

       E Cstar-Cov(H_1(xbar),H_0(zbar))
          =-sum_i(xbar_i-zbar_i)^2/2-Z_10((xbar_i-zbar_j)^2)/2,

   and E Cstar<=Cov(H_1(xbar),H_0(zbar)).
6. For all x,z, n^2(E Vstar_n-Var H_n)=R(xbar,zbar), and Var H_n<=E Vstar_n.
7. After E,hseparated, quantify c:U->R and **then assume** pi_11ij>0 and pi_00ij>0 for all distinct i,j. With xbar=zbar=cbar,

       E Vstar_n-Var H_n=Z_10((cbar_i-cbar_j)^2)/n^2,
       E Vstar_n=Var H_n iff
          for every i,j, i!=j and pi_10ij=0 imply cbar_i=cbar_j.

8. After E,hseparated, quantify x,z, an assignment w:C->Bool, and then assume its weight is strictly positive. Pointwise,

       Vstar_n(w)=[U_1(w)+U_0(w)-2Cstar(w)]/n^2.

9. After E,hseparated, for all x,z,r:U->R, with residual totals v=xbar-rbar and t=zbar-rbar,

       n^2[E Vstar_n(v,t)-Var G_n(xbar,zbar,rbar)]=R(v,t),
       Var G_n(xbar,zbar,rbar)<=E Vstar_n(v,t).

   The prediction in G is fixed across assignments.
10. For all x,z after E,hseparated, R(xbar,zbar)>=0.
11. A separate closed clause for B, N=6 and x=z=(1,2,1,1,1,1), asserts Var H_N=2759/12600, E V_N=151/1400, E Vstar_N=3109/12600, and 2759/12600<3109/12600.
12. A fresh universal clause has finite nonempty U,C and E, but **no hseparated**. For every x,z,r, the cluster totals of x-r and z-r equal xbar-rbar and zbar-rbar, respectively, and as functions of assignments G_n(xbar,zbar,rbar)=H_n(totals(x-r),totals(z-r)).
13. A closed clause asserts d_01>0 and pi_1001=0 for A.
14. A closed clause asserts the B witness in clause 11 has E V_N-Var H_N=-1/9 and E Vstar_N-Var H_N=1/36.

## T3

1. For every finite nonempty U,C, E:ClusterLaw U C, hseparated as above, **then** directed support pi_10ij>0 for distinct i,j, and then all x,z:U->R:

       E C0-Cov(H_1(xbar),H_0(zbar))=-sum_i(xbar_i-zbar_i)^2/2,
       E C0<=Cov(H_1(xbar),H_0(zbar)),
       n^2(E V_n-Var H_n)=sum_i(xbar_i-zbar_i)^2
          +Z_11((xbar_i+xbar_j)^2)/2+Z_00((zbar_i+zbar_j)^2)/2,
       Var H_n<=E V_n.

   Within this conclusion: if all xbar_i=zbar_i, and then all distinct pairs have positive 11 and 00 joints, E V_n=Var H_n.
2. With the same law/support quantifiers, then all x,z,r, Var G_n(xbar,zbar,rbar)<=E V_n(xbar-rbar,zbar-rbar). If the cluster arm totals agree and both same-arm supports are positive off the diagonal, equality holds.
3. A closed clause: D is a probability law with positive marginals and directed support. For all distinct i,j:Fin 10, pi_10ij>=1/6, pi_11ij>=1/15, pi_00ij>=1/6, and d_ij>0. Separately for each of the three inequalities there exist distinct i,j attaining equality (the witnesses need not coincide).
4. The same universal residual aggregation and G=H function identity as T2 clause 12, without hseparated or directed support.

## T4

Closed conjunction, with no input hypotheses. All potential outcomes below are x=1,z=0.

For X6:

1. It is a probability law with positive marginals; for every unit both marginals equal 1/2.
2. For all i,j:Fin 6, if floor(i/2)!=floor(j/2), then for every a,b:Bool, pi_abij=1/4. No such assertion is made within one of the three two-unit pairs.
3. Every assignment treats three units. For every w,i the specified xorSixFit equals A_1i(w).
4. For every i, Cov(A_1i,fit_i)=1/4.
5. For every w, G_1(1,fit)=3, G_0(0,fit)=3, G_6(1,0,fit)=0, and H_6(1,0)=1.
6. tau_6(1,0)=1 and E G_6-tau_6=-1.

For X3:

1. It is a probability law with positive marginals. For every distinct i,j and every a,b, pi_abij=1/4.
2. For every w,i, xorThreeFit_i(w)=A_1i(w), and for every i its covariance with A_1i is 1/4.
3. E G_3(1,0,xorThreeFit)=0.
4. Cov(A_12,productFit_2)=-1/8, E G_3(1,0,productFit)=7/6, and tau_3(1,0)=1.

## T5

All laws here are real UnitLaws.

1. For every finite nonempty I, then E:UnitLaw I, arbitrary type Theta, i:I, finite J subset I, outcomes y1,y0:I->R, G:(J->R)->Theta, P:Theta->R, **then** assume T_i is finiteIndependent of the whole assignment vector T_J. Conclude T_i is independent of G(Y_J) and of P(G(Y_J)), and Cov(A_1i,P(G(Y_J)))=0. There is no separate assumption i not in J; the premise decides which instances are possible.
2. The same quantifiers in the same order and the same three conclusions, with the weaker premise that T_i is independent of the whole observed-response vector Y_J.
3. For every finite nonempty I, E, x,z:I->R, a family of fitting sets J_i, a family of deterministic maps G_i:(J_i->R)->R, **then** assume for every i that T_i is independent of the full assignment vector T_{J_i}. Put f_i(w)=G_i(Y_{J_i}(w)). Conclude E G_1(x,f)=sum_i x_i, E G_0(z,f)=sum_i z_i, and E G_|I|(x,z,f)=tau_|I|(x,z).
4. For every finite nonempty I,E, then i,J,x,z, real a, coefficients b:J->R, **then** assume T_i independent of T_j for every j in J. Conclude

       Cov(A_1i,a+sum_{j in J}b_jY_j)
         =sum_{j in J} b_j(x_j-z_j)Cov(A_1i,A_1j)=0.

   The two equalities are a conjunction; both are under the independence premise.
5. For every finite I,E, then assume independentAssignments, then for every i:I, T_i is independent of the full assignment vector on I minus {i}. Nonemptiness is not an explicit typeclass assumption in this clause, but an i is quantified.
6. For every finite I,B, E, a map c:I->B, **then** independentBlocks(E,c), **then** every i:I, T_i is independent of the full assignment vector on all j with c(j)!=c(i). There is no surjectivity assumption on c.

## T6

Closed assertions about the numerical D, prediction, residual vector e, and beta defined above:

1. sum_i Xc_i^2>0, and for every one of the 90 assignments sum_i r_i(w)^2>0.
2. e=(1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93).
3. With x=z=e,N=16, E H_N=0, Var H_N=38307/634880, E V_N=38307/634880, and Var V_N=2400328658503/15687787688755200.
4. Var H_N>265/10000 and >(1625/10000)^2; Var V_N>(75/10000)^2.
5. -145/10000<E beta<-135/10000; 775/10000<Var beta<785/10000; sdRoundsToThree(Var beta,279/1000); sdRoundsToThree(Var beta+(E beta)^2,279/1000); and 38307/634880<Var beta+(E beta)^2.

No fit-optimality statement is asserted. The FE moments are bounded and rounded, not asserted as explicit exact rational equalities.

## T7

Closed assertions for the same D:

1. The same two denominator-positivity assertions as T6.
2. The same four exact e-based moments as T6 clause 3. In addition sdRoundsToThree(38307/634880,246/1000), roundsToThree(38307/634880,60/1000), and sdRoundsToThree(2400328658503/15687787688755200,12/1000).
3. The same seven bounds, rounding assertions, and strict comparison for beta as T6 clause 5.
4. For every cluster k, q_k is the fiber sum of y and t_k is the fiber sum of y-1/2. With N=16:

       E H_N(q,q)=0, Var H_N(q,q)=353/1920, E V_N(q,q)=353/1920,
       E H_N(t,t)=0, Var H_N(t,t)=233/2560, E V_N(t,t)=233/2560.

   Finally roundsToThree(353/1920,184/1000) and roundsToThree(233/2560,91/1000).

## T8

1. For every finite nonempty U,C, ClusterLaw E, then hseparated, then x,z:U->R: Cov(H_1(xbar),H_0(zbar))=K(xbar,zbar).
2. Independently with the same quantifiers: Cov(H_1(xbar),H_0(zbar))-L(xbar,zbar)=sum_i(xbar_i-zbar_i)^2/2.
3. For every such U,C,E, then hseparated, then directed support, then x,z:

       E C0=L(xbar,zbar), E C0<=Cov(H_1(xbar),H_0(zbar)),
       E C0=Cov(H_1(xbar),H_0(zbar)) iff every xbar_i=zbar_i.

4. Independently with the quantifiers of clause 1 (no directed support), L(xbar,zbar)<=Cov(H_1(xbar),H_0(zbar)).

## T9

Closed conjunction for D4 and x=z=(1,2,4,7):

1. D4 is a probability law with positive marginals and directed support.
2. For every distinct i,j:Fin 4, pi_11ij=1/6, pi_00ij=1/6, and pi_10ij=1/3.
3. For every w in D4's row order, Apx(w) equals the corresponding entry of (-68,-52,2,-62,-20,-52); E Apx=-42.
4. Cov(H_1(x),H_0(x))=-28, K(x,x)=-28, E C0=-28, Var H_1(x)=28, and -42!=-28.
5. L(x,x)=-28.

## T10

Every clause quantifies finite U,C with decidable equality and nonempty U, then E:ClusterLaw U C. Nonempty C follows from E and nonempty U, rather than being a separate typeclass premise.

1. For every y:U->R, a:Bool, and w:C->Bool, H_a(y) using E's unit design equals H_a(ybar) using its cluster design.
2. For every x,z:U->R and w:C->Bool, H_|U|(x,z) in the unit design equals H_|U|(xbar,zbar) in the cluster design.
3. For every y,a,w, define

       groupedUnits=sum_c sum_{i:c(i)=c} A_ai(unit)y_i/pi_ai(unit),
       groupedClusters=sum_c sum_{i:c(i)=c} A_ac(cluster)y_i/pi_ac(cluster),
       factored=sum_c A_ac(cluster)[sum_{i:c(i)=c} y_i]/pi_ac(cluster).

   Then the unit-design H_a equals groupedUnits, groupedUnits equals groupedClusters, groupedClusters equals factored, and factored equals the cluster-design H_a(ybar). All assignments are included, even zero-weight ones.

## T11

Every clause quantifies finite nonempty U,C, ClusterLaw E, and then hseparated.

1. For every a:Bool and then y:U->R, Var H_a(ybar)=W_a(ybar).
2. For every a and then x,z:U->R, set y=xbar if a=true, zbar otherwise. Conclude

       B_a(y)-Var H_a(y)=Z_aa((y_i+y_j)^2)/2,
       E U_a=B_a(y), Var H_a(y)<=E U_a.

   If, additionally, pi_aaij>0 for every distinct i,j, conclude E U_a=Var H_a(y).
3. For every a, then x,z, **then assume** pi_aaij>0 for every distinct i,j. Conclude E F_a=Var H_a(if a then xbar else zbar).

## T12

Each clause independently quantifies a finite nonempty I with decidable equality, then E:UnitLaw I. No pairwise support or independence assumption is made.

1. For every x,z:I->R, with n=|I|,

       Var H_n(x,z)=[Var H_1(x)+Var H_0(z)-2Cov(H_1(x),H_0(z))]/n^2.

2. For every a:Bool and then y:I->R, all three equalities hold:

       Var H_a(y)=sum_i sum_j Cov(A_ai,A_aj)(y_i/pi_ai)(y_j/pi_aj),
       Var H_a(y)=sum_i Var(A_ai)(y_i/pi_ai)^2
                    +O(Cov(A_ai,A_aj)(y_i/pi_ai)(y_j/pi_aj)),
       Var H_a(y)=W_a(y).

3. For every a,b:Bool, then x,z:I->R,

       Cov(H_a(x),H_b(z))
         =sum_i sum_j (pi_abij-pi_ai*pi_bj)(x_i/pi_ai)(z_j/pi_bj).

4. For every x,z:I->R,

       Var H_n(x,z)=[W_1(x)+W_0(z)-2S(x,z)]/n^2.

5. For every x,z:I->R, Cov(H_1(x),H_0(z))=S(x,z).

