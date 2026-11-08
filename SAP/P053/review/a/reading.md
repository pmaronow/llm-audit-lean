# Blind reading of the Challenge

This file was written using only `SAP/P053/Defs.lean`, all seven `Defs/Part*.lean` files, `SAP/P053/Challenge.lean`, `Challenge/Part1.lean`, and the Mathlib sources identified below. Neither `claims.json` nor `record.json` had been opened when this reading was saved. The Challenge contains eight theorem stubs. Their propositions, rather than the prose attached to them, are expanded here.

## Common objects and conventions

* `Fin N` consists of the integers 0 through N−1. A `Finset` is a finite set with no repetitions. Complements are taken in the entire finite unit type. `support k` is the set of **all** k-element subsets of that type; there are binomial(N,k) such subsets. On `Fin (n1+n0)` this support is nonempty for every pair of natural arm sizes, even if an arm size is zero.
* For Boolean outcomes y, write a_y(s) for the number of true entries in s and M_y for the total number of true entries. These are ordinary natural-number counts. Put
  `C(n1,n0,M,a) = (a, n1−a, M−a, n0−M+a)` with **all four coordinates computed in the integers**, and
  `D_y(s) = a_y(s)/n1 − (M_y−a_y(s))/n0`, with the subtraction and division in the real numbers in this formula.
* `reconstruct(n1,n0,M,t) = (n1*n0*t+n1*M)/(n1+n0)`. For a function h from integer quadruples to S, `tableFactor(n1,n0,M,h)(t)` is h evaluated at `(b,n1−b,M−b,n0−M+b)`, where b is the integer floor of `reconstruct(n1,n0,M,t)`. This is defined on every real t, including unattainable statistic values.
* `canonical(n,a)` is the length-n Boolean vector whose first a entries are true and whose remaining entries are false (if a exceeds n, every entry is true). `orderedBinarySample(y,s,hs)` lists the outcomes on s in increasing unit-label order, with hs certifying its length.
* For any real-valued statistic T on subsets, `upperP(k,T,z)` is `#{w in support k : T(z) ≤ T(w)} / #support k`. Thus ties count in the upper tail. All uses in the Challenge have a nonempty support.
* A `Population` P specifies natural sizes n1,n0 and two fixed real outcome vectors Y1,Y0 on `Fin N`, N=n1+n0. For any finite subset s and real vector y, `sampleMean(s,y)=sum_{i in s} y_i / |s|`, `centeredSS(s,y)=sum_{i in s}(y_i−sampleMean(s,y))²`, and `sampleVariance(s,y)=centeredSS(s,y)/(|s|−1)`, with the denominator subtraction in the **reals**. The population mean and variance use the full unit set and hence divisor N or N−1 respectively.
* Let tau(P)=mean(Y1)−mean(Y0), delta_i=Y1_i−Y0_i, V1(P)=sampleVariance(univ,Y1), V0(P)=sampleVariance(univ,Y0), and Vdelta(P)=sampleVariance(univ,delta). `SharpNull P` means Y1_i=Y0_i for every unit. `ConstantEffects P` means delta_i=tau(P) for every unit.
* For assignment z, `observed(P,z)_i` equals Y1_i on z and Y0_i off z. `difference(P,z,y)` is the mean on z minus the mean on its complement. The estimate H(P,z) is that difference for the observed outcome vector.
* For any real X on assignments, randomization mean is the arithmetic mean of X over `support n1`; randomization variance RVar(P,X) is the arithmetic mean of `(X−randomizationMean(P,X))²` over that support. Randomization probability of an event is the fraction of supported assignments satisfying it. These definitions use the uniform complete-randomization distribution, not an independently supplied probability measure.
* Set RSS(P,z)=centeredSS(z,observed)+centeredSS(z-complement,observed). The three variance estimators are
  `O(P,z)=RSS(P,z)/(N−2)*(1/n1+1/n0)` (pooled OLS),
  `Ney(P,z)=sampleVariance(z,observed)/n1+sampleVariance(z-complement,observed)/n0`, and
  `F(P,z)=N*sampleVariance(univ,observed)/(n1*n0)` (Fisher). Subtractions here are real subtractions.
* A sequence E: natural numbers → Population has `Regularity E p v1 v0 vt tauInf` exactly when: N_k→∞; eventually n1_k≥2 and n0_k≥2; 0<p<1; n1_k/N_k→p; V1_k→v1; V0_k→v0; Vdelta_k→vt; tau_k→tauInf; and there exists a real B≥0 such that for **every** k,
  `(1/N_k)*sum_i(Y1_{ki}^4+Y0_{ki}^4) ≤ B`.
  The structure has no positivity field for the variance limits, no assumed consistency result, and no assumed central limit theorem. It uses a bound on raw, not centered, fourth moments. Eventual arm bounds allow arbitrary finitely many early degenerate populations.
* `InProbability E X c` means: for **every real epsilon>0**, the uniform randomization probability of `epsilon < |X(k,z)−c|` tends to zero as k→∞. Write `X→p c` for this. `LittleOInvSize E X` means `N_k*X(k,z)→p 0`; write this as `X=o_p(1/N_k)`. This is not a deterministic little-o assertion or an almost sure assertion.
* Put `L_N(p,v1,v0)=v1/p+v0/(1−p)` and `L_O(p,v1,v0)=v1/(1−p)+v0/p`. In formulas below, let
  `A_k=V1_k/n0_k+V0_k/n1_k`, `B_k=V1_k/n1_k+V0_k/n0_k`, and `R_k=RVar(E_k,H(E_k,·))`.
* `PositiveOLS E` means that there exists K such that, for every k≥K and **every** z in that population's assignment support, O(E_k,z)>0. It is stronger than positivity with probability tending to one.
* `Phi(t)=standardNormalCDF(t)` is the probability of the real interval (−∞,t] under Mathlib's Gaussian measure with mean 0 and **variance** 1. `q(alpha)=normalCritical(alpha)` is `inf {t : 1−alpha/2 ≤ Phi(t)}`, a real infimum. The theorem only uses q when 0<alpha<1; for that range the set is nonempty and bounded below.
* Lean's real division is total, with x/0=0; its real square root is zero on nonpositive arguments; real infima are total even on empty or unbounded-below sets. These conventions are part of the definitions, but the positive-arm hypotheses/eventual arm bounds, positive variance conditions, and alpha bounds delimit the intended uses. No integral of a possibly nonintegrable outcome vector occurs: all randomization averages are finite sums.

Mathlib semantics checked directly: `Data/Finset/Powerset.lean:198` (`powersetCard`, its membership and cardinality formulas); `Data/Finset/Sort.lean:194` (`orderEmbOfFin`); `Order/Monotone/Defs.lean:99` (`StrictMonoOn`); `Order/Filter/Defs.lean:422` (`Tendsto` as filter-map convergence); `Order/Filter/AtTopBot/Defs.lean:39` (`atTop`); `Probability/Distributions/Gaussian/Real.lean:222` (`gaussianReal`, including its probability-measure instance); `Algebra/Order/Floor/Defs.lean:248` (integer floor); `Algebra/GroupWithZero/Basic.lean:402` (division by zero); `Analysis/Real/Sqrt.lean:142,268` (real square root on nonpositive inputs). Paths here are relative to `/home/ubuntu/sal/deps/mathlib/Mathlib/`.

## SAP.P053.T1

Universally quantified over an arbitrary type S (no nonemptiness assumption). For **every** natural n1,n0, assuming n1>0 and n0>0, and then for **every** Boolean vector y on n1+n0 labelled units, all six following clauses hold, with M=M_y:

1. For every supported assignment s,
   `D_y(s)=((n1+n0)*a_y(s)−n1*M)/(n1*n0)` and
   `reconstruct(n1,n0,M,D_y(s))=a_y(s)`.
2. For every pair of supported assignments s,t, `D_y(s)=D_y(t)` iff `a_y(s)=a_y(t)`, and `a_y(s)=a_y(t)` iff `C(n1,n0,M,a_y(s))=C(n1,n0,M,a_y(t))`.
3. For **every** h: integer quadruples → S there exists g: reals → S such that g is exactly `tableFactor(n1,n0,M,h)` and, for **every** Boolean vector yy on the same units satisfying M_yy=M and **every** supported assignment s,
   `h(C(n1,n0,M,a_yy(s)))=g(D_yy(s))`.
   The same g works for all yy with that total; it is not chosen after yy or s.
4. For **every** F taking a Boolean length-n1 vector and a Boolean length-n0 vector into S, if for **every** x1,x0 and pair of permutations p1,p0, `F(x1 composed with p1,x0 composed with p0)=F(x1,x0)`, then there exists g: reals → S such that for **every** supported s there exist cardinality certificates ht:|s|=n1 and hc:|s-complement|=n0 with both
   `F(ordered sample on s,ordered sample on s-complement)=F(canonical(n1,a_y(s)),canonical(n0,M−a_y(s)))` and
   `F(ordered sample on s,ordered sample on s-complement)=g(D_y(s))`.
   Here g may depend on y and F. The natural subtraction M−a_y(s) is exact since s is a subset of the population.
5. For **every** h: integer quadruples → S, every length-n1 and length-n0 Boolean vectors x1,x0, and every pair of permutations p1,p0, h applied to the four success/failure counts of the permuted vectors equals h applied to those counts of the original vectors. This is the converse symmetry assertion for table statistics.
6. For **every** statistic T from the subtype of n1-element assignments into S,
   `(there exists g: reals → S such that for every assignment s, T(s)=g(D_y(s)))`
   iff
   `(for every s,t, equality of C(n1,n0,M,a_y(s)) and C(n1,n0,M,a_y(t)) implies T(s)=T(t))`.

There is no assertion that every labelled statistic satisfies the table-constancy premise. The first three clauses have no symmetry assumption because h already takes only the table as input. Empty S does not make an existential conclusion impossible: the antecedent functions h,F,T then cannot exist, because their domains are nonempty.

## SAP.P053.T2

A conjunction of unconditional, explicit finite assertions and a universally quantified repeated family:

* On four units, y=(1,1,0,0), x=(1,0,1,0), treatment size 2, A={0,2}, B={1,2}. The support has size 6, both A and B are supported, both D_y values are 0, and both tables are (1,1,1,1). The label statistic `1_{0 in z}` takes values 1 at A and 0 at B. The difference in means for the Boolean product x AND y is 1/2 at A and −1/2 at B.
* There is **no** real function g such that for **every** supported z, `1_{0 in z}=g(D_y(z))`. Separately, there is **no** real function g such that for **every** supported z, `D_{x AND y}(z)=g(D_y(z))`.
* For **every** natural m and **every** certificate hm:m>0, use units `Fin m × Fin 4`, each block copying y,x. Let A_m be all pairs whose second coordinate belongs to A and B_m similarly. Treatment and control sizes are each 2m. A_m and B_m are supported; both D_y values are zero; both tables equal (m,m,m,m). The statistic indicating whether the particular unit (0,0) is treated is 1 at A_m and 0 at B_m. The product-outcome difference is 1/2 and −1/2 respectively. Both the allocation fraction (2m)/(4m) and total-success fraction M/(4m) equal 1/2. Neither of these two statistics factors through D_y on the whole repeated assignment support (two separate negated existentials, with g quantified before all assignments).
* Along m=k+1, for k running through all natural numbers, 4(k+1)→∞, the allocation fraction tends to 1/2, and the success fraction tends to 1/2. For **every** k, the average over the 4(k+1) units of `binaryReal(y)^4+binaryReal(y)^4` is at most 2. Here `binaryReal(true)=1`, `binaryReal(false)=0`.

The repeated-family statement does **not** contain a `Population` sequence, a `Regularity` certificate, outcome/effect variance limits, or an average-effect limit.

## SAP.P053.T3

All of the following hold:

1. On six units, y=(1,1,1,0,0,0), treatment size 3, there are respectively 1,9,9,1 assignments having treated success count a=0,1,2,3. On **every** supported z, `D_y(z)=(2*a_y(z)−3)/3`.
2. The support has size 20 and z_top={0,1,2} is supported. Its D_y is 1. Its inclusive upper-tail p-value for D_y is 1/20, and for |D_y| is 1/10. Therefore the first p-value is ≤1/20 and the second is not ≤1/20.
3. On the four-unit y=(1,1,0,0), treatment size 2, the support has size 6, and z_top={0,1}, z_bottom={2,3} are supported. Their D_y values are 1 and −1. At the top assignment the upper-tail p-values for D_y and |D_y| are respectively 1/6 and 1/3. At the bottom they are 1 and 1/3. For **every** other supported z, D_y(z)=0 and the corresponding p-values are 5/6 and 1.
4. For **every** natural n1,n0 with n1>0,n0>0, every **real** outcome vector y on n1+n0 units, and every real function g, let T(z)=mean(z,y)−mean(z-complement,y). If g is strictly increasing **on the attainable values** `{T(z):z in support n1}` (for every a,b in this set, a<b implies g(a)<g(b)), then for **every** supported z, `upperP(n1,g composed with T,z)=upperP(n1,T,z)`.

Thus the last clause is not confined to binary outcomes and does not require g to be increasing outside the finite attainable range.

## SAP.P053.T4

For **every** real p,S1,S0, assuming in order 0<p, p<1, S1≥0, S0≥0, the following identity and equivalence both hold:

`[S0²/p+S1²/(1−p)]−[S1²/p+S0²/(1−p)] = (S1²−S0²)*(2p−1)/(p*(1−p))`,

`S1²/p+S0²/(1−p) < S0²/p+S1²/(1−p)` iff
`(p>1/2 and S1>S0) or (p<1/2 and S1<S0)`.

S1,S0 are nonnegative standard-deviation parameters; no population or asymptotic sequence is quantified here.

## SAP.P053.T5

For **every** sequence E of populations and **every** real p,v1,v0,vt,tauInf, if `Regularity E p v1 v0 vt tauInf`, all five conclusions hold (quantification over epsilon inside each probability limit is as defined above):

1. `F(E_k,z)−[A_k+tau_k²/N_k]=o_p(1/N_k)`.
2. `O(E_k,z)−A_k=o_p(1/N_k)`.
3. `N_k*(F(E_k,z)−O(E_k,z))−tau_k² →p 0`.
4. `N_k*F(E_k,z) →p L_O(p,v1,v0)+tauInf²`.
5. `N_k*O(E_k,z) →p L_O(p,v1,v0)`.

No sharp null, constant-effect assumption, or positivity of either limiting variance is imposed. The argument vt in `FisherOLSAsymptotics` is unused, but the regularity premise still asserts the Vdelta limit.

## SAP.P053.T6

For **every** E and every real p,v1,v0,vt,tauInf, assume `Regularity E p v1 v0 vt tauInf`. Then these three implications hold together:

1. **If** tau_k→0, **then** `F(E_k,z)−O(E_k,z)=o_p(1/N_k)`; and **if additionally** L_O(p,v1,v0)>0 and `PositiveOLS E`, **then** `F(E_k,z)/O(E_k,z)→p 1`.
2. **If** `ConstantEffects(E_k)` for **every** k, **then** `O(E_k,z)−R_k=o_p(1/N_k)` and `N_k*(F(E_k,z)−R_k)−tau_k²→p 0`.
3. **If** `SharpNull(E_k)` for **every** k, **and** v0>0, **and** `PositiveOLS E`, **then** both:
   * for **every real** t, the randomization probability that `H(E_k,z)/sqrt(O(E_k,z)) ≤ t` tends to Phi(t);
   * for **every real** alpha, if 0<alpha<1, the randomization probability that `q(alpha)<|H(E_k,z)|/sqrt(O(E_k,z))` tends to alpha.

The positivity conditions are local to the indicated implications; they are not extra premises of every regularity statement. No conditional Fisher-randomization distribution, Fisher critical value, p-value, rejection-rule, or equivalence-of-tests assertion occurs in the proposition. All division and square-root statistics are real-valued, not extended-real-valued.

## SAP.P053.T7

For **every** E and real p,sigma1,sigma0,vt,tauInf, assume sigma1≥0, sigma0≥0, and `Regularity E p sigma1² sigma0² vt tauInf`. All the following hold, with v1=sigma1²,v0=sigma0²:

1. `Ney(E_k,z)−B_k=o_p(1/N_k)`.
2. `O(E_k,z)−Ney(E_k,z)−(A_k−B_k)=o_p(1/N_k)`.
3. `N_k*O(E_k,z)→p L_O(p,v1,v0)` and `N_k*Ney(E_k,z)→p L_N(p,v1,v0)`.
4. `L_O(p,v1,v0)−L_N(p,v1,v0)=(v1−v0)*(2p−1)/(p*(1−p))`.
5. If these two limits are unequal, then v1≠v0 and p≠1/2; also, separately, if these limits are unequal, then sigma1≠sigma0 and p≠1/2.
6. **If additionally** tau_k→0, then
   `F(E_k,z)−Ney(E_k,z)−(A_k−B_k)=o_p(1/N_k)`,
   `N_k*F(E_k,z)→p L_O(p,v1,v0)`, and
   `N_k*Ney(E_k,z)→p L_N(p,v1,v0)`.

The sigma nonnegativity assumptions concern standard-deviation parameterization, not positivity. No finite-sample order of the estimators is asserted.

## SAP.P053.T8

This theorem conjoins a general implication, a family of finite equalities, a particular sequence's regularity and limits, and a numerical inequality.

First, for **every** E and every real p,v1,v0,vt,tauInf, if `Regularity E p v1 v0 vt tauInf`, then:

* `N_k*R_k→L_N(p,v1,v0)−vt`, `L_N(p,v1,v0)−vt ≤ L_N(p,v1,v0)`, and `N_k*Ney(E_k,z)→p L_N(p,v1,v0)`.
* **If also** `ConstantEffects(E_k)` for **every** k, then: for **every** k, V1_k=V0_k and Vdelta_k=0; v1=v0 and vt=0; `N_k*R_k→L_N(p,v1,v0)`; `L_N(p,v1,v0)=L_O(p,v1,v0)`; `O(E_k,z)−Ney(E_k,z)=o_p(1/N_k)`; and for **every** k, `sqrt(V1_k)=sqrt(V0_k)` and `sqrt(Vdelta_k)=0`.

Second, for **every** natural k, put r=k+1 and define the explicit population P with n1=2r,n0=8r,N=10r, Y0_i=1 for i<5r and −1 otherwise, and Y1_i=2Y0_i. Then:

* tau(P)=0;
* V0(P)=N/(N−1), V1(P)=4N/(N−1), Vdelta(P)=N/(N−1);
* RVar(P,H(P,·))=81/[4(N−1)];
* `V1(P)/n0+V0(P)/n1=10/(N−1)`;
* `V1(P)/n1+V0(P)/n0=85/[4(N−1)]`;
* `10/(N−1)<RVar(P,H(P,·))`.

Third, this same sequence has `Regularity heterogeneousWitness (1/5) 4 1 1 0`, has tau_k=0 for **every** k, has `N_k*R_k→81/4`, and has `N_k*O(E_k,z)→p 10`. In addition `L_O(1/5,4,1)=10`, `L_N(1/5,4,1)=85/4`, and 10<81/4.

Finally, 81/4<85/4. This is an asymptotic and explicit-variance comparison; the proposition contains no rejection probability or claim that a particular test exceeds its nominal size.
