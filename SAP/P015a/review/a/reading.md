# Blind mathematical reading

This file was written and saved before opening either `claims.json` or `record.json`. It reads the twelve declarations in `SAP/P015a/Challenge/Part1.lean`, through all three Defs parts, without treating the docstrings as mathematical hypotheses. All twelve declarations are closed propositions; the assumptions below occur inside their universally quantified clauses. Universe parameters allow the indicated arbitrary measurable spaces.

## Mathematical dictionary and Mathlib conventions

For a finite set A, write E_p Z = sum over a in A of p(a)Z(a), and P_p(E) = sum over a satisfying E of p(a). A probability vector means every p(a) is nonnegative and their sum is 1. Define

* e_p(x) = E_p[1_{X=x}D]/P_p(X=x), and more generally E_p[Z|X=x] by the same quotient.
* q_p(x,d) = P_p(X=x,D=d)/P_p(X=x).
* w_p(a) = (D(a)-e_p(X(a)))^2, Z_p = E_p w_p, and p*(a) = p(a)w_p(a)/Z_p.
* Var_p(Z) = E_p[(Z-E_p Z)^2].

These are the literal finite-sum definitions, even when p is not a probability vector. Division is real division, so a quotient with denominator zero is zero. Finite conditional independence of U and D given X means, for every x,u,d (in that order),
P_p(X=x,U=u,D=d) P_p(X=x) = P_p(X=x,U=u) P_p(X=x,D=d).
For a potential-outcome function Y(a,d), the contrast from d to d' is (Y(a,d')-Y(a,d))/(d'-d); all contrasts used below have endpoints 0 and 1. The inverse-probability variable is D Y/e - (1-D)Y/(1-e).

For finite row and column sets, matrix multiplication and dot products are ordinary sums. Write beta_p(W,Y) = (E_p[W W^T])^{-1} E_p[WY], where W(a) is a column of regressors; write LS(W,Y) = (W^T W)^{-1}W^T Y. The inverse is Mathlib's nonsingular matrix inverse, equal to the usual inverse when the determinant is nonzero and to the zero matrix when it is zero (`LinearAlgebra/Matrix/NonsingularInverse.lean`, `inv_def`, `nonsing_inv_apply_not_isUnit`). Fitted treatment residuals for controls V and coefficients omega are D-V omega.

For n natural and a sample a: {0,...,n-1}->A, p^n(a) = product_i p(a_i) and bar Z_n(a) = (sum_i Z(a_i))/n. The latter is zero at n=0 under real division. Moment and deviation-bound clauses below explicitly require n>=1. Convergence of event masses as n tends to infinity is ordinary real convergence. Convergence in measure means, for every positive extended-real epsilon, the measure of {epsilon <= extended distance from the proposed limit} tends to zero (`MeasureTheory/Function/ConvergenceInMeasure.lean:57`); no measurability requirement on the estimator T is built into that predicate. Independent uniform sampling means each draw is measurable, the entire sequence is mutually independent (`iIndepFun`), and each of its four values has probability 1/4.

Write L_m(W,n,k;theta) = sum_i [k_i log(m(W_i theta))+(n_i-k_i)log(1-m(W_i theta))]. This omits the parameter-independent binomial coefficient. Write h_m(eta) = m'(eta)/(m(eta)(1-m(eta))), R_m(theta) = W^T(k-n m(W theta)), and S_m(theta) = W^T[h_m(W theta)(k-n m(W theta))], with products inside brackets pointwise. In Defs these are `logLikelihood`, `likelihoodMultiplier`, `residualEquation`, and `likelihoodScore` respectively. `deriv` is the actual derivative when one exists and zero otherwise (`Analysis/Calculus/Deriv/Basic.lean:153`). `HasDerivAt` asserts actual differentiability with the specified derivative, also for vector-valued functions. Real.log is log of the absolute value off zero, and is zero at zero; likelihood clauses using it are to be read with their stated admissibility conditions.

Let g(a) = 1/(1+exp(-a)), c(p) = log(p/(1-p)), and T1(f,c;a) = f(c)+f'(c)(a-c). These expand `Real.sigmoid`, `logOdds`, and `firstTaylorPolynomial`. Let Phi be the cumulative distribution function of the Gaussian probability measure with mean 0 and variance 1, and phi(a) = exp(-a^2/2)/sqrt(2 pi). Mathlib's `gaussianReal 0 1` is Lebesgue measure with this density; for a probability measure `cdf` is the real mass of (-infinity,a] (`Probability/Distributions/Gaussian/Real.lean:49,222`, `Probability/CDF.lean:57`). Set H(a) = phi(a)/(Phi(a)(1-Phi(a))).

For a probability measure P and measurable X, G_X denotes the sub-sigma-algebra pulled back from the codomain of X. E_P[Z|G_X] is Mathlib conditional expectation, a chosen function representative. Mathlib defines it to be zero if the sigma-algebra is not a sub-sigma-algebra, the trimmed measure is not sigma-finite, or Z is not integrable; the measurable-X, probability, and L2 assumptions below address these cases. A statement with ordinary equality of functions is stronger than an almost-everywhere equality; the reading distinguishes them. L2 (`MemLp D 2 P`) requires almost-everywhere strong measurability and finite second absolute moment. Bochner integrals of nonintegrable real functions are defined as zero (`MeasureTheory/Integral/Bochner/Basic.lean:158`).

For a cell x, define P_x = P(X=x)^{-1} times P restricted to {X=x}, in extended nonnegative measure arithmetic. Then mu_x = integral D dP_x, v_x = integral (D-mu_x)^2 dP_x, and q_x(d) = the real value of P_x(D=d). Define w(s) = (D(s)-mu_{X(s)})^2, Z = integral w dP, and P* = (ofReal Z)^{-1} times P with density ofReal(w). These are the literal `conditionalCellLaw`, `cellExpectation`, `cellVariance`, `cellProbability`, `discreteResidualWeight`, and `discreteEffectiveLaw`. Their positive-cell and positive-Z hypotheses below are consequential, not implicit conventions. `toReal` sends infinity to zero; probability and finiteness hypotheses prevent that interpretation in the asserted cell conclusions.

The degree-N inverse-logit Taylor polynomial is T_N(g,c;a) = sum_{k=0}^N g^{(k)}(c)(a-c)^k/k!. `taylorWithinEval` includes degree N, and its within-set is all of R (`Analysis/Calculus/Taylor.lean:60-77`). A formal complex multilinear power series has the usual scalar power-series interpretation here. `HasFPowerSeriesAt f s c` asserts equality with the summed series on some positive-radius neighborhood of c. Its `radius` is the supremum of nonnegative radii r for which the sequence of coefficient operator norms times r^n is bounded (`Analysis/Analytic/Basic.lean:95`, `ConvergenceRadius.lean:108`); for scalar complex series this is the usual convergence radius. `sInf` and `sSup` are infimum and supremum in the conditionally complete real order, so their usual meanings require the bounds/nonemptiness noted below.

## SAP.P015a.T1

The proposition has no external assumptions. On A={0,1,2,3}, set X=(0,0,1,1), D=(0,1,0,1), p_epsilon=((1-epsilon)/2,epsilon/2,1/4,1/4), and Y(a,d)=2X(a)+(1+X(a))d. Let V_epsilon be the inverse-probability variable for the observed Y(a,D(a)), with e(X)=epsilon+(1/2-epsilon)X. Set epsilon0=1/1000000. The bundled proposition `rareWitness` (call it R1) is exactly the conjunction of the following five groups:

1. At epsilon0, p is a probability vector; for every a then d, Y(a,d)=Y(a,0)+(1+X(a))d; (Y(a,0),1+X(a)) and D are conditionally independent given X. For every x in {0,1}, e_p(x)=epsilon0+(1/2-epsilon0)x and q_p(x,0)>0 and q_p(x,1)>0. The conditional means of w at x=0,1 are respectively 999999/1000000000000 and 1/4. P_p(X=0)=1/2, P_p*(X=0)=999999/250000999999<1/250000, V=(0,1000000,-4,8), E_p(1+X)=E_p V=3/2, E_p(V^2)=500020, Var_p(V)=2000071/4, and E_p*(1+X)=500000999999/250000999999, which is unequal to 3/2.
2. For every real epsilon, assuming first 0<epsilon and then epsilon<1/2: p_epsilon is a probability vector; the same pointwise affine potential-outcome identity and conditional independence hold; for every x in {0,1} the displayed propensity formula and strict positivity of both treatment probabilities hold; and P_p*(X=0)=epsilon(1-epsilon)/(epsilon(1-epsilon)+1/4), which is strictly positive and less than 4 epsilon.
3. At epsilon0, for W(a)=(1,D(a),X(a)), det(E_p WW^T) is nonzero and coordinate 1 of beta_p(W,Y(D)) is 500000999999/250000999999.
4. For every natural n with n>=1: p^n is a probability vector, E_{p^n} bar V_n=3/2, Var_{p^n}(bar V_n)=2000071/(4n); and, for every real delta>0, P_{p^n}(delta<=|bar V_n-3/2|)<=2000071/(4n delta^2).
5. For every real delta>0, P_{p^n}(delta<=|bar V_n-3/2|) tends to zero as n tends to infinity.

T1 asserts R1 and, at epsilon0, the four explicit conditional probabilities q_p(0,1)=epsilon0, q_p(0,0)=1-epsilon0, q_p(1,1)=q_p(1,0)=1/2; E_p[w|X=0]=epsilon0(1-epsilon0); P_p*(X=0)=epsilon0(1-epsilon0)/(epsilon0(1-epsilon0)+1/4); and Z_p>0. All conclusions are conjoined; none of R1 is assumed.

## SAP.P015a.T2

No external assumptions. On the same four atoms take uniform p=(1/4,1/4,1/4,1/4), X=(0,0,1,1), and D=(0,1,0,2). Let Y_A(a,d)=d and let Y_B(a,d)=3 when X(a)=1 and d=1, and d otherwise. Call the following conjunction R2 (`multivaluedWitness`):

1. p is a probability vector; for every a, e_p(X(a))=1/2+X(a)/2; w=(1/4,1/4,1,1) and each coordinate is strictly positive; Z_p=5/8; p*=(1/10,1/10,2/5,2/5); P_p*(X=0)=1/5 and P_p*(X=1)=4/5; q_p(1,1)=q_p*(1,1)=0. In each world the vector (Y(a,0),Y(a,1),Y(a,2)) is conditionally independent of D given X. For every a the observed response in both worlds is D(a). The population means of the 0-to-1 contrast are 1 in A and 2 in B; the corresponding effective-law means are 1 and 13/5.
2. For every real d, [q_p(0,d)>0 and q_p(1,d)>0] iff d=0. Separately, for every real d, the same equivalence holds under p*.
3. For every measurable space Omega, then probability measure P, then sequence of draws draw_n:Omega->Fin 4 satisfying measurable independent uniform sampling, then every collection of estimators T_n:(Fin n->R x R x R)->R: it is impossible that T_n applied to the observed triples (X,D,Y_A(D)) of the first n draws converges in P-measure to 1 while the same estimator in world B converges in P-measure to 2. It is also impossible for the respective limits to be 1 and 13/5. T is quantified after the sampling law and may be arbitrary; a single T must serve both worlds in each impossibility statement.

T2 asserts R2 and E_p[w|X=0]=1/4 and E_p[w|X=1]=1. The sampling-space universe is the theorem's arbitrary u.

## SAP.P015a.T3

No external assumptions. Let p be uniform on four atoms, X=(0,0,1,1), D=(0,1,0,1) as population variables. Let the ordered sample be a=(0,0,2,3). Let V have rows (1,0),(1,0),(1,1),(1,1), let d=(0,0,0,1), and let W have rows (1,0,0),(1,0,0),(1,0,1),(1,1,1). Call R3 (`fittedZeroWitness`) this conjunction:

* p is a probability vector; for every x in {0,1}, then d0 in {0,1}, q_p(x,d0)=1/2; for each x in {0,1}, E_p[w|X=x]=1/4; (1/4)^4=1/256>0.
* V^T V=[[4,2],[2,2]], V^T d=(1,1), and [[4,2],[2,2]](0,1/2)=(1,1). det(V^T V) is nonzero. d-V(0,1/2)=(0,0,-1/2,1/2), whose coordinatewise squares are (0,0,1/4,1/4). W^T W=[[4,1,2],[1,1,1],[2,1,2]] and its determinant is 2.
* LS(V,d)=(0,1/2), the residual using LS(V,d) is (0,0,-1/2,1/2), and p^4(a)=1/256.
* For every sample index i, V(i,1)=X(a_i) and d_i=D(a_i).

T3 asserts R3 and that the squared residual using the actual LS(V,d) is (0,0,1/4,1/4). There is no arbitrary outcome regression being asserted here.

## SAP.P015a.T4

The theorem asserts a conjunction, not an implication from the counterexamples. Its first component (`positivityRepair`) consists of R1, R2 at universe zero, R3, and the following universally quantified measure-theoretic statement.

For every pair of measurable spaces Omega and B, with B countable and every singleton of B measurable, every probability measure P on Omega, every X:Omega->B and D:Omega->R, assuming (in order) measurable X, measurable D, and D in L2(P):

1. For every x, if P(X=x)>0, then both: for every d then d' with d!=d', q_x(d)>0 and q_x(d')>0 imply v_x>0; and v_x=0 implies D=mu_x P_x-almost everywhere.
2. If D is binary P-almost everywhere, then for every x with P(X=x)>0, v_x=q_x(1)(1-q_x(1)), and v_x>0 iff 0<q_x(1)<1.
3. If Z>0, then if w is P-integrable, then for every x with P(X=x)>0: the real cell mass P*(X=x)=P(X=x) v_x/Z; P*(X=x)=0 iff v_x=0; and, if D is P-almost-everywhere binary and 0<q_x(1)<1, the conditional treatment probabilities under P* at x are q*_x(1)=1-q_x(1) and q*_x(0)=q_x(1).

Its second component universally quantifies the same Omega,B,P,X,D and the same assumptions, then x, then P(X=x)>0, and asserts:

* If v_x=0 then, for every distinct real d,d', it is not the case that both q_x(d)>0 and q_x(d')>0.
* If D is P-almost-everywhere binary then q_x(0)=1-q_x(1), and v_x>0 iff q_x(0)>0 and q_x(1)>0.
* If Z>0 and w is P-integrable, then P* is a probability measure; and if D is P-almost-everywhere binary and P*(X=x)>0, then v_x>0 and both q*_x(0) and q*_x(1) are strictly positive.

The extra integrability condition is an explicit antecedent of the effective-law statements. All real-valued cell probabilities use the normalized-cell measure defined above.

## SAP.P015a.T5

No external assumptions. Rows are indexed by (d,x) in {0,1} x {0,1,2}; W(d,x)=(1,d,x), n(d,x)=12, k(d,x)=(7,6,10)_x, m(eta)=eta/(1+eta), and theta0=(1,0,1). The conjunction is:

* For every row, W_i theta0>0 and 0<k_i<12. R_m(theta0)=0, S_m(theta0)=(2/3,1/3,-2/3), and S_m(theta0)!=0.
* It is false that for every theta, if all W_i theta>0 then L_m(theta)<=L_m(theta0). Thus an admissible parameter with strictly greater likelihood exists.
* det(W^T W)=36. For every row the intercept is 1, the treatment column is 0 or 1, and k has the specified count formula. For every row, m(W_i theta0)=(1/2,2/3,3/4)_x. det(12 W^T W)=62208.
* For every vector v in R^3, the derivative at t=0 of L_m(theta0+t v) is (2/3,1/3,-2/3) dot v.
* For every real eta, eta>0 implies h_m(eta)=1/eta.

This statement supplies a root of R which is not a likelihood maximizer. It does not quantify over an actual likelihood maximizer having nonzero R.

## SAP.P015a.T6

No external assumptions. Let q=inf{a in R:Phi(a)>=3/4}. On rows (d,x) in {0,1} x {0,1,2}, W(d,x)=(1,d,x-1), n_i=8, k_i=(3,2,7)_x, and theta0=(0,0,q). Assert:

* 0<q<7/10; Phi(-q)=1/4, Phi(0)=1/2, Phi(q)=3/4.
* R_Phi(theta0)=0 and S_Phi(theta0)=(4(H(q)-H(0)),2(H(q)-H(0)),0). H(q)=(16/3)phi(q), H(0)=4phi(0), and 13/625<2(H(q)-H(0)).
* It is false that all theta in R^3 have L_Phi(theta)<=L_Phi(theta0).
* Every row has intercept 1, binary treatment, and counts strictly between 0 and 8; det(8 W^T W)=18432.
* The set defining q is nonempty and bounded below.
* For every v in R^3, the derivative at zero of L_Phi(theta0+t v) is sum_i H(W_i theta0)(k_i-8Phi(W_i theta0))(W_i v).

## SAP.P015a.T7

No external assumptions. On six ordered cells let X=(-1,-1,0,0,1,1), D=(0,1,0,1,0,1), p=(1/4,1/12,1/6,1/6,1/12,1/4), e(x)=1/2+x/4, b_a(x)=1/4+a(3x^2-2), W_i=(1,D_i-e(X_i),X_i), and q_{a,epsilon,i}=b_a(X_i)+epsilon(D_i-e(X_i)). Let m(eta)=eta^2, ell_{a,epsilon}(theta)=E_p[q log((W theta)^2)+(1-q)log(1-(W theta)^2)], and s_{a,epsilon}(theta)=E_p[W h_m(W theta)(q_{a,epsilon}-m(W theta))]. Admissible theta means 0<W_i theta<1 for every i.

The proposition `SquareLinkMLDerivative(a,b)` means: there exists a function theta:R->R^3 such that theta(0)=(1/2,0,0); there exists a real r with 0<r<=1/16 such that for every epsilon with |epsilon|<r, theta(epsilon) is admissible and is the unique global maximizer of ell_{a,epsilon} over all admissible vectors; and the scalar function epsilon->theta(epsilon)_1 has actual derivative b at zero. Only coordinate 1 is required to be differentiable. The theta function is quantified before r; its values outside the indicated neighborhood have no optimality restriction.

T7 asserts all of the following:

1. `SquareLinkMLDerivative(1/16,120/119)` and `SquareLinkMLDerivative(0,1)`. For every epsilon with |epsilon|<=1/16, E_p q_{1/16,epsilon}=1/4 and beta_p(W,q_{1/16,epsilon})_1=epsilon. 120/119!=1.
2. p is a probability vector. A=E_p WW^T=diag(1,5/24,2/3). B=E_p[WW^T(b_{1/16}(X)-1/4)]=diag(0,-1/384,1/24). (-32/9)B-(16/3)A=J=diag(-16/3,-119/108,-100/27). For every vector t, Jt+(0,10/9,0)=0 iff t=(0,120/119,0). Again 120/119!=1. The mean and OLS identities of item 1 are also repeated as a separate universal conjunct with the same epsilon bound.
3. Let U have Lebesgue measure restricted to [0,1], and let P be the measure on ((R x R) x R) formed by summing, over the six cells, p_i times [Dirac_(X_i,D_i) product U]. Both U and P are probability measures. Write X(s),D(s),U(s) for the coordinate functions and Y_{a,epsilon}(d,s)=1{U(s)<=b_a(X(s))+epsilon(d-e(X(s)))}; tau(s)=Y(1,s)-Y(0,s).
4. For every a then epsilon, assuming a=0 or a=1/16 and |epsilon|<=1/16: each X value -1,0,1 has mass 1/3; D is binary almost everywhere; U belongs to [0,1] almost everywhere; for every real u with 0<=u<=1, P(U<=u)=ofReal(u); U is independent of (X,D); (Y(0),tau) and D are conditionally independent given G_X; E_P[D|G_X]=e(X) almost everywhere; Y(D)=Y(0)+tau D almost everywhere; E_P[Y(D)|G_(X,D)]=b_a(X)+epsilon(D-e(X)) almost everywhere; and integral Y(D) dP=1/4.
5. For every real eta with 0<eta<1, h_m(eta)=2/(eta(1-eta^2)); m'(1/2)=1; h_m(1/2)=16/3; h_m'(1/2)=-32/9; s_{1/16,0}(1/2,0,0)=0. For every v in R^3, the vector derivative at zero of s_{1/16,0}((1/2,0,0)+t v) is Jv. The vector derivative at epsilon=0 of s_{1/16,epsilon}(1/2,0,0) is (0,10/9,0). For every a,epsilon,theta,v, if a is 0 or 1/16, |epsilon|<=1/16 and theta is admissible, then the directional derivative of ell_{a,epsilon} at theta in direction v is s_{a,epsilon}(theta) dot v.
6. For every theta in R^3, set gamma=(theta_0-theta_1/2,theta_1,theta_2-theta_1/4). Then gamma_1=theta_1 and for every cell i, (1,D_i,X_i) dot gamma=W_i theta. For every real alpha,beta,gamma0 there exists theta with this transformed vector equal to (alpha,beta,gamma0).
7. D is P-integrable. For every real a then epsilon, Y_{a,epsilon}(D) is P-integrable, without the parameter restrictions in item 4.

Conditional independence in item 4 is Mathlib's `CondIndepFun` for the pulled-back sigma-algebra and its conditional-expectation kernel; independence is `IndepFun` for the sigma-algebras generated by the functions. Here the covariate takes three atoms and the unit variable is an independent actual uniform variable.

## SAP.P015a.T8

The statement is a conjunction of seven independently quantified clauses:

1. For every N,K natural, W an N by (K+2) real matrix, Y in R^N, assume Y_i is 0 or 1 for every i and W_i0=1 for every i. Then quantify an open real set I, a function m differentiable on I with 0<m(eta)<1 at every eta in I, vectors theta,v in R^(K+2), and the hypothesis W_i theta in I for every i. The derivative at zero of L_m(W,1,Y;theta+t v) is sum_i h_m(W_i theta)(Y_i-m(W_i theta))(W_i v). No full-rank assumption is imposed.
2. For every real eta, g has derivative g(eta)(1-g(eta)) at eta, and h_g(eta)=1.
3. For every pair of finite types N,Q, W:N x Q->R, a selected j0 in Q and hypothesis W_ij0=1 for every i, then a measure nu on R, real functions kappa and carrier, real s, real sets I and support: assume s>0, I open, support measurable, nu(support complement)=0, and for every eta in I the density exp((y eta-kappa(eta))/s+carrier(y)) is nu-integrable with integral 1. Next quantify Y:N->R with Y_i in support, theta:Q->R with W_i theta in I, and differentiability of kappa at every W_i theta. Then, for every v:Q->R, the derivative at zero of sum_i [(Y_i W_i(theta+t v)-kappa(W_i(theta+t v)))/s+carrier(Y_i)] is s^{-1}sum_i (Y_i-kappa'(W_i theta))(W_i v). Also [for every j, s^{-1}sum_i W_ij(Y_i-kappa'(W_i theta))=0] iff [for every j, sum_i W_ij(Y_i-kappa'(W_i theta))=0]. There is no general response-mean identity in this clause.
4. For every real eta, the measure placing mass g(eta) at 1 and 1-g(eta) at 0 is a probability measure, its identity response is integrable, its mean is g(eta), and g(eta) is the derivative at eta of log(1+exp(a)). Also the Poisson measure on naturals with mass exp(-exp(eta)) exp(eta)^n/n! at n is a probability measure, its real-valued count is integrable, its mean is exp(eta), and exp(eta) is the derivative at eta of exp. These are Mathlib `bernoulliMeasure 1 0` and `poissonMeasure`, not axiomatized families.
5. For every N,K,W,Y with the binary-response and intercept hypotheses of clause 1, and every theta,v, the derivative of L_Phi(W,1,Y;theta+t v) at zero is sum_i H(W_i theta)(Y_i-Phi(W_i theta))(W_i v). In the same universally quantified conclusion, there exists no real constant c such that H(eta)=c for all real eta.
6. Phi(0)=1/2 and H'(0)=0.
7. Quantify N,K,W,Y and the same binary-response and intercept hypotheses, then open I, differentiable m:I->(0,1), then eta0,p0 with eta0 in I, 0<p0<1, m(eta0)=p0, and differentiability of the function m' at eta0. Put theta0=(eta0,0,...,0), h=h_m, h0=h(eta0), f0=m'(eta0), h1=h'(eta0), r=W^T(Y-p0), A=W^T W, and B_jk=sum_i (Y_i-p0)W_ij W_ik. For every delta in R^(K+2), the vector whose j coordinate is sum_i W_ij T1(eta->h(eta)(Y_i-m(eta)),eta0;W_i(theta0+delta)) equals h0 r+(-h0 f0 A+h1 B)delta. Delta is unrestricted: this is an identity of affine Taylor polynomials, not an error estimate for the nonlinear score.

## SAP.P015a.T12

First, for every real p with 0<p<1: for every real a, T1(g,c(p);a)=p+p(1-p)(a-c(p)); and the function g(a)-[p+p(1-p)(a-c(p))] is O((a-c(p))^2) as a tends to c(p). Big-O asserts a finite constant bound in some neighborhood, not a global bound.

Second, for every real p,r,rho, assuming in order 0<p, p<1, 0<=r, r<rho, and rho<R=sqrt(c(p)^2+pi^2), put f_C(z)=(1+exp(-z))^{-1} and M=sup{norm(f_C(z)):norm(z-c(p))=rho}. The conclusion is a conjunction of:

* If this norm image of the circle is nonempty, then if it is bounded above, there exists a formal complex power series s such that f_C has s at the real center c(p), and s.radius=ofReal(R).
* For every natural N then every real a, if |a-c(p)|<=r, then |g(a)-T_N(g,c(p);a)|<=M(r/rho)^(N+1)/(1-r/rho).
* The real sequence M(r/rho)^(N+1)/(1-r/rho) tends to zero as N tends to infinity.

The nonempty and bounded-above antecedents scope only over the power-series existence/radius conjunct, not over the last two conjuncts. Positivity of rho and 1-r/rho follows from the explicit radius inequalities. The statement neither asserts attainment of M nor supplies an outside-radius statistical dataset.

## SAP.P015a.T13

For every real p, assuming first 0<p then p<1, assert the following conjunction:

* For every real a, g has actual derivative exp(a)/(1+exp(a))^2 at a.
* g(c(p))=p; g'(c(p))=exp(c(p))/(1+exp(c(p)))^2; and g'(c(p))=p(1-p).
* For every real a, T1(g,c(p);a)=p+p(1-p)(a-c(p)) and also equals (p-p(1-p)c(p))+p(1-p)a.
* c(1/2)=0; exp(c(1/2))/(1+c(1/2))^2=1; and g'(c(1/2))=1/4.

The last fraction has denominator (1+c)^2, unlike the correct derivative's denominator (1+exp(c))^2. Those last constant identities are inside the quantification over p but do not depend on p.

## SAP.P015a.T16

No external assumptions. Assert:

1. 10800420763/10000000000<exp(77/1000)<10800420765/10000000000<6/5, and 800420763/100000000<100(exp(77/1000)-1)<800420765/100000000.
2. For every real alpha,beta,d,controls (in this order), exp(alpha+beta(d+1)+controls)/exp(alpha+beta d+controls)=exp(beta).
3. For the four-row matrix W with rows (1,0),(1,0),(1,1),(1,1), S=(1,1,0,3), and Y_i=log((1+S_i)/2), LS(W,Y)_1=0 and exp(LS(W,Y)_1)=1. Also [log(1/2)+log(2)]/2=0; (S_0+S_1)/2=1; (S_2+S_3)/2=3/2; and ((3/2)/1-1)100=50.
4. For this same W, det(W^T W)=4.

## SAP.P015a.T19

For every pair of measurable spaces Omega,B, every probability measure P on Omega, every D:Omega->R, then every X:Omega->B, assume measurable D, measurable X, and D in L2(P), in that order. Define w(s)=(D(s)-E_P[D|G_X](s))^2 and V=E_P[w|G_X]. Then:

* E_P[w|G_X]=V as literal functions (this is exactly the definition of `conditionalTreatmentVariance`).
* If D is binary P-almost everywhere, then V=E_P[D|G_X](1-E_P[D|G_X]) P-almost everywhere.

There is no countability, atom-positivity, nondegeneracy, or finite-covariate assumption here. The first conjunct defines conditional variance by the conditional squared centered residual; the second is a substantive identity for that definition.
