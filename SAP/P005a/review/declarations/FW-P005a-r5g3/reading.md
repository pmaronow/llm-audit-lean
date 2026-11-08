# Blind reading

Written before opening `claims.json` or `record.json`. Sources inspected: the three Challenge declarations and docstrings, every named entry of their `closure.json` closures, and the definitions below. The 23 generated proof constants and four generated Population constructor/projections were also inspected with `#print` in `scratch/ClosurePrint.lean`. Generated proofs only supply `Nat.AtLeastTwo` instances for numeral elaboration or `NeZero` instances for nonempty finite coordinate types; none supplies a statistical hypothesis or conclusion. `scratch/Elaboration.lean` confirms the casts and quantifier order.

## SAP.P005a.T12

### Objects and complete expansion

This is a closed proposition, with no external parameters or hypotheses. Its data are fixed finite arrays of real numbers. Write I_n = {0,...,n−1}, implemented by `Fin n`. For any subset A of I_n and array z, define z̄_A = (Σ_{i∈A} z_i)/|A| and z̄ = z̄_{I_n}. Sums and division here are Mathlib finite sums and real field operations. Define C_A(u,v) = (uv)̄_A − ū_A v̄_A. For a vector array x, x̄_A is the vector of coordinate means. Dot products are Σ_{k∈I_d} u_k v_k, and matrix multiplication is the corresponding finite coordinate sum. Let

- L_A[k,l] = (x_k x_l)̄_A − x̄_A[k] x̄_A[l];
- q_A(y)[k] = (yx_k)̄_A − ȳ_A x̄_A[k];
- B(y)[k] = (yx_k)̄; and b_A(y) = L_A⁻¹ q_A(y);
- h_i = Σ_k x_i[k]²;
- u_A(y)[k] = ((y−ȳ)x_k)̄_A − ((y−ȳ)x_k)̄;
- v_A(y) = (L_A⁻¹−Id)q_A(y);
- w_A(y)[k] = −x̄_A[k](y−ȳ)̄_A.

These expand `mean`, `popMean`, `sampleCov`, `xMean`, `armL`, `armN`, `populationSlope`, `armBetaHat`, `leverage`, `armNu1`, `armNu2`, `armNu3`, `centered`, and `dot`. Inverses are Mathlib matrix inverses, equivalently det(L)⁻¹ times the adjugate over ℝ. `Population n d` is exactly the record of x : I_n → I_d → ℝ and yT,yC : I_n → ℝ; it carries no implicit properties. Its constructor/projections add nothing. `standardized` means x̄ = 0 and the matrix [(x_k x_l)̄] is Id.

`design n m` is the finite set of every m-element subset of I_n; `control S` is I_n\S. E_m f denotes (Σ_{S⊆I_n, |S|=m} f(S))/binomial(n,m), the expansion of `expectation`. There is one uniformly selected assignment, with no replicate sampling in this statement. pT(n,m) is the real quotient m/n.

Here n=6, d=1, m=2. Define a=(-3,−2,−1,0,1,5), Y_i=a_i², s=√(3/20), x_i=s a_i. These expand `weightA`, `weightY`, `weightScale`, `weightX`, `scalarPopulation` and `T12Population`. The last has yT_i=0, yC_i=Y_i. In the one-dimensional notation vectors have one real coordinate. For T=I_6\S put

U(S) = x̄_T · [u_T(Y)+v_T(Y)+w_T(Y)],

J(S) = (1/8) C_T(h,Y) + x̄_T · [(L_S⁻¹−Id)q_T(Y)],

K(S) = (1/8) C_T(h,Y) + x̄_T · [(L_T⁻¹−Id)q_T(Y)].

These are precisely `T12ControlNuisance`, `T12PrintedEstimator` and `T12CorrectedEstimator`; the source writes 2/((6−2)4) for 1/8. The theorem asserts the conjunction of all the following facts, without further assumptions:

1. There are 15 assignments; i↦x_i is injective; (a²)̄=40/6; x̄=0 and (x²)̄=1 (so the population is standardized); also (x²)̄=(3/20)(40/6); (yT²)̄=0; (yC²)̄≤121; and 1/4 < 2/6 < 3/4.
2. For every S in the design, det(L_S)≠0 and det(L_T)≠0. For every such S, |S|=2, |T|=4, L_S[0,0]=(3/20)C_S(a,a), L_T[0,0]=(3/20)C_T(a,a), both scalar matrix entries are strictly positive, and b_T(Y)=B(Y)+u_T(Y)+v_T(Y)+w_T(Y). This is the full expansion of `interactedRegular` and the following universal conjunction.
3. For every label i, h_i=x_i²=(3/20)a_i², and h̄=1.
4. E_2 x̄_T=0; E_2[x̄_T·B(Y)]=0; E_2 U=E_2[x̄_T·b_T(Y)]; and both of these last expectations equal r=31085815448171/17062566567774.
5. E_2 J=t=12010469/846720; E_2 K=r; E_2 J≠E_2 U; E_2 K=E_2 U; |r−1.822|<0.0005; |t−14.18|<0.005. The decimal numerals denote exact rationals.
6. 2/((6−2)4)=1/8. For every S in the design the four additional scalar-coordinate identities are

   x̄_T·b_T(Y) = ā_T C_T(a,Y)/C_T(a,a),

   x̄_T·q_T(Y) = (3/20)ā_T C_T(a,Y),

   x̄_T·[L_S⁻¹q_T(Y)] = ā_T C_T(a,Y)/C_S(a,a),

   C_T(h,Y) = (3/20)[(a²Y)̄_T − (a²)̄_T Ȳ_T].

The docstrings call J the estimator in the printed display and say it is biased for E_2 U; they identify replacement of L_S⁻¹ by L_T⁻¹ as the correction. This is a statement about the fixed population, not a universal correctness result for K.

### Totalizations and edge cases

Real division by zero is zero; the mean of an empty arm and the expectation over an empty design consequently equal zero by definition. Neither occurs here: all assignments have arm sizes 2 and 4 and the design has 15 elements. The two covariance denominators in the coordinate formulas are strictly positive by the scaling and positivity assertions. Mathlib gives the zero matrix as inverse of a singular real matrix; every inverse used here is certified nonsingular for each assignment. `Real.sqrt` is zero on nonpositive real inputs, but its sole input here is 3/20>0. The one coordinate index 0 is legitimate in `Fin 1`. The numeric vectors are total functions on `Fin 6`, with no out-of-range lookup or partial-function default. Natural-number cardinalities are cast exactly to reals; all subtractions inside the real fractions are real subtraction. No truncated subtraction affects these formulas. No logs, real powers, integrals, ENNReal coercions, extrema or limits occur. Finite real arrays make all expectations well-defined ordinary finite sums. The generated constants in this closure (including reused constants named after `signX` and `signPopulation`) are only numeral/nonempty-type certificates, not dependencies on the sign-example arrays as statistical data.

## SAP.P005a.T13

### Objects, quantifiers and complete expansion

Use the finite-sum notation and expanded array, matrix and nuisance definitions above, now for arbitrary n,d,m. `leverageCov P y` is H(y)=C_{I_n}(h,y)=(hy)̄−h̄ȳ. `NTTT n m` is

g_T(n,m) = (n−m)(n−2m)/[(n−1)(n−2)m²],

with real arithmetic. `NCCC n m` is g_T(n,n−m), where the inner n−m is natural subtraction. Under m<n set c=n−m>0; it is exactly the ordinary integer difference, and

g_C = m(2m−n)/[(n−1)(n−2)c²].

The theorem quantifies, in order, over natural n,d,m, then P=(x,yT,yC), then hypotheses n≥3, m>0, m<n, standardization (x̄=0, (xxᵀ)̄=Id), and finally the hypothesis that for EVERY S of size m, det(L_{I_n\S})≠0. After these assumptions its conclusion is one conjunction. There is no positive-dimension assumption, no restriction on the potential-outcome values, and no treated-arm nonsingularity assumption. All expectations are uniform over the entire design, not a law conditioned on nonsingularity.

Put T=I_n\S, α=m/[(n−2)c], δ=m/[(n−1)c], ρ=(c−1)n/[c(n−1)] and η=mn(c−1)/[(n−1)(n−2)c²]. The conclusion consists of all eight clauses:

1. E_m[α C_T(h,yC) + x̄_T·v_T(yC)] = E_m[x̄_T·(u_T(yC)+v_T(yC)+w_T(yC))].
2. That latter expectation equals E_m[x̄_T·b_T(yC)].
3. For every S in the design, x̄_T·v_T(yC)=x̄_T·[(L_T⁻¹−Id)q_T(yC)]. This particular clause expands the definition of v_T.
4. E_m[x̄_T·u_T(yC)]=δ H(yC).
5. E_m[x̄_T·w_T(yC)]=−g_C H(yC).
6. E_m C_T(h,yC)=ρ H(yC).
7. δ−g_C=η.
8. η=αρ.

Thus every SAP notion in the assertion is an explicit finite sum, a field operation, a finite matrix operation or the stated determinant predicate. The Challenge docstring says these are the expectation chain, component expectations and coefficient identities for the control-inverse correction.

### Totalizations and edge cases

The real denominators n, n−1, n−2, c, c² and the design cardinality are all positive under the assumptions. Every arm is nonempty. `NCCC` uses natural subtraction but m<n prevents truncation from changing its meaning. `#print` confirmed that all other displayed n−m differences in these formulas are real subtraction. All control inverses are actual inverses by the universal determinant hypothesis; there are no treated inverses. The definitions on arbitrary non-design subsets are total but never used in the conclusions or finite expectations. Dimension zero is allowed: empty coordinate sums are zero and the unique 0×0 matrix has determinant one. Hence control singleton cases may exist in dimension zero; in positive dimension a singleton covariance matrix is singular, so that particular parameter choice cannot meet the inverse hypothesis. This does not make the general theorem vacuous. Outcomes are real arrays on a finite type, so no missing integrability or moment assumption is needed. There are no square roots, logs, rpow, Bochner integrals, extrema, infinite extended-real coercions, limiting operations or partial-function defaults in this statement. The extra generated constants in the closure only witness numeral elaboration.

## SAP.P005a.T14

### Objects and complete expansion of the estimators

Again let P=(x,yT,yC) be arrays on I_n, with d real coordinates. For n,m define p=m/n, q=(n−m)/n, B=pB(yT)+qB(yC) and, for T=I_n\S,

Δ=x̄_S−x̄_T, D=−Δ,

H_S=Id−p x̄_S x̄_Sᵀ−q x̄_T x̄_Tᵀ,

Q_S=p q_S(yT)+q q_T(yC),

z1_S=p u_S(yT)+q u_T(yC),

z2_S=(H_S⁻¹−Id)Q_S,

z3_S=p w_S(yT)+q w_T(yC).

These are `pT`, `pC`, `N`, `Lhat`, `Nhat`, `nu1`, `nu2`, and `nu3`, expanded using the means, dot products and arm quantities already defined. Products x̄ x̄ᵀ have entries x̄[k]x̄[l]. `betaHat` is H_S⁻¹Q_S. Put M_S=yT̄_S−yC̄_T, C_T^S=C_S(h,yT), C_C^S=C_T(h,yC). Then

A_S=M_S−Δ·H_S⁻¹Q_S,

biasEstimate_S=(C_C^S−C_T^S)/(n−2)+D·z2_S,

A_S^db=A_S−biasEstimate_S.

These expand `adjustedATE`, `biasEstimate` and `debiasedATE`; `ate` is yT̄−yC̄. `noninteractedRegular P m` means det(H_S)≠0 for every S of size m. `observedResidual S eT eC` is the pointwise conditional expression eT_i if i∈S and eC_i otherwise; `observedOutcome P S` consequently is o_i=yT_i on S and yC_i on T. There is no unspecified observation map.

### Quantifiers and every conclusion

`T14WholeStatement` is the conjunction of `T14Statement`, the four-unit witness facts and its explicit inequality, and a stronger observability assertion. `T14Statement` itself consists of the following FOUR independent universally quantified assertions:

1. For every n,d, then P, m, S, and vector v∈ℝ^d, under n≥3, 0<m<n, S⊆I_n with |S|=m, and det(H_S)≠0, the following five equations hold. No centering or standardization is assumed in this block. Write R_S(v)=mean_S(yT_i−x_i·v)−mean_T(yC_i−x_i·v), and U_S=(C_T^S−C_C^S)/(n−2). Then

   A_S^db=M_S−Δ·Q_S+U_S;

   A_S^db=R_S(v)−Δ·(Q_S−v)+U_S;

   A_S^db=(M_S−Δ·H_S⁻¹Q_S)−D·[(H_S⁻¹−Id)Q_S]+U_S;

   −Δ·H_S⁻¹Q_S−D·[(H_S⁻¹−Id)Q_S]=−Δ·Q_S;

   M_S−Δ·Q_S=R_S(v)−Δ·(Q_S−v).

   In the source the two covariance fractions comprising U_S are written separately, with treated plus and control minus. The arbitrary v is universally quantified before the hypotheses.
2. For every n,d,m and P, under n>0, 0<m<n and x̄=0, for every S of size m, D=(1/p)x̄_T and D=−(1/q)x̄_S. Neither covariance standardization nor an inverse is assumed in this block.
3. For every n,d,m and P, under n≥3, 0<m<n, standardization and det(H_S)≠0 for every S in the design,

   E_m A_S−(yT̄−yC̄)=E_m[D·(z1_S+z2_S+z3_S)].

4. For every n,d,m, under n≥3 and 0<m<n, there EXISTS a single function

   F : (subsets of I_n) → (I_n→I_d→ℝ) → (I_n→ℝ) → ℝ

   such that for EVERY P, if P is standardized, then for EVERY S in the design with det(H_S)≠0, D·z2_S=F(S,x,o). In particular F is chosen before P, not separately for each pair of potential-outcome arrays. No measurability predicate is explicitly attached to F, and no explicit F is supplied in the statement.

The additional closed witness `W1WrongSumPopulation` has n=4, d=1, m=1, x=(-1,−1,1,1), yT=0 and yC=1. `W1WrongSumFacts` asserts all of these facts together:

- x̄=0 and (x²)̄=1; det(H_S)≠0 for every singleton S;
- B=0; the singleton S₀={0} is in the design;
- (yT²)̄≤1, (yC²)̄≤1 and, for every coordinate k, (x_k²)̄≤1;
- 1/5<p=1/4<4/5;
- (Σ_{i∈S₀}(yC_i−x_i·B))/(4−1)=1/3;
- yC̄_{I_4\S₀}−x̄_{I_4\S₀}·B=1.

The whole statement explicitly adds that the last two quantities are unequal, so the closed example distinguishes a sum over treated labels divided by the control size from a mean over control labels.

Finally, the last conjunct repeats the quantifiers n,d,m, n≥3, 0<m<n, then ∃F, then ∀P, then ∀S in the design with det(H_S)≠0, asserting D·z2_S=F(S,x,o), this time WITHOUT the standardization assumption. F can depend on n,d,m because it is chosen after them, but cannot depend on unobserved potential outcomes because it is chosen before P and takes only S,x,o as inputs. This implies the preceding standardized observability clause but is separately asserted.

The Challenge and WholeW1 docstrings describe corrected debiasing, inverse cancellation, arbitrary-vector residual identities, centered arm-mean identities, an actual bias decomposition, the four-unit treated-sum discrepancy, and a function selected before potential outcomes. They do not call the entire T14 declaration a refutation.

### Totalizations and edge cases

Arithmetic means and design expectations are totalized to zero on empty sets, but all places using them here have nonempty arms and nonempty designs. Every n−2 divisor has n≥3. The p and q reciprocals occur under n>0 and 0<m<n, hence are legitimate. All n−m quantities in these displayed real formulas are real differences; cardinalities and natural parameters have exact real casts. Matrix inverse is zero on a singular real matrix, but all inverses evaluated in the theorem's conditional conclusions or expectations have the corresponding determinant hypothesis. (The algebraic cancellation can in fact be written for arbitrary matrices, but the theorem has these explicit hypotheses.) The four-unit witness asserts every-assignment regularity, so its claim does not rest on a singular inverse. Empty coordinate types are allowed in the universal blocks; their sums vanish and their matrix determinant is one, which is ordinary dimension-zero linear algebra. The fixed witness has dimension one. The if-expression defining observed outcomes is total and uses actual set membership, with no default missing value. F ranges over total functions; its value on inadmissible or singular inputs is unconstrained, which is distinct from invoking a partial inverse on those inputs in an asserted equality. No sqrt, log, rpow, Bochner integral, toReal(∞), empty/unbounded infimum or supremum, limsup/liminf, or partial-function lookup occurs. All expectations are finite sums of real values, so integrability is automatic.

## Closure coverage

Every non-generated definition named in each closure is expanded in its corresponding section (shared finite-sum notation is explicitly reused). All generated proof constants were printed and read; all are numeric/typeclass certificates. The only natural truncated subtraction with semantic relevance in these closures is the second argument of `NCCC`, where m<n ensures it agrees with the ordinary difference. No additional SAP axioms or conclusion-bearing structures are present in the definitions.
