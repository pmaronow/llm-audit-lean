# Blind reading

This file was written before opening `claims.json` or `record.json`. It records the statements, rather than trying to infer the intended claims from their labels. I read the five Challenge docstrings and all source declarations in their `closure.json` closures. The 112 distinct compiler-generated auxiliary declarations were also inspected with Lean; their types are saved in `scratch/closure-auxiliary-types.txt`. They supply numeral instances, finite-index bounds, injectivity/cardinality proofs, and nonnegativity/normalization proofs, not additional substantive hypotheses.

## Mathematical notation used below

All vectors and matrices have real entries. A finite type is an ordinary finite index set, `Fin n` is {0,...,n−1}, a `Finset` is a finite set, and all displayed sums run over the entire indicated finite index set. Matrix multiplication, transpose, determinant, matrix-vector multiplication, dot products, scalar multiplication, and entrywise addition/subtraction have their ordinary meanings. On real matrices, Mathlib `IsHermitian` means symmetry; `PosSemidef` means symmetry and nonnegative quadratic form on all vectors; `PosDef` means symmetry and strictly positive quadratic form on every nonzero vector. Mathlib states the latter two with finitely supported vectors, equivalent to all vectors here.

The following are expansions of the shared SAP definitions, not extra hypotheses:

* A dyad is a finite set D_r of members with exactly two elements. Thus its two members are distinct. Different records may carry the same unordered dyad.
* I_D(r,s)=1 if D_r∩D_s is nonempty and 0 otherwise (`dyadicMask`); I_rep(r,s)=1 if D_r=D_s and 0 otherwise (`repeatedMask`); I_0(r,s)=1 if r=s and 0 otherwise (`recordMask`).
* I_i(r,s)=1_{i∈D_r and i∈D_s}+1_{r=s and i∉D_r} (`memberMask`). The second term treats records outside member i as singleton clusters.
* A restricted covariance is A^D_rs=I_D(r,s)A_rs (`dyadicRestriction`). The quadratic form q(A,h)=Σ_rs h_r h_s A_rs is `quadForm`.
* B_X=(XᵀX)⁻¹ (`olsBread`), b_X(Y)=B_XXᵀY (`leastSquares`), e_X(Y)=Y−Xb_X(Y) (`fitResidual`). This is the ordinary inverse when XᵀX is nonsingular, and Mathlib's total matrix inverse otherwise.
* For pattern I and score vectors z_r, S(I,z)_ij=Σ_rs I(r,s)z_ri z_sj (`scoreCovariance`). The residual sandwich C_X(I,u)=B_XXᵀ[I(r,s)u_ru_s]_rs XB_X expands `plugInCovariance`, `sandwichCovariance`, and `patternMeat`.
* A finite distribution is a real function w_s≥0 with Σ_s w_s=1. Its mean is E_w f=Σ_s w_s f_s and its variance is Σ_s w_s(f_s−Σ_t w_t f_t)². Its associated measure is Σ_s ENNReal.ofReal(w_s)δ_s (`distributionMeasure`).
* For a measure μ, A(μ,u)_rs=∫u_ru_s dμ (`errorMoments`): this is an uncentered second moment, a covariance when all means are zero. Integrals are Mathlib real Bochner integrals. Var_μ f is Mathlib's `variance`: the extended integral of |f−∫f dμ|², converted with `ENNReal.toReal`.
* `TendstoInMeasure μ f atTop (fun _ => L)` says that for every ε>0 the μ-measure of {|f_m−L|≥ε} tends to zero. `∀ᵐ ω ∂μ` means μ-almost every ω. `iIndepFun block μ` means the random variables block_b are jointly independent (every finite subfamily satisfies the product law). `Measurable` uses the given measurable spaces, with the standard discrete measurable spaces on the finite sample alphabets here.

## SAP.P032.T1

The theorem is universally quantified over an arbitrary type Ω and a measurable-space structure on Ω. There is no probability measure or data hypothesis at the theorem's outer level. Its conclusion is the conjunction below. All the fixed finite facts are unconditional; the replication clauses are implications for every law and block sequence on that Ω. There are also two existential probability-space clauses independent of the outer Ω.

### Fixed two-record model

There are four members and two records with dyads {0,1} and {2,3}. The four possible error vectors, in sample order, are (−1,−1),(−1,1),(1,−1),(1,1). The negative law has probabilities (1,3,3,1)/8 and the positive law has (3,1,1,3)/8. Put A_s=[[1,s/2],[s/2,1]]. The intercept design X_+=(1,1)ᵀ and slope design X_−=(−1,1)ᵀ both have one coefficient.

`pairMomentStatement` asserts, for every record, that its mean is zero under each law and, for every ordered record pair, that its second moment is respectively A_−1 or A_1. `pairSamplingStatement` asserts |u_r|≤1 for every sample/record, both covariances are positive definite, both design Gram determinants are nonzero, and the actual one-coefficient OLS sampling variances are 1/4 (negative-law intercept), 1/4 (positive-law slope), and 3/4 (positive-law intercept).

`pairSpectrumStatement` asserts A_−1 Q=Q diag(1/2,3/2), A_1 Q=Q diag(3/2,1/2), and Q(Q/2)=I, where Q=[[1,1],[1,−1]].

For c=(1), `pairInterceptStatement` asserts det(X_+ᵀX_+)≠0, h=X_+B_Xc=(1/2,1/2), q(A_−1,h)=1/4, q(A_−1^D,h)=1/2, and the first quadratic form is strictly smaller than the second. `pairSlopeStatement` asserts det(X_−ᵀX_−)≠0, h=(−1/2,1/2), q(A_1,h)=1/4, q(A_1^D,h)=1/2, and also q(A_1,(1/2,1/2))=3/4 while its restricted version equals 1/2. Here D is always the two disjoint dyads above.

### Four-record block

There are six members, dyads ({0,1},{0,2},{3,4},{3,5}), and the 16 sign vectors in {−1,1}⁴ in lexicographic order (−1 first). Every vector has mass 3/64, with an additional 1/8 on samples 3=(−1,−1,1,1) and 12=(1,1,−1,−1). The stated covariance is

```
A4 = [ 1    1/4 −1/4 −1/4
       1/4  1   −1/4 −1/4
      −1/4 −1/4  1    1/4
      −1/4 −1/4  1/4  1   ].
```

Every component has mean zero, every second moment equals the corresponding A4 entry, A4 is positive definite, and the following exact spectral equalities hold:

```
Q4 = [ 1  1  0  1; 1 −1  0  1; −1  0  1  1; −1  0 −1  1 ]
L4 = [ 1/4  1/4 −1/4 −1/4; 1/2 −1/2 0 0;
       0 0 1/2 −1/2; 1/4 1/4 1/4 1/4 ]
L4 Q4 = I,  A4 Q4 = Q4 diag(7/4,3/4,3/4,3/4).
```

For h=(1/4,...,1/4), q(A4,h)=3/16 and q(A4^D,h)=5/16. The actual finite-law variance of (Σ_r u_r)/4 is 3/16. For every one of the 16 samples the intercept fit identities given below hold.

### Six-edge block

The four members have all six distinct dyads in order 01,02,03,12,13,23. Write A6 for the matrix with diagonal 1, incident off-diagonal entries 1/8 and disjoint entries −1/2. A sample a is a function {0,...,12}→{0,1}, uniformly distributed with mass 1/8192. Put η_j=−1 when a_j=0 and +1 otherwise. For edge r, let t_r=(0,1,2,2,1,0)_r and σ_r=+1 for r<3 and −1 for r≥3. The errors are exactly

u_r=(√2/4)Σ_{i∈D_r}η_i + σ_r(√2/2)η_{4+t_r} + (1/2)η_{7+r}.

Every error has mean zero and every second moment equals A6. For every a,r, |u_r|≤√2+1/2. A6 is positive definite, and

```
Q6 = [ 1  1  1  1  0  0;
      −1  0  1  0  1  0;
       0 −1  1  0  0  1;
       0 −1  1  0  0 −1;
      −1  0  1  0 −1  0;
       1  1  1 −1  0  0 ]
L6 = [ 1/6 −2/6 1/6 1/6 −2/6 1/6;
       1/6 1/6 −2/6 −2/6 1/6 1/6;
       1/6 1/6 1/6 1/6 1/6 1/6;
       1/2 0 0 0 0 −1/2; 0 1/2 0 0 −1/2 0; 0 0 1/2 −1/2 0 0 ]
L6 Q6 = I,  A6 Q6 = Q6 diag(1/4,1/4,1,3/2,3/2,3/2).
```

Every row of A6 sums to 1; every row of A6^D sums to 3/2; each dyadic-mask row sums to 5. At h=(1/6,...,1/6), the full, dyad-restricted and diagonal-only quadratic forms are 1/6, 1/4, 1/6 respectively. Every sample satisfies the intercept fit identities. The atomic measure of the uniform 13-bit distribution equals the product of 13 fair two-point measures (`sixProductMeasure`), not merely a formal assertion about its moments.

### Intercept fits, existence, and replication

For any finite record vector u involved here, N is its number of records, ū=N⁻¹Σ_r u_r, and the design is the N×1 matrix of ones. `interceptFitStatement u` means b_X(u) is the constant one-coordinate vector ū, e_X(u)_r=u_r−ū, and X B_X(1) is the constant N⁻¹ vector. The residual variance used below is

V_D(u)=N^(−2)Σ_rs I_D(r,s)(u_r−ū)(u_s−ū).

For each of the four-block and six-block sample weights, there exists a type Ω', a measurable-space structure on it, a probability measure μ', and a sequence block:ℕ→Ω'→S, with every block_b measurable, the block_b jointly independent, and every atom probability μ'{block_b=a}=ENNReal.ofReal(w_a). These are genuine existential conjuncts.

Replicated records are (b,r) with b∈Fin m. Their members are tagged pairs (b,i), so two distinct blocks have disjoint member sets. Errors are the corresponding component of block_b. This expands `blockDyad`, `fourReplicatedDyads`, `sixReplicatedDyads`, and both replicated-error functions.

For every μ on the outer Ω, every instance that μ is a probability measure, and every sequence block:ℕ→Ω→Fin 16, assume (in that order) every block is measurable, joint independence, and the atom probabilities of the four-block law. Then:

* For every natural m≥1, every ω satisfies the intercept fit identities, and
  (4m)² V_D(u)=Σ_{b<m}[(u_b0+u_b1)²+(u_b2+u_b3)²]−8mū².
* For every such m, Var_μ ū=3/(16m), E_μ V_D=(10m−3)/(32m²), E_μ V_D−Var_μ ū=(4m−3)/(32m²), and Var_μ ū<E_μ V_D.
* The ratio V_D/Var_μ ū, evaluated with m+1 blocks and indexed by m→∞, converges in probability to 5/3.

For every μ on Ω, every probability-measure instance, and every block:ℕ→Ω→(Fin 13→Fin 2), assume measurable blocks, joint independence and μ{block_b=a}=1/8192 for every b,a. Put Q(a)=Σ_rs I_D(r,s)u_r(a)u_s(a), the explicitly defined `sixIncidentQuadratic`. Then:

* For every natural m≥1, every ω satisfies the intercept fit identities. For all b,r, E_μ u_r(block_b)=0; for all b,r,s its second moment is A6_rs; and for every b, E_μ Q(block_b)=9.
* For every such m and every ω, (6m)V_D=Σ_{b<m}Q(block_b)/(6m)−5ū².
* For every such m, Var_μ ū=1/(6m); the population dyad-restricted second-moment quadratic form at constant weights 1/(6m) is 3/(2·6m), and its diagonal-only version is 1/(6m).
* E_μ V_D=3/(2·6m)−5/(6m)². The strict inequality Var_μ ū<E_μ V_D holds if and only if m≥2.
* With one block, E_μ V_D=1/9 and E_μ V_D<Var_μ ū.
* For μ-almost every ω, (6(m+1))V_D, using m+1 blocks, tends to 3/2 as m→∞.

The scope of m≥1 in each replication clause includes all its displayed finite-block equalities. The limits and the one-block six-edge assertions follow after that universal clause, under just the block hypotheses.

### Junk-value audit

All fixed probability weights are nonnegative and normalized; an empty finite sample type cannot carry `FiniteDistribution`, since its total would be 0=1. `ENNReal.ofReal` normally truncates negative reals to zero, but no weight here is negative. Finite sums need no integrability convention. The actual probability-space integrals and variances concern bounded measurable functions of finite-valued blocks, so their Bochner integrals exist and extended variances are finite; neither the integral's default zero nor `toReal ∞=0` is used substantively. Every measure in these applications is a probability measure, hence finite and σ-finite.

Scalar inverse and division are total with 0⁻¹=0. `recordMean` and `residualInterceptVariance` would return zero on empty record types, and a singular Gram matrix has total inverse zero. The relevant fixed designs have nonzero determinants; replication finite formulas require m≥1; limits use m+1, so N is positive and the denominator sampling variances are positive. The empty-type behavior does not drive any counterexample. Natural differences such as 4m−3 in the formulas are real differences after casting, not truncated natural subtraction. Integer power −2 means inverse square. √2 is in its ordinary nonnegative domain. All array entries and constructed finite indices are in bounds; finite literals can in general wrap modulo their size, but none of these labels do. No logarithm, real power, supremum, infimum, limsup or liminf occurs. An outer Ω admitting no probability measure makes its two replication implications vacuous on that Ω, but leaves the finite facts and the separate existential independent-realization conjuncts intact.

## SAP.P032.T5

This is a closed proposition with no parameters or assumptions. It asserts four separate negations, not one negation of their conjunction:

1. It is false that for every n,p,k∈ℕ, dyad assignment D:Fin n→two-element subsets of Fin k, real n×p design X, contrast c∈ℝ^p and real n×n matrix A, the following implication holds: if det(XᵀX)≠0, A is positive semidefinite and there exist disjoint dyads r,s with A_rs≠0, then q(A^D,XB_Xc)≤q(A,XB_Xc).
2. The same universal implication with strict `<` is false.
3. It is false that for every (small-universe) type Ω, measurable-space structure, probability measure μ, natural n,p,k, dyads D, design X, coefficient vector β, contrast c and errors u:Fin n→Ω→ℝ, the following implication holds: if det(XᵀX)≠0, every u_r is in L²(μ), every ∫u_r dμ=0, and some disjoint dyads r,s have ∫u_ru_s dμ≠0, then E_μ[q(C_X(I_D,e_X(Xβ+u)),c)]≤Var_μ[cᵀb_X(Xβ+u)].
4. It is false that for every type Ω, measurable-space structure, probability measure μ, p∈ℕ, sequences of finite record types R_m and member types M_m with decidable equality, dyads D_m, designs X_m with p columns, fixed β,c, and errors u_m, the following implication holds: if |R_m|→∞, every det(X_mᵀX_m)≠0, every u_mr is L² with mean zero, eventually some nonincident second moment is nonzero, and eventually Var_μ[cᵀb_Xm(X_mβ+u_m)]>0, then for every real L, convergence in probability of q(C_Xm(I_Dm,e_Xm(X_mβ+u_m)),c)/Var_μ[cᵀb_Xm(X_mβ+u_m)] to L implies L≤1.

Quantifier order matters: in each negated statement all data precede its hypotheses. In the fourth universal reading, L is universally quantified after the growth/full-rank/moment/nonincident/positive-variance hypotheses. Its negation requires a genuine limiting example with a real limit above 1. The witnesses to the four negations may be different.

`UniversalPopulationBound`, `UniversalStrictPopulationBound`, `UniversalExpectationBound` and `UniversalLimitBound` expand to exactly these assertions. The covariance, residual and sandwich notation is fully expanded in the shared notation above; there is no separate lower-bound predicate hidden inside it.

### Junk-value audit

Nonsingular Gram hypotheses block singular-inverse junk values. L² on a probability space implies integrability of errors, products, fitted contrasts and residual quadratic sandwiches, so all moments in the expectation/limit readings exist and the variances do not use `toReal ∞`. Zero real division is allowed at finitely many early indices in the limit reading, but the denominator is eventually positive; convergence in probability is unchanged by a finite prefix. The population readings do not require c≠0: a zero contrast cannot violate the weak inequality, but can violate the strict universal reading. The negation of a universal statement does not assert that every allowed input is a counterexample. Empty finite types are syntactically allowed; the nonincident-pair existence forces records and members in any witness, and full rank rules out positive-dimensional designs with no rows. For p=0 the empty Gram determinant is 1 and the quadratic forms are zero; this cannot witness failure of the weak population reading. The asymptotic cardinalities are naturals with ordinary divergence, not truncated differences. No log, sqrt, rpow, extrema or partial-function defaults occur in these closures.

## SAP.P032.T3

This is a closed conjunction about fixed data, with no universal data assumptions. There are ten records, six subject ids, four members and one real covariate. The record table (id, unordered dyad, start, stop, x, status), with labels starting at zero, is:

```
0: (0,01,0,1, 1,1)    1: (1,23,0,1,−1,1)
2: (2,02,0,1, 1,0)    3: (2,02,1,2, 3,1)
4: (3,13,0,1,−1,0)    5: (3,13,1,2,−3,1)
6: (4,03,0,1, 1,0)    7: (4,03,1,3, 1,2)
8: (5,12,0,1,−1,0)    9: (5,12,1,3,−1,2).
```

A record is at risk at natural time t exactly when start<t≤stop. It is an event at t exactly when status=1 and stop=t. Let R_t be the risk set, d_t the event count, N_t its risk count, and x̄_t=N_t⁻¹Σ_{r∈R_t}x_r. The log likelihood is the Breslow tied-event expression over just t=1,2:

ℓ(β)=Σ_{t=1,2}[Σ_{r:event at t}βx_r−d_t log(Σ_{r∈R_t}exp(βx_r))].

`survivalFitStatement` asserts for every β∈ℝ that
ℓ(β)=−2log(6cosh β)−2log(2cosh(3β)+2cosh β), and for every nonzero β, ℓ(β)<ℓ(0). Thus the maximum is uniquely at 0, rather than merely stationary there.

`survivalRiskSetsStatement` gives R_1={0,1,2,4,6,8} and R_2={3,5,7,9}. `survivalScoresStatement` gives N_1=6,N_2=4,d_1=d_2=2,x̄_1=x̄_2=0. The observed-information expression Σ_t d_t[(Σ_{r∈R_t}x_r²)/N_t−x̄_t²] is 12. For every record, its score

Σ_{t=1,2}1_{r∈R_t}(1_{event(r,t)}−d_t/N_t)(x_r−x̄_t)

equals the corresponding entry of z=(2/3,−2/3,−1/3,3/2,1/3,−3/2,−1/3,−1/2,1/3,1/2), and Σ_r z_r=0. These are the expanded `survivalEfficientScore`, `survivalScores`, and `survivalInformation`. Subject sums of z, for each id 0,...,5, are (2/3,−2/3,7/6,−7/6,−5/6,5/6). The influence value v_r is defined to be z_r/12.

For any scalar record scores v, `recordScalarCovariance` is Σ_r v_r²; `clusterScalarCovariance g` is Σ_k(Σ_{r:g_r=k}v_r)²; and the member-i scalar covariance is (Σ_{r:i∈D_r}v_r)²+Σ_{r:i∉D_r}v_r². At these influences the record covariance is 19/432, the subject covariance is 5/144, the four member covariances are (25/864,59/2592,89/2592,185/2592), and their sum is 17/108.

The direct dyadic ordered-pair sum Σ_rs I_D(r,s)v_rv_s is 5/144. Numerically the correct subtraction 17/108−5/144−2(19/432) equals 5/144, replacing the final term by the subject covariance gives 23/432, and its excess is 8/432. The stated multiplicative correction ((10−1)/10)(6/(6−1)) is 27/25; using that corrected subject term gives 103/2160. Each of the three final values is positive, the latter two differ from 5/144, and clipping each scalar value with max(value,0) leaves it unchanged. Finally the predicates id_r=id_s and D_r=D_s agree for all r,s (`survivalPartitionStatement`).

### Junk-value audit

The risk-mean helper accepts arbitrary natural t, including empty risk sets, where total division returns 0. The likelihood, score and information expressions here only evaluate t=1,2, with counts 6 and 4. Both exponential risk sums are strictly positive for all real β. The closed likelihood's log arguments are also strictly positive because cosh is positive. Thus Mathlib's real-log extension (log 0=0, log negative input=log its absolute value) does not affect this claim. Divisors 12, 432 and other rational denominators are positive. The correction uses real subtraction (10−1 and 6−1), not truncated natural subtraction. No integrals, infinite variances, empty relevant index sets, square roots, rpow, limsup/liminf or partial-function defaults occur. Status 2 is simply non-event by the explicit predicate; the statistical interpretation of that coding must be checked later against the claim. All finite table indices are valid.

## SAP.P032.T6

This is a closed assertion with no data assumptions. There are ten distinct dyads among five members, in order 01,02,12,03,13,23,04,14,24,34. The covariate vector is x=(3,0,2,1,−1,1,−3,−2,3,−2), the response is y=(3,−2,−2,1,1,0,0,2,1,0), and row r of X is (1,x_r). Put B=(1/208)[[21,−1],[−1,5]], e=(31,−31,−33,7,9,−6,−2,23,5,−3)/13, z_r=e_r(1,x_r), M=S(I_D,z), and V=BMB. These unfold all of `tenDyadData`, `tenCovariate`, `tenResponse`, `tenDesignMatrix`, `tenBreadMatrix`, `tenResidualValues`, `tenScoreValues`, `tenDyadicMeat`, and `tenCovariance`.

`tenFitStatement` asserts XᵀX=[[10,2],[2,42]], B(XᵀX)=I, B=(XᵀX)⁻¹, Xᵀy=(4,4), b_X(y)=(5/13,1/13), e_X(y)=e, and Xᵀe=0.

`tenVarianceStatement` asserts

```
M = (1/169)[[1984,−1108],[−1108,50]],
S(I_0,z) = (1/169)[[3744,4052],[4052,15584]],
V = (1/3655808)[[460765,−79681],[−79681,7157]].
```

`tenDecompositionStatement` asserts Σ_{i=0}⁴S(I_i,z)−S(I_0,z)−3S(I_0,z)=M. The dyad-cluster mask here equals the record mask because all ten dyads are distinct.

V is symmetric. Every diagonal V_ii is strictly positive, det V=−70529/308915776, q(V,(1,6))=−237755/3655808, and V is not positive semidefinite. For every proof hV of its symmetry, the diagonal-gated PSD operation returns V itself. Also q((5/4)V,(1,6))=−1188775/14623232.

In full, for a symmetric real matrix A, Mathlib supplies orthonormal eigenvectors Q and real eigenvalues λ. `clipEigenvalues Q λ` is Q diag(max(λ_j,0))Qᵀ; `psdPart A hA` uses that spectral data for A. `diagonalGate A hA` is this clipped matrix if any A_ii<0, and A otherwise. Consequently the universal quantifier over hV concerns proof independence, not an assumption that V is symmetric: symmetry is separately asserted in this conjunction.

### Junk-value audit

The design's Gram determinant is 416, so its inverse is ordinary and B's denominator 208 is nonzero. Every rational denominator is positive. All indices in the input arrays are valid. No Bochner expectation, variance conversion, real logarithm, square root, rpow, extrema of sets or limits occur. Eigenvalue clipping uses a complete Mathlib spectral decomposition of an actually symmetric finite real matrix; it has no unspecified/default partial eigendecomposition. The gate skips clipping because of strict positive diagonal entries, not a junk value. The subtraction coefficient 3 is real; no natural truncation occurs. Empty types are not involved (the coefficient type is Fin 2).

## SAP.P032.T9

This is `T9WholeStatement`, a closed proposition polymorphic in two universe levels. Its first conjunct universally quantifies, in order, finite coefficient index type P, finite component index type J, their `Fintype` instances, natural m, a proof m≥2, real weight and factor functions s,a:J→ℝ, a proof every a_j≠0, completed-data matrices U_jt (P×P), a proof every U_jt is symmetric, and common coefficient estimates b_t∈ℝ^P. No positive-definiteness, probability-space, nonzero-between-variance, or finite-sample-factor positivity hypothesis is imposed.

The SAP operations expand as follows:

b̄_i=m⁻¹Σ_t b_ti,
B_ij=(m−1)⁻¹Σ_t(b_ti−b̄_i)(b_tj−b̄_j),
Q=(1+m⁻¹)B,
Ū_j=m⁻¹Σ_tU_jt,
Pfirst=Σ_j s_ja_j[a_j⁻¹Ū_j+Q],
Cfirst=m⁻¹Σ_tΣ_j s_jU_jt+Q,
c=Σ_j s_ja_j.

These expand `estimateAverage`, `betweenCovariance`, `rubinContribution`, `componentAverage`, `poolBeforeCombining`, and `combineBeforePooling`. Factors a_j do not vary by imputation. The first conjunct asserts all four equalities, for every such input:

Pfirst=Σ_j s_jŪ_j+cQ;
Cfirst=Σ_j s_jŪ_j+Q;
Pfirst−Cfirst=(c−1)Q;
Pfirst+(1−c)Q=Cfirst.

The next conjunct says that for every natural k the component set J=Fin k ⊕ Fin 2 has weights 1 on its k left components, −1 on right component 0 and −(k−2) on right component 1, and their sum equals 1. Here k−2 is real subtraction, so this remains an algebraic identity at k=0,1.

The next conjunct quantifies over finite P, natural k,m with m≥2, symmetric U:(Fin k ⊕ Fin 2)→Fin m→Matrix P P ℝ and common b. With those decomposition weights and all a_j=1, it asserts Pfirst=Cfirst.

The final universal scalar conjunct quantifies over natural k, arbitrary real Gi_i (i∈Fin k), GD and n, with no nonzero assumptions. `undoFactors` gives a_i=1−1/Gi_i, a_D=1−1/GD, a_0=1−1/n. It asserts

Σ_j s_ja_j−1=−Σ_i(1/Gi_i)+1/GD+(k−2)/n.

Finally, at k=4, all Gi_i=13, GD=6 and n=24, this coefficient difference equals −3/52 and is nonzero. The numerical conjunction does not supply a particular b or require Q≠0, so it does not on its own assert that a particular matrix gap is nonzero.

### Junk-value audit

m≥2 prevents zero m and m−1 denominators in the pooling identity, and all a_j≠0 makes the factor cancellation legitimate. The difference m−1 is formed in ℝ after casting m, with no natural truncation. The separate scalar identity deliberately permits Gi_i,GD,n=0, uses real total division 1/0=0, and the docstring explicitly discloses this extension; it must not be silently read as a valid statistical finite-sample factor in that case. Its displayed numerical specialization has no zero denominators. P and J may be empty, and k may be 0: empty sums are 0 and empty matrices are legitimate. The general algebraic identities still hold (with J empty Pfirst=0,Cfirst=Q,c=0), while the DCR component set always has two right components. The nonzero numerical coefficient avoids an exclusively empty-index result. There are no logs, square roots, real powers, integrals, infinite extended quantities, sInf/sSup or limsup/liminf. Symmetry is an explicit assumption and no PSD modification is present in the operations, so there is no spectral partial-function issue.
