# Blind reading

This file was saved before opening `claims.json` or `record.json`. Sources read:
the five docstrings and declarations in `SAP/P032/Challenge/Part1.lean`, all
source definitions in their closures, and the types of all 128 distinct closure
entries, including generated proof declarations. `scratch/ClosurePrint.lean` and
`scratch/ClosureTypes.lean` both compile; their output records the elaborated
definitions and auxiliary types. The auxiliary declarations certify positive
literal bounds (`Nat.AtLeastTwo`, `NeZero`), cardinality two of the listed dyads,
or nonnegative normalized finite weights. Names mentioning another statement do
not import that other statement: Lean reuses proofs of numeric literal bounds.

The notation below is mathematical shorthand, not additional assumptions.
Finite matrices mean functions on their row and column types; matrix
multiplication, matrix-vector multiplication, and dot products are finite sums.
For a real symmetric matrix, Mathlib positive semidefinite means symmetry and
nonnegativity of every quadratic form; positive definite replaces this by strict
positivity on nonzero vectors. All type parameters are universally quantified.

## SAP.P032.T4

**Types and definitions.** Universally choose finite types `R` (records), `M`
(members), and `P` (coordinates), with decidable equality, and any type `G`
(subject labels) with decidable equality; `G` need not be finite. A `DyadData M`
is an actual finite subset of `M` of cardinality exactly two. Write `d_r` for
the two-element subset assigned by `d : R → DyadData M`, and `N = |M|`.
For an ordered pair `(r,s)`, define real-valued masks

- `D_rs = 1` if `d_r ∩ d_s` is nonempty, otherwise zero (`dyadicMask`);
- `E_rs = 1` if `d_r = d_s`, otherwise zero (`repeatedMask`);
- `I_rs = 1` if `r=s`, otherwise zero (`recordMask`);
- `B^i_rs = 1_{i∈d_r and i∈d_s} + 1_{r=s and i∉d_r}` (`memberMask`);
- `J_rs = 1_{g(r)=g(s)}` and `K_rs = 1_{r≠s and g(r)=g(s)}`
  (`subjectMask` and `subjectCrossMask`).

In particular **every** diagonal entry of every `B^i` is one, including for
members not in that record. For real vectors `z_r : P → ℝ`, write
`S(H,z)_{pq} = Σ_r Σ_s H_rs z_{rp} z_{sq}` (`scoreCovariance`). Define
`q(A,h) = Σ_r Σ_s h_r h_s A_rs` (`quadForm`) and
`L_rs = Σ_i B^i_rs - E_rs - (N-2)I_rs` (`pairCoefficient`). All subtractions
involving `N` in these formulas occur **after casting to ℝ**.

**Quantifiers and assertions.** The theorem is the conjunction of five parts.

1. For every dyad assignment `d`, then every real score array `z`,
   `Σ_i S(B^i,z) - S(E,z) - (N-2) S(I,z) = S(D,z)`.
2. For every `d`, then records `r,s`, `L_rs=D_rs`. Also, conditionally:
   if `r=s`, `L_rs=N-1-(N-2)`; if `r≠s` and `d_r=d_s`, `L_rs=2-1-0`;
   if `d_r≠d_s` and their intersection has cardinality one,
   `L_rs=1-0-0`; if their intersection is empty, `L_rs=0`.
3. For every two dyads `a,b`, either they are equal and their intersection has
   cardinality two, or they are unequal and the intersection has cardinality at
   most one. Together with nonnegative natural cardinalities this exhausts the
   possibilities used by part 2.
4. For every `d,z,g` in that order, put `V0=S(I,z)`, `Vi=S(J,z)`,
   `Vr=S(D,z)`, `C=Σ_i S(B^i,z)-S(E,z)`, `k=N-2`. Then
   `Vi=V0+S(K,z)`, `C-k Vi=Vr+k(V0-Vi)`, and
   `C-k Vi=Vr-k S(K,z)`. If `g` is injective then `Vi=V0` and
   `C-k Vi=Vr`. Finally for **every real** `α`,
   `C-k(α Vi)=Vr+k(V0-α Vi)`. No injectivity, scalar sign, nonzero score,
   covariance interpretation, fit, or stochastic assumption is required.
5. The closed proposition `survivalDiscrepancyStatement`, described next.

**Closed survival data and last conjunct.** `sixDyadData`, indexed from zero,
is `[{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}]` on `Fin 4`. `SurvivalRecord` is
a structure with an id in `Fin 6`, such a dyad, start/stop/status in `ℕ`, and a
real covariate. `survivalRecords` is the following total array; columns are
`id, sixDyadData index, start, stop, x, status`:

```
0  0  0  1   1  1
1  5  0  1  -1  1
2  1  0  1   1  0
2  1  1  2   3  1
3  4  0  1  -1  0
3  4  1  2  -3  1
4  2  0  1   1  0
4  2  1  3   1  2
5  3  0  1  -1  0
5  3  1  3  -1  2
```

`survivalScores = [2/3,-2/3,-1/3,3/2,1/3,-3/2,-1/3,-1/2,1/3,1/2]` and
`v_r = survivalInfluence r = survivalScores r / 12`.
The final conjunct asserts exactly:

```
q(D,v) = 5/144
17/108 - 5/144 - 2(19/432) = 5/144
17/108 - 5/144 - 2(5/144) = 23/432
23/432 - 5/144 = 8/432
((10-1)/10)(6/(6-1)) = 27/25
17/108 - 5/144 - 2((27/25)(5/144)) = 103/2160
5/144 ≠ 23/432; 5/144 ≠ 103/2160
0 < 5/144; 0 < 23/432; 0 < 103/2160.
```

Apart from the first line, these are identities/inequalities of literal real
numbers. This conjunct alone does not assert that those literals equal fitted
component covariances, that the scores are derivatives of a Cox likelihood, or
that 12 is its information. The generic substitution identities are separate
universal assertions in part 4. The docstring says common scores yield the
decomposition and coefficient count, and describes subject-id substitution and
residual scaling discrepancies.

**Junk-value audit.** All sums are finite and all numbers real. The closed
fractions have nonzero denominators 3, 2, 12, 108, 144, 432, 10, 5, 25, and
2160 (and their products). No divide-by-zero is used. `N-2` and `N-1` are real
subtractions, not truncated natural subtraction. Natural fields in survival
records are just literals here. `Fin` arrays are indexed within their declared
lengths; literal coercion modulo a `Fin` size is harmless because all labels fit.
No integral, infinity, log, sqrt, rpow, infimum, supremum, or limiting operation
occurs, despite some shared auxiliary proof names containing `Likelihood`.
Empty `R` or `P` makes some sums zero; if `R` is inhabited, a dyad assignment
forces `|M|≥2`. These edge cases do not account for the nonempty fixed survival
conjunct. `G` may be empty, making the `g` quantifier empty for inhabited `R`;
the theorem also covers ordinary inhabited label types.

## SAP.P032.T2

**Types and shared notions.** Universally choose finite decidable types `R,M,P`
and a type `Ω` with a sigma algebra. Dyads, `D`, `q`, and all finite sums have
the meanings above. For a real design matrix `X : R×P → ℝ`, define
`B=(XᵀX)⁻¹` (`olsBread`), `LS(X,y)=B Xᵀ y` (`leastSquares`), and
`Sand(X,A)=B Xᵀ A X B` (`sandwichCovariance`). Matrix inverse here is Mathlib's
total nonsingular inverse, not a generalized inverse. For real errors
`u_r : Ω → ℝ`, `A_rs=∫ u_r(ω)u_s(ω) dμ` (`errorMoments`),
`AD_rs=D_rs A_rs` (`dyadicRestriction`), and
`O(d,A,h)=Σ_r Σ_s 1_{d_r∩d_s=∅} h_r h_s A_rs` (`omittedSum`).
For real random variables, Mathlib covariance is
`∫ (f-∫f)(g-∫g) dμ`; variance is the real conversion of the extended integral
of the squared centered norm. In the finite-second-moment setting here these
are the ordinary real covariance and variance. `MemLp f 2 μ` means almost
everywhere strong measurability and finite L² seminorm.

**Universal part, quantifier order and hypotheses.** For every measure `μ` on
`Ω` with total mass one, every dyad assignment `d`, and every fixed real matrix
`X` with `det(XᵀX) ≠ 0`, then for every coefficient vector `β : P → ℝ` and
error family `u : R → Ω → ℝ` such that each `u_r` is in L² and has mean zero,
put `A,AD` as above and
`V(c)=Var(cᵀ LS(X,Xβ+u))`. The following conjunction holds:

- For every `c : P → ℝ`, let `h=XBc`. For every `ω`,
  `cᵀ LS(X,Xβ+u(ω))-cᵀβ=hᵀu(ω)`.
- For that same `c`, `V(c)=q(A,h)=q(Sand(X,A),c)` and
  `q(A,h)-q(AD,h)=O(d,A,h)`.
- For that `c`, `q(AD,h)≤V(c)` iff `O≥0`; `q(AD,h)<V(c)` iff `O>0`;
  and `V(c)<q(AD,h)` iff `O<0`.
- The assertion `∀c, q(AD,XBc)≤V(c)` is equivalent to positive
  semidefiniteness of `Sand(X,A-AD)`.
- `Sand(X,A-AD)` is positive semidefinite iff `Xᵀ(A-AD)X` is positive
  semidefinite.

There is no independence, sign of covariance, normality, or asymptotic
assumption, and no random-design assertion.

**Closed finite examples.** A `FiniteDistribution S` is a real weight for each
element of a finite type, all weights nonnegative and summing to one.
`finiteMean(w,f)=Σ_s w_s f_s` and
`finiteVar(w,f)=Σ_s w_s(f_s-Σ_t w_t f_t)²`. On the four atoms
`(-1,-1),(-1,1),(1,-1),(1,1)` (`pairErrorValues`), the negative law has weights
`(1,3,3,1)/8`, and the positive law has weights `(3,1,1,3)/8`.
`pairDyads=[{0,1},{2,3}]` on four members. `pairCovariance(t)` is
`[[1,t/2],[t/2,1]]`; `pairIntercept` is the two-by-one all-one matrix, and
`pairSlope` has its single column `[-1,1]`. The remaining conjuncts say:

1. Under each law both error coordinates have mean zero; every second moment
   is the corresponding entry of `pairCovariance(-1)` or `pairCovariance(1)`.
2. Every error coordinate has absolute value at most one, both covariance
   matrices are positive definite, and both one-column designs have nonsingular
   Gram matrices. The negative-law intercept estimator has finite variance
   `1/4`, the positive-law slope estimator variance `1/4`, and the positive-law
   intercept estimator variance `3/4`.
3. For the intercept design and contrast one, `h=[1/2,1/2]`, the negative-law
   full quadratic variance is `1/4`, and the dyad-restricted value is `1/2`,
   with the strict ordering `1/4<1/2`.
4. For the slope design and contrast one, `h=[-1/2,1/2]`, the positive-law full
   quadratic variance is `1/4`, and the dyad-restricted value is `1/2`.
   For the same positive covariance and weights `[1/2,1/2]`, the values are
   instead `3/4` and `1/2`.
5. Omitted sums for the negative-law intercept, positive-law intercept, and
   positive-law slope weights respectively are `-1/4`, `1/4`, and `-1/4`.
   Both positive-law off-diagonal covariances are strictly positive.

The docstring describes an exact weighted-omitted-covariance comparison and its
sign and PSD characterizations.

**Junk-value audit.** Singular Gram matrices would give a total inverse (zero
for singular real square matrices), but the universal hypothesis excludes
them, and the fixed designs explicitly have nonzero determinants. The zero by
zero matrix is possible if `P` is empty: its determinant is one and there are
only empty contrasts. Nontrivial one-column examples are separately present.
An inhabited record type forces at least two members. If `Ω` is empty there
is no probability measure, so only the universal stochastic part is empty;
the fixed finite examples persist independently of `Ω`.
Bochner integration of a nonintegrable function is defined to be zero, and
variance uses `ENNReal.toReal`, which sends infinity to zero. L² plus a
probability measure guarantees all individual means, pair products, and finite
linear combinations used here are integrable with finite second moments, so
neither convention affects this theorem. All finite-law expressions are finite
sums of real numbers. Every closed denominator (2, 4, 8 and the Gram determinant
2) is nonzero. No truncated subtraction, log, sqrt, rpow, extrema of sets,
limsup/liminf, limit, or partial-function default occurs.

## SAP.P032.T11

**Types, hypotheses, and quantifiers.** Universally choose finite decidable
types `R,M,P`. For every dyad assignment `d : R → DyadData M` and every
real matrix `X : R×P → ℝ`, assume `det(XᵀX) ≠ 0` and that **every** member
`i∈M` occurs in at least one record's two-element dyad. For every response
`Y : R → ℝ`, let `B=(XᵀX)⁻¹`, `βhat=B XᵀY`, and `u=Y-Xβhat`
(`fitResidual`). For any real mask `H`, define the record-by-record matrix
`Meat(H,u)_rs=H_rs u_r u_s` (`patternMeat`) and
`F(H)=B Xᵀ Meat(H,u) X B` (`plugInCovariance`). Masks `D,E,I,B^i`
are exactly the masks fully unfolded under T4, including all diagonal entries
of `B^i` equal to one.

The sole conclusion is the matrix identity
`F(D)=Σ_i F(B^i)-F(E)-(|M|-2)F(I)`, with the cardinality cast to the reals
before subtraction. The same design, residuals, and bread occur in every term.
There are no degrees-of-freedom factors, expectations, probability hypotheses,
asymptotics, standard-error operations, or software execution semantics. The
docstring explicitly limits the assertion to this residual-sandwich display;
it excludes a separate pointwise coefficient identity, equivalence to
conventional multiway clustering, software computability, taking diagonal
square roots, and eigenvalue clipping.

**Junk-value audit.** Nonsingularity excludes use of a singular inverse, exactly
as under T2. All other operations are finite real sums and products, with no
division except the legitimate matrix inverse. The coverage hypothesis
excludes padding `M` with unused members. If `R` is empty, coverage forces
`M` empty; nonzero Gram determinant then forces `P` empty. An inhabited `R`
forces `|M|≥2`. Empty parameter matrices also yield valid identities when the
record/member types are inhabited. Natural subtraction is absent: `|M|-2` is
real subtraction. There is no integral, infinity conversion, log, sqrt, rpow,
infimum, supremum, limit, or partial-function default. Nonempty, full-rank
designs and member coverage can be satisfied together.

## SAP.P032.T7

**Generic definitions.** Universally choose a finite decidable type `P` of
matrix coordinates. For a real square matrix `Q` and real vector `λ`, define
`Clip(Q,λ)=Q diag(max(λ_j,0)) Qᵀ` (`clipEigenvalues`). Given a real symmetric
matrix `V` (Mathlib `V.IsHermitian`) with proof `hV`, choose Mathlib's
orthonormal eigenvector matrix `Q` and real eigenvalues `λ`, and set
`Vplus=Clip(Q,λ)` (`psdPart`). `diagonalGate(V)` is `Vplus` if some diagonal
entry of `V` is strictly negative, and is otherwise `V`. These definitions
use a genuine Mathlib spectral decomposition, not an assumed or encoded PSD
conclusion. `q(A,c)` remains the full double sum from T4.

**Conjunction and quantifier order.**

1. For every `Q`, then every `λ`, if `QᵀQ=I` and `QQᵀ=I`, then `Clip`
   is symmetric and PSD. For every real vector `c`,
   `q(Clip,c)=Σ_j max(λ_j,0)(Σ_i Q_ij c_i)²`, and `0≤q(Clip,c)`.
   Further, `Clip(Q,λ)=Q diag(λ)Qᵀ` iff `Q diag(λ)Qᵀ` is PSD.
   No input matrix in addition to this reconstructed one is quantified here.
2. For every matrix `V` and every proof that it is symmetric, `Vplus` is PSD,
   `Vplus=V` iff `V` is PSD, and the gated output is PSD iff either some input
   diagonal is negative or the input already is PSD.
3. For every `a,b,d∈ℝ`, assuming `a≥0` and `d≥0`, the real two-by-two matrix
   `[[a,b],[b,d]]` is PSD iff `b²≤ad`.
4. The fixed ten-record covariance defined below has strictly positive
   diagonals but is not PSD; its trace is `467922/3655808` and its determinant
   is `-70529/308915776`.
5. There exists a proof `hV` of symmetry of that fixed covariance such that its
   two Mathlib eigenvalues are `λplus,λminus` in either order,
   `λminus<0<λplus`, and there exists `q : Fin 2 → ℝ` with `qᵀq=1`,
   `Vq=λplus q`, and `Vplus=λplus q qᵀ`. In addition, this `Vplus` has matrix
   rank one, is PSD, and differs from `V`.

**Fixed data, unfolded.** `tenDyadData` on members `Fin 5` lists
`[{0,1},{0,2},{1,2},{0,3},{1,3},{2,3},{0,4},{1,4},{2,4},{3,4}]`.
`tenCovariate=[3,0,2,1,-1,1,-3,-2,3,-2]`. Row `r` of
`tenDesignMatrix` is `[1,tenCovariate_r]`.
`tenBreadMatrix=(1/208)[[21,-1],[-1,5]]` and
`tenResidualValues=[31,-31,-33,7,9,-6,-2,23,5,-3]/13`.
`tenScoreValues_{ri}=tenResidualValues_r tenDesignMatrix_{ri}`.
`tenDyadicMeat_{ij}=Σ_rΣ_s D_rs tenScoreValues_ri tenScoreValues_sj` and
`tenCovariance=tenBreadMatrix tenDyadicMeat tenBreadMatrix`.
Writing `t=467922/3655808` and `δ=-70529/308915776`,
`tenPositiveRoot=(t+sqrt(t²-4δ))/2` and
`tenNegativeRoot=(t-sqrt(t²-4δ))/2`.
The theorem itself does not assert a response vector, fit equations, or that
the hard-coded bread is an inverse Gram matrix; it asserts the stated
properties of the matrix built from this data. Its docstring describes
unconditional clipping, fixed points, a quadratic formula, the gate criterion,
and the rank-one example.

**Junk-value audit.** All fixed denominators 208, 13, 3655808, 308915776, and
2 are positive. `Real.sqrt` is total and equals zero for negative arguments,
but the discriminant here is strictly positive (`δ<0`), so it is the ordinary
positive root. Spectral choices have no missing-case defaults: symmetry
supplies an orthonormal eigenbasis in every finite dimension. No inverse,
log, rpow, measure, infinite integral, `toReal`, set extrema, or limit occurs.
If `P` is empty, the generic statements concern the unique zero-dimensional
matrix and are valid; the ten-record `Fin 2` example remains nonempty.
`Fin` data accesses use in-range indices. Rank is Mathlib's finite-dimensional
matrix rank; its natural value one has its usual meaning. No truncated
natural subtraction is used (the discriminant subtraction is in ℝ).

## SAP.P032.T12

**Types, quantifier order, and definitions.** For every type `Ω` with a sigma
algebra, and for every probability measure `μ` on it, the theorem asserts two
universal clauses. `outcomeAverage(Y1,Y2)(ω)=(Y1(ω)+Y2(ω))/2` and
`naiveAverageVariance(μ,Y1,Y2)=(Var(Y1)+Var(Y2))/4`. Here variance and
covariance are the genuine Mathlib centered integrals described under T2.

1. For every two real functions `Y1,Y2 : Ω → ℝ`, assuming `MemLp Y1 2 μ`
   and `MemLp Y2 2 μ`,
   `Var((Y1+Y2)/2)=(Var(Y1)+Var(Y2))/4+Cov(Y1,Y2)/2`.
2. For every five real functions `Z : Fin 5 → Ω → ℝ`, assume that each is
   in L² and `Cov(Z_i,Z_j)=0` for every pair of distinct indices. Then for
   **every** four reals `a,b,c,d`, let
   `Y1=a Z0+b Z1+Z3` and `Y2=c Z0+d Z2+Z4` (`countryOutcomes`),
   `Vn=(Var(Y1)+Var(Y2))/4`, and `V=Var((Y1+Y2)/2)`.
   The simultaneous conclusions are:
   `Cov(Y1,Y2)=ac Var(Z0)`;
   `V=Vn+(ac/2)Var(Z0)`;
   if `ac>0` and `Var(Z0)>0` then `Vn<V`;
   if `ac<0` and `Var(Z0)>0` then `V<Vn`;
   if `ac=0` **or** `Var(Z0)=0` then `V=Vn`.

No primitive needs mean zero or a positive variance. Independence is not
assumed, only pairwise zero covariance. The pair-specific noises need not
have equal variances. The docstring describes the covariance correction and
all of these sign cases for five pairwise uncorrelated finite-variance
primitives.

**Junk-value audit.** L² includes almost everywhere strong measurability and
finite second moment; a probability measure makes all involved means and
products integrable. The finite linear combinations and averages also lie in
L². Consequently the Bochner-integral default zero and `toReal(∞)=0` cannot
affect any stated value. Denominators 2 and 4 are nonzero. The five primitive
indices are in range. If `Ω` is empty there is no probability measure, but
ordinary finite probability spaces supply models, including ones with positive
shared variance for the strict cases. No natural subtraction, inverse matrix,
log, sqrt, rpow, extrema of sets, limsup/liminf, limit, or partial-function
default occurs.
