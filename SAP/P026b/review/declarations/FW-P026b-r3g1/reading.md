# Blind reading

Saved before opening either `claims.json` or `record.json`. I read the five
Challenge statements and docstrings, all source declarations in their closures,
and printed every generated declaration named in `closure.json` in
`scratch/Blind.lean` (compiled successfully). No canonical claim or architect
decision was used in this reading.

## Common notation, fully expanded

A `Design Ω I R` is just two functions: a weight `q : Ω → R` and a binary
assignment `t : Ω → I → Bool`. It contains no probability axioms.
Here all relevant sample and unit sets are finite and `R` is either the rational
or real field. Write

* `E_q h = Σ_w q(w) h(w)`. `probabilityDesign` means every weight is nonnegative
  and their sum is one.
* `A_ai(w) = 1` if `t(w,i)=a`, and zero otherwise;
  `p_ai = Σ_w q(w) A_ai(w)`;
  `p_abij = Σ_w q(w) A_ai(w) A_bj(w)`.
  `positiveMarginals` means `p_true,i>0` and `p_false,i>0` for every unit.
* `o_i(w) = y1_i` when `t(w,i)=true`, and `y0_i` otherwise.
  Population total is `Σ_i y_i`, and ATE with argument `N : ℕ` is
  `Δ_N=(Σ_i y1_i-Σ_i y0_i)/(N : R)`.
* Arm HT total is `H_a(y,w)=Σ_i A_ai(w)y_i/p_ai`;
  `H_N(y1,y0,w)=(H_true(y1,w)-H_false(y0,w))/N`.
* Generalized arm total is
  `G_a(y,f,w)=Σ_i [A_ai(w)y_i/p_ai-A_ai(w)f_i(w)/p_ai+f_i(w)]`;
  generalized ATE is `(G_true(y1,f,w)-G_false(y0,f,w))/N`.
* Covariance is exactly `C_q(h,k)=Σ_w q(w)h(w)k(w)
  -(Σ_w q(w)h(w))(Σ_w q(w)k(w))`; variance is `C_q(h,h)`.
* For the variance estimator define `e(p)=1` if `p=0`, and zero otherwise,
  and
  `B_abij(w)=A_ai(w)A_bj(w)/(p_abij+e(p_abij))
  ·(p_abij-p_ai p_bj)·(o_i(w)/p_ai)·(o_j(w)/p_bj)`.
  The printed variance estimator is `1/N²` times
  `Σ_i [A_true,i(o_i/p_true,i)²+A_false,i(o_i/p_false,i)²]`
  plus `Σ_{i≠j}[B_true,true,ij+B_false,false,ij-2B_true,false,ij]`
  plus, for each `a∈{true,false}`,
  `Σ_{i≠j : p_aaij=0}[A_ai o_i²/(2p_ai)+A_aj o_j²/(2p_aj)]`.
  All sums over `i≠j` are ordered, implemented by summing over all `i` and
  over `univ.erase i` for `j`.
* `crossSupport` is the directed condition `p_true,false,ij>0` for every
  distinct ordered pair. `disagreement(i,j)` is
  `Σ_w q(w)·1[t(w,i)≠t(w,j)]`.
* `UnitExperiment I` is a law on the entire finite function set `I → Bool`:
  `q(w)≥0`, `Σ_w q(w)=1`, and both arm marginals of every unit are strictly
  positive. Its associated Design has `t(w,i)=w(i)`. It permits zero weights,
  dependence between units, and allocations with an empty arm.

These expansions are used literally in each section below; no probability,
estimation, covariance, or variance notation stands for an additional SAP
assumption.

## SAP.P026b.T13

Source: `Challenge/Part1.lean:7–10`, `Defs/Part3.lean:37–51` and the listed
Part1 definitions.

Quantifiers, in order: every type `I : Type`, finite enumeration of `I`, decidable
equality on `I`, proof that `I` is nonempty, `UnitExperiment I` as expanded above,
two fixed vectors `y1,y0 : I → ℝ`, and arbitrary predictions
`f : (I → Bool) → I → ℝ`. Let `N=|I|` and `y_a=y1` for true and `y0` for false.
The conclusion is a conjunction:

1. For every Boolean arm `a`,
   `E_q G_a(y_a,f)=Σ_i y_ai-Σ_i C_q(A_ai, w↦f_i(w)/p_ai)`.
2. `E_q[(G_true(y1,f)-G_false(y0,f))/N]-Δ_N`
   equals `(Σ_i C_q(A_false,i,f_i/p_false,i)
   -Σ_i C_q(A_true,i,f_i/p_true,i))/N`.

There is no assumption that the predictions are fixed, fitted by a particular
procedure, or independent of assignment. The docstring describes both arm
identities and the ATE bias identity.

Junk values: field division would give zero for a zero denominator, but all
`p_ai` are positive and `N>0`. The cast of `N` into the reals is exact and
nonzero. Every expectation is a finite sum of finite real values, so no
nonintegrability convention occurs. The unit index is nonempty; the assignment
set is nonempty even without that hypothesis. There are no logs, roots,
extended reals, suprema, limits, truncated subtractions, or partial choices in
this closure.

## SAP.P026b.T14

Source: `Challenge/Part1.lean:12–16`, `Defs/Part4.lean:12–57`, and the listed
Part1/Part2 dependencies.

This is a closed conjunction about one dataset, with no external hypotheses.
There are sixteen units indexed `0,…,15` and ten clusters indexed `0,…,9`:

* Cluster labels: `[0,0,1,1,2,3,4,4,4,5,5,6,6,7,8,9]`.
* Outcomes in both arms: `[1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0]`.
* Covariates: `[4,0,4,1,4,2,4,1,2,5,4,1,4,2,2,3]`.

The assignment sample space is `Fin 6 × Fin 15`, with weight `1/90` each.
The first coordinate enumerates all six two-treated-of-four allocations of
clusters `0,…,3`. The second coordinate enumerates all fifteen
two-treated-of-six allocations of clusters `4,…,9`. Thus the two within-stratum
allocations are independent uniform draws. In the implementation the second
cluster index is the natural subtraction `i.val-4`, used only in the branch
`i.val≥4`.

For real `z`, set `s(z)=1-1/(1+exp(z))`. For `β=(a,b)∈ℝ²`, define
`L_false(β)=Σ_{i<6}[y_i log(s(a+b x_i))+(1-y_i)log(1-s(a+b x_i))]`
and define `L_true` by the same sum over `i≥6`.
A maximizer means `L_b(γ)≤L_b(β)` for every `γ∈ℝ²`.
`β_b` is an arbitrarily chosen maximizer if one exists, and `(0,0)` otherwise.
The prediction for unit `i` is `s(β_true,0+β_true,1 x_i)` when `i<6`, and uses
`β_false` otherwise. In particular, the likelihood's Boolean-to-stratum map and
the prediction's Boolean-to-stratum map are reversed: each unit uses the fit
from the other subset. This is part of the literal definition, regardless of
what the intended algorithm is.

Let `r_c=Σ_{i:cluster(i)=c}(y_i-prediction_i)`. The cluster total is literally a
finite sum over the indicated filtered set. Let `U(w)=H_16(r,r,w)` using the
ten-cluster assignment law, with denominator sixteen, and let `Vhat(w)` be the
printed variance estimator above for this law, `N=16`, and both outcome vectors
equal to `r`. Set `μ=E_q U`, `v=C_q(U,U)`, `e=E_q Vhat`, and `Δ=0`, the ATE of
the identical sixteen-unit outcome vectors.

The ten column entries, in order, are
`[Δ,μ,μ-Δ,√v,√E_q(U-Δ)²,v,e,e-v,√C_q(Vhat,Vhat),√E_q(Vhat-v)²]`.
For real `x,r`, `roundsTo(x,r)` is the half-open interval condition
`r-0.0005≤x<r+0.0005`.

The conjunction asserts all of the following:

1. Each of the two likelihoods has exactly one real maximizer.
2. The coordinates of `β_true` are within `0.0000005` of
   `(-1.1201076,0.5657586)`; those of `β_false` are within the same tolerance of
   `(1.0843223,0.2280259)`.
3. `μ=0`, `0.247090≤√v≤0.247093`, `0.0605≤v<0.0615`, `e=v`, and
   `0.0125≤√C_q(Vhat,Vhat)<0.0135`.
4. For every Boolean `b`, the chosen `β_b` maximizes `L_b`.
5. For every real pair `(a,b)`, each of the following two implications holds:
   `(a≥0 ∧ a+4b≥0 ∧ a+2b≤0) ⇒ (a=b=0)`;
   `(a+b≥0 ∧ a+4b≥0 ∧ a+2b≤0) ⇒ (a=b=0)`.
   In Lean the three premises are curried implications.
6. Each column entry rounds to the corresponding entry of
   `[0,0,0,0.247,0.247,0.061,0.061,0,0.013,0.013]`.
7. For every index in `{3,4,5,6,8,9}` (zero based), its entry does not round to
   the corresponding entry of
   `[0,0,0,0.170,0.170,0.029,0.029,0,0.007,0.007]`.

Junk values: `s(z)` and `1-s(z)` are strictly between zero and one for every
finite real `z`, so neither zero-denominator division nor `log 0`/negative log
arguments occurs. Lean's `Real.log` is total, but its extra-domain behavior is
irrelevant here. The fallback `(0,0)` in `logitCoefficients` is not used if the
asserted existence clauses hold; uniqueness also removes the ambiguity of
choice. `Real.sqrt` returns zero on negative inputs; the variance and mean
square inputs here are nonnegative under the explicitly enumerated uniform
law. All arm marginals are positive (one half in the first cluster stratum,
one third treated in the second). Some same-arm and directed cross joints may
vanish; the explicit epsilon correction and zero-joint terms govern those,
and do not silently use division by zero. `N=16`, the constants 2 and 2000,
and all other numeral denominators are nonzero. Rational-to-real casts are
exact. Fin indices in the vectors are in range. The only natural subtraction
is guarded as described above and cannot truncate incorrectly. All sums are
finite; there are no empty population types, integrals, infinities, extrema
defined by `sInf`/`sSup`, or limits.

## SAP.P026b.T15

Source: `Challenge/Part1.lean:18–23`, `Defs/Part3.lean:69–93`, and its listed
Part1/Part2 dependencies.

This is a closed finite example over the rational numbers except for its OLS
certificate, which casts responses and fitted values to the reals. There are
three units `i=0,1,2`; the sample space is `w=0,1,2`, each of weight `1/3`,
and unit `i` is treated exactly when `w=i`. Potential outcomes are
`y1_i=1,y0_i=0`; the one supplied covariate is `x_i=i`.
The fitting matrix has rows `(1,i)` because `designWithIntercept` prepends a
column of ones. The fitted response is
`f(w,i)=[5/6,1/3,-1/6]_w+[-1/2,0,1/2]_w i`.

For a real finite matrix `V` with `K` columns,
`IsLeastSquaresFitted K V y z` means both
`∃β : Fin K → ℝ, (Σ_k V_ik β_k)_i=z` and
`∀β, Σ_i(y_i-z_i)²≤Σ_i(y_i-Σ_k V_ik β_k)²`.
The theorem asserts:

1. The displayed design is a nonnegative normalized probability law and has
   positive arm marginals; for every unit they are `(1/3,2/3)`.
2. For every assignment and unit the fitted response matrix is exactly
   `[[5/6,1/3,-1/6],[1/3,1/3,1/3],[-1/6,1/3,5/6]]`.
3. For every `w`, with observed real response equal to the indicator of `i=w`,
   this fitted vector is in the column space of the two-column matrix `(1,i)`,
   minimizes squared residual error over all real coefficient vectors, and
   every other fitted vector satisfying that definition equals it.
4. The generalized ATEs for `w=0,1,2` are `[1/4,1,1/4]`.
5. For every unit `i`, `C_q(A_true,i,w↦f(w,i))=[1/6,0,1/6]_i`.
6. The estimator's expectation is `1/2`, ATE is `1`, their difference is
   `-1/2`, and the explicit covariance arithmetic
   `-(1/3)(3+3/2)(1/6+0+1/6)=-1/2` holds.
7. Every unadjusted HT estimate is `1`, and `1/2≠1`.

There are no hypotheses assumed in exchange for these conclusions. The
docstring says the example refutes a reading of the package's help, rather
than declaring the package's printed assertion itself false.

Junk values: all inverse-probability denominators, population size three, and
numeral denominators are nonzero. `i.val` is the bounded natural `0,1,2` cast
exactly to the rational or real field; there is no subtraction on naturals.
OLS is defined by attained finite-dimensional minimization, with no inverse
matrix, arbitrary pseudoinverse default, or division by a possibly singular
determinant. No population or sample index is empty. Expectations and
covariances are finite sums. No roots, logs, integrals, infinities, suprema,
limits, or partial-function defaults occur in this closure.

## SAP.P026b.T16

Source: `Challenge/Part1.lean:25–29`, `Defs/Part3.lean:95–124`, plus the full
T15 dependency closure, including the explicit example just unfolded.

This is a conjunction of five statements, with independently quantified data
in each universal block:

1. For every nonempty finite decidable unit type `I`, every `UnitExperiment I`,
   and all fixed real vectors `y1,y0,g`, writing `N=|I|`, for every allocation
   `w` the generalized estimator with `f_i(w)=g_i` equals
   `R_N(w)={Σ_i A_true,i(w)(o_i(w)-f_i(w))/p_true,i
   -Σ_i A_false,i(w)(o_i(w)-f_i(w))/p_false,i}/N`.
   Also its expectation is `Δ_N`.
2. For every such `I,E`, natural `K` (possibly zero), real matrix
   `X : I × Fin K → ℝ`, and real potential outcome vectors, prepend an
   intercept to obtain `V : I × Fin(K+1) → ℝ`. Map a coefficient vector to
   `Vβ` in the Euclidean space of real functions on `I`; its range is a
   real linear subspace. For each `w`, define `f(w)` to be the orthogonal
   projection of the observed response vector onto this range, expressed
   again as a function on `I`. Then for every `w`, `f(w)` satisfies the
   attained least-squares definition given in T15; the generalized estimator
   equals `R_N(w)`; and its expectation minus ATE is
   `-(1/N)Σ_i C_q(A_true,i,f_i)(1/p_true,i+1/p_false,i)`.
3. For every such `I,E`, all real potential outcome vectors and *arbitrary*
   allocation-dependent real predictions `f`, if
   `∀i, C_q(A_true,i,f_i)=0`, then the generalized estimator has expectation
   `Δ_N`.
4. For every such `I,E`, fixed real vector `x`, and arbitrary function
   `G : (I → ℝ) → (I → ℝ)`, use identical potential outcomes `y1=y0=x`
   and predictions `f(w)=G(o(w))`. The expectation of the generalized
   estimator equals `Δ_N=0`.
5. The entire concrete T15 conjunction holds, including the real OLS
   certificate, rational moments, and nonzero bias. This final conjunct is
   not a hypothesis about the universally quantified data above.

`EuclideanSpace` uses the ordinary sum-of-coordinate-products real inner
product, so this is ordinary unweighted all-unit least squares with an
intercept. It does not include treatment as an additional regressor.
The sharp-null block allows any deterministic response-only fitting map; it
does not allow `G` to receive the assignment as another argument.

Junk values: positive marginals and nonempty `I` exclude all estimator
zero denominators. `K=0` is permitted and gives just the intercept column;
it does not give an empty regression matrix. A deficient rank is permitted,
but the column space is finite dimensional and closed, so its orthogonal
projection exists and is unique without any singular-matrix default.
The generated projection instance proves exactly that fact. All vectors and
moments have finite coordinates and finite sums. The exact casts in the T15
conjunct have the properties stated there. No logs, roots, extended reals,
partial choices, unbounded extrema, or limits occur.

## SAP.P026b.T17

Source: `Challenge/Part1.lean:31–35`, `Defs/Part4.lean:59–70`, and its listed
Part1/Part2 dependencies.

The first conjunct is the negation of the following precise universal
assertion: for every `D : Design (Fin 3) (Fin 2) ℝ`, if `D` is a nonnegative
normalized law, both marginals are positive for each unit, and
`Σ_w q(w)1[t(w,i)≠t(w,j)]>0` for every distinct pair, then for every pair of
real potential outcome vectors `x,z : Fin 2 → ℝ`, both
`p_true,false,ij>0` for every distinct ordered pair and
`C_q(H_2(x,z),H_2(x,z))≤E_q Vhat_2(x,z)` hold.
Thus the negation logically requires failure of at least one of support and
conservativeness for some admissible design and outcome pair; it does not
separately assert a strict failure of conservativeness.

The remaining conjuncts specify one design: `Ω={0,1,2}`, `I={0,1}`,
weight `1/3` at each outcome, allocations in order `[(false,false),
(false,true),(true,true)]`. They assert normalization and nonnegativity,
positive marginals, and for every distinct unit pair positive disagreement,
positive joint treatment, and positive joint control. Finally, for sharp-null
outcomes `x_i=z_i=1` and fixed predictions `f_i(w)=0`, they assert
`E_q Vhat_2(1,1) ≠ C_q(G_2(1,1,0),G_2(1,1,0))`.
There is no assertion in this last conjunct about the direction of the
inequality. All its variables are fixed, with no external assumptions.

The docstring calls the printed claim false, refers to a universal
support/conservativeness assertion, and describes the last conjunct as a
separate refutation of footnote 9's unbiasedness assertion. At this blind
stage these are descriptions to check later, not premises supplied to Lean.

Junk values: in the explicit design treatment marginals are `(1/3,2/3)` and
control marginals `(2/3,1/3)`; all are nonzero, and `N=2`. In the negated
universal assertion the explicit positive-marginal hypotheses and the fixed
size two likewise exclude zero denominators. Joint zeros are intentionally
handled by `p+e(p)` and by the displayed zero-joint correction sums. With a
probability law these denominators are always nonzero. There are two units
and three allocation labels, so no empty index issue. No natural subtraction,
casts of negative indices, logarithms, roots, integrals, extended reals,
suprema, limits, or partial defaults occur.

## Generated declarations in the closures

All were printed and read. `Design.mk`, `.weight`, `.treatment` and
`UnitExperiment.mk`, `.weight` are precisely the constructor/projections
described above. `olsDesignMap._proof_1` and `_proof_2` supply compatibility
of identity real ring homomorphisms; `olsFitted._proof_1` supplies existence of
orthogonal projection by completeness of the finite-dimensional subspace.
`tableDesign._proof_2` proves that `i.val-4<6` when `i.val≥4` for `i : Fin 10`.
`tableCluster._proof_1` and `T14Statement._proof_3` prove `NeZero 10` for Fin
numerals. Every other listed generated proof supplies `AtLeastTwo` for an
ordinary positive numeral (in T14Statement, corrected/printedLogitColumn,
logitCoreFacts, printedVariance, roundsTo, or realAsymmetricTwo). None adds a
statistical hypothesis, changes a denominator, or hides an additional
substantive definition.
