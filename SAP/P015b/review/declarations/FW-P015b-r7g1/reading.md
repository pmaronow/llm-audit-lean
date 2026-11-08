# Blind reading

This document was written and saved before opening either `claims.json` or
`record.json`. It describes the elaborated statements, rather than trusting their
names. Every source declaration in `closure.json` was read. The 46 distinct
generated `_proof_` declarations were also printed with proofs by the successful
`scratch/PrintClosure.lean` check. They supply numeral/typeclass facts, not
statistical assumptions. A per-target closure inventory follows each section.

Throughout, real matrices are finite arrays, matrix multiplication and `mulVec`
are finite sums, transpose is ordinary transpose, and dot product is the sum of
coordinate products. For a square real matrix, Mathlib's inverse is the ordinary
inverse when its determinant is nonzero and the zero matrix when singular.
Matrix `1` is the identity, not the all-ones matrix. `PosSemidef` means symmetric
with nonnegative quadratic form; `PosDef` means symmetric with strictly positive
quadratic form on nonzero vectors. Function/vector equalities are pointwise.

## SAP.P015b.T9

Location: `SAP/P015b/Challenge/Part1.lean:12-15`. This is the conjunction
`PoolingCounterexample ∧ RawPoolingCounterexample`, with no external parameters
or hypotheses. Its docstring describes a counterexample to a scalar averaging
interpretation, not a universal statistical model theorem.

Let

```
Z1 = [[1,0],[1,1],[1,1]],  y1 = (0,0,0),
Z2 = [[1,0],[1,0],[1,1]],  y2 = (2,2,2),
P1 = [[5/8,1/4],[1/4,1/2]],
P2 = [[5/7,1/7],[1/7,3/7]],
B  = [[52/61,-22/61],[-22/61,75/61]].
```

`sampleCoefficients Z y` means exactly `(Zᵀ Z)⁻¹ Zᵀ y`. The first
conjunct asserts all of the following:

1. `det(Z1ᵀ Z1)=det(Z2ᵀ Z2)=2`.
2. The two OLS vectors are `(0,0)` and `(2,0)`.
3. For each group, `Pg = (I + (Zgᵀ Zg)⁻¹)⁻¹`.
4. `(P1+P2)⁻¹=B`.
5. `(P1+P2)⁻¹(P1 OLS1+P2 OLS2)=(68/61,-10/61)`.
6. For every real pair `a1,a2`, `a1*0+a2*0 ≠ -10/61`.
7. For every pair of arbitrary real two-vectors `t1,t2`, the coordinate with
   index 1 of `(P1+P2)⁻¹(P1 t1+P2 t2)` is
   `(5/61)t1[0]-(5/61)t2[0]+(32/61)t1[1]+(29/61)t2[1]`.

For the second conjunct let `Vg=Zg I Zgᵀ+I3`, and let

```
r = (Z1ᵀ V1⁻¹ Z1 + Z2ᵀ V2⁻¹ Z2)⁻¹
      (Z1ᵀ V1⁻¹ (0,0,0) + Z2ᵀ V2⁻¹ (2,2,2)).
```

It asserts that the two-dimensional identity is positive semidefinite,
`r=(68/61,-10/61)`, both separate OLS treatment coordinates are zero, and for
every real pair `a1,a2` the treatment coordinate `r[1]` differs from the scalar
combination of those separate coordinates. The coefficient covariance and error
variance in this calculation are respectively `I2` and 1. No independence,
sampling law, or random-coefficient distribution is asserted; this is a fixed
GLS algebra example.

Junk conventions: all literal denominators are nonzero positive integers. The
designs have the asserted nonzero Gram determinants. The displayed precisions
and their sum have actual inverses; `Vg=Zg Zgᵀ+I3` is positive definite.
Consequently the matrix zero-inverse convention does not explain the example.
All indices are nonempty `Fin 2` or `Fin 3`; numeric `Fin` indices are valid.
Subtraction is real subtraction, not truncated natural subtraction. There are
no integrals, logarithms, square roots, real powers, extended-real conversions,
extrema, partial functions, or sequence limits.

Closure declarations read (source locations from `closure.json`; line 0
means an elaborator-generated declaration inspected by `#print`):

- `SAP.P015b.PoolingCounterexample` — `SAP/P015b/Defs/Part3.lean:45`.
- `SAP.P015b.PoolingCounterexample._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.PoolingCounterexample._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.PoolingCounterexample._proof_3` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.PoolingCounterexample._proof_4` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.PoolingCounterexample._proof_5` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.RawPoolingCounterexample` — `SAP/P015b/Defs/Part3.lean:58`.
- `SAP.P015b.T9Statement` — `SAP/P015b/Defs/Part3.lean:69`.
- `SAP.P015b.firstGroupDesign` — `SAP/P015b/Defs/Part3.lean:21`.
- `SAP.P015b.firstGroupPrecision` — `SAP/P015b/Defs/Part3.lean:25`.
- `SAP.P015b.firstGroupPrecision._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.firstGroupPrecision._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.firstGroupPrecision._proof_3` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.firstGroupPrecision._proof_4` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.poolingInverse` — `SAP/P015b/Defs/Part3.lean:29`.
- `SAP.P015b.poolingInverse._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.poolingInverse._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.poolingInverse._proof_3` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.poolingInverse._proof_4` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.sampleCoefficients` — `SAP/P015b/Defs/Part1.lean:16`.
- `SAP.P015b.secondGroupDesign` — `SAP/P015b/Defs/Part3.lean:23`.
- `SAP.P015b.secondGroupPrecision` — `SAP/P015b/Defs/Part3.lean:27`.
- `SAP.P015b.secondGroupPrecision._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.secondGroupPrecision._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.

## SAP.P015b.T10

Location: `SAP/P015b/Challenge/Part1.lean:17-35`. The target is
`T10WholeStatement_W3`, a conjunction of six independently quantified
propositions. In particular, the stochastic within-group theorem is not a
hypothesis of the finite matrix theorem, and no convergence of the pooled
estimator to a common population parameter is stated.

First, `MatrixPooling`: for every natural `G,q` with `1≤G` and `1≤q`, every
group sample-size function `n:Fin G→ℕ`, designs
`Zg:Matrix (Fin (n g)) (Fin q) ℝ`, outcomes `yg:Fin (n g)→ℝ`, common real
`q×q` matrix `S`, and real variances `σ²g`, assume `S` symmetric positive
semidefinite, every `σ²g>0`, and every `det(Zgᵀ Zg)≠0`. These choices precede
all conclusions. Define

```
Qg = Zgᵀ Zg,
Pg = (S + σ²g Qg⁻¹)⁻¹,
H = Σg Pg,
Ag = H⁻¹ Pg,
tg = Qg⁻¹ Zgᵀ yg,
Vg = Zg S Zgᵀ + σ²g I,
m* = H⁻¹ Σg Pg tg,
L(m) = Σg (tg-m)ᵀ Pg (tg-m).
```

These expand `precisionMatrix`, `sampleCoefficients`, `pooledCoefficients`,
and `precisionLoss`. The conclusions, in order, are:

1. For every real `q`-vector `m`, `L(m*)≤L(m)`.
2. For every such `m`, `L(m)=L(m*)` implies `m=m*`.
3. `m*=Σg Ag tg`, and `Σg Ag=I`.
4. For every group, `Zgᵀ Vg⁻¹ Zg=Pg` and
   `Zgᵀ Vg⁻¹ yg=Pg tg`.
5. `m*=(Σg Zgᵀ Vg⁻¹ Zg)⁻¹ Σg Zgᵀ Vg⁻¹ yg`.
6. For every chosen coordinate `b:Fin q`, if for every `g,j≠b` both
   `Pg[b,j]=0` and `Pg[j,b]=0`, and if each `Pg[b,b]>0`, then for all `g,j`,
   `Ag[b,j]` equals `Pg[b,b]/Σh Ph[b,b]` when `j=b`, and zero otherwise.

Second, `PoolingCovariancesW3`: independently universally quantify the same
finite dimensions, sample sizes, designs, common `S` and variances under exactly
the same nonemptiness, positive-variance, positive-semidefinite, and nonzero-Gram-
determinant conditions (no outcomes are needed). Conclude each
`S+σ²g Qg⁻¹`, `Pg`, and `Vg`, and their precision sum `Σg Pg`, are positive
definite.

Third, `ScalarRowCriterionW3`: for every natural `G,q`, arbitrary finite
real matrix family `Ag`, prescribed scalar vector `a:Fin G→ℝ`, and selected
coordinate `b:Fin q`, assert two equivalences:

```
(∀ t:Fin G→Fin q→ℝ, (Σg Ag tg)[b] = Σg ag tg[b])
  ↔ (∀ g, Ag[b,j] = (if j=b then ag else 0), for every j),

(∀ g, Ag[b,j] = (if j=b then ag else 0), for every j)
  ↔ ((∀ g,j≠b, Ag[b,j]=0) ∧ (∀ g, Ag[b,b]=ag)).
```

The coefficient vectors are quantified *inside* the left side of the first
equivalence; weights are fixed before them. These are arbitrary matrices, not
only matrices arising from GLS. Here `G` may be zero; selection of `b` rules out
`q=0` in any instance.

Fourth, `BoundedInputApproximationW3`: for every natural `G,q`, every sequence
`Ak,g` of arbitrary real `q×q` matrices, and selected `b:Fin q`, suppose for
every `g,j≠b`, `Ak,g[b,j]→0` as the natural index `k→∞`. For every coefficient
family `tk,g[j]` satisfying `UniformlyBoundedCoefficientsW3`, that is
`∃ M∈ℝ, M≥0 ∧ ∀k,g,j, |tk,g[j]|≤M`, conclude

```
(Σg Ak,g tk,g)[b] - Σg Ak,g[b,b] tk,g[b] → 0.
```

There is no convergence assumption on diagonal entries, no approximation using
independently prescribed weights, and no growing dimension.

Fifth, `WithinGroupExpression7W3`: for every type `Ω` in its universe with a
measurable-space structure, every probability measure `P` on it, every natural
number `K` of controls, real processes `Di,Y0i,τi:Ω→ℝ` indexed by `i∈ℕ`, and
control process `Xi:Ω→(Fin K→ℝ)`, assume all coordinate functions are
measurable. The joint tuples `(Di,Y0i,τi,Xi)` are independent across all finite
sets of distinct natural indices (`iIndepFun`), and each has the same law as
tuple zero (`IdentDistrib`, meaning equal pushforward measures and the
associated a.e. measurability). Next assume conditional independence given
`X0` of `(Y00,τ0)` and `D0`. Precisely, for every measurable set
`C⊆ℝ×ℝ` and measurable `J⊆ℝ`,

```
E[1{(Y00,τ0)∈C and D0∈J} | σ(X0)]
  = E[1{(Y00,τ0)∈C} | σ(X0)] E[1{D0∈J} | σ(X0)]  a.s.
```

This unfolds `ConditionalIndependentW3`. Finally choose
`ω∈ℝ^(K+1)` with `E[D0|σ(X0)]=v(X0)·ω` a.s., where
`controlVector v(x)=(1,x[0],...,x[K-1])`, and assume
`RegressionRegularity`. The latter means all of the following, rather than
merely measurability:

* For every control pair `j,k`, the processes `vi[j]vi[k]` and
  `vi[j]vi[k]τi` have `MomentConvergence`.
* For every control `j`, the processes `vi[j]Di`, `vi[j]Y0i`, and
  `vi[j]Diτi` have `MomentConvergence`.
* The processes `Di²`, `Di Y0i`, and `Di²τi` have `MomentConvergence`.
* The matrix `E[v(X0)v(X0)ᵀ]` has nonzero determinant.
* The real weight `w(s)=(D0(s)-E[D0|σ(X0)](s))²` is integrable and
  `E[w]>0`.

For a scalar process `Zi`, `MomentConvergence` is the conjunction of
integrability of every `Zi` and convergence in measure of
`(1/n)Σi∈Fin n Zi` to the constant `E[Z0]`. On a probability space this means
for every positive tolerance, the probability that the absolute deviation
exceeds that tolerance tends to zero. There are eight moment families as
grouped in the source. `squaredPopulationResidual` is precisely `w` above.
All expectations are Bochner integrals of real functions.

The conclusions are integrability of `wτ0` and convergence in probability of
the actual OLS treatment estimate to the constant `E[wτ0]/E[w]`. Explicitly,
`regressorVector(d,x)=(1,d,x[0],...,x[K-1])`,
`linearOutcome(y0,τ,d)=y0+τd`, `regressionDesign` consists of the first `n`
such rows, and `treatmentEstimate` is coordinate 1 of
`(WnᵀWn)⁻¹Wnᵀ(Y0i+τi Di)i<n`. No eventual deterministic sample size of
invertibility is assumed. There is no cross-group stochastic premise in this
conjunct; it is a universally applicable single-group assertion.

Sixth, `RawPoolingCounterexample` is exactly the fixed raw-GLS counterexample
fully expanded under T9 above, with the same data, covariance matrices, and
universal exclusion of scalar combinations of the two zero slopes.

Junk conventions: the finite GLS inverses are protected by rank and positivity,
and the second conjunct explicitly certifies positive definiteness. The scalar
ratio in the block-diagonal case has a positive denominator since `G≥1` and
every summand is positive. The arbitrary-matrix row and approximation clauses
use no inverses or division; empty group sets give empty sums zero. The latter
uses an explicit bound, not a supremum of an empty or unbounded set.
`MomentConvergence` includes `n=0`, whose empty sum divided by zero is zero in
Lean; one initial term cannot affect the `atTop` limit. Finite-sample singular
OLS Grams produce the zero vector, a genuine completion convention that can
occur at finite `n`; the theorem asserts convergence in probability despite
this completion. The limiting denominator is integrable and strictly positive,
so no zero denominator is used there.

Mathlib conditional expectation is zero if the conditioning σ-algebra is not
a subalgebra, if the trimmed measure is not σ-finite, or if the integrand is
not integrable. The conditioning fields here are comaps of measurable controls,
so are subalgebras, and probability measures are finite on them. Event
indicators are bounded and integrable. Integrability of `D0` follows from the
intercept-coordinate `vD` moment family. Conditional-expectation representatives
are only canonical a.e.; all relevant model equalities and limits respect a.e.
equality. Bochner integration is zero for nonintegrable functions, but the
moment hypotheses give integrability of the expectations they use; the
weighted numerator's integrability is a conclusion, not a fake assigned value.
No logarithm, square root, real power, `toReal ∞`, extrema, `limsup`, `liminf`,
or partial-function defaults appear. Natural casts in averages are ordinary
nonnegative integer casts, with only the explicitly discussed `n=0` case.

Closure declarations read (source locations from `closure.json`; line 0
means an elaborator-generated declaration inspected by `#print`):

- `SAP.P015b.BoundedInputApproximationW3` — `SAP/P015b/Defs/WholeW3.lean:63`.
- `SAP.P015b.ConditionalIndependentW3` — `SAP/P015b/Defs/WholeW3.lean:15`.
- `SAP.P015b.MatrixPooling` — `SAP/P015b/Defs/Part3.lean:71`.
- `SAP.P015b.MomentConvergence` — `SAP/P015b/Defs/Part2.lean:45`.
- `SAP.P015b.PoolingCounterexample._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.PoolingCounterexample._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.PoolingCounterexample._proof_3` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.PoolingCovariancesW3` — `SAP/P015b/Defs/WholeW3.lean:29`.
- `SAP.P015b.RawPoolingCounterexample` — `SAP/P015b/Defs/Part3.lean:58`.
- `SAP.P015b.RegressionRegularity` — `SAP/P015b/Defs/Part2.lean:49`.
- `SAP.P015b.ScalarRowCriterionW3` — `SAP/P015b/Defs/WholeW3.lean:44`.
- `SAP.P015b.T10WholeStatement_W3` — `SAP/P015b/Defs/WholeW3.lean:97`.
- `SAP.P015b.UniformlyBoundedCoefficientsW3` — `SAP/P015b/Defs/WholeW3.lean:57`.
- `SAP.P015b.WithinGroupExpression7W3` — `SAP/P015b/Defs/WholeW3.lean:74`.
- `SAP.P015b.controlVector` — `SAP/P015b/Defs/Part2.lean:17`.
- `SAP.P015b.firstGroupDesign` — `SAP/P015b/Defs/Part3.lean:21`.
- `SAP.P015b.firstGroupPrecision._proof_4` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.linearOutcome` — `SAP/P015b/Defs/Part2.lean:22`.
- `SAP.P015b.pooledCoefficients` — `SAP/P015b/Defs/Part1.lean:23`.
- `SAP.P015b.poolingInverse._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.precisionLoss` — `SAP/P015b/Defs/Part1.lean:27`.
- `SAP.P015b.precisionMatrix` — `SAP/P015b/Defs/Part1.lean:20`.
- `SAP.P015b.regressionDesign` — `SAP/P015b/Defs/Part2.lean:27`.
- `SAP.P015b.regressorVector` — `SAP/P015b/Defs/Part2.lean:19`.
- `SAP.P015b.sampleCoefficients` — `SAP/P015b/Defs/Part1.lean:16`.
- `SAP.P015b.secondGroupDesign` — `SAP/P015b/Defs/Part3.lean:23`.
- `SAP.P015b.squaredPopulationResidual` — `SAP/P015b/Defs/Part2.lean:41`.
- `SAP.P015b.treatmentEstimate` — `SAP/P015b/Defs/Part2.lean:37`.
- `SAP.P015b.treatmentEstimate._proof_1` — `SAP/P015b/Defs/Part2.lean:0`.

## SAP.P015b.T20

Location: `SAP/P015b/Challenge/Part1.lean:37-39`. `T20Statement` has no
parameters or hypotheses. There are four atoms indexed by `Fin 4`:

```
atom i         0       1       2        3
p(i)           1/20    1/5     11/20    1/5
X(i)           0       0       1        1
D(i)           0       1       0        1
z(i)           (1,D(i),X(i)).
```

These are `leveragePopulation`, `binaryProfile`, `binaryTreatment`, and
`leverageDesign`. `finiteMean p Z=Σi pi Zi`,
`IsFiniteLaw p=(∀i,pi≥0)∧Σi pi=1`, and
`finiteMass p E=Σi (if E(i) then pi else 0)`. For any cell value `x`,
`finiteCellMean p X Z x=(Σi:X(i)=x pi Zi)/(Σi:X(i)=x pi)`.
`finiteWeight p X D i=(D(i)-finiteCellMean p X D (X(i)))²`.
Set `M=Σi pi z(i)z(i)ᵀ` (`leverageMoment`),
`L(i)=z(i)ᵀM⁻¹z(i)` (`scaledLeverage`). The conclusions are:

* `p` is a finite probability law.
* `E[w|X=0]=4/25` and `E[w|X=1]=44/225`.
* `M=[[1,2/5,3/4],[2/5,2/5,1/5],[3/4,1/5,3/4]]`.
* `M⁻¹=[[52/7,-30/7,-44/7],[-30/7,75/14,20/7],
  [-44/7,20/7,48/7]]` (`leverageMomentInverse`).
* The vector `L` is `(52/7,59/14,12/7,59/14)`.
* `E[L|X=0]=34/7` and `E[L|X=1]=50/21`.
* `(44/225)/(4/25)=11/9` and `1-(50/21)/(34/7)=26/51`.
* The following rounding inequalities hold, with
  `RoundsWithin(x,display,resolution)` meaning the strict inequality
  `|x-display|<resolution/2`:

```
exact value          display        resolution
4/25                 0.160          0.001
44/225               0.196          0.001
52/7                 7.43           0.01
59/14                4.21           0.01
12/7                 1.71           0.01
34/7                 4.86           0.01
50/21                2.38           0.01
100(11/9-1)          22              1
100(26/51)           51              1
```

The underlying cell treatment means are `4/5` and `4/15`; the atom weights are
`(16/25,1/25,16/225,121/225)` by the unfolded definition, although the
statement does not separately list those four values. The two profile
comparisons are expressed through the exact ratios and numerical roundings.

Junk conventions: finite cell means would be zero at a zero-mass cell because
of division by zero. Both cells actually have positive masses `1/4,3/4`.
All literal fractions and comparison ratios have nonzero denominators. `M`
is nonsingular (its determinant is `7/200`), so scaled leverage uses an actual
inverse. Resolution is positive in every instantiated rounding comparison;
ties are excluded by the strict definition, and none occurs here. There are no
empty index sets, integrals, nonreal quantities, logarithms, roots, real powers,
extended-real conversions, extrema or limits. All subtraction is real.

Closure declarations read (source locations from `closure.json`; line 0
means an elaborator-generated declaration inspected by `#print`):

- `SAP.P015b.IsFiniteLaw` — `SAP/P015b/Defs/Part1.lean:33`.
- `SAP.P015b.RoundsWithin` — `SAP/P015b/Defs/Part3.lean:43`.
- `SAP.P015b.T20Statement` — `SAP/P015b/Defs/Part3.lean:106`.
- `SAP.P015b.T20Statement._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_10` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_11` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_12` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_13` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_14` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_15` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_16` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_17` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_18` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_19` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_3` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_4` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_5` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_6` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_7` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_8` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.T20Statement._proof_9` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.binaryProfile` — `SAP/P015b/Defs/Part3.lean:17`.
- `SAP.P015b.binaryTreatment` — `SAP/P015b/Defs/Part3.lean:19`.
- `SAP.P015b.finiteCellMean` — `SAP/P015b/Defs/Part1.lean:39`.
- `SAP.P015b.finiteMass` — `SAP/P015b/Defs/Part1.lean:36`.
- `SAP.P015b.finiteMean` — `SAP/P015b/Defs/Part1.lean:31`.
- `SAP.P015b.finiteWeight` — `SAP/P015b/Defs/Part1.lean:47`.
- `SAP.P015b.firstGroupPrecision._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.firstGroupPrecision._proof_3` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.firstGroupPrecision._proof_4` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.leverageDesign` — `SAP/P015b/Defs/Part3.lean:33`.
- `SAP.P015b.leverageMoment` — `SAP/P015b/Defs/Part3.lean:35`.
- `SAP.P015b.leverageMomentInverse` — `SAP/P015b/Defs/Part3.lean:38`.
- `SAP.P015b.leverageMomentInverse._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.leverageMomentInverse._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.leverageMomentInverse._proof_3` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.leverageMomentInverse._proof_4` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.leveragePopulation` — `SAP/P015b/Defs/Part3.lean:31`.
- `SAP.P015b.leveragePopulation._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.leveragePopulation._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.poolingInverse._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.poolingInverse._proof_3` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.poolingInverse._proof_4` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.scaledLeverage` — `SAP/P015b/Defs/Part3.lean:41`.
- `SAP.P015b.secondGroupPrecision._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.secondGroupPrecision._proof_2` — `SAP/P015b/Defs/Part3.lean:0`.

## SAP.P015b.T14

Location: `SAP/P015b/Challenge/Part1.lean:41-49`. `T14WholeStatement` is a
conjunction of a model-membership equivalence and an independent injectivity
statement.

First universally quantify a type `Ω` with a measurable space, a probability
measure `P`, a natural number `K`, real processes `Yi,Di:Ω→ℝ`, and
`Xi:Ω→(Fin K→ℝ)`, all indexed by `i∈ℕ`. Then
`CommonLogisticModel P K Y D X` is equivalent to the conjunction that all those
functions are measurable, every `Yi` belongs to `{0,1}` a.s., and there exist
common real parameters `α,β` and `γ:Fin K→ℝ` such that for every index `i`,

```
E[1{Yi=1}|σ(Di,Xi)](s)
  = 1/(1+exp(-(α+βDi(s)+Σj Xi(s)[j]γ[j])))  for P-a.e. s.
```

The order is `∀ data, (model membership ↔ (measurability ∧ binary outcome ∧
∃α ∃β ∃γ ∀i, a.s. equality))`. The parameters cannot depend on `i`.
`CommonLogisticModel` itself is exactly that right-hand definition except that
the logistic function is named `sigmoidMean`. `sigmoidMean=Real.sigmoid`,
whose definition is `(1+exp(-a))⁻¹`. Thus this part unfolds membership in a
specified family; it does not deduce logistic structure from binary outcomes
alone. There is no iid assumption, treatment positivity, rank condition,
parameter uniqueness, or parameter-estimation assertion.

Second, `T14Statement`: for every `α,β,x,d,d',p∈ℝ`, if `β≠0` and `d≠d'`,
then it is impossible that both
`p=1/(1+exp(-(α+βd+x)))` and
`p=1/(1+exp(-(α+βd'+x)))`. Here `x` is an arbitrary fixed real offset,
not a control vector or a varying function. The constant `p` is unrestricted
real data; it is not defined as a marginal probability. The statement excludes
a constant value across two distinct treatments at a fixed offset, and does
not claim every unconditional logistic probability formula is impossible.

Junk conventions: exponentials are everywhere finite and positive, hence the
sigmoid denominator is strictly positive and its value lies in `(0,1)`.
Indicator functions are integrable under `P`. Measurability of `(Di,Xi)`
makes its comap a sub-σ-algebra, and its trimmed probability measure is finite,
so conditional expectation avoids all its zero defaults. A.e. binary values
and conditional expectations are explicitly a.e.; behavior on null sets is
unconstrained. With `K=0`, the control sum is the legitimate empty sum zero,
and the intercept/treatment model remains meaningful. Natural process indices
are inhabited. There are no inverses of matrices, logs, roots, real powers,
infinite-to-real conversions, extrema, sequence limits, or partial functions.

Closure declarations read (source locations from `closure.json`; line 0
means an elaborator-generated declaration inspected by `#print`):

- `SAP.P015b.CommonLogisticModel` — `SAP/P015b/Defs/WholeW1.lean:131`.
- `SAP.P015b.T14Statement` — `SAP/P015b/Defs/Part3.lean:122`.
- `SAP.P015b.T14WholeStatement` — `SAP/P015b/Defs/WholeW1.lean:143`.
- `SAP.P015b.sigmoidMean` — `SAP/P015b/Defs/Part1.lean:73`.

## SAP.P015b.T21

Location: `SAP/P015b/Challenge/Part1.lean:51-58`. `T21WholeStatement` is the
conjunction of three separately quantified propositions. Write
`s(a)=1/(1+exp(-a))` and `p=K+2`. `residualEquation W n k m θ` is the
vector with coordinates `Σi Wij (ki-ni m(Σj Wij θj))`.
`binomialLogLikelihoodSAP m n k η=k log(mη)+(n-k)log(1-mη)` and
`binaryLogLikelihood W n k m θ` is the sum of these expressions over sample
rows. Thus for `n_i=1`, binary `Yi`, and logistic `m=s`, it is

```
ell(θ)=Σi [Yi log(s(Wi·θ))+(1-Yi)log(1-s(Wi·θ))].
```

First, `UnrestrictedLogisticScore`: for every natural `N,K`, arbitrary real
`N×(K+2)` design `W`, real outcome vector `Y` with
`∀i,Yi=0∨Yi=1`, and parameter vector `θ∈ℝ^(K+2)`, the function `ell` has a
Fréchet derivative at `θ` equal to the continuous linear map

```
h ↦ Σj [Σi Wij (Yi-s(Wi·θ))] hj
  = Σi (Yi-s(Wi·θ)) (Wi·h).
```

This unfolds `logisticScoreMap`, which sums residual-coordinate multiples of
the coordinate projections. There is no rank or intercept assumption and no
assumption that `θ` maximizes anything. The conclusion is differentiability,
not existence of a finite logistic maximum or of a logistic score root.

Second, `AffinePredictorIdentity`: for every natural `N,K`, arbitrary real
design `W` with `∀i,Wi0=1`, every real `b,c`, and every real parameter and
outcome vectors `θ,Y`, define `θ'j=(if j=0 then b else 0)+cθj`
(`affineCoefficients 0 b c θ`). Then for every row
`Wi·θ'=b+c Wi·θ`, and as entire vectors
`Wᵀ(Y-b-cWθ)=Wᵀ(Y-Wθ')`. Binary outcomes and nonzero `c` are not needed
for this identity. This does not itself approximate the sigmoid.

Third, `AffineWholeRoot`: for every natural `N,K`, arbitrary real design `W`
and binary `Y`, assume a unit intercept column and
`det(WᵀW)≠0`; then for every `b,c∈ℝ` with `c≠0`, there exists exactly
one real vector `θ` satisfying

```
Wᵀ(Y-b-cWθ)=0.
```

Furthermore every vector satisfying that equation has
`b e0+cθ=(WᵀW)⁻¹WᵀY`, and its treatment coordinate satisfies
`OLS[1]=cθ[1]`. Existence/uniqueness is for the affine surrogate equations;
it is not claimed for the original logistic likelihood equations. The
quantifiers choose `W,Y,b,c` before the unique root, and the final implication
quantifies again over every candidate root. Coordinate 0 is the intercept and
coordinate 1 is the scaled treatment coordinate; other columns are arbitrary.

Junk conventions: logarithm is Mathlib's total real logarithm, assigning zero
at zero and using the logarithm of the absolute value for negative arguments.
All log arguments here are strictly between zero and one, so neither convention
is used. The binomial definition has real subtraction `n-k`, not natural
truncation; instantiated outcomes are binary with `n=1`. The generic affine
mean is used only in residual equations, never inserted into logarithms, so it
need not be a probability. `c=0` is allowed only in the predictor-identity
part; it is excluded where solving for a unique root needs division by `c`.
The OLS inverse appears only in the full-rank part and is an actual inverse.
`N=0` is allowed in the differentiability and identity parts and gives an
empty sum/zero derivative; it cannot satisfy the full-rank part because
`K+2≥2`. All coefficient index types have at least two elements, so indices
0 and 1 are valid and different, as certified by the generated `NeZero`
proofs. There are no integrals, square roots, real powers, extended-real
conversions, extrema, sequence limits, or partial-function defaults.

Closure declarations read (source locations from `closure.json`; line 0
means an elaborator-generated declaration inspected by `#print`):

- `SAP.P015b.AffinePredictorIdentity` — `SAP/P015b/Defs/Part3.lean:127`.
- `SAP.P015b.AffinePredictorIdentity._proof_1` — `SAP/P015b/Defs/Part3.lean:0`.
- `SAP.P015b.AffineWholeRoot` — `SAP/P015b/Defs/WholeW1.lean:176`.
- `SAP.P015b.AffineWholeRoot._proof_1` — `SAP/P015b/Defs/WholeW1.lean:0`.
- `SAP.P015b.T21WholeStatement` — `SAP/P015b/Defs/WholeW1.lean:188`.
- `SAP.P015b.UnrestrictedLogisticScore` — `SAP/P015b/Defs/WholeW1.lean:168`.
- `SAP.P015b.affineCoefficients` — `SAP/P015b/Defs/Part1.lean:90`.
- `SAP.P015b.binaryLogLikelihood` — `SAP/P015b/Defs/Part1.lean:84`.
- `SAP.P015b.binomialLogLikelihoodSAP` — `SAP/P015b/Defs/Part1.lean:77`.
- `SAP.P015b.logisticScoreMap` — `SAP/P015b/Defs/WholeW1.lean:163`.
- `SAP.P015b.logisticScoreMap._proof_1` — `SAP/P015b/Defs/WholeW1.lean:0`.
- `SAP.P015b.logisticScoreMap._proof_2` — `SAP/P015b/Defs/WholeW1.lean:0`.
- `SAP.P015b.logisticScoreMap._proof_3` — `SAP/P015b/Defs/WholeW1.lean:0`.
- `SAP.P015b.residualEquation` — `SAP/P015b/Defs/Part1.lean:80`.
- `SAP.P015b.sampleCoefficients` — `SAP/P015b/Defs/Part1.lean:16`.
- `SAP.P015b.sigmoidMean` — `SAP/P015b/Defs/Part1.lean:73`.
