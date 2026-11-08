# Blind reading

This file was saved before opening `claims.json` or `record.json`. The sources read
were the two declarations and their docstrings, all source declarations listed in
`closure.json`, and the generated declarations printed by
`scratch/BlindClosure.lean`. The complete printed auxiliary declarations are in
`scratch/blind-closure-declarations.txt`.

## SAP.P039.T6

The theorem has no parameters or hypotheses. It asserts the conjunction below
about explicitly defined finite data, and universal algebraic facts about real
coefficients. The docstring describes a corrected magnitude selection rule, both
samples, attained margins, a signed fitted contribution, and a rounded example.

`ExtremismMeasure` is `Fin 5`, the five natural numbers 0 through 4. Write
`E_j` for `extremismElections j`, `e_j(t)` for `depositedExtremism j t`, `w_j`
for `magnitudeWinner j`, `c_j` for `closestCompetitor j`, and `d_j` for
`magnitudeMargin j`. These are literal finite sets and rational-valued lookup
tables, not optimization operators. Every deposited value is reproduced in the
table at the end of this section. Outside its listed election set, each `e_j` is
zero.

For j=0,2, `E_j` is {1948,1952,...,2012}. For j=1,3 it is
{1972,1976,...,2012}. For j=4 it is
{1960,1964,1968,1972,1984,1996,2004,2008}.

| j | w_j | c_j | d_j | magnitudeMaximumScore j |
|---|---:|---:|---|---|
| 0 | 1980 | 1972 | 33171961114209/250000000000000 | -0.498138285011637 |
| 1 | 1972 | 2004 | 85752092421407/500000000000000 | -0.51177218671487 |
| 2 | 1980 | 1972 | 20648643625509/125000000000000 | -0.621023999873778 |
| 3 | 1972 | 2008 | 12092835415297/50000000000000 | -0.60215659702977 |
| 4 | 1964 | 1968 | 13/125 | -0.22 |

All decimals in this file mean exact rational numbers. `modelElections j bp` is
`E_j` with 1948 removed exactly when Boolean `bp` is true and j=0 or j=2;
otherwise it is `E_j`. `maximumEffect β j` is the real product `β e_j(w_j)`.

The seven conjuncts are:

1. For every j, `w_j` belongs to `E_j`, `e_j(w_j)<0`, and for every natural
   number t belonging to `E_j`, if `t≠w_j` then `|e_j(t)|<|e_j(w_j)|`.
2. For every j, `d_j>0`, `c_j∈E_j`, `c_j≠w_j`, and
   `|e_j(w_j)|-|e_j(c_j)|=d_j`. For every t in `E_j` other than `w_j`,
   `d_j≤|e_j(w_j)|-|e_j(t)|`. Thus the positive margin is achieved by a
   competitor and bounds every competing gap from below.
3. For every j and then every Boolean bp, `w_j` belongs to `modelElections j bp`
   and uniquely maximizes absolute score there. In addition, the natural-number
   expression `card(modelElections j false)-5` equals 12 for j=0,2, 3 for j=4,
   and 6 for j=1,3; `card(modelElections j true)-6` equals 10 for j=0,2,
   2 for j=4, and 5 for j=1,3. These cardinality clauses do not depend on bp.
4. For every real β, then every real g, then every j,
   `(g+βx)-(g+β·0)=βx` for every real x; and for every t in `E_j`,
   `|β e_j(t)|≤|β e_j(w_j)|`.
5. For every real β and then every j, `β e_j(w_j)>0` iff `β<0`,
   `β e_j(w_j)=0` iff `β=0`, and `β e_j(w_j)<0` iff `β>0`.
6. `(-2.23)(-0.62)=1.3826`, this product belongs to `[1.375,1.385)`, and
   `e_2(1980)` belongs to `[-0.625,-0.615)`.
7. For every j, `e_j(w_j)` equals the corresponding exact score in the table
   above.

There is no assumed maximizing property: the strict inequalities actually compare
the separately deposited data against the separately specified winner years.
Likewise, the margin inequalities are conclusions, not hypotheses.

Junk-value and boundary audit:

- The fallback zero values in `depositedExtremism` are placeholders. Every
  optimization quantifier is guarded by membership in `E_j` or its subset, and
  each selected year and competitor is asserted to belong to `E_j`. No fallback
  value is used as an observed datum.
- All real division is by explicit positive integer denominators. There is no
  division by β or by a potentially zero score.
- The two degrees-of-freedom expressions use truncated natural subtraction.
  The actual sample sizes are (17,11,17,11,8) and (16,11,16,11,8), respectively,
  so subtraction by 5 or 6 is ordinary subtraction here.
- `Fin 5` is nonempty. Boolean equality tests on j are ordinary equality.
  All vector literal indices are in range, and years are natural numbers with
  no arithmetic conversion that changes their value.
- No integral, logarithm, square root, real power, infimum, supremum, limiting
  operation, extended-real conversion, or partial-choice operator occurs.
- The generated `depositedExtremism._proof_1` through `_proof_83` and
  `magnitudeMargin._proof_1` through `_proof_5` prove only numeric
  `Nat.AtLeastTwo` instances; `modelElections._proof_1` proves `NeZero 5`.
  `extremismElections.match_1` is exhaustive case analysis on `Fin 5`, with its
  unreachable branches eliminated using the index bound. None adds assumptions
  or mathematical content to the assertion.

Exact deposited extremism values (a dash means a fallback zero outside E_j):

| year | e_0 | e_1 | e_2 | e_3 | e_4 |
|---:|---|---|---|---|---|
| 1948 | 186449401704861/1000000000000000 | — | 239968577629729/1000000000000000 | — | — |
| 1952 | 34178139300207/500000000000000 | — | 175955071969269/2000000000000000 | — | — |
| 1956 | -39661945232703/1000000000000000 | — | -1595208354199/31250000000000 | — | — |
| 1960 | -1291245001547/31250000000000 | — | -106360901712767/2000000000000000 | — | -17/250 |
| 1964 | -24728138844441/100000000000000 | — | -63652403833659/200000000000000 | — | -11/50 |
| 1968 | 21313513173683/125000000000000 | — | 109725714189791/500000000000000 | — | 29/250 |
| 1972 | -365450440554801/1000000000000000 | -51177218671487/100000000000000 | -227917425434853/500000000000000 | -60215659702977/100000000000000 | -41/1000 |
| 1976 | 22321319108051/500000000000000 | -115844246379719/500000000000000 | 101692388889377/2000000000000000 | -4509698730617/20000000000000 | — |
| 1980 | -498138285011637/1000000000000000 | -85731054060753/500000000000000 | -310511999936889/500000000000000 | -294347822983647/1000000000000000 | — |
| 1984 | 235890938802093/1000000000000000 | -71228875084027/2000000000000000 | 6845007275751/25000000000000 | 114745734296501/50000000000000000 | 77/2000 |
| 1988 | 153129340875841/1000000000000000 | -74126802891113/250000000000000 | 34639145815011/200000000000000 | -55288164673047/200000000000000 | — |
| 1992 | 133646079679683/1000000000000000 | -61530236247573/1000000000000000 | 48128903307363/250000000000000 | -53214053956201/20000000000000000 | — |
| 1996 | -104467146002477/1000000000000000 | 42109491513391/125000000000000 | -14605008654561/100000000000000 | 147646495781997/500000000000000 | 83/2000 |
| 2000 | -171942930345359/2000000000000000 | 237764496391801/1000000000000000 | -42411239115459/250000000000000 | 30818201020529/200000000000000 | — |
| 2004 | 9745517486293/200000000000000 | -42533500234007/125000000000000 | 49898136705373/200000000000000 | -27900981155331/200000000000000 | 13/250 |
| 2008 | -12363873861033/200000000000000 | -30311773910617/100000000000000 | -4760060756913/40000000000000 | -36029988872383/100000000000000 | -9/2000 |
| 2012 | 294616125544001/10000000000000000 | 16577130166183/50000000000000 | 403303265691201/10000000000000000 | 17120565866919/50000000000000 | — |

## SAP.P039.T7

The theorem has no outer hypotheses or parameters. `T7WholeStatement` is the
conjunction of `T7Statement`, `AlternativeRMSQStatement`, and three actual
Student-reference tail bounds. `T7Statement` in turn conjoins
`NestedStandardErrorsStatement`, `PrintedCellsImpossibleStatement`, explicit
rational arithmetic, `PrintedCellsBoundStatement`, and
`CorrectedTableCellsStatement`. The docstrings describe all these components and
assume the usual measure-theoretic conditions.

Here are the SAP definitions in ordinary finite-dimensional real mathematics.
`Matrix (Fin n) (Fin p) ℝ` is a real n-by-p array, and a vector is a function
`Fin n → ℝ`. Matrix products and matrix-vector products are finite sums;
transpose interchanges row and column indices; `squaredLength v` is
`∑_{i=0}^{n-1} v_i²`, Mathlib's dot product `v·v`.

- `FullColumnRank A` says that `b↦Ab` is injective: for all p-vectors a,b,
  `Aa=Ab` implies `a=b`.
- `ols A y` is `b_A(y)=(AᵀA)⁻¹Aᵀy`, with Mathlib's total matrix inverse.
- `olsResidual A y` is `r_A(y)=y-Ab_A(y)`.
- `olsSSE A y` is `S_A(y)=∑_i r_A(y)_i²`.
- `olsSESquared A y j` is `V_A(y,j)=S_A(y)/(n-p) · ((AᵀA)⁻¹)_{jj}`.
- `olsResidualStandardError A y` is `s_A(y)=sqrt(S_A(y)/(n-p))`.
- `olsT A y j` is `b_A(y)_j/sqrt(V_A(y,j))` (zero-null statistic).
- `IsLeastSquares A y b` means that for every p-vector c,
  `∑_i(y-Ab)_i²≤∑_i(y-Ac)_i²`.
- `fullDesign Z q` appends q as the final column of Z. Its first k columns
  are Z and its column k is q, giving n-by-(k+1).
- `wholeRMSQ A y` is `m_A(y)=sqrt(S_A(y)/n)`.

First, for every natural n,k₁,k₂, then every real n-by-k₁ matrix Z₁,
n-by-k₂ matrix Z₂, then every n-vector q, assume, in this order:

1. For every k₁-vector a there is a k₂-vector b such that `Z₁a=Z₂b`.
2. `A₁=[Z₁ q]` and `A₂=[Z₂ q]` each have full column rank.
3. `k₁+1<n` and `k₂+1<n`.

Put `R_i=S_{Z_i}(q)`. The conclusion is: for each i there exists a least-squares
coefficient vector a with `∑(q-Z_i a)²=R_i`; `R₁>0`, `R₂>0`, `R₂≤R₁`;
the final diagonal entry of `(A_iᵀA_i)⁻¹` equals `1/R_i`. Moreover, for every
n-vector y, if `S_{A₁}(y)>0` and `S_{A₂}(y)>0`, put
`s_i=sqrt(S_{A_i}(y)/(n-k_i-1))` and
`se_i=sqrt(V_{A_i}(y,k_i))`. Then
`se₁=s₁/sqrt(R₁)`, `se₂=s₂/sqrt(R₂)`,
`se₁/s₁≤se₂/s₂`, and `se₁≤se₂ s₁/s₂`.

Second, for every Z₁ of size 17-by-2, Z₂ of size 17-by-3, and 17-vectors
q,y, assume the same nesting and both appended designs' full column rank. It is
impossible for all four closed intervals to hold:
`se₁∈[1.35,1.45]`, `se₂∈[0.955,0.965]`,
`s₁∈[4.615,4.625]`, `s₂∈[4.695,4.705]`. The standard-error indices here are
2 and 3, respectively. These intervals themselves imply positive residual
variances; no positive-SSE premise is needed in this impossibility statement.

Third, the unconditional arithmetic assertions are
`0.965·4.625/4.695=7141/7512<0.951` and
`27/20-7141/7512=15001/37560>0`.

Fourth, for the same universally quantified 17-row matrices and vectors,
assume nesting, both appended ranks, positive SSE for both responses, and then
`se₂≤0.965`, `s₁≤4.625`, `4.695≤s₂`. The conclusion is
`se₁≤7141/7512`. No bound on se₁ is assumed here.

Fifth, the corrected-data clause uses the exact 17-by-5 rational array reproduced
below, whose rows correspond in order to 1948,1952,...,2012. Its columns are
outcome y, income q, tenure, fatalities, extremism. `tableTwoOutcome` is column 0.
`tableA1` has columns (1,q,tenure); `tableA2` has
(1,q,tenure,fatalities); `tableA3` has
(1,q,tenure,fatalities,extremism). The assertion is that each of these three
least-squares problems has exactly one minimizing coefficient vector. It also
asserts these formulas and half-open display intervals for coefficient index 1:

- For A1, the income coefficient is
  `7146187962914975000000/1117667657915636289559`, in `[6.385,6.395)`.
  Its squared SE is
  `7736251837253462080128985902187500000000000/8744266954854366478686864008983610246901367`,
  in `[0.935²,0.945²)`, and its SE is in `[0.935,0.945)`.
- For A2, the income coefficient is
  `315309901567374756223272228924480076940000000/49481205176565031631955325062456554157036059`,
  in `[6.365,6.375)`, and its SE is in `[0.955,0.965)`.
- For A3, the income coefficient is
  `560959205595590684404193874010188762669512981839878401170000000/87848341864933029922153613743599975715147930782629447955391927`,
  in `[6.385,6.395)`, and its SE belongs to both `[0.95,1.05)` and
  `[1.005,1.015)`.

Sixth, the alternative RMSQ clause first states
`0<sqrt(13/14)<1` and
`(7141/7512)sqrt(13/14)<7141/7512`. For every Z₁,Z₂,q,y of the 17-row types
above, under nesting and the two full-rank assumptions, put `m_i=sqrt(S_{A_i}(y)/17)`.
If both response SSEs are positive, then
`s₁/s₂=sqrt(13/14)·(m₁/m₂)`; furthermore, if
`se₂≤0.965`, `m₁≤4.625`, `4.695≤m₂`, then
`se₁≤(7141/7512)sqrt(13/14)`. Separately, without assuming positive SSE,
the same closed bins for se₁,se₂ and the printed RMSQ bins now imposed on
m₁,m₂ imply False.

Finally, for each ν, `studentLaw ν` is the pushforward of the product measure of
ν+1 independent `gaussianReal 0 1` coordinates under
`z↦z₀/sqrt((∑_{i≠0}z_i²)/ν)`. Thus at positive ν this is the central Student
reference distribution with ν degrees of freedom. `studentTailProbability ν t`
is the real conversion of this measure of `{s∈ℝ : t≤|s|}`. The three concluding
assertions are the probability bounds
`Pr(|T_14|≥|olsT A1 y 1|)<1/100`,
`Pr(|T_13|≥|olsT A2 y 1|)<1/100`, and
`Pr(|T_12|≥|olsT A3 y 1|)<1/100`.
No regression error distribution is assumed: these are reference probabilities
for fixed computed test statistics.

Junk-value and boundary audit:

- Matrix inverse is zero on singular real square matrices. In the general
  clauses, full column rank of each appended design implies both its Gram
  matrix and the controls' Gram matrix are nonsingular. In the fixed tables,
  uniqueness of minimizers entails full column rank; this must also be checked
  against the actual rational input data. There is no pseudoinverse convention.
- Real division by zero is zero. The degrees of freedom in the general
  conventional SE expressions are positive by `k_i+1<n`; in the fixed
  applications they are 14,13,12. All data denominators are positive.
  The quantities R₁,R₂ are positive because q is outside the respective
  control spans, as implied by the appended rank assumption. Positive response
  SSE is explicitly required wherever a ratio by s₁ or s₂ is used; in the
  impossible-bin statements it follows from the positive lower bin endpoints.
- `Real.sqrt` returns zero on nonpositive inputs. The SSE expressions are sums
  of squares, their denominators in use are positive, and inverse Gram
  diagonals are positive under the applicable rank conditions. Zero residuals
  can give zero SE, but cannot satisfy the positive printed bins and are
  excluded in the ratio clauses.
- `wholeRMSQ` at n=0 would divide by zero, but it is used only with n=17.
- The Student map uses a totalized zero denominator at z with all ν denominator
  coordinates zero. For ν=12,13,14 this set has product-Gaussian measure zero;
  its assigned statistic is zero and does not alter the distribution. At ν=0
  the definition would be a degenerate point mass at zero, but no such ν is
  used in this theorem.
- `ENNReal.toReal` sends infinity to zero, but the Student pushforward is a
  probability measure (the map is measurable), so its measurable tail sets
  have finite mass at most one. The toReal convention cannot make these tail
  probabilities spuriously small.
- General control dimensions may be zero: the coefficient type is then the
  single empty vector, and its column span is {0}; the statement still has its
  usual meaning. The observation and appended-column types are nonempty by
  the dimension inequalities. No unguarded choice from an empty type occurs.
- All n,p,k casts in SE denominators are into the reals before subtraction;
  there is no truncated natural subtraction in these clauses. The fixed Fin
  indices 0,1,2,3 fit their dimensions; Fin numeral totalization does not wrap
  them to unintended columns.
- No Bochner integral, mean of a nonintegrable function, logarithm, rpow,
  infimum/supremum, or limsup/liminf occurs in the actual dependency closure.
- All 107 line-zero dependencies for this theorem were printed and read.
  They are numeric `Nat.AtLeastTwo` or `NeZero` certificates, including the
  shared `WitnessTailComparisons._proof_4` and `studentFourTail._proof_1`.
  `studentLaw._proof_1` proves `NeZero (ν+1)` for every ν. They add no
  probabilistic, regression, or numerical-bound assumptions.

Exact deposited regression inputs:

| year | y | income | tenure | fatalities | extremism |
|---:|---|---|---|---|---|
| 1948 | 112/25 | 1934828833/500000000 | 16 | 0 | 119984289/500000000 |
| 1952 | -217/20 | 2417476109/1000000000 | 20 | 1904152679/10000000 | 1374649/15625000 |
| 1956 | 77/5 | 72046309/125000000 | 4 | 0 | -51046667/1000000000 |
| 1960 | -17/100 | 336587/20000000 | 8 | 0 | -53180451/1000000000 |
| 1964 | 1129/50 | 3258883307/1000000000 | 4 | 474421501/500000000 | -318262019/1000000000 |
| 1968 | -7/10 | 1398802867/1000000000 | 8 | 91018219/625000 | 54862857/250000000 |
| 1972 | 463/20 | 303629933/125000000 | 4 | 0 | -455834851/1000000000 |
| 1976 | -103/50 | 628281/800000 | 8 | 2086606979/1000000000 | 25423097/500000000 |
| 1980 | -487/50 | -207120123/250000000 | 4 | 0 | -19407/31250 |
| 1984 | 1821/100 | 1283325533/500000000 | 4 | 0 | 273800291/1000000000 |
| 1988 | 193/25 | 189045253/125000000 | 8 | 0 | 173195729/1000000000 |
| 1992 | -139/25 | 77430623/100000000 | 12 | 0 | 192515613/1000000000 |
| 1996 | 851/100 | 283826897/250000000 | 4 | 0 | -146050087/1000000000 |
| 2000 | 51/100 | 837710937/500000000 | 8 | 0 | -42411239/250000000 |
| 2004 | 123/50 | 32470207/31250000 | 4 | 3860627651/1000000000 | 62372671/250000000 |
| 2008 | -727/100 | -349851591/500000000 | 8 | 1398476601/100000000 | -119001519/1000000000 |
| 2012 | 96/25 | 86756221/250000000 | 4 | 24/5 | 40330327/1000000000 |
