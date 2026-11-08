# Blind reading

This file was written before opening `claims.json` or `record.json`. Source statements and docstrings, every entry of `closure.json`, and the generated auxiliary declarations printed in `scratch/BlindPrint.out` were read. No paper or external account was used at this stage. The mathematical notation below expands the SAP definitions into finite sums, ordinary field operations, finite functions, real square roots, and real least-squares minimization.

## Shared mathematical notation (expanded definitions)

An `AssignmentDesign Ω I R` is just two functions: weights `q : Ω → R` and assignments `t : Ω → I → Bool`. The structure itself imposes no probability axioms. The statements here use `R = ℚ` or `ℝ`. All indexing types are finite. Write

* `E f = Σω qω fω` (the SAP `mean`, a weighted finite sum);
* `A_a(ω,i) = 1` if `tωi = a`, and `0` otherwise (`armIndicator`);
* `p_ai = Σω qω A_a(ω,i)` (`inclusion`), and `p_abij = Σω qω A_a(ω,i)A_b(ω,j)` (`jointInclusion`);
* `Yωi = x_i` when `tωi` is true, and `z_i` otherwise (`response`);
* `O F = Σi Σj≠i F(i,j)` (`orderedOffDiagonalSum`, over ordered pairs);
* `U_ab F = O (1_{p_abij=0} F(i,j))` (`unavailablePairSum`);
* `H_a(y)(ω) = Σi A_a(ω,i)y_i/p_ai` (`htSum`);
* `H_N(x,z) = (H_1(x)-H_0(z))/N` (`htContrast`);
* `S_a(y,f)(ω) = Σi [A_a y_i/p_ai - A_a f(ω,i)/p_ai + f(ω,i)]` (`adjustedSum`);
* `G_N(x,z,f) = [S_1(x,f)-S_0(z,f)]/N` (`adjustedContrast`);
* `Δ_N(x,z) = (Σi x_i-Σi z_i)/N` (`averageEffect`, with `fixedTotal` the unweighted finite sum);
* `Cov(f,g) = E(fg)-(Ef)(Eg)`, `Var(f)=E(f²)-(Ef)²` (`designCovariance`, `designVariance`).

`isProbability` means `qω ≥ 0` for every ω and `Σω qω=1`. `hasPositiveMarginals` means `p_1i>0` and `p_0i>0` for every i. `directedSupport` means `p_10ij>0` for every distinct i,j. Disagreement probability is `Σω qω 1_{tωi≠tωj}`.

The estimated ordered pair term (`estimatedPairTerm`) is

`P_ab(ω,i,j) = [A_a(ω,i) A_b(ω,j)/(p_abij+δ(p_abij))] (p_abij-p_ai p_bj) (Yωi/p_ai)(Yωj/p_bj)`,

where `δ(p)=1` at `p=0` and `0` elsewhere (`zeroAdjustment`). Thus its joint denominator is replaced by 1 exactly at a zero joint probability. Define

`V_N(x,z)(ω) = {Σi [A_1(Yωi/p_1i)² + A_0(Yωi/p_0i)²] + O(P_11+P_00-2P_10) + U_11[(A_1i Yωi²/(2p_1i))+(A_1j Yωj²/(2p_1j))] + U_00[(A_0i Yωi²/(2p_0i))+(A_0j Yωj²/(2p_0j))]}/N²`.

This is `printedVarianceEstimate`, evaluated with the indicated x,z and design. The covariance statistic with omitted zero joints (`covarianceWithZeroOmission`) is

`C(x,z)(ω) = O [if p_10ij=0 then 0 else (A_1i A_0j/p_10ij)(p_10ij-p_1i p_0j)(Yωi/p_1i)(Yωj/p_0j)] - Σi A_1i Yωi²/(2p_1i) - Σi A_0i Yωi²/(2p_0i)`.

The population cross covariance expression (`populationCrossCovariance`) and lower-bound expression (`populationCovarianceBound`) are, respectively,

`K(x,z) = O[(p_10ij-p_1i p_0j)(x_i/p_1i)(z_j/p_0j)] - Σi x_i z_i`,

`B(x,z) = O[(p_10ij-p_1i p_0j)(x_i/p_1i)(z_j/p_0j)] - (Σi x_i²)/2 - (Σi z_i²)/2`.

`roundsToThree(v,r)` means `r-1/2000 ≤ v < r+1/2000`. `sdRoundsToThree(v,r)` means `(r-1/2000)² ≤ v < (r+1/2000)²`; it is a predicate on v, not a call to square root. All its uses in these targets have positive r and positive lower endpoints, so it expresses the corresponding rounding of the nonnegative square root.

The common sixteen-unit example is the following *fixed* rational data, in zero-based Lean indexing:

* unit-to-cluster map `c = [0,0,1,1,2,3,4,4,4,5,5,6,6,7,8,9]`;
* outcomes `y = [1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0]`, used for both potential outcomes;
* covariates `X = [4,0,4,1,4,2,4,1,2,5,4,1,4,2,2,3]`.

Units 0–5 form block 1 and units 6–15 form block 2. Cluster assignments have sample space `Fin 6 × Fin 15`, with every pair given weight 1/90. The first component selects the treated pair of the first four clusters in the order `(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)` (`twoOfFourLaw`). The second selects the treated pair of the last six clusters, in lexicographic pair order `(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)` (`paperTwoOfSix`). The two choices are the complete Cartesian product (`paperTableDesign`); units inherit their cluster's assignment and the same weights (`paperTableUnitDesign`).

For any unit function f, `fiberTotal c f k = Σ{i : c_i=k} f_i`. `paperTableLinearPrediction` is `l_i=1/4+X_i/8` in block 1, `l_i=70/93+X_i/31` in block 2. `paperTableLinearResidual` is `r_k=Σ{i:c_i=k}(y_i-l_i)`. The block-centered variables are `X°_i=X_i-5/2` in block 1 and `X_i-14/5` in block 2; `y°_i=y_i-5/6` in block 1 and `y_i-3/5` in block 2. For an assignment ω, `t̄_b` is the mean treatment indicator over the 6 or 10 units of block b, `t°_i=t_i-t̄_b`, and

`u_i=t°_i - [Σj X°_j t°_j / Σj (X°_j)²] X°_i`;
`e_FE(ω)=Σi u_i y°_i / Σi u_i²`;
`b_X(ω)=Σi X°_i(y°_i-e_FE t°_i)/Σi (X°_i)²`.

These expand `paperTableTreatmentMean`, `paperTableCenteredT`, `paperFeTreatmentResidual`, `paperFeEstimate`, and `paperFeXCoefficient`.

## SAP.P026a.T6

The docstring describes a refutation of printed Table 2 values, supplies corrected generalized and FE moments, and says every displayed approximation has error less than 0.00000005. The actual statement is the following conjunction, with no external parameters or hypotheses. All data are the fixed sixteen-unit example above, not arbitrary inputs.

1. `Σi(X°_i)²>0`, and for every one of the 90 assignments, `Σi u_i²>0`.
2. The ten residual cluster totals are exactly `[1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93]`.
3. For `h=H_16(r,r)` and `v=V_16(r,r)`, computed on the ten-cluster design, `Eh=0`, `Var(h)=38307/634880`, `Ev=38307/634880`, and `Var(v)=2400328658503/15687787688755200`.
4. `Var(h)>265/10000`, `Var(h)>(1625/10000)²`, and `Var(v)>(75/10000)²`. These are strict departures from the rounding intervals centered at .026, .162 and .007, respectively.
5. `-145/10000 < E e_FE < -135/10000`, `775/10000 < Var(e_FE) < 785/10000`; both `Var(e_FE)` and `Var(e_FE)+(E e_FE)²` satisfy `sdRoundsToThree(·,279/1000)`; and `38307/634880 < Var(e_FE)+(E e_FE)²`.
6. The ninety weights are nonnegative and sum to 1; both marginals for every cluster are positive; every directed distinct-cluster treatment/control joint is positive; both same-arm distinct-cluster joints are positive.
7. `Δ_16(y,y)=0`.
8. For **each** `b : Bool` and **every** real coefficient vector `β : Fin 2 → ℝ`, minimizing `Σ{i in block b}(y_i-β_0-X_i β_1)²` over **all real** coefficient vectors is equivalent to `β=[70/93,1/31]` for block 1 (`b=false`), or `β=[1/4,1/8]` for block 2 (`b=true`). This expands `w1BlockUnits`, `w1BlockDesign`, `w1BlockY`, `w1BlockCoefficients`, `w1Predict`, `w1Loss`, `w1Minimizes`. The coefficients are fitted in the opposite block from the block where l is used.
9. Define the actual unit statistic `g=G_16(y,y,f)` with `f(ω,i)=l_i` (`w1LinearG`), and `v=V_16(r,r)` (`w1LinearV`). For every assignment, `g=h`. Explicitly `Eg=0`, `Var(g)=38307/634880`, `Ev=38307/634880`, `Var(v)=2400328658503/15687787688755200`. The two biases `Eg-Δ_16(y,y)` and `Ev-Var(g)` are zero.
10. `sqrt(E(g-0)²)=sqrt(Var(g))` and `sqrt(E(v-Var(g))²)=sqrt(Var(v))`, after embedding rational expectations in ℝ. This is the full content of `w1RMSE` in these uses.
11. For **every** assignment ω and **every** real `β : Fin 4 → ℝ`, minimizing `Σi(y_i-β_0-t_iβ_1-1_{block2}β_2-X_iβ_3)²` over all real coefficients is equivalent to `β=[a,e_FE,d-a,b_X]`, where `a=5/6-e_FE t̄_1-(5/2)b_X`, `d=3/5-e_FE t̄_2-(14/5)b_X`. Its coordinate 1 is explicitly asserted to be `e_FE` cast to ℝ. This expands `w1FeDesign` and `w1FeCoefficients`.
12. With absolute error strictly below `1/20000000`, the real numbers `Var(g)`, `sqrt(Var(g))`, `sqrt(Var(v))`, `E e_FE`, `Var(e_FE)`, `sqrt(Var(e_FE))` equal the supplied centers `.0603374`, `.2456367`, `.0123696`, `-.0139874`, `.0777347`, `.2788094`, respectively (`w1Approx7`).
13. `E e_FE` fails the three-decimal rounding interval centered at `-.012`, `Var(e_FE)` fails that centered at `.036`, and `Var(e_FE)` fails the squared square-root interval centered at `.191`.

Junk/convention audit: Rational/real division is total with `a/0=0`. Here N=16, the finite positive marginals and positive joints are conclusions, and both FE projection sums are strictly positive conclusions. Thus the statistic is genuinely evaluated at nonzero denominators; no claimed number relies on a zero denominator. The pair-term replacement/omission is defined everywhere but inactive on distinct pairs in this design. `Real.sqrt` is 0 on negative arguments, but every used argument is a nonnegative second moment or variance of a certified finite probability law. Rational-to-real casts are the exact ordered field embedding. All unit/cluster/allocation types are nonempty fixed finite types. The `i.val-4` in the last-block assignment lookup is natural truncated subtraction, used only on the branch `i.val≥4`, with `i.val<10`, so it is the intended reindexing. Finite array lookups have in-range `Fin` indices, not partial-function defaults. No integrals, `toReal`, extrema, limits, logarithms or real powers occur. The auxiliaries in this closure only supply `NeZero`/`AtLeastTwo` instances for numerals and the safe `Fin 6` lookup bound; they add no mathematical premise.

## SAP.P026a.T7

The docstring describes corrected G (Linear) and FE (Cov.) values and unchanged noncovariate columns. This theorem is another closed conjunction on the same fixed rational example; it does not quantify over populations or designs.

The included `T7Statement` asserts:

1. Both FE projection denominators are strictly positive for all 90 assignments.
2. The same four exact G (Linear) moments as T6: mean 0, variance and expected variance estimate `s=38307/634880`, variance of variance estimate `z=2400328658503/15687787688755200`. `sqrt(s)` rounds to .246, s rounds to .060, and `sqrt(z)` rounds to .012, using the squared inequalities defined above.
3. The same strict FE (Cov.) mean and variance intervals as T6, SE and RMSE rounding to .279, and `s<Var(e_FE)+(E e_FE)²`.
4. For each cluster k, `Σ{i:c_i=k}y_i = [2,2,1,0,2,2,2,0,0,0]_k` (`paperTableClusterY`), and `Σ{i:c_i=k}(y_i-1/2)=[1,1,1/2,-1/2,1/2,1,1,-1/2,-1/2,-1/2]_k` (`paperTablePriorResidual`). The H_16 contrasts of these respective cluster arrays have means zero, variances `353/1920` and `233/2560`, and expected V_16 estimates equal to those variances. They round to .184 and .091.

The rest of `T7WholeStatement` asserts the following, with the quantifiers stated explicitly:

5. `Δ_16(y,y)=0`. For every block b the intercept/X fit is the unique global real least-squares fit with coefficients `[70/93,1/31]` or `[1/4,1/8]`, selected by b. For every assignment the FE (Cov.) regression on `(1,t,block2,X)` is the unique global real least-squares fit with coefficients `[a,e_FE,d-a,b_X]`, as expanded for T6.
6. Here the precise meaning of `w2UniqueFit(A,q,y,c)` is `(∀d∈ℝ^k, L(c)≤L(d)) ∧ (∀d∈ℝ^k, L(d)=L(c) → d=c)`, with `L(d)=Σi q_i(y_i-Σj A_ij d_j)²`, after rational inputs are cast to reals (`w2Loss`). A block fit uses the 16 rows and weights 1 on the chosen block, 0 on the other (`w2BlockWeight`); the design is `(1,X)` (`w2LinearDesign`, `w2LinearBeta`). The FE covariate design and coefficients are `w2FeCovDesign` and `w2FeCovBeta`, exactly the arrays in item 5. `W2Allocation` is just `Fin 6 × Fin 15`.
7. For every assignment, let inverse-probability weights q_i be 2 in block 1, and 3 for treated / 3/2 for control units in block 2 (`w2IPWWeight`). Every q_i is positive and is exactly `1/p_{observed arm,i}`. Set `Q_a=Σ{i:t_i=a}q_i` and `M_a=Σ{i:t_i=a}q_i y_i/Q_a` (`w2IPWArmWeight`, `w2IPWArmMean`). Both Q_a are positive. The weighted Gram matrix `B_jl=Σi q_i A_ij A_il` has nonzero determinant for `A=(1,t)` (`w2Gram`, `w2IPWDesign`); `[M_0,M_1-M_0]` is its unique real weighted least-squares coefficient vector (`w2IPWBeta`). Its second coordinate `M_1-M_0` is `w2IPWEstimate`.
8. For every assignment, `Σi(t°_i)²>0`. For the unweighted design `(1,t,block2)` (`w2FeDesign`), the Gram determinant is nonzero and `[a0,e0,d0-a0]` is the unique real least-squares fit, where `e0=Σi t°_i y°_i/Σi(t°_i)²`, `a0=5/6-e0 t̄_1`, `d0=3/5-e0 t̄_2` (`w2FeEstimate`, `w2FeBeta`).
9. For every assignment the three unit-level G statistics with prediction l, constant 0, and constant 1/2, respectively, equal the three cluster H_16 statistics on residuals r, raw totals, and prior residuals (`w2LinearEstimate`, `w2HTEstimate`, `w2PriorEstimate`). Their associated variance estimates (`w2LinearVariance`, `w2HTVariance`, `w2PriorVariance`) are exactly V_16 on those same respective arrays. The variances of the HT and prior variance estimates are `10147/7372800` and `20083/52428800`.
10. The IPW and FE variance estimates are the following actual clustered sandwich expression (`w2ClusterHC1`), with the above q,A,c, coordinate t=1, and k=2 for IPW, k=3 for FE:

   `(10/9) [15/(16-k)] Σg [Σj (B⁻¹)_{1j} Σ{i:c_i=g} q_i A_ij(y_i-Σl A_il c_l)]²`.

   Matrix inverse is Mathlib's inverse of a square rational matrix; the asserted determinants are nonzero. `w2Predict` is the finite dot product `Σl A_il c_l`. These yield `w2IPWVariance` and `w2FeVariance`.
11. For any estimator e and variance estimate v, the ten numbers used by `w2TableColumn` are exactly `[0, m, m, sqrt(s), sqrt(s+m²), s, a, a-s, sqrt(z), sqrt(z+(a-s)²)]` in ℝ, where `m=Ee`, `s=Var(e)`, `a=Ev`, `z=Var(v)`. The first row hardcodes the true ATE 0, which item 5 also establishes; the third row is bias relative to zero. Each entry lies in the lower-closed/upper-open interval of width .001 about the corresponding rational entry (`w2RealRounds`, `w2ColumnRounds`, `w2PrintedColumn`). The five complete asserted columns are:

   * G (Linear): `[0,0,0,.246,.246,.060,.060,0,.012,.012]`;
   * HT: `[0,0,0,.429,.429,.184,.184,0,.037,.037]`;
   * G (Prior): `[0,0,0,.302,.302,.091,.091,0,.020,.020]`;
   * IPW: `[0,-.014,-.014,.276,.277,.076,.071,-.005,.017,.018]`;
   * FE: `[0,-.016,-.016,.283,.283,.080,.074,-.006,.019,.020]`.
12. FE (Cov.) real square-root SE and RMSE each round to .279. G (Linear)'s `sqrt(38307/634880)` is strictly smaller than FE (Cov.)'s `sqrt(Var(e_FE)+(E e_FE)²)`.

Junk/convention audit: All rational divisions and real divisions are totalized at zero. N=16 and the numerical constants are nonzero; block treatment means use 6/10; IPW Q_a, FE denominators and sandwich Gram determinants are explicitly positive/nonzero. The statement has no separate `isProbability paperTableDesign` conjunct, but the weights are explicitly 1/90 on exactly 90 outcomes, so they are an actual probability law. Its cluster marginals are 1/2 in block 1 and 1/3,2/3 in block 2; its distinct-cluster same-arm and directed joints are positive by the enumerated Cartesian-product design. Thus V_16's zero-pair conventions are inactive here. A singular square matrix has totalized inverse in Mathlib, but all sandwich uses have nonsingular Gram matrices in the statement. `16-(k:ℚ)` is **field subtraction**, not natural truncated subtraction, and k=2 or 3, so the HC1 denominator is 14 or 13. Real square roots are applied to nonnegative true finite-law variances/MSEs. Squared rounding intervals are used with positive lower endpoints. Natural subtraction only reindexes the last six clusters under its guarded branch. All arrays have valid `Fin` indices. No empty types or nonintegrable expectations occur, nor logs, rpow, extended-real coercions, extrema or limits. The closure's generated auxiliaries are numeric typeclass certificates, not additional assumptions.

## SAP.P026a.T8

The docstring calls this the **corrected** Appendix E display under directed support, with the exact gap and equality characterization. The statement is a conjunction of four separately universally quantified propositions.

In each proposition, first quantify finite types U,C with decidable equality and nonemptiness, then a `ClusterLaw E`, then (where shown) a separation proof and a directed-support proof, then arbitrary potential outcomes `x,z : U → ℝ`. A cluster law consists of a fixed **surjective** map `c:U→C` and a law q on **all** Boolean cluster allocation vectors `ω:C→Bool`, with `q≥0`, `Σω q=1`, and positive probabilities for both arms of each cluster (`UnitLaw`). The induced cluster design has weight q and assignment ω itself (`UnitLaw.assignmentDesign`, `ClusterLaw.clusterAssignmentDesign`). Write `X_c=Σ{i:c_i=c}x_i`, `Z_c=Σ{i:c_i=c}z_i` (`ClusterLaw.totals`). Separation means `Pr(ωc≠ωd)>0` for every distinct c,d. No same-arm support assumption is imposed.

1. For every E, separation proof, x,z: `Cov(H_1(X),H_0(Z))=K(X,Z)`, where K is the complete ordered off-diagonal expansion minus `Σc X_c Z_c` given above.
2. For every E, separation proof, x,z: `Cov(H_1(X),H_0(Z))-B(X,Z)=(Σc(X_c-Z_c)²)/2`.
3. For every E, separation proof, **also** directed support `p_10cd>0` for all c≠d, then x,z: `E C(X,Z)=B(X,Z)`, `E C(X,Z)≤Cov(H_1(X),H_0(Z))`, and `[E C(X,Z)=Cov(H_1(X),H_0(Z)) ↔ ∀c,X_c=Z_c]`. C is exactly the cross-arm statistic expanded above, with the two half-square diagonal penalties, and zero-joint omission (inactive off diagonal under this premise).
4. For every E, separation proof, x,z: `B(X,Z)≤Cov(H_1(X),H_0(Z))`.

This concludes equality for cluster totals, not unitwise x=z. The hypotheses precede the arbitrary outcomes in each implication; there is no existential choice of outcomes or partition. Separation is weaker than the directed support used only in clause 3, and is redundant for these algebraic identities but explicitly present.

Junk/convention audit: Positive marginal conditions are fields of `UnitLaw`, so divisions by marginal probabilities are valid. The cross-arm statistic omits zero joints by definition; clause 3 assumes directed support and therefore genuinely uses the literal cross-arm ratios on all distinct pairs. The other clauses do not divide by joint probabilities. There is no ATE or N denominator. Nonempty U,C and surjectivity guard any intended population/cluster interpretation; single-cluster instances are allowed, with off-diagonal sums empty and separation/support vacuous on distinct pairs. They still have substantive diagonal identities. All expectations are finite sums on the finite full Boolean allocation type, so measurability and finite moments can be supplied automatically. There are no integrals, logarithms, square roots, real powers, unbounded extrema/limits, extended-real conversions, or partial lookups. Numeric auxiliary proof constants (including those shared by other definitions through elaboration) merely certify numeral construction.

## SAP.P026a.T9

The docstring calls this a refutation of the literal Appendix E display, including the ambiguity between the variance named on its left side and covariance named in the surrounding text. The theorem is a closed conjunction on a concrete four-unit/four-singleton-cluster example; it has no hypotheses.

The sample space has six elements. All six treated pairs of four clusters are listed in order `(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)`, each with weight 1/6 (`twoOfFourLaw`). Both potential-outcome vectors are `y=[1,2,4,7]` (`appendixNullOutcomes`). In addition to the previously expanded quantities, the *literal* appendix statistic is

`D_app(ω)=Σi A_1i(1-p_1i)(Yωi/p_1i)² + O[if p_11ij>0 then P_11(ω,i,j) else 0] - Σi A_1i Yωi²/(2p_1i) - Σi A_0i Yωi²/(2p_0i)`

(`appendixDisplay`). This has a treatment-arm diagonal and treatment/treatment ordered-pair terms before the two half-square penalties; it is **not** the cross-arm statistic C. The arm population bound is

`B_a(y)=Σi p_ai(1-p_ai)(y_i/p_ai)² + O[if p_aaij>0 then (p_aaij-p_ai p_aj)(y_i/p_ai)(y_j/p_aj) else 0] + U_aa[(y_i²+y_j²)/2]`.

This is `armPopulationBound`; the theorem uses a=true.

The full asserted conjunction is:

1. The design is a probability law, has positive marginals, and has directed support.
2. For every distinct i,j, `p_11ij=p_00ij=1/6` and `p_10ij=1/3`.
3. For every ω in the listed order, `D_app(ω)=[-68,-52,2,-62,-20,-52]_ω`, and its weighted expectation is -42.
4. `Cov(H_1(y),H_0(y))=-28`, `K(y,y)=-28`, `E C(y,y)=-28`, and `Var(H_1(y))=28`; also the explicit rational inequality `-42≠-28`.
5. `B(y,y)=-28`.
6. For every i, `p_1i=p_0i=1/2`.
7. For every ω, `C(y,y)(ω)=[-37,-25,-22,-22,-25,-37]_ω`.
8. `B_true(y)=28`.
9. `E D_app≠B(y,y)` and `E D_app≠B_true(y)`.

Junk/convention audit: All weights, marginals and distinct-pair joints are strictly positive at the positions used. No ratio uses a zero denominator; the pair replacement, omission and support conditionals have no effect on their intended domains. Diagonal joint exclusions are explicit ordered off-diagonal sums, not hidden 0/0 terms. There are no square roots, integrals or limits in this statement. All finite types are concretely nonempty. All array lookups are valid `Fin` applications. There is no natural subtraction or empty-supremum convention. The sole shared numeric auxiliary is an ordinary numeral construction certificate. Thus any refutation furnished by these numbers concerns a substantive finite statistic, not nonmeasurability or an undefined expectation.

## SAP.P026a.T10

The docstring says grouping by a fixed cluster partition preserves each displayed HT total identity and the ATE contrast. The statement is a conjunction of three universal propositions, each independently quantifying finite U,C with decidable equality, nonempty U, and a `ClusterLaw E` as expanded for T8. C is not explicitly given a `Nonempty` instance in the binder, but a map from nonempty U and surjectivity ensure it is nonempty. No separation or joint-support premise is imposed. The cluster allocation space is `C→Bool`, with probabilities q and positive marginals in both arms. The unit design has the same weights and unit assignment `ω(c_i)` (`ClusterLaw.unitAssignmentDesign`); cluster totals are the finite fiber sums.

1. For **every** E, **every** `y:U→ℝ`, **each** arm a and **every** allocation `ω:C→Bool`,

   `Σi 1_{ω(c_i)=a}y_i/p^unit_ai = Σc 1_{ωc=a}(Σ{i:c_i=c}y_i)/p^cluster_ac`.

   The two inclusion probabilities in each corresponding fiber are expectations of the identical indicator under the same q.
2. For **every** E, **every** `x,z:U→ℝ`, and **every** allocation ω, the difference of the unit treatment/control HT totals divided by `|U|` equals the difference of their grouped cluster totals divided by the **same** `|U|`. In other words the average-effect normalization remains the number of units.
3. For **every** E,y,a,ω, set

   `G_U=Σc Σ{i:c_i=c} 1_{ω(c_i)=a} y_i/p^unit_ai`,
   `G_C=Σc Σ{i:c_i=c} 1_{ωc=a} y_i/p^cluster_ac`,
   `F=Σc [1_{ωc=a}(Σ{i:c_i=c}y_i)/p^cluster_ac]`.

   Assert all four equalities `H^unit_a(y)=G_U`, `G_U=G_C`, `G_C=F`, and `F=H^cluster_a(totals(y))`. Thus the individual grouping, indicator/probability substitution, factoring, and final HT expression are all included; the main total identity is not merely referred to informally.

Junk/convention audit: Positive cluster marginal probabilities are structure fields; unit marginals coincide with the corresponding cluster marginals. Since U is nonempty, `|U|` is a positive natural number and its cast to ℝ is nonzero. All w are allowed, including allocations of probability zero; denominators remain the population inclusion probabilities and are positive independently of the realized allocation. All sums are finite. Cluster fibers are nonempty by surjectivity. There are no joint-probability ratios or omission rules, no square roots/logarithms/rpow, no Bochner integrals, no `toReal`, no infima/suprema or limits, no partial functions, and no truncated subtraction. Casts only turn the positive finite cardinality into the real ATE denominator.

## Closure coverage and generated declarations

The shared expansions cover the design constructor/projections, response, totals, all indicator/inclusion/moment operations, support predicates, variance and covariance statistics, and fiber sums. The T6/T7 sections additionally expand every numerical-data and least-squares definition in their closures; T8/T10 expand every `UnitLaw`/`ClusterLaw` structure and projection used; T9 expands its distinct appendix statistic and arm bound. No conclusion is inferred from a definition named “Statement”: its entire conjunction is enumerated above.

All 22 distinct generated `._proof_` entries in the five closures were printed and read in `scratch/BlindPrint.out`. They are `T6WholeStatement._proof_1` through `_proof_8`; `T8Statement._proof_1`; `paperTableCluster._proof_1`; `paperTableDesign._proof_2`; `printedVarianceEstimate._proof_1`; `repairedBias._proof_1`; `w1Approx7._proof_1`; `w1BlockCoefficients._proof_1` through `_proof_5`; `w2FeVariance._proof_1`; `w2IPWEstimate._proof_1`; `w2RealRounds._proof_1`. Apart from the array-bound certificate `∀i:Fin 10, ¬i.val<4 → i.val-4<6`, their types are only `NeZero(n+1)` or `AtLeastTwo(n+1)` at the displayed positive numerals. They cannot encode a statistical conclusion, restrict a model, or select a junk value.
