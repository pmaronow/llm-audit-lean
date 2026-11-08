# Blind reading (step 1) — SAP.P013a.T11, T12, T13, T14

Written before opening `claims.json` / `record.json`. All four theorems are in
`SAP/P013a/Challenge/Part2.lean` (lines 29, 33, 37, 45; `closure.json` lists the docstring start lines 27, 31, 35, 39).

Common objects (`SAP/P013a/Defs/Part1.lean`):

* `Design Ω` (l.14): `Ω` a `Fintype`; `weight : Ω → ℝ`, every weight `> 0`, total `= 1`.
  So a design is a probability law on a finite set with full support.
* `expectation P X = Σ_z w(z) X(z)` (l.19); `covariance P X Y = E[XY] − E[X]E[Y]` (l.21);
  `variance P X = covariance P X X = E[X²] − E[X]²` (l.24).
* `indicator D i d z = 1[D z i = d]` (l.29), real-valued.
* `Population P N K` (l.32): `exposure : Ω → Fin N → Fin K` (the exposure mapping composed with the
  assignment: unit `i`'s exposure condition under assignment `z`), `outcome : Fin N → Fin K → ℝ`
  (potential outcome `y_i(d)`). `N` units, `K` exposure conditions.
* `pi F i d = E[1[D_i = d]] = π_i(d)` (l.36); `jointPi F i j d e = E[1[D_i=d] 1[D_j=e]] = π_ij(d,e)` (l.39).
* `observed F z i = y_i(D_i(z))` (l.43).
* `Positivity F d :≡ ∀ i, 0 < π_i(d) ∧ π_i(d) < 1` (l.46). Note: this includes the upper bound `π_i(d) < 1`.
* `potentialTotal F d = Σ_i y_i(d)` (l.49); `potentialMean = total / N` (l.52);
  `causalEffect F d e = mean(d) − mean(e)` (l.55).
* `htTotal F d z = Σ_i 1[D_i(z)=d] · y_i(d)/π_i(d)` (l.58);
  `htEffect F d e z = (htTotal d z − htTotal e z)/N` (l.64).
* `pairTerm F i j d e z = 1[D_i=d]1[D_j=e] · ((π_ij(d,e) − π_i(d)π_j(e))/π_ij(d,e)) · (y_i(d)/π_i(d)) · (y_j(e)/π_j(e))` (l.67).
* `varianceHT F d z = Σ_i 1[D_i=d](1−π_i)(y_i/π_i)² + Σ_i Σ_{j≠i} pairTerm i j d d z` (l.73).
* `correctionA2 F d z = Σ_i Σ_{j≠i} [π_ij(d,d)=0] (1[D_i=d] y_i²/(2π_i) + 1[D_j=d] y_j²/(2π_j))` (l.77).
* `missingA F d = Σ_i Σ_{j≠i} [π_ij(d,d)=0] y_i(d) y_j(d)` (l.82).

---------------------------------------------------------------------------------------------------

## SAP.P013a.T11 (`Challenge/Part2.lean:29`, statement `Defs/Part6.lean:124`)

Docstring: "P013-T11; Section 9, the two descriptions of the simulation design's exposure
probabilities (the degree-39 student; no no-exposure probability below 0.01), corrected claim; p. 1931
(PDF p. 20); design and exposure mapping on p. 1930 (PDF p. 19). Exact complete-randomization counting
links the degree-39 exposure probabilities and proves that the two printed probability descriptions are
incompatible."

Closure: `T11Statement` (Part6:124), seven `_proof_k` auxiliaries (all `Nat.AtLeastTwo` instances for the
numerals 39, 9, 27, 40000, 243, 100, 900 — checked by `#print`), `completeProbability` (Part4:83),
`isolatedExposure` (Part4:86), `noExposure` (Part4:89).

Definitions unfolded:

* `completeProbability U n A = #{S ∈ powersetCard n U : A S} / C(|U|, n)` (real division): the
  probability of event `A` when the treated set `S` is a uniformly random `n`-subset of `U`
  (complete randomization of `n` treated out of `|U|`).
* `isolatedExposure i nb S :≡ i ∈ S ∧ Disjoint S nb` (unit treated, no neighbour treated).
* `noExposure i nb S :≡ i ∉ S ∧ Disjoint S nb` (unit control, no neighbour treated).

Statement in plain mathematics: for all finite sets `U, nb ⊆ ℕ` and naturals `i, n` such that
`i ∈ U`, `nb ⊆ U`, `i ∉ nb`, `|nb| = 39`, `1 ≤ n`, `n ≤ |U| − 39`; writing
`p = P(i ∈ S, S ∩ nb = ∅)` and `q = P(i ∉ S, S ∩ nb = ∅)` for a uniform `n`-subset `S` of `U`:

1. `p = C(|U|−40, n−1) / C(|U|, n)`;
2. `q = C(|U|−40, n) / C(|U|, n)`;
3. `q = ((|U| − 39 − n)/n) · p` (real arithmetic);
4. if `|U| ≤ 10n + 5` then (a) `q ≤ 9p`; (b) `p ≤ 27/40000 → q ≤ 243/40000 ∧ q < 1/100`;
   (c) `1/100 ≤ q → 1/900 ≤ p ∧ 27/40000 < p`.

All quantifiers are universal, outermost; no existential. The statement is a general combinatorial
fact about a degree-39 unit (39 neighbours) under complete randomization; the application to the paper's
school network enters only through the hypothesis `|U| ≤ 10n + 5` (a treated fraction of roughly at
least 10%) and through the numerals 27/40000 = 0.000675 and 1/100.

Math check: with `M = |U| − 40`, the favourable sets are `{i} ∪ T`, `T` an `(n−1)`-subset of the `M`
non-neighbour, non-`i` units (resp. `T` an `n`-subset) — (1),(2) hold. `C(M,n)/C(M,n−1) = (M−n+1)/n =
(|U|−39−n)/n` gives (3) (including the boundary `n = M+1` where both sides vanish). Under
`|U| ≤ 10n+5`: `(|U|−39−n)/n ≤ (9n−34)/n < 9`, giving (a), (b), (c).

Junk values: division by `C(|U|, n)` — positive since `n ≤ |U| − 39 ≤ |U|`; no junk. Truncated
subtractions `|U| − 39`, `|U| − 40`, `n − 1`: the hypotheses force `|U| ≥ 40` (`nb ∪ {i} ⊆ U`) and
`n ≥ 1`, so none truncates. Real division by `n`: `n ≥ 1`. `Nat`→`ℝ` casts of `|U|`, `n` and binomials
are exact. No empty-type issue (`U` nonempty). Nothing affects the meaning.

Hypotheses jointly satisfiable: e.g. `U = {0,…,399}`, `nb = {1,…,39}`, `i = 0`, `n = 40`
(`400 ≤ 405`).

---------------------------------------------------------------------------------------------------

## SAP.P013a.T12 (`Challenge/Part2.lean:33`, statement `Defs/Part6.lean:151`)

Docstring: "The printed claim is false: the unrestricted relative-bias bound and the logarithmic
replicate guarantee are both refuted on the nonzero-total domain. P013-T12; Proposition 4.1; p. 1920
(PDF p. 9); proof in Appendix A.3, p. 1938 (PDF p. 27)."

Closure: `Design` (+`mk`, `weight`), `Population` (+`mk`, `exposure`, `outcome`), `Positivity`,
`expectation`, `indicator`, `observed`, `pi`, `potentialTotal` (Part1); `independentProduct` (Part2:57,
+2 proof auxiliaries: positivity and total of product weights), `replicateDesign` (Part2:63, +2
auxiliaries), `replicateCount` (Part2:71), `simulatedPi` (Part2:75), `simulatedHTTotal` (Part2:79),
`IsMinimumPi` (Part2:83); `PrintedBiasBound` (Part6:136), `PrintedReplicateRule` (Part6:143),
`T12Statement` (Part6:151).

Definitions unfolded:

* `independentProduct P Q`: product law on `Ω × Ξ`, weight `P(z₁)Q(z₂)`.
* `replicateDesign P R`: law on `Fin R → Ω`, weight `Π_r P(z_r)` — `R` i.i.d. draws from `P`.
* `replicateCount F d R zs i = Σ_r 1[D_i(zs_r) = d]` (number of replicates putting `i` in `d`).
* `simulatedPi F d R zs i = (replicateCount + 1)/(R + 1)` — the add-one simulated exposure probability.
* `simulatedHTTotal F d R (z, zs) = Σ_i 1[D_i(z)=d] · y_i(D_i(z)) / simulatedPi(zs, i)`
  `= Σ_i 1[D_i(z)=d] y_i(d) (R+1)/(B_i+1)`: HT total with simulated probabilities, the actual assignment
  `z` and the `R` replicates independent (product law).
* `IsMinimumPi F d p0 :≡ (∃ i, π_i(d) = p0) ∧ ∀ i, p0 ≤ π_i(d)` — `p0 = min_i π_i(d)`.

`PrintedBiasBound`: for every finite `Ω : Type`, `N, K`, design `P`, population `F`, with `N > 0`,
every `d` with `0 < π_i(d) < 1 ∀i`, every `R ∈ ℕ` (including `R = 0`), `p0 = min_i π_i(d)`, and
`T_d = Σ_i y_i(d) ≠ 0`:  `|(E_{P⊗P^R}[Ŷ_sim] − T_d)/T_d| ≤ (1 − p0)^{R+1}`.
Outcomes `y_i(d)` are arbitrary reals (no sign condition).

`PrintedReplicateRule`: same quantifiers, plus `∀ b > 0`, `R ≥ log b / log(1−p0) − 1` →
`|(E[Ŷ_sim] − T_d)/T_d| ≤ b`.

`T12Statement :≡ ¬PrintedBiasBound ∧ ¬PrintedReplicateRule`, i.e. there exist (Ω, N>0, K, P, F, d,
R, p0) satisfying positivity, minimality and `T_d ≠ 0` whose relative bias exceeds `(1−p0)^{R+1}`;
and there exist such data plus `b > 0` with `R ≥ log b/log(1−p0) − 1` whose relative bias exceeds `b`.
The witnesses are not displayed in the statement; the existential `R` may be `0`, and nothing forces
outcomes of one sign (signed outcomes are needed: for one-signed outcomes,
`E[Ŷ_sim] − T = −Σ y_i(1−π_i)^{R+1}`, whose relative size is ≤ `(1−p0)^{R+1}`).

Math check: `E[(R+1)/(B+1)] = (1 − (1−π)^{R+1})/π` for `B ~ Bin(R, π)`, so
`E[Ŷ_sim] − T = −Σ_i y_i(d)(1−π_i(d))^{R+1}`. With signs mixed and `T` near zero, the relative bias is
unbounded, for every `R` (including every `R ≥ 1`), so both negations are true; they are certified
anyway.

Junk values: division by `T_d` guarded by `T_d ≠ 0`; `simulatedPi ≥ 1/(R+1) > 0` (no zero division);
`Real.log b` with `b > 0`; `Real.log(1 − p0)` with `p0 ∈ (0,1)` (Positivity + IsMinimumPi), so it is
negative and finite — no junk. `R = 0` is allowed: then `simulatedPi = 1` and the bound reads `1−p0`;
this is a degenerate but well-defined case. Note that for a *negated* universal, allowing `R = 0`,
dropping sign conditions, or quantifying `p0` as the per-`d` minimum makes the negation *weaker* — a
witness in a case outside the printed claim's scope would not refute the printed claim. Whether this
matters depends on the printed reading (step 2).

---------------------------------------------------------------------------------------------------

## SAP.P013a.T13 (`Challenge/Part2.lean:37`, statement `Defs/Part6.lean:153`)

Docstring: "P013-T13; Lemma 4.1 and Proposition 4.2; p. 1919 (PDF p. 8); pp. 1920–1921 (PDF pp.
9–10); proofs in Appendix A.2 and A.4, p. 1938 (PDF p. 27). The exposure total and contrast have the
printed expectations, variance formulas and covariance expansion."

Closure: `Design`, `Population`, `Positivity`, `causalEffect`, `covariance`, `expectation`,
`htEffect`, `htTotal`, `indicator`, `jointPi`, `pi`, `potentialMean`, `potentialTotal`, `variance`
(Part1), `T13Statement` (Part6:153), `T7Statement._proof_1` (the `Nat.AtLeastTwo` instance for the
numeral `2`, shared by the exponent `^2`; checked by `#print`).

Statement (universe-polymorphic in Ω's universe): conjunction of

(A) for every finite `Ω`, `N, K`, design `P`, population `F`, with `N > 0`, every `d` with
`0 < π_i(d) < 1 ∀ i`:
  * `E[Ŷ^T(d)] = Σ_i y_i(d)`;
  * `Var[Ŷ^T(d)] = Σ_i π_i(1−π_i)(y_i/π_i)² + Σ_i Σ_{j≠i} (π_ij(d,d) − π_iπ_j)(y_i/π_i)(y_j/π_j)`.

(B) for every such data with `N > 0`, every `d ≠ e` with positivity at both `d` and `e`:
  * `E[τ̂(d,e)] = τ(d,e) = (Σ y_i(d) − Σ y_i(e))/N` (written as difference of means);
  * `Var[τ̂] = (Var Ŷ^T(d) + Var Ŷ^T(e) − 2 Cov(Ŷ^T(d), Ŷ^T(e)))/N²`;
  * `Cov(Ŷ^T(d), Ŷ^T(e)) = Σ_i Σ_{j≠i} (π_ij(d,e) − π_i(d)π_j(e))(y_i(d)/π_i(d))(y_j(e)/π_j(e)) − Σ_i y_i(d)y_i(e)`.

Math check: all identities are correct (the diagonal term of the covariance is `−π_i(d)π_i(e)·…` because
`1[D_i=d]1[D_i=e] = 0` for `d ≠ e`). `d ≠ e` is necessary for the covariance expansion.

Hypotheses beyond "π_i(d) > 0": `N > 0` (harmless; with `N = 0` the statement would hold anyway),
and the upper bound `π_i(d) < 1` (resp. at `e`) inside `Positivity`. The identities hold with
`π_i(d) = 1` too, so `π < 1` is a genuine narrowing unless the paper's standing assumption includes it
(to check at step 2; note that if every exposure condition has positive probability and `K ≥ 2` then
`π_i(d) < 1` follows). Designs have full support (all weights > 0): no loss for finite randomization
designs (restrict to the support).

Junk values: `y/π` divisions — `π > 0`, none; `/N`, `/N²` — `N > 0`, none; `variance` as
`E[X²] − E[X]²` on a finite law, always defined. Nothing affects meaning.

Satisfiable: `sharedDesign` (two equally likely assignments), `N = 1`, `K = 2`, exposure `= z`;
`π_1(0) = π_1(1) = 1/2`.

---------------------------------------------------------------------------------------------------

## SAP.P013a.T14 (`Challenge/Part2.lean:45`, statement `Defs/WholeW1.lean:206`, `Defs/Part6.lean:172`)

Docstring: "P013-T14; Lemma 5.1 and Propositions 5.1–5.2, pp. 1921–1922 (PDF pp. 10–11), and Appendix
A.5, Propositions A.1–A.2 and Corollary A.2, pp. 1939–1942 (PDF pp. 28–31). The exposure variance
estimate has the stated unbiasedness, missing-joint bias and quadratic conservativeness. For general
binary inclusion sampling with positive marginals, including certainty units, the same bias identity
and both conjugate-power and quadratic conservative corrections hold. All missing-pair sums are
ordered and outcomes may have either sign."

Closure: Part1 `Design`, `Population`, `Positivity`, `correctionA2` (+aux `2`), `covariance`,
`expectation`, `htTotal`, `indicator`, `jointPi`, `missingA`, `pairTerm`, `pi`, `variance`,
`varianceHT`; Part6 `T14Statement`; WholeW1 `WholeSamplingDesign` (+`mk`, `selected`, `weight`),
`samplingExpect`, `samplingIndicator`, `samplingPi`, `samplingJoint`, `samplingVariance`,
`samplingTotal`, `samplingVarianceHT`, `samplingMissingA`, `samplingYoungCorrection`,
`samplingQuadraticCorrection`, `T14WholeStatement`, `T1WholeStatement._proof_3` (numeral `2`).

`T14WholeStatement :≡ T14Statement.{0} ∧ General`.

`T14Statement` (Ω : Type): for every finite design `P`, population `F`, `N > 0`, `d` with
`0 < π_i(d) < 1 ∀ i`:
  (a) if `π_ij(d,d) > 0` for all `i, j`, then `E[V̂(d)] = Var[Ŷ^T(d)]`;
  (b) `E[V̂(d)] = Var[Ŷ^T(d)] + A(d)` with `A(d) = Σ_i Σ_{j≠i, π_ij=0} y_i(d) y_j(d)` (ordered pairs);
  (c) `Var[Ŷ^T(d)] ≤ E[V̂(d) + A₂(d)]` with
      `A₂(d) = Σ_i Σ_{j≠i, π_ij=0} (1[D_i=d] y_i²/(2π_i) + 1[D_j=d] y_j²/(2π_j))`.
Here `V̂(d) = Σ_i 1[D_i=d](1−π_i)(y_i/π_i)² + Σ_i Σ_{j≠i} 1[D_i=d]1[D_j=d] ((π_ij−π_iπ_j)/π_ij)(y_i/π_i)(y_j/π_j)`.

`General`: for all finite `U, Ω : Type` and a `WholeSamplingDesign U Ω` (weights `≥ 0` summing to 1 —
zero-weight atoms allowed — and an arbitrary inclusion map `selected : Ω → U → Bool`) with
`π_i = E[I_i] > 0` for all `i` (`π_i = 1` allowed), for every `y : U → ℝ`:
  (i) `E[V̂_s] = Var(Ŷ_s) + A_s`, where `Ŷ_s = Σ_i I_i y_i/π_i`, `Var` is `E[(X − EX)²]`,
      `V̂_s = Σ_i Σ_j [π_ij > 0] I_iI_j ((π_ij−π_iπ_j)/π_ij)(y_i/π_i)(y_j/π_j)` (diagonal included:
      gives `I_i(1−π_i)(y_i/π_i)²`), `A_s = Σ_{i≠j, π_ij=0} y_i y_j`;
  (ii) for every `a, b : U → U → ℝ` with `a_ij > 0, b_ij > 0, 1/a_ij + 1/b_ij = 1` on every ordered
      missing pair (`i ≠ j`, `π_ij = 0`): `Var(Ŷ_s) ≤ E[V̂_s + Σ_{i≠j, π_ij=0} (I_i |y_i|^{a_ij}/(a_ij π_i) + I_j |y_j|^{b_ij}/(b_ij π_j))]`;
  (iii) `Var(Ŷ_s) ≤ E[V̂_s + Σ_{i≠j, π_ij=0} (I_i y_i²/(2π_i) + I_j y_j²/(2π_j))]`.

Math check: `E[V̂] − Var = −Σ_{i≠j, π_ij=0}(0 − π_iπ_j) y_iy_j/(π_iπ_j) = A`. Corrections have expectation
`Σ (|y_i|^a/a + |y_j|^b/b)` resp. `Σ (y_i² + y_j²)/2`, and Young's inequality gives
`y_iy_j + |y_i|^a/a + |y_j|^b/b ≥ 0`. All correct.

Junk values:
* `pairTerm` divides by `π_ij(d,d)`; when `π_ij = 0` Lean gives `x/0 = 0`. Because every design weight is
  strictly positive, `π_ij = 0` forces `1[D_i=d]1[D_j=d] ≡ 0` on all of `Ω`, so the term is `0` in any
  convention — harmless. The general version guards with `if 0 < π_ij`.
* `y/π`: `π > 0` by hypothesis. `2π > 0`. `a_ij π_i > 0` on missing pairs; `a, b` are unconstrained
  elsewhere, but they only appear under the guard. `|y|^a` is `Real.rpow` of a nonnegative base with
  `a > 1` (forced by `a, b > 0`, `1/a + 1/b = 1`) — standard.
* `variance` (exposure part) = `E[X²] − E[X]²`, `samplingVariance` = `E[(X−EX)²]` — equal on finite laws.
* Universe: exposure part restricted to `Ω : Type` (harmless).

Extra hypotheses: `N > 0` (harmless) and `π_i(d) < 1` in `Positivity` for the exposure part (narrower
than `π_i(d) > 0`), but the general part (positive marginals only, certainty allowed, zero atoms
allowed, any sign) covers the exposure indicator `I_i = 1[D_i = d]` as a binary inclusion, and its
quadratic correction coincides with `A₂`. So jointly the bias identity and the quadratic
conservativeness are stated without the `π < 1` restriction. The unbiasedness (a) is stated in the
general part only implicitly (`A_s = 0` when no joint vanishes).

Satisfiable: `sharedDesign`, `N = 1`, `K = 2` as for T13 (`π = 1/2`); general part: any design with
positive marginals.
