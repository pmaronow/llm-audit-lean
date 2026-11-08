# Blind reading (written before opening claims.json / record.json)

Common definitions (SAP/P016a/Defs/Part1.lean, Part2.lean), unfolded to Mathlib notions:

- `Outcome n = Fin n → ℝ`, `Assignment n = Fin n → Bool` (true = treated); `bit b = 1` if `b` else `0` (Part1:10-14).
- `groupSize z g = #{i : z i = g}` (ℕ) (Part1:16); `groupSum u z g = Σ_{z i = g} u i` (Part1:19);
  `groupMean u z g = groupSum / (groupSize : ℝ)` (Part1:22) — **junk: 0 when the group is empty** (x/0 = 0).
- `pooledMean u = (Σ u i)/n` (Part1:25) — junk 0 for n = 0. `tss u = Σ (u i − ū)²` (Part1:27).
- `rss u z = Σ_i (u i − groupMean u z (z i))²` = within-group sum of squares (Part1:29).
- `meanDifference u z = mean_treated − mean_control` (Part1:32).
- `ecdf u z g t = #{i : z i = g ∧ u i ≤ t} / groupSize z g` (Part1:35) — junk 0 if group empty.
- `ks u z = max(0, max_i |F₁(u i) − F₀(u i)|)` via `List.foldr max 0` (Part1:38). Because both ECDFs are right-continuous
  step functions jumping only at data points, this equals `sup_{t∈ℝ} |F₁(t) − F₀(t)|` (two-sample KS distance) whenever
  both groups are non-empty; the seed 0 is harmless (all terms ≥ 0; for n = 0 it gives 0).
- `FiniteLaw Ω` = nonnegative weights on a Fintype summing to 1 (Part1:50); `mass P E = Σ_{E ω} P.weight ω` (Part1:55);
  `expectation P f = Σ P.weight ω · f ω` (Part1:58); `covariance P f g = E[fg] − E f E g` (population covariance)
  (Part1:61); `variance P f = covariance P f f` (Part1:64).
- `doubledP L U = min 1 (2·min L U)` (Part1:73). `uniformLaw Ω` = weight `1/|Ω|` (Part1:75).
- `complete4 : Fin 6 → Assignment 4` = the 6 assignments of 4 units with 2 treated, ordered
  TTFF, TFTF, TFFT, FTTF, FTFT, FFTT (Part1:80). `blocked4 : Fin 4 → Assignment 4` = TTFF, TFFT, FTTF, FFTT, i.e. the
  paired design with pairs {0,2},{1,3} (Part1:84). `u4 = (0,1,2,3)` (Part1:88).
- `lsObjective u X b = Σ_i (u i − Σ_j X i j b j)²` (Part1:90); `lsRSS u X = sInf (range (lsObjective u X))` (Part1:96)
  — sInf of a nonempty set bounded below by 0, so it is the true infimum of the least-squares objective (no junk: the
  range is never empty since `Fin k → ℝ` is inhabited, and it is bounded below by 0).
- `degree S i = Σ_j S j i` (column sum) (Part1:102); `basicX z i = (1, bit (z i))` (Part1:107).
- `groupValues u z g` = multiset `{u i : z i = g}` (Part1:110); `sameMargins u z v w` ⇔ ∀ g, the multisets of
  group-g values coincide (Part1:113).
- `pairedCovariance2 t c = [(t₀−t̄)(c₀−c̄) + (t₁−t̄)(c₁−c̄)]/2` — 2-pair covariance with **divisor 2** (population
  convention, not n−1 = 1) (Part1:116).
- `exposureSum S z i = Σ_j S i j · bit (z j)` (row-i sum over treated units) (Part2:11).
- `similarity s i j = 0` if `i = j`; else `1 − |a−b|/2` if `s i = some a, s j = some b`; else 0 (Part2:14). All uses
  below pass `some ∘ scores`, so the `none` default is never reached.
- `distance s i j = |s i − s j|` (Part2:19).
- `conditionalMean S bank i a = (Σ_{b : bank b i = a} exposureSum S (bank b) i) / #{b : bank b i = a}` — average
  exposure of unit i over bank entries (with multiplicity) giving unit i status a (Part2:21). **Junk: 0 if no bank entry
  gives unit i status a.**
- `centeredExposure S bank z i = exposureSum S z i − bit(z i)·cm(i,true) − (1−bit(z i))·cm(i,false)` (Part2:26).
- `sampleVariance h = Σ (h i − h̄)²/(n − 1)` (real subtraction; junk: n = 1 divides by 0 → 0; n = 0 divides by −1)
  (Part2:31). `sampleSD = √sampleVariance` (Part2:34; sqrt of a nonnegative quantity for n ≥ 2).
- `standardize h i = (h i − h̄)/sampleSD h` (Part2:36) — **junk: 0 when sampleSD = 0**.
- `codedExposure S bank z = standardize (centeredExposure S bank z)` with `bank : Fin N → Assignment n` (Part2:39).
- `applicationAdjust Y Z e b1 b2 i = Y i − bit(Z i)·b1 − b2·e i` (Part2:43); `applicationX z e i = (1, bit(z i), e i)`
  (Part2:46).
- `printedReject p ⇔ p < 1/20` (Part2:49); `codedReject p ⇔ p ≤ 1/20` (Part2:51).
- `matchedBank4` = FTFT, FTTF, TFFT, TFTF (pairs {0,1},{2,3}) (Part2:53); `matchedBank6 b = (b₀,¬b₀,b₁,¬b₁,b₂,¬b₂)`
  over `b : Fin 3 → Bool` (8 entries; pairs {0,1},{2,3},{4,5}) (Part2:57).
- `scores4 = (−1,−1/2,1/2,1)` (Part2:60), `scores6 = (−1,−3/4,−1/2,0,1/4,1)` (Part2:62).
- `IsDistanceMatrix Γ` = nonnegative, symmetric, zero diagonal, triangle inequality (Part2:64).
- `lowerCount ref obs = #{b : ref b ≤ obs}`, `upperCount ref obs = #{b : obs ≤ ref b}` (inclusive) (Part2:68,71);
  `rawP ref obs = doubledP (lower/B) (upper/B) = min(1, 2·min(lower/B, upper/B))` (Part2:74) — junk 0 if B = 0.

---

## SAP.P016a.T1 (Challenge/Part1.lean:8; statement Defs/Part3.lean:11-31)

`T1 : T1Statement`, a closed proposition (no variables, no hypotheses): a conjunction of explicit finite facts.

1. (Part3:12-13) `complete4` is injective and its range is exactly `{z : Fin 4 → Bool : #treated = 2}` — the complete
   randomization design with 4 units, 2 treated (6 assignments).
2. (Part3:14-15) `blocked4` is injective and its range is exactly `{z : z₀ ≠ z₂ ∧ z₁ ≠ z₃}` — the paired design with
   pairs {0,2},{1,3} (4 assignments).
3. (Part3:16-19) Pairing-association witness: `pairedCovariance2 (0,2) (1,3) = 1` and `pairedCovariance2 (0,2) (3,1) =
   −1` (divisor-2 covariance across the two pairs of treated value vs control value). For outcome tables
   (0,2,1,3) and (0,2,3,1) under TTFF (treated units 0,1; control units 2,3; so pairs {0,2},{1,3} are (0,1),(2,3) resp.
   (0,3),(2,1)): `rss = 4` and `ks = 1/2` for both. I.e. the within-pair covariance flips sign while RSS and KS are equal.
4. (Part3:20-23) Statistic tables with `u4 = (0,1,2,3)`: over `complete4`, RSS = (1,4,5,5,4,1), KS =
   (1,½,½,½,½,1); over `blocked4`, RSS = (1,5,5,1), KS = (1,½,½,1).
5. (Part3:24-31) Under the uniform law on design indices, with observed assignment index 0 (TTFF):
   complete design: `P(RSS_k ≤ RSS_0) = 1/3`, `P(KS_k ≥ KS_0) = 1/3`, `Cov(mean_treated, mean_control) = −5/12`;
   paired design: `P(RSS_k ≤ RSS_0) = 1/2`, `P(KS_k ≥ KS_0) = 1/2`, `Cov = −1/2`.
   Tail masses are inclusive (≤ / ≥); covariance is population covariance under the uniform law (divisor 6 resp. 4).

I verified all numbers by hand (e.g. treated means over complete4: .5,1,1.5,1.5,2,2.5, control mean = 3 − treated
mean, variance 5/12; blocked: .5,1.5,1.5,2.5, variance 1/2).

Junk values: none can matter. Every `groupMean`/`ecdf` denominator is a group of size 2; `ks` seed 0 harmless;
`uniformLaw` on nonempty `Fin 6`/`Fin 4`; no sqrt/log/sInf. Conventions that *are* choices: `pairedCovariance2` uses
divisor 2 (with divisor n−1 = 1 the values would be ±2); `covariance` is the population covariance; tails inclusive.

## SAP.P016a.T2 (Challenge/Part1.lean:12; statement Defs/Part3.lean:33-90)

`T2 : T2Statement`, a conjunction of eleven parts. Throughout `n : ℕ`, `u v : Fin n → ℝ`, `z w : Fin n → Bool`,
`n₀ = groupSize z false`, `n₁ = groupSize z true`, `m_g = groupMean u z g`, `d = meanDifference u z = m₁ − m₀`.

(a) (Part3:34-40) ∀ n ≥ 2, u, z with n₀ > 0, n₁ > 0: (i) `inf_{b∈ℝ²} Σ (u i − b₀ − b₁ bit(z i))² = rss u z`;
   (ii) ∀ a b, the objective at (a,b) equals rss ⇔ a = m₀ ∧ b = d (unique minimizer = control mean, mean difference);
   (iii) `rss = Σ u i² − n₀ m₀² − n₁ m₁²`.
(b) (Part3:41-43) same hypotheses: `rss = tss − (n₀ n₁ / n)·d²` (ANOVA decomposition).
(c) (Part3:44-47) ∀ n ≥ 2, u, z, w with n₀,n₁ > 0 and `groupSize w true = n₁`: `rss u w ≤ rss u z ⇔ |d(z)| ≤ |d(w)|`.
(d) (Part3:48-53) ∀ n ≥ 2, finite Ω with law P, u, zobs (both groups nonempty), `assign : Ω → Assignment n` with every
   `assign ω` having the same treated count as zobs: `P(rss(assign ω) ≤ rss(zobs)) = P(|d(zobs)| ≤ |d(assign ω)|)`
   (RSS lower-tail p-value = |mean difference| upper-tail p-value).
(e) (Part3:54-58) n ≥ 2, n₀,n₁ > 0: `rss = n₀(mean_0(u²) − m₀²) + n₁(mean_1(u²) − m₁²)`.
(f) (Part3:59-61) n ≥ 2, u v z w, n₀,n₁ > 0 for z, `sameMargins u z v w` (equal treated multisets and equal control
   multisets): `rss u z = rss v w ∧ ks u z = ks v w`.
(g) (Part3:62-73) n ≥ 2, finite Ω with law P, u, assign, n₀ n₁ > 0 with every `assign ω` having group sizes (n₀,n₁):
   ∀ ω, `n₁ m₁(ω) + n₀ m₀(ω) = n·ū`; `Cov_P(m₁, m₀) = −(n₁/n₀) Var_P(m₁)`; ∀ x: ∀ ω,
   `n₁ F₁(ω)(x) + n₀ F₀(ω)(x) = #{i : u i ≤ x}` and `Cov_P(F₁(x), F₀(x)) = −(n₁/n₀) Var_P(F₁(x))`. (Cov/Var population
   moments under P.)
(h) (Part3:74-81) Network-alignment witness: z = complete4 1 = TFTF, S the symmetric 0/1 adjacency with edges
   0–2, 1–3, 2–3, X = (1, bit z, degree): u4 = (0,1,2,3) and v = (2,1,0,3) have the same margins under z, both have
   RSS 4 and KS ½; degrees are (1,1,2,2); `lsObjective u4 X (−1,−1,2) = 0 = lsRSS u4 X`; `lsObjective v X (2,−1,0) =
   4 = lsRSS v X`. (Same margins, different network-regression RSS: 0 vs 4.)
(i) (Part3:82-83) Scalar-KS witness: `ks u4 (TFTF) = ks u4 (TFFT) = 1/2` but `rss = 4` vs `5`.
(j) (Part3:84-87) ∀ n, u, z with n₀,n₁ > 0: `rss = Σ_{control}(u − m₀)² + Σ_{treated}(u − m₁)²`.
(k) (Part3:88-90) ∀ n, u, z with n₀,n₁ > 0: the infimum `lsRSS u (basicX z)` is attained.

Junk values: groupMean/ecdf denominators: guarded by n₀,n₁ > 0 for z; for w in (c) `groupSize w false = n − n₁ = n₀`
so both positive; in (d) each `assign ω` has the same sizes; in (f) equal multisets give equal sizes; in (g) by hsize.
In (d),(g) Ω cannot be empty (a FiniteLaw has total mass 1). `lsRSS` is a genuine infimum. `pooledMean` divides by
n ≥ 2. The `ks`-equality in (f) holds because KS depends only on the two group multisets. `−(n₁:ℝ)/n₀ * Var` parses
as `(−n₁/n₀)·Var`, n₀ > 0. The `n ≥ 2` hypotheses are implied by n₀,n₁ > 0 (redundant, harmless). No junk value can
affect the meaning.

## SAP.P016a.T3 (Challenge/Part1.lean:16; statement Defs/Part4.lean:11-66)

`T3 : T3Statement`, a closed proposition; conjunction of five blocks of explicit computations.

A. Four-unit witness (Part4:12-27). `S = similarity(scores4)`, scores (−1,−½,½,1), S_ij = 1 − |s_i − s_j|/2 off-diag:
   S = [[0,¾,¼,0],[¾,0,½,¼],[¼,½,0,¾],[0,¼,¾,0]]. Bank = matchedBank4 (pairs {0,1},{2,3}). Conditional mean exposures:
   control (7/8, 9/8, 9/8, 7/8), treated (1/8, 3/8, 3/8, 1/8). For z = TFTF: raw similarity exposure x^S =
   (¼, 5/4, ¼, ¾); raw distance exposure x^D = Σ_j |s_i − s_j| bit z_j = (3/2, 3/2, 3/2, 5/2); centered similarity
   exposure h = (1/8, 1/8, −1/8, −1/8). No A,B,C with h = A + B·z + C·x^S, nor with h = A + B·z + C·x^D (units 0 and 2
   have equal z and equal x but h = ±1/8).
B. Six-unit witness (Part4:28-46). scores6 = (−1,−¾,−½,0,¼,1), S = similarity (8·S given), z = TFTFTF,
   bank = matchedBank6 (8 assignments, pairs {0,1},{2,3},{4,5}), x = x^S(z) = (9/8, 9/4, 11/8, 17/8, 1, 7/8),
   cm(i, z i) = (13/16, 31/16, 5/4, 2, 19/16, 17/16), h = (5/16, 5/16, 1/8, 1/8, −3/16, −3/16), degree =
   (5/2, 3, 13/4, 13/4, 3, 3/2); `pooledMean h = 1/12`, `sampleVariance h = 49/960` (divisor 5), `standardize h =
   √15/42·(11,11,2,2,−13,−13)`; h is not affine in x (¬∃A C), nor in (z, x) (¬∃A B C); for y = (0,1,0,1,1,0):
   `lsRSS y [1,z,h] = lsRSS y [1,z,std h] = 4/3`, `lsRSS y [1,z,x] = 655/708`, `lsRSS y [1,z,x,degree] = 515/859`.
   (I recomputed x, h, degree and the three RSS values exactly with Python fractions: they match.)
C. (Part4:47-53) Two exact 4×4 determinants: det[1, z, x^S, h] of block A = 1/8 (≠ 0), and det of a matrix with columns
   1, (0,0,1,1), decimals (21.6630956840236, 19.1947426509578, 20.8676713418681, 22.5467332911212),
   (0.370753999962044, 0.240866262449021, 0.286925998351727, −0.193126413625389) = −1.4030283848669586515272953541.
D. (Part4:54-59) The fourth column of that recorded table is not of the form A + B·(0,0,1,1) + C·(third column).
E. (Part4:60-66) Reference values ref = (1, 2, …, 1000), B = 1000, inclusive counts:
   obs 25: lower 25, upper 976, rawP = 1/20, `p ≤ 1/20` holds but `p < 1/20` fails;
   obs 40: lower 40, rawP = 2/25, one-sided lower proportion 0.04 ≤ 1/20 but rawP ≤ 1/20 fails;
   obs 980: lower 980, rawP = 21/500 (upper 21), lower proportion 0.98 > 1/20, rawP ≤ 1/20 holds.

Junk values: conditionalMean denominators are 2 (bank4) and 4 (bank6) — each unit takes both values; sampleVariance
divisor 5 (n = 6); sqrt of 49/960 > 0; standardize divides by positive SD; lsRSS genuine infimum; rawP with B = 1000;
`similarity` never reaches the `none` branch. Decimal literals are exact rationals. No junk value affects meaning.
Conventions that are choices: similarity = 1 − |Δ|/2 with zero diagonal; inclusive tail counts; doubled p capped at 1;
"coded" rejection p ≤ 0.05 vs "printed" p < 0.05; sample (n−1) standardization.

## SAP.P016a.T4 (Challenge/Part1.lean:20; statement Defs/Part4.lean:68-100)

`T4 : T4Statement`, a conjunction of seven parts, the last being the whole `T3Statement`.

(a) (Part4:69-75) ∀ n ≥ 2, N, S symmetric with zero diagonal, `bank : Fin N → Assignment n` in which every unit takes
   both values, a finset Ω of assignments on each of which the centered exposure has positive sample SD, `y0`,
   potential outcomes `y : Assignment n → Outcome n`, b1, b2, with the model `y z i = y0 i + bit(z i) b1 + b2·
   codedExposure S bank z i` for z ∈ Ω: then for every z ∈ Ω, `y z − b1·bit z − b2·codedExposure = y0` (adjustment
   recovers the baseline). Pure cancellation; hS, hdiag, hbank, hsd, hn are not used by the conclusion.
(b) (Part4:76-79) ∀ n ≥ 2, h, u, z with sampleSD h > 0: standardize h sums to 0, has sample variance 1 (divisor n−1),
   and `lsRSS u [1,z,std h] = lsRSS u [1,z,h]` (regression RSS invariant under standardizing the exposure column).
(c) (Part4:80-90) ∀ n ≥ 2, N, scores s, bank in which every unit takes both values, z with m treated, and **every bank
   assignment with m treated** (hm): with S = similarity(s), D = distance(s):
   (i) `x^S_i(z) = m − bit(z i) − ½ x^D_i(z)` (does not need hm);
   (ii) centered exposures: `h^S = −½ h^D` (needs hm and hbank);
   (iii) if SD(h^D) > 0 and SD(h^S) > 0 then `coded^S = −coded^D`. (The second positivity follows from the first, and
   without positivity both sides are the junk 0, so the identity would hold anyway.)
(d) (Part4:91-95) Four-unit (block A of T3): SD(h) > 0, h not affine in (z, x^S), and standardize h not affine in
   (z, x^S).
(e) (Part4:96-97) ∀ B > 0, ref, obs: `lower/B + upper/B ≥ 1` (inclusive tails overlap).
(f) (Part4:98-99) ∀ p α : ℝ, `(p ≤ α ∧ ¬ p < α) ⇔ p = α` (the coded vs printed rejection rules differ exactly at p = α).
(g) (Part4:100) T3Statement verbatim (see above).

Junk values: in (a) conditionalMean is nonjunk by hbank and standardize nonjunk by hsd, but the conclusion is pure
cancellation and would hold for any e anyway; in (b) hs excludes the SD = 0 junk; in (c)(ii) hbank excludes the empty
conditioning-set junk (without it the identity fails: cm = 0 on both sides breaks the −½ relation); (c)(iii) positivity
hypotheses exclude junk, which here would only make the identity trivially true; (e) B > 0. sampleVariance with n ≥ 2
is a genuine sample variance. No junk value changes the meaning.

## SAP.P016a.T6 (Challenge/Part1.lean:25; statement Defs/Part5.lean:11-20)

`T6 : T6Statement`:
(a) (Part5:12-18) ∀ n ≥ 2, finite nonempty Ω, `assign : Ω → Assignment n`, Γ a distance matrix (nonneg, symmetric,
   zero diagonal, triangle inequality), any map `g : (Fin n → ℝ) → (Fin n → ℝ)` such that for every ω the vector
   `g(x^Γ(assign ω))` (with `x^Γ_i(z) = Σ_j Γ_ij bit(z j)`, the raw distance exposure) has sample variance (divisor n−1)
   exactly 1; baseline y0, observed outcomes y ω, b1, b2 with the generation equation
   `y ω i = y0 i + b1·bit(assign ω i) + b2·g(x^Γ(assign ω)) i`: then ∀ ω, `y ω − b1·bit − b2·g(x^Γ) = y0`.
   The conclusion follows from `hy` by ring; hn, Nonempty, hΓ and hg are never used. It is an algebraic consistency
   statement (true for any g).
(b) (Part5:19-20) ∀ p, `printedReject p ⇔ p < 1/20` — definitional unfolding.

Junk values: sampleVariance with n ≥ 2 is a genuine sample variance; `hg` is satisfiable (e.g. n = 3, g ≡ (−1,0,1)).
No junk affects the meaning. The statement is trivially true: it asserts no property of g beyond the generation
equation and imposes no linearity/affine-normalization constraint.
