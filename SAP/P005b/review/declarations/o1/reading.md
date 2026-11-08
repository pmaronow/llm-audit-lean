# Blind reading (step 1) — P005b, T15–T19

Written before opening `claims.json` / `record.json`. Elaborated forms were checked with
`#print` (scratch/Print.lean, scratch/Print2.lean, `pp.numericTypes`): every subtraction
like `((t+c : ℕ)-1 : ℝ)` or `(n - 2*m : ℝ)` elaborates as **real** subtraction of casts
(`↑(t+c) - 1`, `↑n - 2*↑m`). There is no truncated ℕ subtraction in any of the five
statements, except `armSize n m .control = n - m` (ℕ) in T19, which is harmless because
`m < n` is a hypothesis.

Common objects (Defs/Part1, Part2):
- `design n m` = all m-subsets of `Fin n`; `expectation m f` = (1/C(n,m)) Σ_{|S|=m} f(S)
  (uniform complete randomization); `variance m f` = E[(f − E f)²]; `probability m E` =
  #{S : |S|=m, E S}/C(n,m). For `m ≤ n`, C(n,m) ≥ 1, so no division by zero.
- `mean S a` = (Σ_{i∈S} a_i)/|S| (junk 0 if S = ∅); `popMean a` = mean over all of Fin n.
- `sampleCov S a b` = mean_S(ab) − mean_S(a)·mean_S(b) (divisor |S|, not |S|−1);
  `popCov a b` = sampleCov over univ.
- `control S` = complement. `Population n d` = covariates x : Fin n → Fin d → ℝ and potential
  outcomes yT, yC. `dot u v` = Σ_k u_k v_k. `xMean P S` = arm mean of covariates;
  `gram P` = (1/n) Σ_i x_i x_iᵀ; `standardized P` :⇔ x̄ = 0 ∧ gram P = I.
- `leverage P i` = ‖x_i‖² (equals n·H_ii when gram = I).
- `kappa P` = sSup (range (i ↦ ‖x_i‖²/n)). For n ≥ 1 the range is finite and nonempty,
  so kappa = max_i ‖x_i‖²/n (≥ 0). For n = 0 it is sSup ∅ = 0 (junk; only relevant in
  asymptotic statements, where finitely many n do not matter).
- `pT n m` = m/n, `pC n m` = (n−m)/n.
- `populationSlope P y` = (1/n) Σ_i y_i x_i (the population OLS slope when x is standardized).
- `N P m` = pT·β(yT) + pC·β(yC). `commonResidual P m y i` = (y_i − ȳ) − x_i·N.
- `NTTT n m` = (n−m)(n−2m)/((n−1)(n−2)m²); `NTTC n m` = −(n−2m)/((n−1)(n−2)m).

---

## SAP.P005b.T15 (`T15Statement`, Defs/Part3:33)

Write n = t + c (the population size), treated arm size t, control arm size c.

For all naturals t, c with t ≥ 2 and c ≥ 2:

1. `controlCoefficient t c` := (1/(n−1))·(c(n−1)/((c−1)n)) − NTTC(n,t)·(t(n−1)/((c−1)n))
   equals 1/(n−2).
2. `treatedCoefficient t c` := (−1/(n−1))·(t(n−1)/((t−1)n)) + NTTT(n,t)·(t²(n−1)/(c(t−1)n))
   equals (n − t·n)/((n−2)(t−1)n).
3. (n − t·n)/((n−2)(t−1)n) = −1/(n−2).
4. For every d, every population P of size n with d covariates, and every S with |S| = t:
   `covarianceCombination t c A B` = (1/(n−1))·( c(n−1)/((c−1)n)·B − t(n−1)/((t−1)n)·A )
   + NTTT(n,t)·t²(n−1)/(c(t−1)n)·A − NTTC(n,t)·t(n−1)/((c−1)n)·B
   equals B/(n−2) − A/(n−2), where A = sampleCov_S(leverage, yT) and
   B = sampleCov_{S^c}(leverage, yC).

Content: pure algebra. covarianceCombination = controlCoefficient·B + treatedCoefficient·A, so
(4) follows from (1)–(3) for arbitrary reals A, B; the population quantifier only instantiates
A, B. Hand check: (1) c(n−2) + n − 2t = n(c−1), giving 1/(n−2); (2) −t(n−2) + n − 2t = n(1−t).
The factors c(n−1)/((c−1)n), t(n−1)/((t−1)n) look like the reciprocals of the unbiasedness
factors E[sampleCov_arm] = (n_arm−1)n/(n_arm(n−1))·popCov, i.e. the bias estimator
coefficients after correcting sample covariances.

Junk values: none can matter. With t, c ≥ 2 we have n ≥ 4, so n−1, n−2, n, t−1, c−1, c are
all nonzero; NTTT/NTTC denominators (n−1)(n−2)t² ≠ 0. No ℕ subtraction (all casts real).
The hypotheses are satisfiable (t = c = 2).

---

## SAP.P005b.T16 (`T16Statement`, Defs/Part3:48)

For all n, m with n ≥ 3, 0 < m < n, and all a, b, c : Fin n → ℝ with Σa = Σb = Σc = 0
(E = uniform expectation over m-subsets S, 1_i = indicator of i ∈ S, S3 := Σ_i a_i b_i c_i):

1. ∀ i ≠ j: E[1_i 1_j] = m(m−1)/(n(n−1)).
2. ∀ pairwise distinct i, j, k: E[1_i 1_j 1_k] = m(m−1)(m−2)/(n(n−1)(n−2)).
3. E[repeatedPair] = Σ_i Σ_{j≠i} E[1_i1_j] a_i b_i c_j, with
   repeatedPair S = Σ_i Σ_{j≠i} 1_i 1_j a_i b_i c_j.
4. E[repeatedPair] = −m(m−1)/(n(n−1))·S3.
5. E[distinctTriple] = 2·m(m−1)(m−2)/(n(n−1)(n−2))·S3, with
   distinctTriple S = Σ over pairwise distinct (i,j,k) of 1_i1_j1_k a_i b_j c_k.
6. E[ā_S b̄_S c̄_S] = (1/m³)( E[Σ_i 1_i a_i b_i c_i] + E[Σ_i Σ_{j≠i} 1_i1_j (a_ib_ic_j + a_ib_jc_i +
   a_jb_ic_i)] + E[distinctTriple] ) (expansion of the cube of sums).
7. E[ā_S b̄_S c̄_S] = (1/m³)( m/n − 3m(m−1)/(n(n−1)) + 2m(m−1)(m−2)/(n(n−1)(n−2)) )·S3.
8. E[ā_S b̄_S c̄_S] = NTTT(n,m)·popMean(abc).
9. E[ā_S b̄_S c̄_{S^c}] = NTTC(n,m)·popMean(abc).
10. (1/m³)(m/n − 3m(m−1)/(n(n−1)) + 2m(m−1)(m−2)/(n(n−1)(n−2))) = (1/n)·NTTT(n,m).
11. E[repeatedPair] = m(m−1)/(n(n−1))·Σ_i Σ_{j≠i} a_i b_i c_j.
12. m(m−1)/(n(n−1))·Σ_iΣ_{j≠i} a_ib_ic_j = m(m−1)/(n(n−1))·(Σ_iΣ_j a_ib_ic_j − S3).
13. (1/n)NTTT(n,m) = (n−m)(n−2m)/(n m²(n−1)(n−2)).
14. ∀ S with |S| = m: c̄_{S^c} = −(m/(n−m))·c̄_S.
15. NTTC(n,m) = −(m/(n−m))·NTTT(n,m).

All quantifiers are universal; conclusions are a conjunction. Items 1, 2, 3, 10, 12, 13, 15 do
not use centering; 4, 5, 7, 8, 9, 11, 14 use it (e.g. Σ_{j≠i} c_j = −c_i; inclusion–exclusion
gives Σ_distinct a_ib_jc_k = 2·S3). Hand-checked: (n−1)(n−2) − 3(m−1)(n−2) + 2(m−1)(m−2) =
(n−m)(n−2m).

Junk values: none. C(n,m) ≥ 1; |S| = m > 0 and |S^c| = n−m > 0 so both means are genuine;
n ≥ 3 makes n−2 ≠ 0; n−m ≠ 0 since m < n; m ≠ 0. All subtractions real. Hypotheses
satisfiable (e.g. n = 3, m = 1, a = b = c = 0, or a = b = c = (1, −1, 0)).

---

## SAP.P005b.T17 (`T17WholeStatement`, Defs/WholeW1:47, with `T17Statement`, Defs/Part4:14)

A conjunction of six universally quantified parts. Notation: x_i ∈ ℝ^d, β(y) =
populationSlope = (1/n)Σ y_i x_i, lev_j = ‖x_j‖², δ arbitrary, and for the residual parts
e_T = commonResidual(yT), e_C = commonResidual(yC), Δ_i = e_T,i − e_C,i (= `wholeW1Delta`).

(A) For all n ≥ 2, 0 < m < n, d, P with gram P = I, and δ : Fin n → ℝ, with μ = β(δ):
  (A1) ∀ i: Σ_j (x_i·(x_jδ_j − μ))² ≤ Σ_j (x_i·x_j δ_j)²;
  (A2) c_V·Σ_iΣ_j (x_i·x_jδ_j)² = c_V·n²·Σ_j (1/n) lev_j δ_j², where
       c_V = (1/(pC·m·n))²·m(n−m)/(n(n−1)) (= `wholeW1VarianceCoefficient`);
  (A3) c_V·Σ_iΣ_j (x_i·x_jδ_j)² = 1/(pT pC n(n−1))·popMean(lev·δ²);
  (A4) 1/(pT pC n(n−1))·popMean(lev·δ²) ≤ kappa/(pT pC (n−1))·popMean(δ²).
(B) For all n > 0, d, P with gram P = I, and a: Σ_iΣ_j (x_i·x_j a_j)² =
    Σ_j a_j²·x_jᵀ(Σ_i x_i x_iᵀ)x_j = n·Σ_j a_j² lev_j.
(C) For all n > 0, d, m, P, K: popMean(yT²) ≤ K ∧ popMean(yC²) ≤ K ⇒ popMean(Δ²) ≤ 4K.
    (Δ = centered(yT − yC) because the x·N terms cancel, so this is popVar(yT−yC) ≤ 4K.)
(D) For all sequences d(n), m(n), P(n) ∈ Population n (d n) satisfying
    [∀ n ≥ 3: d ≤ n, 0 < m < n] ∧ [∃ K ≥ 0, ∀ n ≥ 3: popMean(yT²), popMean(yC²),
    popMean(x_k²) ≤ K ∀k] ∧ [eventually standardized] ∧ [∃ 0 < lo < hi < 1, ∀ n ≥ 3:
    lo < m/n < hi]:
    1/(pT pC n(n−1))·popMean(lev·Δ²) = O(kappa_n/n) and popMean(Δ²) = O(1) (Mathlib IsBigO
    at atTop).
(E) For all n ≥ 2, 0 < m < n, d, P standardized:
    Var_S(W(S)) ≤ c_V·Σ_iΣ_j K_ij² ≤ c_V·Σ_iΣ_j (x_i·x_jΔ_j)²,
    where W(S) = `wholeW1Star P m S` = (x̄_S − x̄_{S^c})·β(e^obs_S), e^obs_S,i = e_T,i if i ∈ S
    else e_C,i, and K_ij = `wholeW1Kernel` = x_i·(x_jΔ_j − β(Δ)). Under standardization
    W(S) = (1/(pC m n)) Σ_{i∈S}Σ_{j∈S} K_ij (by the T18 identities), a doubly-centred
    quadratic form, and c_V = (1/(pC m n))²·m(n−m)/(n(n−1)).
(F) For all sequences d, m, P with `wholeW1Standing` (identical to the hypothesis of (D),
    d = 0 allowed): W_n = O_p(√(kappa_n·d_n/n)), where O_p is `stochasticO`:
    ∀ ε > 0 ∃ M > 0 ∃ n₀ ∀ n ≥ n₀, P_S(|W_n(S)| > M·√(kappa_n d_n/n)) < ε (probability over
    uniform m(n)-subsets).

Remarks. (A1) is "centering reduces the sum of squares" (Σ_j x_i·x_jδ_j = n x_i·μ), true
without gram = I; (A4) only uses lev_j ≤ n·kappa (true without gram = I); (A2),(A3),(B)
use gram = I. The O(kappa/n) in (D) does not need standardization. Rate in (F):
E[W] = Σ lev_iΔ_i/(n(n−1)) ≲ √(kappa d/n) and Var W = O(kappa/n), which explains the
√(kappa d/n) rate (weaker than √(kappa/n) for d ≥ 1; both 0 when d = 0, and W ≡ 0 when d = 0).

Junk values: kappa uses sSup of a finite nonempty set for n ≥ 1 (genuine max); n = 0 (sSup ∅
= 0) only appears inside asymptotic statements. `Real.sqrt` is applied to kappa·d/n ≥ 0.
pC·m·n = m(n−m) > 0 and pT pC > 0 under the hypotheses; n−1 ≥ 1. In (C), m is
unconstrained (pT, pC may be junk-ish, e.g. m > n gives pC < 0), but they cancel in Δ, so
nothing depends on them. In (D)/(F) nothing is assumed for n < 3 (pT etc. may be junk there),
which is immaterial for O/O_p statements. The `let`s are plain abbreviations.
Hypotheses satisfiable: e.g. d = 0 populations, or the standardized population
x = (1, −1) for n = 2.

---

## SAP.P005b.T18 (`T18Statement`, Defs/Part4:59)

Two universally quantified parts.

(G) For all n > 0, 0 < m < n, d, P (no standardization), S with |S| = m, and arbitrary
    e_T, e_C : Fin n → ℝ satisfying the weighted normal equation pT·β(e_T) + pC·β(e_C) = 0:
    with A = β(e_T − e_C), B = β(e_C), U_k = (Σ_{i∈S} x_ik(e_T,i − e_C,i))/n,
    (G1) B = −pT·A; (G2) U + B = ( Σ_{i∈S} (x_ik Δ_i + (1/pT)·B_k) )/n;
    (G3) U + B = ( Σ_{i∈S} (x_ik Δ_i − A_k) )/n; (G4) (1/pC)·x̄_S·(U + B) =
    (1/pC)·x̄_S·((Σ_{i∈S}(x_ikΔ_i − A_k))/n).
(H) For all n > 0, 0 < m < n, d, P standardized, S with |S| = m, and e_T, e_C the common
    residuals: (H1) x̄_S − x̄_{S^c} = (1/pC)·x̄_S; (H2) pT·β(e_T) + pC·β(e_C) = 0;
    (H3) residualStarTerm P S e_T e_C = (x̄_S − x̄_{S^c})·β(e^obs_S) = (1/pC)·x̄_S·(U + B).

All hand-checked: (G1) from pT + pC = 1 and linearity; (G2) |S|·(1/pT)·B/n = B since
pT = m/n; (G3) from (G1); (G4) congruence of (G3); (H1) from x̄ = 0; (H2) β(e_y) =
β(y) − N under standardization; (H3) splits β(e^obs) over S and S^c.

Junk values: none affecting meaning (pT, pC ∈ (0,1); n > 0; |S| = m > 0, |S^c| > 0, so
x̄_S, x̄_{S^c} genuine). Hypotheses satisfiable (e.g. e_T = e_C = 0; any standardized P).

---

## SAP.P005b.T19 (`T19Statement`, Defs/Part5:13) — a negation

T19Statement = ¬ ( ∀ n ≥ 4, ∀ 0 < m < n, ∀ arm t ∈ {treated, control}, ∀ a, b : Fin n → ℝ
(arbitrary, NOT required to be centered):
   (i)  E[sampleCov_{arm_t(S)}(a,b)] = (n_t − 1)n/(n_t(n−1))·popCov(a,b), and
   (ii) Var[sampleCov_{arm_t(S)}(a,b)] ≤ covarianceBound(n_t; a, b) ),
where arm_t(S) = S (treated) or S^c (control), n_t = m or n − m, and
covarianceBound(n_t; a, b) = 2(n−n_t)/(n_t(n−1))·popMean((ab − popMean(ab))²)
                         + 2(n−n_t)n/(n_t³(n−1))·popMean(a²)·popMean(b²).

So it asserts: there exist n ≥ 4, 0 < m < n, an arm and vectors a, b for which (i) or (ii)
fails. (i) is in fact always true (E[mean_S(ab)] = popMean(ab), Cov(ā_S, b̄_S) =
(n−n_t)/(n_t(n−1))·popCov), so the refutation must come from (ii).

Key observation (numerical probe, $TMPDIR scripts, exhaustive enumeration of subsets):
sampleCov and popCov are shift-invariant, but covarianceBound is not (it uses the
uncentered second moments popMean(a²), popMean(b²) and popVar(ab)). Hill-climbing over
centered a, b (n = 4..8, all m) gave max Var/bound ≈ 0.69 < 1, i.e. no centered
counterexample was found; with uncentered a, b the ratio reaches > 3 (e.g. n = 7, m = 6).
Hence the negation is (apparently) witnessed only by uncentered vectors. Whether this is a
genuine refutation therefore depends on whether the source lemma assumes centered vectors
(Σa = Σb = 0) — to be checked at step 2.

Junk values: none. C(n,m) ≥ 1; arm sizes are in [1, n−1] (ℕ subtraction n − m is exact as
m < n); denominators n_t, n−1, n_t³ nonzero. The negation is not vacuous: it requires an
actual failing instance (the theorem is proved, so one exists).
