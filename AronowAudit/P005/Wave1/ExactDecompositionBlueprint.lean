import AronowAudit.P005.P005_Formalization

/-!
# Blueprint: P005-T20 (association) / P005-T24 content, `interacted_exact_decomposition`

Wave 1, group P005-P006-P017-P023-P046-P047. Resolution `prove_as_is` (mapper, accepted by
both referees with no fixes).

The frozen declaration `AronowAudit.P005.interacted_exact_decomposition` (P005_Formalization.lean,
line 801) states the *valid* exact part of Theorem 4.1 (Econometrica p. 1509): the two
assignmentwise slope decompositions, the bias expression, the two first-component (`ν₁`)
expectations and their difference. It does not contain the false third-component identity
(already refuted by `ConfidenceFollowup02.printed_interacted_third_bias_refuted`) nor the
asymptotic expansion (refuted in `InteractedExpansionBlueprint`). `Target` is its type,
unchanged (checked by `rfl` below); the completion is proved under the fresh name
`AronowAudit.P005.Wave1.interacted_exact_decomposition_completion`.

Registry note for the orchestrator: this record's T20 association is a provenance error; the
proved type is T24 content. Do not transfer credit between this completion and the T20 sign
refutation.

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P005/Wave1/ExactDecomposition/Nk.lean`.
`Sk` is the mathematical statement of node k; `Nk` is `Sk` with, as hypotheses, the statements
of the nodes it may use (so all nodes can be written in parallel).
Do not use any declaration of `P005_Formalization.lean` whose proof is `sorry` (in particular
`interacted_exact_decomposition`, `corrected_covariance_lemma`, `interacted_exact_unbiasedness`).
The proved helpers `arm_slope_decomposition`, `armN_decomposition`, `mean_unbiased`,
`indicator_expectation`, `inclusion_count`, `expectation_sum`, `expectation_mul`,
`expectation_congr`, `indicator_sum`, `mean_sub`, `mean_mul`, `mean_const`, `mean_add`,
`complement_x_mean_identity` are available.

Paper proof: map-P005-P006-P017-P023-P046-P047 REPORT.md, §1 "Paper proof", steps 1–4.
-/

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.ExactDecomposition

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

/-! ## Frozen target -/

/-- **Target (P005-T24 content of the T20 record).** The exact type of the frozen declaration
`AronowAudit.P005.interacted_exact_decomposition` (Theorem 4.1, p. 1509: slope decompositions,
bias expression, first-component identities). -/
def Target : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n → standardized P →
    interactedRegular P m →
    (∀ S ∈ design n m,
      armBetaHat P S P.yT = populationSlope P P.yT + armNu1 P S P.yT + armNu2 P S P.yT +
          armNu3 P S P.yT ∧
      armBetaHat P (control S) P.yC = populationSlope P P.yC + armNu1 P (control S) P.yC +
        armNu2 P (control S) P.yC + armNu3 P (control S) P.yC) ∧
    expectation m (fun S => interactedATE P S - ate P) =
      expectation m (fun S => dot (xMean P (control S))
        (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT + armNu2 P S P.yT +
        armNu3 P S P.yT)) ∧
    expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
      ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC -
        ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT

/-! ## Node statements -/

/-- **Statement S1** (node N1) (paper proof §1 step 0, "Complementation is an involutive bijection from the
t-subsets to the c-subsets, so E_t[F(Sᶜ)]=E_c[F(S)]"). Prove with `Finset.sum_nbij'` (or
`Finset.sum_bij`) on `powersetCard`, using `Finset.card_sdiff`, `Finset.sdiff_sdiff_right_self`
/ `compl_compl` and `Nat.choose_symm`. -/
def S1 : Prop :=
  ∀ (n m : ℕ), m ≤ n → ∀ F : Finset (Fin n) → ℝ,
    expectation m (fun S => F (control S)) = expectation (n - m) F

/-- **Statement S2** (node N2) (paper proof §1 step 1, "For i≠j and t≥2, counting subsets containing {i,j}
gives E_t I_iI_j=t(t-1)/(N(N-1)). For t=1, I_iI_j=0, and the same formula is zero"). Real
subtraction; the case `m = 1` must be covered. Use `inclusion_count` with `R = {i, j}`
(when `2 ≤ m`) and `Nat.choose` identities. -/
def S2 : Prop :=
  ∀ (n m : ℕ), 2 ≤ n → 0 < m → m ≤ n → ∀ i j : Fin n, i ≠ j →
    expectation m (fun S => indicator S i * indicator S j) =
      (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))

/-- **Statement S3** (node N3) (paper proof §1 step 1, "E_t[ā_S b̄_S] = ā b̄ + (N-t)/(t(N-1)) [overline{ab}-ā b̄]",
including `t = 1`). Expand `mean S a * mean S b` as a double sum of indicator products, split
the diagonal, use `indicator_expectation` and S2. -/
def S3 : Prop :=
  ∀ (n m : ℕ), 2 ≤ n → 0 < m → m ≤ n → ∀ a b : Fin n → ℝ,
    expectation m (fun S => mean S a * mean S b) =
      popMean a * popMean b + ((n : ℝ) - m) / ((m : ℝ) * ((n : ℝ) - 1)) * popCov a b

/-- **Statement S4** (node N4) (paper proof §1 step 4, treated arm: "For coordinate k set a_i=x_ik and
b_i=yT_i* x_ik ... Sum over k ... overline{h y*}=leverageCov"). Only centered covariates are
needed (no Gram normalisation), and `y` is arbitrary. -/
def S4 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m ≤ n → xMean P univ = 0 →
    ∀ y : Fin n → ℝ,
      expectation m (fun S => dot (xMean P S) (armNu1 P S y)) =
        ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P y

/-- **Statement S5** (node N5) (paper proof §1 step 4, control arm: "Repeat the same computation for a
c-subset and yC, then use the complement bijection, obtaining t/[c(N-1)] leverageCov(P,yC)").
Apply S1, then S4 at size `n - m` (cast with `Nat.cast_sub`). -/
def S5 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n → xMean P univ = 0 →
    ∀ y : Fin n → ℝ,
      expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) y)) =
        (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P y

/-- **Statement S6** (node N6) (paper proof §1 step 2, "βhat_A=β+ν1_A+ν2_A+ν3_A. Apply this separately to
(A,y)=(S,yT) and (Sᶜ,yC)"): the first conjunct of `Target`. Both arms are nonempty
(`card S = m > 0`, `card (control S) = n - m > 0`); apply the proved `arm_slope_decomposition`
with the two determinant facts from `interactedRegular`. -/
def S6 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n → standardized P →
    interactedRegular P m →
    ∀ S ∈ design n m,
      armBetaHat P S P.yT = populationSlope P P.yT + armNu1 P S P.yT + armNu2 P S P.yT +
          armNu3 P S P.yT ∧
      armBetaHat P (control S) P.yC = populationSlope P P.yC + armNu1 P (control S) P.yC +
        armNu2 P (control S) P.yC + armNu3 P (control S) P.yC

/-- **Statement S7** (node N7) (paper proof §1 step 3, "Substitute those two identities into the definition of
interactedATE ... Each of the first four terms has expectation zero"): the bias conjunct of
`Target`. Rewrite on the design with `expectation_congr` and S6; the outcome-mean terms vanish
by `mean_unbiased` (and S1 for controls); the population-slope terms vanish because each
`xMean` coordinate is unbiased for `0`. -/
def S7 : Prop :=
  ∀ {n d m : ℕ} (P : Population n d), 2 ≤ n → 0 < m → m < n → standardized P →
    interactedRegular P m →
    expectation m (fun S => interactedATE P S - ate P) =
      expectation m (fun S => dot (xMean P (control S))
        (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT + armNu2 P S P.yT +
        armNu3 P S P.yT))

/-! ## Nodes (`Sk` is the statement; `Nk` adds, as hypotheses, the statements it may use) -/

/-- Node N1 = S1. -/
def N1 : Prop := S1
/-- Node N2 = S2. -/
def N2 : Prop := S2
/-- Node N3: may use S2. -/
def N3 : Prop := S2 → S3
/-- Node N4: may use S3. -/
def N4 : Prop := S3 → S4
/-- Node N5: may use S1 and S4. -/
def N5 : Prop := S1 → S4 → S5
/-- Node N6 = S6. -/
def N6 : Prop := S6
/-- Node N7: may use S1 and S6. -/
def N7 : Prop := S1 → S6 → S7

/-! ## Assembly -/

/-- **Assembly.** The nodes prove the frozen type. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7) :
    Target := by
  have s4 : S4 := h4 (h3 h2)
  have s5 : S5 := h5 h1 s4
  have s7 : S7 := h7 h1 h6
  intro n d m P hn hm hmn hP hreg
  have hT := s4 P hn hm hmn.le hP.1 P.yT
  have hC := s5 P hn hm hmn hP.1 P.yC
  refine ⟨h6 P hn hm hmn hP hreg, s7 P hn hm hmn hP hreg, hT, hC, ?_⟩
  rw [hT, hC]

/-- Fidelity check: `Target` is literally the type of the frozen declaration
`AronowAudit.P005.interacted_exact_decomposition` (only its type is read; its `sorry` proof is
never used). -/
example : Target = type_of% @AronowAudit.P005.interacted_exact_decomposition := rfl

/-- Nonvacuity: the existing six-unit witness `signPopulation` (n = 6, d = 1, m = 2) satisfies
every hypothesis; this is already proved inside `interacted_sign_counterexample`
(its first two conjuncts are `standardized signPopulation` and `interactedRegular signPopulation 2`). -/
example : standardized signPopulation ∧ interactedRegular signPopulation 2 :=
  ⟨interacted_sign_counterexample.1, interacted_sign_counterexample.2.1⟩

end

end AronowAudit.P005.Wave1.ExactDecomposition
