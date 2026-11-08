import AronowAudit.P001.Wave1.MarSelectionBlueprint

/-!
# Blueprint: MAR and the propensity score, paper support (P001-T112)

Record 13 of group P001a: P001-T112 / held `AronowAudit.P001.mar_balancing_score`;
resolution `repair_and_prove`. Theorem 6.1.12 (pp. 217-218, proof p. 218). The held draft
(:4312, sorry) allows a constant response indicator and pointwise bounds. The repair
(mapper's `mar_propensity_paper_support_balance`) restores `Supp[R] = {0,1}` (`hR0`, `hR1`),
uses a.e. binary values and a.e. positivity, and keeps all three bullets:
balance `R ⊥ X | p(X)`, `Y ⊥ R | p(X)`, and `Pr[R = 1 | p(X)] > ε`, the last as
`IsCEF μ (p ∘ X) R id` (the score is its own response probability) together with
`ε < p(X)` a.e. No integrability of `Y` is assumed (only indicators of `Y` occur).

Write `G = σ(X)`, `S = p(X)`, `H = σ(S) ≤ G`, `r_A(s) = 1_{0∈A}(1-s) + 1_{1∈A}s`.
Nodes: shared `MarSelection.N1` (unit-interval bound); record nodes `MarBalance.N1` (binary
event CEF), `MarBalance.N2` (balance and self-CEF), `MarBalance.N3` (MAR reduction). Writers prove `theorem nk_proof : Nk` in
`AronowAudit/P001/Wave1/MarBalance/Nk.lean`.
-/

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1.MarBalance

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The frozen statement the record is resolved by (mapper's
`AronowAudit.P001.Wave1.mar_propensity_paper_support_balance`). -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ), Measurable Y → Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} →
    ∀ (p : (Fin K → ℝ) → ℝ) (hp : IsCEF μ X R p), CI μ X hX Y R →
    ∀ (ε : ℝ), 0 < ε → (∀ᵐ ω ∂μ, ε < p (X ω)) →
    CI μ (p ∘ X) (hp.1.comp hX) R X ∧ CI μ (p ∘ X) (hp.1.comp hX) Y R ∧
      IsCEF μ (p ∘ X) R id ∧ (∀ᵐ ω ∂μ, ε < p (X ω))

open Classical in
/-- **Node N1** (paper proof, record 13, first paragraph: "Since R is a.e. binary, for every
Borel A⊆ℝ define r_A(s)=1_{0∈A}(1-s)+1_{1∈A}s. Then E[1_{R∈A}|G]=r_A(S)"). Binary event
CEF from the propensity.
Suggested route: `(if R ω ∈ A then 1 else 0) = r_A(R ω)` a.e. (binary), and `r_A` is affine
in `R`; `condExp_add`, `condExp_smul`/`condExp_const_mul`, `condExp_const`, `condExp_sub`;
`μ[R|G] = p ∘ X` a.e. from the proved `isCEF_condExp` (:3337). -/
def N1 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (R : Ω → ℝ) (p : E → ℝ), Measurable X →
    Measurable R → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → IsCEF μ X R p →
    ∀ A : Set ℝ, MeasurableSet A →
      μ[(fun ω => if R ω ∈ A then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]
        =ᵐ[μ] fun ω => (if (0 : ℝ) ∈ A then 1 - p (X ω) else 0) +
          (if (1 : ℝ) ∈ A then p (X ω) else 0)

/-- **Node N2** (paper proof, record 13, second and fourth paragraphs: "For a measurable
covariate set B ... tower and pullout give E[1_{R∈A}1_{X∈B}|H]=r_A(S)E[1_{X∈B}|H]. Another
tower application gives E[1_{R∈A}|H]=r_A(S) ... Finally E[R|H]=E[E[R|G]|H]=E[S|H]=S ...
proves IsCEF μ S R id"). Balance given the score and the score's self-CEF, under `N1` and
`N1`.
Suggested route: `H ≤ G` from `MeasurableSpace.comap_comp` and `hp.1.comap_le`;
`condExp_condExp_of_le`; `condExp_mul_of_stronglyMeasurable_left` with the
`H`-measurable bounded `r_A(p(X))`; `condExp_of_stronglyMeasurable` for `r_A(p(X))`.
`IsCEF μ (p∘X) R id`: every `(p∘X)⁻¹ A` is `X⁻¹ (p⁻¹ A)`, so `hp.2.2.2 (p⁻¹ A)` applies. -/
def N2 : Prop :=
  N1.{u, v} → MarSelection.N1.{u} →
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X) (R : Ω → ℝ) (p : E → ℝ)
    (hp : IsCEF μ X R p), Measurable R → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    CI μ (p ∘ X) (hp.1.comp hX) R X ∧ IsCEF μ (p ∘ X) R id

/-- **Node N3** (paper proof, record 13, third paragraph: "For a Borel outcome set C, MAR
gives E[1_{Y∈C}1_{R∈A}|G]=E[1_{Y∈C}|G]r_A(S). Conditioning this identity on H gives
E[1_{Y∈C}1_{R∈A}|H]=r_A(S)E[1_{Y∈C}|H], again by tower and H-pullout. Combine with
E[1_{R∈A}|H]=r_A(S) to obtain CI of Y and R given S"). MAR reduces to the score, under `N1`
and `N1`. Same route as `N2`, starting from the `CI μ X hX Y R` factorization. -/
def N3 : Prop :=
  N1.{u, v} → MarSelection.N1.{u} →
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X) (Y R : Ω → ℝ) (p : E → ℝ)
    (hp : IsCEF μ X R p), Measurable Y → Measurable R → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    CI μ X hX Y R → CI μ (p ∘ X) (hp.1.comp hX) Y R

/-- The nodes suffice: `N2` gives the first and third bullets, `N3` the second, and the
positivity is the hypothesis. -/
theorem assemble (h0 : MarSelection.N1.{u}) (h1 : N1.{u, 0}) (h2 : N2.{u, 0})
    (h3 : N3.{u, 0}) : Target.{u} := by
  intro Ω _ K μ _ X hX Y R hY hR hbin _ _ p hp hmar ε _ hpos
  obtain ⟨hbal, hself⟩ := h2 h1 h0 μ X hX R p hp hR hbin
  exact ⟨hbal, h3 h1 h0 μ X hX Y R p hp hY hR hbin hmar, hself, hpos⟩

end

end AronowAudit.P001.Wave1.MarBalance
