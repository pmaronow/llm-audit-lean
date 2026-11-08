import SAP.P046.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- Both asymptotic distributions and their efficiency comparison. -/
def EfficiencyComparison (M : Study) (F : ∀ n, CrossFit n) (gstar : ℝ → ℝ) : Prop :=
  NormalLimit M (fun n => adjusted M (F n)) (V M gstar) ∧
  NormalLimit M (fun _ => ht M) (V M (fun _ => 0)) ∧ V M gstar ≤ V M (fun _ => 0)

/-- Corrected weighted fitting theorem, and its restricted direct variant. -/
def T5Statement : Prop :=
  (∀ (M : Study), ValidStudy M →
    ∀ (d : ℕ) (family : (Fin d → ℝ) → ℝ → ℝ) (F : ∀ n, CrossFit n), Balanced F →
    (∀ theta, MemLp (fun o => family theta (W o)) 2 M.law) →
    ZeroBenchmark M (Set.range family) →
    (∀ n j, ∀ᵐ a ∂sampleLaw M n, ∃ theta,
      (F n).g j a = family theta ∧ ∀ eta,
      empiricalRisk M (Finset.univ.filter (fun i => (F n).fold i ≠ j)) a (family theta) ≤
      empiricalRisk M (Finset.univ.filter (fun i => (F n).fold i ≠ j)) a (family eta)) →
    ∀ (gstar : ℝ → ℝ), gstar ∈ Set.range family →
    (∀ theta, risk M gstar ≤ risk M (family theta)) →
    (∀ j, L2InProbability M F j gstar) → EfficiencyComparison M F gstar) ∧
  (∀ (M : Study), ValidStudy M →
    ∀ (F : ∀ n, CrossFit n), Balanced F → ∀ (gstar : ℝ → ℝ),
    MemLp (fun o => gstar (W o)) 2 M.law →
    (∀ j, L2InProbability M F j gstar) →
    (∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) →
    risk M gstar ≤ risk M (fun _ => 0) → EfficiencyComparison M F gstar)

/-- Negation of the universally quantified printed population-tail assertion. -/
def T6Statement : Prop :=
  ¬ ∀ (M : Study), ValidStudy M → ∀ (n : ℕ), 0 < n → ∀ (alpha : ℝ),
    0 < alpha ∧ alpha < 1 → tailProb M (ht M) (printedRadius M alpha (n := n)) ≤ alpha

/-- Unbiasedness, common-positivity uniform root-n consistency, and the stated CLT. -/
def T7Statement : Prop :=
  (∀ delta : ℝ, 0 < delta → UniformRootN delta) ∧
  ∀ (M : Study), ValidStudy M →
    (∀ n : ℕ, 0 < n →
      Integrable (ht M (n := n)) (sampleLaw M n) ∧
      (∫ a, ht M a ∂sampleLaw M n) = mu M) ∧
    variance (fun o => htTerm (M.pi (W o)) (X o) (Y o)) M.law =
      (∫ o, M.m (W o) / M.pi (W o) ∂M.law) - (mu M)^2 ∧
    NormalLimit M (fun _ => ht M)
      ((∫ o, M.m (W o) / M.pi (W o) ∂M.law) - (mu M)^2)

/-- Integrable evaluated cross-fitted predictions give finite-sample unbiasedness. -/
def T8Statement : Prop := ∀ (M : Study), ValidStudy M → ∀ (n : ℕ), 0 < n →
  ∀ (F : CrossFit n),
    (∀ i, Integrable (fun a => F.g (F.fold i) a (W (a i))) (sampleLaw M n)) →
    (∫ a, adjusted M F a ∂sampleLaw M n) = mu M

/-- Root-n consistency and the Hahn-variance normal limit for square-integrable fits. -/
def T9Statement : Prop :=
  (∀ (M : Study), ValidStudy M → ∀ (F : ∀ n, CrossFit n), Balanced F →
    ∀ (g : Bool → ℝ → ℝ), (∀ j, MemLp (fun o => g j (W o)) 2 M.law) →
    (∀ j, L2InMeanSquare M F j (g j)) →
    (∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) →
    RootN M (fun n => adjusted M (F n))) ∧
  (∀ (M : Study), ValidStudy M → ∀ (F : ∀ n, CrossFit n), Balanced F →
    (∀ j, L2InProbability M F j M.m) →
    (∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law) →
    NormalLimit M (fun n => adjusted M (F n)) (hahnBound M))

/-- Estimators receive only observed triples and never a population's propensity. -/
abbrev ObservationalEstimator := ∀ n : ℕ, (Fin n → Observed) → ℝ

/-- No observed-data estimator is uniformly consistent over all valid studies. -/
def T10Statement : Prop := ∀ (est : ObservationalEstimator), (∀ n, Measurable (est n)) →
  ∃ eps > 0, ∃ c > 0, ∀ N : ℕ, ∃ n ≥ N, 0 < n ∧ ∃ M : Study,
    ValidStudy M ∧ (sampleLaw M n
      {a | eps < |est n (fun i => observe (a i)) - mu M|}).toReal ≥ c

end
end SAP.P046
