import SAP.P002a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P002a
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

def T4Unadjusted : Prop :=
  ∀ (α : ℝ) (hα : 0 < α ∧ α < 1),
  (∀ n, 2 ≤ n → ∀ β, Theta (degenerateModel n β) 0 (1/4) (1/2) ∧
      late (degenerateModel n β) = β) ∧
    (∀ n, 2 ≤ n → ∀ P : Population n, Theta P 0 (1/4) (1/2) →
      coverage P (late P) α = 1) ∧
    (∀ n, 2 ≤ n → infCoverageTheta n 0 (1/4) (1/2) α = 1) ∧
    Tendsto (fun n => infCoverageTheta n 0 (1/4) (1/2) α) atTop (nhds 1) ∧
    ¬Tendsto (fun n => infCoverageTheta n 0 (1/4) (1/2) α) atTop
      (nhds (ENNReal.ofReal (1-α)))

def T4Adjusted : Prop :=
  ∀ (α : ℝ) (hα : 0 < α ∧ α < 1),
  (∀ n, 2 ≤ n → ∀ β, Xi (degenerateCovModel n β) 0 (1/4) 4 (1/2) (1/4) ∧
      late (degenerateCovModel n β).pop = β) ∧
    (∀ n, 2 ≤ n → ∀ P : CovPopulation n 1, Xi P 0 (1/4) 4 (1/2) (1/4) →
      max 0 (1-1548/((n : ℝ)-1)) ≤ adjustedCoverage P (late P.pop) α) ∧
    Tendsto (fun n => infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α) atTop (nhds 1) ∧
    ¬Tendsto (fun n => infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α) atTop
      (nhds (ENNReal.ofReal (1-α)))

def T4Collapse : Prop :=
  ∀ {n : ℕ} (q : Fin n → ℝ) (hn : 2 ≤ n)
    (hq : fourthNorm q ≤ (1/2)*Real.sqrt ((∑ i, q i^2)/((n : ℝ)-1))),
  ∀ i, q i = 0

def T4Constant : Prop :=
  ∀ {n : ℕ} (P : Population n)
    (hP : Theta P 0 (1/4) (1/2)),
  ∃ c : ℝ, ∀ a i, w P a (late P) i=c

def T4Statement : Prop := T4Collapse ∧ T4Constant ∧ T4Unadjusted ∧ T4Adjusted

def T5Raw : Prop :=
  ∀ (δ r A α : ℝ) (hδ : δ < 1)
    (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A) (hα : 0 < α ∧ α < 1)
    (_hclasses : NeBot (atTop ⊓ Filter.principal (thetaSizes δ r A))),
  ENNReal.ofReal (1-α) ≤ Filter.liminf (fun n => infCoverageTheta n δ r A α)
      (atTop ⊓ Filter.principal {n | ∃ P : Population n, Theta P δ r A})

def T5Adjusted : Prop :=
  ∀ (k : ℕ) (δ e A B r α : ℝ) (hk : 0 < k) (hδ : δ < 1)
    (he : 0 < e) (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1/2)
    (hα : 0 < α ∧ α < 1)
    (_hclasses : NeBot (atTop ⊓ Filter.principal (xiSizes k δ e A B r))),
  ENNReal.ofReal (1-α) ≤ Filter.liminf (fun n => infCoverageXi n k δ e A B r α)
      (atTop ⊓ Filter.principal {n | ∃ P : CovPopulation n k, Xi P δ e A B r})

def T5Sharpness : Prop :=
  ∀ (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ n, Population (sizes n)) (δ r A α : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A)
    (hα : 0 < α ∧ α < 1) (hP : ∀ n, Theta (P n) δ r A)
    (hconstant : ∀ n, ∃ β, ∀ i, (P n).y i true=(P n).y i false+β)
    (hnondegenerate : ∀ n, 0 < popVar (fun i => (P n).y i false)),
  Tendsto (fun n => ENNReal.ofReal (coverage (P n) (late (P n)) α))
      atTop (nhds (ENNReal.ofReal (1-α))) ∧
    Filter.liminf (fun N => infCoverageTheta N δ r A α)
      (atTop ⊓ Filter.principal {N | ∃ Q : Population N, Theta Q δ r A}) =
        ENNReal.ofReal (1-α)

def T5Statement : Prop := T5Raw ∧ T5Adjusted ∧ T5Sharpness

def T6Statement : Prop :=
  (∀ m, 4 ≤ m →
      let P := nearSingularModel m
      Xi P 0 (1/4) 16 5 (1/3) ∧ late P.pop = 0 ∧
      (∀ S ∈ assignments P.pop, (gram P.x S).det ≠ 0 ∧ (gram P.x Sᶜ).det ≠ 0) ∧
      (∀ S ∈ assignments P.pop,
        let q := observedW P.pop 0 S
        designVariance P.pop (adjustedTau P q) ≥
          8*(2 : ℝ)^(2*(2*m)^2)/(2 : ℝ)^(2*m) ∧
        (∀ T ∈ assignments P.pop, 0 ≤ adjustedSigma2 P q T ∧
          adjustedSigma2 P q T < 5/((2*m : ℕ) : ℝ)) ∧
        probability P.pop (fun T => |adjustedSigma2 P q T /
          designVariance P.pop (adjustedTau P q)-1| ≥ 1/2) = 1)) ∧
    (∀ n, 9 ≤ n → Odd n → Xi (oddNearModel n) 0 (1/4) 16 5 (1/3)) ∧
    Tendsto (fun j =>
      let P := nearSingularModel (j+4)
      probability P.pop (fun T => |adjustedSigma2 P (fun i => P.pop.y i false) T /
        designVariance P.pop (adjustedTau P (fun i => P.pop.y i false))-1| ≥ 1/2))
      atTop (nhds 1)

end
end SAP.P002a
