import SAP.P023.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P023
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def PrintedPropositionTwo : Prop :=
    ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (g f : ℝ → ℝ) (α : ℝ)
    (hprob : ProbabilityLaw ν) (hsupport : MarginSupport (marginLaw ν))
    (hsq : Integrable (fun z => z.2^2) ν)
    (hg : ContinuousOn g (Set.Ico (-1) 0)) (hf : ContinuousOn f (Set.Icc 0 1))
    (hleft : Tendsto g (nhdsWithin 0 (Set.Iio 0)) (nhds α))
    (hmean : ConditionalMean ν (appendixMean g f)) (hiid : IIDSample P ν sample)
    (hpd : ∀ J, 1 ≤ J → MomentPositiveDefinite (marginLaw ν) J)
    (k : ℕ → ℝ) (hkpos : ∀ N, 0 < k N) (hk0 : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N:ℝ)*k N) atTop atTop)
    (hsup : ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ a b : ℝ, -k₀ ≤ a → a < b → b ≤ k₀ →
      0 < marginLaw ν (Set.Ioo a b))
    (hRD : UsualRDRegularity ν (appendixMean g f) k),
    ConvergesInProbability P (sampleRD sample k) (f 0 - α) ∧
    ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, 1 ≤ J →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N J ω - sampleRD sample k N ω)
        (populationCoefficient (marginLaw ν) J (appendixMean g f) - (f 0 - α)) ∧
      |populationCoefficient (marginLaw ν) J (appendixMean g f) - (f 0 - α)| < ε

end
end SAP.P023
