import AronowAudit.P017.Wave1.PropositionOneBlueprint
import AronowAudit.P017.Wave1.PropositionOne.N1
import AronowAudit.P017.Wave1.PropositionOne.N2
import AronowAudit.P017.Wave1.PropositionOne.N3
import AronowAudit.P017.Wave1.PropositionOne.N4
import AronowAudit.P017.Wave1.PropositionOne.N5
import AronowAudit.P017.Wave1.PropositionOne.N6
import AronowAudit.P017.Wave1.PropositionOne.N7

set_option autoImplicit false

namespace AronowAudit.P017.Wave1

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem proposition1_printed_refuted :
    ¬ ∀ {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
      (_hτm : Measurable τ) (_hτi : Integrable τ G) (P : Measure Ξ)
      [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
      (_hh : RootNNormal P hat (populationMean G τ)),
      ∀ n, 1 ≤ n → ∀ ω, Representable G τ
        (clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω)) :=
  PropositionOne.assemble PropositionOne.n1_proof PropositionOne.n2_proof
    PropositionOne.n3_proof PropositionOne.n4_proof PropositionOne.n5_proof
    PropositionOne.n6_proof PropositionOne.n7_proof

example : AronowAudit.P017.Wave1.PropositionOne.Target := proposition1_printed_refuted

end

end AronowAudit.P017.Wave1
