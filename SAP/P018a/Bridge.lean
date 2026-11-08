import SAP.P018a.Defs
import AronowAudit.P018.P018_Audit
import AronowAudit.P018.Wave1.Gap.GP0182B2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.Bridge
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

/-- Preserve the unit law and both data kernels. -/
def toKernel {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) : AronowAudit.P018.Kernel U k := ⟨K.μ, K.X, K.Y⟩

/-- Preserve the record counts, unit law, and record kernels. -/
def toRepeated {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) : AronowAudit.P018.RepeatedKernel U k :=
  ⟨R.μ, R.T, R.X, R.Y⟩

theorem dyads_agree : dyads = AronowAudit.P018.dyads := rfl

theorem endpoints_agree {N : ℕ} (d : Dyad N) :
    firstUnit d = AronowAudit.P018.firstUnit d ∧
    secondUnit d = AronowAudit.P018.secondUnit d := ⟨rfl, rfl⟩

theorem kernel_assumptions_agree {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) : Standing K ↔ AronowAudit.P018.Standing (toKernel K) := Iff.rfl

theorem kernel_sample_agrees {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) :
    unitSampleLaw K N = AronowAudit.P018.unitSampleLaw (toKernel K) N ∧
    design K ω = AronowAudit.P018.design (toKernel K) ω ∧
    response K ω = AronowAudit.P018.response (toKernel K) ω ∧
    epsilon K ω = AronowAudit.P018.epsilon (toKernel K) ω := ⟨rfl, rfl, rfl, rfl⟩

theorem kernel_target_agrees {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) :
    trueTarget K = AronowAudit.P018.trueTarget (toKernel K) ∧
    limitingTarget K = AronowAudit.P018.limitingTarget (toKernel K) := ⟨rfl, rfl⟩

theorem conditional_quantities_agree {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) :
    @conditionalResidualMean U _ k N K =
      @AronowAudit.P018.conditionalResidualMean U _ k N (toKernel K) ∧
    @conditionalResidualCov U _ k N K =
      @AronowAudit.P018.conditionalResidualCov U _ k N (toKernel K) := ⟨rfl, rfl⟩

theorem repeated_assumptions_agree {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) :
    RepeatedStanding R ↔ AronowAudit.P018.RepeatedStanding (toRepeated R) := Iff.rfl

theorem repeated_target_agrees {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) :
    repeatedTarget R = AronowAudit.P018.repeatedTarget (toRepeated R) := rfl

theorem singleRecord_agrees {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) : toRepeated (singleRecord K) =
      AronowAudit.P018.singleRecord (toKernel K) := rfl

/-- The remaining finite sums differ only by a singleton record index. -/
theorem singleWeightedGram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (ω : Fin N → U) :
    recordWeightedGram (singleRecord K) (fun d _ => w d) ω = weightedGram K w ω := by
  change (∑ d, ∑ _ : Fin 1, w d • outer (design K ω d) (design K ω d)) = _
  simp only [Fin.sum_univ_one]
  rfl

theorem singleWeightedXY {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (ω : Fin N → U) :
    recordWeightedXY (singleRecord K) (fun d _ => w d) ω =
      ∑ d, score (design K ω d) (w d * response K ω d) := by
  change (∑ d, ∑ _ : Fin 1, score (design K ω d) (w d * response K ω d)) = _
  simp only [Fin.sum_univ_one]

theorem singleWeightedOLS {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (ω : Fin N → U) :
    recordWeightedOLS (singleRecord K) (fun d _ => w d) ω = weightedOLS K w ω := by
  simp only [recordWeightedOLS, singleWeightedGram, singleWeightedXY, weightedOLS]

theorem singleWeightedBeta {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) :
    recordWeightedBeta (singleRecord K) (fun d _ => w d) = weightedPopulationBeta K w := by
  unfold recordWeightedBeta weightedPopulationBeta
  rw [show recordWeightedGram (singleRecord K) (fun d _ => w d) = weightedGram K w
    from funext (singleWeightedGram K w)]
  rw [show recordWeightedXY (singleRecord K) (fun d _ => w d) =
    (fun ω => ∑ d, score (design K ω d) (w d * response K ω d))
    from funext (singleWeightedXY K w)]
  rfl

theorem singleWeightedScore {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (β : Vec k) (ω : Fin N → U) (d : Dyad N) :
    recordWeightedBlockScore (singleRecord K) (fun d _ => w d) β ω d =
      score (design K ω d) (w d * (response K ω d - dot (design K ω d) β)) := by
  change (∑ _ : Fin 1, score (design K ω d)
    (w d * (response K ω d - dot (design K ω d) β))) = _
  simp only [Fin.sum_univ_one]

theorem singleWeightedH {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) :
    recordWeightedH (singleRecord K) (fun d _ => w d) = weightedPopulationGram K w := by
  unfold recordWeightedH weightedPopulationGram
  rw [show recordWeightedGram (singleRecord K) (fun d _ => w d) = weightedGram K w
    from funext (singleWeightedGram K w)]
  rfl

theorem singleWeightedVariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (ω : Fin N → U) :
    recordWeightedVariance (singleRecord K) (fun d _ => w d) ω = weightedVariance K w ω := by
  rw [recordWeightedVariance, singleWeightedGram, singleWeightedOLS]
  rw [show recordWeightedBlockScore (singleRecord K) (fun d _ => w d)
      (weightedOLS K w ω) ω = (fun d => score (design K ω d)
        (w d * (response K ω d - dot (design K ω d) (weightedOLS K w ω))))
    from funext (singleWeightedScore K w (weightedOLS K w ω) ω)]
  rfl

theorem singleWeightedTarget {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) :
    recordWeightedTarget (singleRecord K) (fun d _ => w d) = weightedTarget K w := by
  rw [recordWeightedTarget, singleWeightedH, singleWeightedBeta]
  have hs : (fun ω => ∑ d : Dyad N, recordWeightedBlockScore (singleRecord K)
      (fun d _ => w d) (weightedPopulationBeta K w) ω d) = weightedScoreSum K w := by
    funext ω
    simp_rw [singleWeightedScore]
    rfl
  rw [hs]
  rfl

theorem singleStanding {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) : RepeatedStanding (singleRecord K) := by
  exact AronowAudit.P018.Wave1.GP0182B2b_singleStanding (toKernel K) hK

end SAP.P018a.Bridge
