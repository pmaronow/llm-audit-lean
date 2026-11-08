import SAP.P004a.WH.W2.Leaves
import AronowAudit.P004.Wave1.ObservationalCoverage.O8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T9_L3

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P004
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

def signs (N : ℕ) : Fin N → Assignment N → ℝ :=
  fun i z => 2 * AronowAudit.P004.bit (z i) - 1

def neighborhoods (N : ℕ) : Fin N → Finset (Fin N) := fun i => {i}

def design (N : ℕ) : Measure (Assignment N) :=
  CLTCompletion.designMeasure (fun _ : Fin N => (1 / 2 : ℝ)) (fun _ => by norm_num)

lemma signs_sum (N : ℕ) (z : Assignment N) :
    (∑ i, signs N i z) = boundarySignSum z := rfl

lemma signs_mean (N : ℕ) (i : Fin N) :
    AronowAudit.P004.expect (fun _ : Fin N => (1 / 2 : ℝ)) (signs N i) = 0 := by
  let f : Bool → ℝ := fun b => 2 * AronowAudit.P004.bit b - 1
  change AronowAudit.P004.expect (fun _ : Fin N => (1 / 2 : ℝ))
    (fun z => f (z i)) = 0
  rw [AronowAudit.P004.Wave1.ObservationalCoverage.own_expect _ i f]
  norm_num [f, AronowAudit.P004.bit]

lemma signs_bound (N : ℕ) (i : Fin N) (z : Assignment N) :
    |signs N i z| ≤ 1 := by
  cases h : z i <;> norm_num [signs, AronowAudit.P004.bit, h]

lemma second_moment (N : ℕ) :
    (∫ z, (∑ i, signs N i z)^2 ∂design N) = (N : ℝ) := by
  change (∫ z, (∑ i, signs N i z)^2 ∂
    CLTCompletion.designMeasure (fun _ : Fin N => (1 / 2 : ℝ)) (fun _ => by norm_num)) = _
  rw [CLTCompletion.designMeasure_integral]
  simpa [signs, AronowAudit.P004.Wave1.t9b6_signsum] using
    (AronowAudit.P004.Wave1.t9b6_moments N).1

end
end SAP.P004a.WH.W2.P.T9_L3

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P004
open SAP.P004a.WH.W2.P.T9_L3
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem SAP.P004a.WH.W2.T9_L3_proof : SAP.P004a.WH.W2.T9_L3 := by
  classical
  unfold SAP.P004a.WH.W2.T9_L3 SAP.P004a.NormalLimit
  let μ : ∀ N, Measure (Assignment N) := design
  let V : ∀ N, Fin N → Assignment N → ℝ := signs
  let B : ∀ N, Fin N → Finset (Fin N) := neighborhoods
  have hμ : ∀ N, IsProbabilityMeasure (μ N) := by
    intro N
    dsimp [μ, design]
    infer_instance
  have hmean : ∀ N i, (∫ z, V N i z ∂μ N) = 0 := by
    intro N i
    change (∫ z, signs N i z ∂
      CLTCompletion.designMeasure (fun _ : Fin N => (1 / 2 : ℝ)) (fun _ => by norm_num)) = 0
    rw [CLTCompletion.designMeasure_integral]
    exact signs_mean N i
  have hbound : ∃ M : ℝ, ∀ N i, ∀ᵐ z ∂μ N, |V N i z| ≤ M := by
    refine ⟨1, ?_⟩
    intro N i
    exact Filter.Eventually.of_forall (fun z => signs_bound N i z)
  have hdep : ∀ N, DependencyGraph (μ N) (V N) (B N) := by
    intro N
    apply CLTCompletion.finiteGraph_to_measureGraph
      (fun _ : Fin N => (1 / 2 : ℝ)) (fun _ => by norm_num)
      (V N) (B N)
    change FiniteDependencyGraph (fun _ : Fin N => (1 / 2 : ℝ))
      (fun i z => 2 * AronowAudit.P004.bit (z i) - 1) (fun i => {i})
    exact AronowAudit.P004.Wave1.ObservationalCoverage.own_finiteDependencyGraph
      (fun _ : Fin N => (1 / 2 : ℝ)) (fun _ b => 2 * AronowAudit.P004.bit b - 1)
  have hdegree : ∃ D : ℕ, ∀ N i, (B N i).card ≤ D := by
    refine ⟨1, ?_⟩
    intro N i
    simp [B, neighborhoods]
  have hsecond (N : ℕ) :
      (∫ z, (∑ i, V N i z)^2 ∂μ N) = (N : ℝ) := by
    simpa only [μ, V, design, signs] using second_moment N
  have hvar : ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop,
      v * N ≤ (∫ z, (∑ i, V N i z)^2 ∂μ N) := by
    refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro N
    rw [hsecond N]
    norm_num
  have hclt := AronowAudit.P004.corrected_dependency_clt μ hμ V B
    (fun N i => measurable_of_finite _) hmean hbound hdep hdegree hvar
  intro x
  have hh := hclt x
  simp_rw [hsecond] at hh
  have hp : Tendsto (fun N : ℕ => AronowAudit.P004.prob (fun _ : Fin N => (1 / 2 : ℝ))
      (fun z : AronowAudit.P004.Assignment N => boundarySignSum z / Real.sqrt N ≤ x)) atTop
      (nhds (AronowAudit.P004.normalCDF x)) := by
    simpa [μ, V, design, signs, boundarySignSum, SAP.P004a.bit, AronowAudit.P004.bit,
      CLTCompletion.designMeasure_apply, Set.mem_setOf_eq] using hh
  have heq (N : ℕ) : SAP.P004a.prob (fun _ : Fin N => (1 / 2 : ℝ))
      (fun z : SAP.P004a.Assignment N => boundarySignSum z / Real.sqrt N ≤ x) =
      AronowAudit.P004.prob (fun _ : Fin N => (1 / 2 : ℝ))
      (fun z : AronowAudit.P004.Assignment N => boundarySignSum z / Real.sqrt N ≤ x) := by
    simp [SAP.P004a.prob, SAP.P004a.expect, SAP.P004a.designWeight, SAP.P004a.coin,
      AronowAudit.P004.prob, AronowAudit.P004.expect, AronowAudit.P004.designWeight,
      AronowAudit.P004.coin]
  have hnormal : SAP.P004a.normalCDF x = AronowAudit.P004.normalCDF x := rfl
  simpa only [heq, hnormal] using hp

end
