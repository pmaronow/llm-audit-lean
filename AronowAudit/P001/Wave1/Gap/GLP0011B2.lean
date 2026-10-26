import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarSelection.N2
import AronowAudit.P001.Wave1.MarSelection.N3
import AronowAudit.P001.Wave1.MarSelection.N4
import AronowAudit.P001.Wave1.MarSelection.N5
import AronowAudit.P001.Wave1.MarDiscrete.N1
import AronowAudit.P001.Wave1.CausalIpwDr.N1
import AronowAudit.P001.Wave1.CausalIpwDr.N2
import AronowAudit.P001.Wave1.MarBalance.N1
import AronowAudit.P001.Wave1.MarBalance.N2

/-! P001-T116: the ATE sum under strong ignorability for countable covariates.

Binary selection on an arbitrary covariate space gives the L1 arm transfer.
The countable result then integrates each arm separately.
-/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0011B2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-- Apply the proved selection transfer to D and to 1-D, retaining the supplied
arm regression versions on the arbitrary covariate space. -/
lemma discreteSI_arm_cefs {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ) (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
   (hpos : ∀ ω,ε < p (X ω) ∧ p (X ω) < 1-ε)
   (hCI : CI μ X hX (fun ω => (Y0 ω,Y1 ω)) D)
   (m0 m1 : E → ℝ)
   (hm0 : IsCEF (μ.restrict {ω | D ω=0}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0)
   (hm1 : IsCEF (μ.restrict {ω | D ω=1}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m1)
   (hmi0 : Integrable (m0 ∘ X) μ) (hmi1 : Integrable (m1 ∘ X) μ) :
   IsCEF μ X Y0 m0 ∧ IsCEF μ X Y1 m1 := by
  have hU : Measurable (fun ω => (Y0 ω, Y1 ω)) := h0.prodMk h1
  have hbin : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1 := ae_of_all μ hbinary
  have hbin0 : ∀ᵐ ω ∂μ, 1 - D ω = 0 ∨ 1 - D ω = 1 :=
    hbin.mono fun ω h => by rcases h with h | h <;> simp [h]
  have hCI0 := CausalIpwDr.n1_proof μ X hX (fun ω => (Y0 ω, Y1 ω)) D hCI
  have hp0 := CausalIpwDr.n2_proof μ X D p hp
  have hD0 : Measurable (fun ω => 1 - D ω) := measurable_const.sub hD
  have hpos1 : ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < p (X ω) :=
    ⟨ε, hε, ae_of_all μ (fun ω => (hpos ω).1)⟩
  have hpos0 : ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < (fun x => 1 - p x) (X ω) :=
    ⟨ε, hε, ae_of_all μ (fun ω => by linarith [(hpos ω).2])⟩
  have hobs1 : ∀ᵐ ω ∂μ, D ω = 1 →
      observedOutcome (Y0 ω) (Y1 ω) (D ω) =
        (fun z : E × ℝ × ℝ => z.2.2) (X ω, (Y0 ω, Y1 ω)) :=
    ae_of_all μ (fun ω h => by simp [observedOutcome, h])
  have hobs0 : ∀ᵐ ω ∂μ, 1 - D ω = 1 →
      observedOutcome (Y0 ω) (Y1 ω) (D ω) =
        (fun z : E × ℝ × ℝ => z.2.1) (X ω, (Y0 ω, Y1 ω)) :=
    ae_of_all μ (fun ω h => by
      have hd : D ω = 0 := by linarith
      simp [observedOutcome, hd])
  have hset : {ω | 1 - D ω = 1} = {ω | D ω = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, sub_eq_self]
  have hm0' : IsCEF (μ.restrict {ω | 1 - D ω = 1}) X
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0 := by
    rw [hset]
    exact hm0
  constructor
  · exact MarSelection.n5_proof MarSelection.n1_proof MarSelection.n4_proof
      MarSelection.n3_proof MarSelection.n2_proof μ X hX
      (fun ω => (Y0 ω, Y1 ω)) (fun ω => 1 - D ω) (fun z => z.2.1)
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) (fun x => 1 - p x) m0
      hU hD0 measurable_snd.fst hbin0 hCI0 hp0 hpos0 hi0 hobs0 hm0' hmi0
  · exact MarSelection.n5_proof MarSelection.n1_proof MarSelection.n4_proof
      MarSelection.n3_proof MarSelection.n2_proof μ X hX
      (fun ω => (Y0 ω, Y1 ω)) D (fun z => z.2.2)
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) p m1
      hU hD measurable_snd.snd hbin hCI hp hpos1 hi1 hobs1 hm1 hmi1

theorem discrete_strong_ignorability_ate_sum_proof {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ) (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
   (hpos : ∀ ω,ε < p (X ω) ∧ p (X ω) < 1-ε)
   (hCI : CI μ X hX (fun ω => (Y0 ω,Y1 ω)) D)
   (m0 m1 : E → ℝ)
   (hm0 : IsCEF (μ.restrict {ω | D ω=0}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0)
   (hm1 : IsCEF (μ.restrict {ω | D ω=1}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m1)
   (hmi0 : Integrable (m0 ∘ X) μ) (hmi1 : Integrable (m1 ∘ X) μ) : mean μ (fun ω => Y1 ω-Y0 ω)=
   (∑' x : E,m1 x*prob μ {ω | X ω=x})-(∑' x : E,m0 x*prob μ {ω | X ω=x}) := by
  obtain ⟨hc0, hc1⟩ := discreteSI_arm_cefs μ X hX Y0 Y1 D h0 h1 hD
    hi0 hi1 hbinary p hp ε hε hpos hCI m0 m1 hm0 hm1 hmi0 hmi1
  obtain ⟨_hsum0, hmean0⟩ := MarDiscrete.n1_proof μ X hX m0 hmi0
  obtain ⟨_hsum1, hmean1⟩ := MarDiscrete.n1_proof μ X hX m1 hmi1
  calc
    mean μ (fun ω => Y1 ω-Y0 ω) = mean μ Y1 - mean μ Y0 := integral_sub hi1 hi0
    _ = mean μ (m1 ∘ X) - mean μ (m0 ∘ X) := by
      rw [MarDiscrete.mean_eq_of_isCEF μ X Y1 m1 hc1,
        MarDiscrete.mean_eq_of_isCEF μ X Y0 m0 hc0]
    _ = _ := by rw [hmean1, hmean0]


end

end AronowAudit.P001.Wave1
