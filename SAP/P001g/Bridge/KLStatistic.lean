import SAP.P001g.Defs
import AronowAudit.P001.Wave1.Gap.RepairT120b

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.Bridge

open AronowAudit.P001 AronowAudit.P001.Wave1 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
local instance instDecidableKLStatistic (p : Prop) : Decidable p := Classical.propDecidable p
universe u

/-- The credited row's covariate has positive singleton mass. -/
theorem kl_positive_support :
    0 < RepairT120b_ν {fun _ : Fin 1 => (0 : ℝ)} := by
  rw [RepairT120b_cell_masses.1]
  norm_num

/-- Reassemble the existing four-atom refutation using its exported witness
components. The additional premise is supplied by the measurable clipped
finite-sample outcome mean; its correspondence uses only the Fin sum identity. -/
theorem t120 : SAP.P001g.T120Statement.{u} := by
  intro h
  let μ := PrintedConfidence.liftStreamLaw.{u} RepairT120b_law
  let Z : ℕ → (ℕ → ULift.{u} (Fin 4)) → Fin 4 := PrintedConfidence.streamObservation
  let A := fun i ω => RepairT120b_a (Z i ω)
  let Y := fun i ω => RepairT120b_b (Z i ω)
  let X := fun i ω (_ : Fin 1) => A i ω
  have hi := (PrintedConfidence.lift_stream_iid.{u} RepairT120b_law).1
  have hz : μ.map (Z 0) = RepairT120b_law :=
    (PrintedConfidence.lift_stream_iid.{u} RepairT120b_law).2
  have his : IID μ (fun i ω => (A i ω,Y i ω)) :=
    RepairT120b_iid_comp μ Z hi (fun j => (RepairT120b_a j,RepairT120b_b j))
      (measurable_of_finite _)
  have hiv : IID μ (fun i ω => (X i ω,Y i ω)) :=
    RepairT120b_iid_comp μ Z hi (fun j => ((fun _ : Fin 1 => RepairT120b_a j),RepairT120b_b j))
      (measurable_of_finite _)
  have hls : μ.map (fun ω => (A 0 ω,Y 0 ω)) =
      (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
      (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1) := by
    change μ.map ((fun j => (RepairT120b_a j,RepairT120b_b j)) ∘ Z 0) = _
    rw [← Measure.map_map (measurable_of_finite _) (hi.1 0),hz]
    exact RepairT120b_scalar_law
  have hlv : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
      (RepairT120b_ν.prod RepairT120b_κ).withDensity
        (fun xy => ENNReal.ofReal (RepairT120b_f xy.2 xy.1)) := by
    change μ.map ((fun j => ((fun _ : Fin 1 => RepairT120b_a j),RepairT120b_b j)) ∘ Z 0) = _
    rw [← Measure.map_map (measurable_of_finite _) (hi.1 0),hz]
    exact RepairT120b_density
  have hY : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1 := by
    intro i ω
    dsimp [Y]
    generalize Z i ω = j
    fin_cases j <;> norm_num [RepairT120b_b]
  have hcp := h μ X Y hiv RepairT120b_κ RepairT120b_ν RepairT120b_f RepairT120b_g hlv
    RepairT120b_Θ
    (fun y x => RepairT120b_binary_nonneg (by split_ifs <;> norm_num) y)
    (fun x => RepairT120b_binary_norm (by split_ifs <;> norm_num)) RepairT120b_f_meas
    (fun t ht => (RepairT120b_binary_meas (t 0)).comp measurable_snd)
    (fun t ht y x => RepairT120b_binary_nonneg
      ⟨by linarith only [ht.1],by linarith only [ht.2]⟩ y)
    (fun t ht x => RepairT120b_binary_norm
      ⟨by linarith only [ht.1],by linarith only [ht.2]⟩)
    (fun _ => 0) kl_positive_support (fun _ => 1/4) (by norm_num [RepairT120b_Θ])
    (by
      intro t ht
      filter_upwards [] with y
      by_cases h1 : y = 1
      · subst y; norm_num [RepairT120b_f,RepairT120b_g,RepairT120b_binary]
        linarith only [ht.1]
      · by_cases h0 : y = 0
        · subst y; norm_num [RepairT120b_f,RepairT120b_g,RepairT120b_binary]
          linarith only [ht.2]
        · simp [RepairT120b_f,RepairT120b_g,RepairT120b_binary,h1,h0])
    (by
      intro t ht
      unfold RepairT120b_κ
      exact Integrable.add_measure (integrable_dirac enorm_lt_top)
        (integrable_dirac enorm_lt_top))
    (by
      intro t ht
      rw [show @SAP.P001g.conditionalKL = @AronowAudit.P001.conditionalKL from rfl,
        RepairT120b_kl,RepairT120b_kl]
      have hz : bernoulliKL (1/4) (1/4) = 0 := by norm_num [bernoulliKL]
      rw [hz]
      have hk := bernoulli_kl_minimum (1/4) (t 0) (by norm_num) (by norm_num)
        (by linarith only [ht.1]) (by linarith only [ht.2])
      refine ⟨hk.1,fun he => ?_⟩
      ext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact hk.2.mp he)
    (fun n ω _ => clip (1/10) (9/10) (sampleMean Y n ω))
    (by
      intro n
      refine ⟨(fun s => fun _ : Fin 1 => clip (1/10) (9/10)
        ((∑ i : Fin n, (s i).2) / (n : ℝ))), ?_, ?_⟩
      · unfold clip
        fun_prop
      · intro ω
        funext j
        simp only [SAP.P001g.sampleMean]
        rw [Fin.sum_univ_eq_sum_range (fun i => Y i ω) n])
    (by
      intro n ω
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩)
    (fun n ω t ht => RepairT120b_mle Y hY n ω t ht X)
  have hp := probability_convergence_continuous_at μ _ _
    (fun t : Fin 1 → ℝ => t 0) hcp (continuous_apply 0).continuousAt
  exact (conditional_kl_mle_wrong_target_supporting μ A Y his hls).2.2.1 hp

end
end SAP.P001g.Bridge
