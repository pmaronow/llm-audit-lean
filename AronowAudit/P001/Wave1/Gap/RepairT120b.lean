import AronowAudit.P001.Wave1.Gap.RepairT120

namespace AronowAudit.P001.Wave1
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableRepairT120b (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
universe u

/-- The printed fixed-covariate contract on the book's positive-PMF support
(Definition 1.2.20, p. 31), expressed by positive singleton mass. This discrete
case already refutes the universal printed claim.
No topological-support premise occurs here. -/
def PrintedFixedCovariateKLMLEPositiveSupport : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (κ : Measure ℝ) [SFinite κ] (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
   (f : ℝ → (Fin K → ℝ) → ℝ) (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (hf : μ.map (fun ω => (X 0 ω,Y 0 ω))=
     (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
   (Θ : Set (Fin τ → ℝ))
   (hfpos : ∀ y x,0 ≤ f y x) (hfnorm : ∀ x,(∫⁻ y,ENNReal.ofReal (f y x) ∂κ)=1)
   (hfmeas : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
   (hgmeas : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hgpos : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hgnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (x : Fin K → ℝ) (hx : 0 < νX {x}) (tstar : Fin τ → ℝ) (ht : tstar∈Θ)
   (hdom : ∀ t∈Θ,∀ᵐ y ∂κ,0 < f y x → 0 < g y x t)
   (hKL : ∀ t∈Θ,Integrable (fun y => f y x*Real.log (f y x/g y x t)) κ)
   (hunique : ∀ t∈Θ,conditionalKL κ f g x tstar ≤ conditionalKL κ f g x t ∧
     (conditionalKL κ f g x t=conditionalKL κ f g x tstar → t=tstar))
   (that : ℕ → Ω → Fin τ → ℝ) (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → (∏ i ∈ Finset.range n,g (Y i ω) (X i ω) t) ≤ 
     ∏ i ∈ Finset.range n,g (Y i ω) (X i ω) (that n ω)),
    CP μ that tstar


-- The imported private witness declarations have names with a numeric component.
-- The aliases expose these constants to elaboration without introducing
-- definitions, propositions, or proof assumptions.

run_cmd do
  let witnessNames := ["binary", "binary_meas", "binary_nonneg", "binary_norm", "κ",
    "f", "g", "Θ", "f_meas", "kl", "law", "a", "b", "ν",
    "cell_masses", "scalar_law", "density", "iid_comp", "mle"]
  for suffix in witnessNames do
    let source := Lean.mkPrivateNameCore `AronowAudit.P001.Wave1.Gap.RepairT120
      (`AronowAudit.P001.Wave1 ++ Lean.Name.mkSimple ("RepairT120_" ++ suffix))
    let aliasName := `AronowAudit.P001.Wave1 ++ Lean.Name.mkSimple ("RepairT120b_" ++ suffix)
    Lean.modifyEnv fun env => Lean.addAlias env aliasName source

private theorem RepairT120b_positive_support :
    0 < RepairT120b_ν {fun _ : Fin 1 => (0 : ℝ)} := by
  rw [RepairT120b_cell_masses.1]
  norm_num

/-- The four-atom IID model refutes the printed claim at a covariate with
probability 1/2, so the failure occurs inside the book's positive-mass support. -/
theorem printed_fixed_covariate_kl_mle_positive_support_refuted :
    ¬ PrintedFixedCovariateKLMLEPositiveSupport.{u} := by
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
    (fun _ => 0) RepairT120b_positive_support (fun _ => 1/4) (by norm_num [RepairT120b_Θ])
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
      rw [RepairT120b_kl,RepairT120b_kl]
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
      intro n ω
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩)
    (fun n ω t ht => RepairT120b_mle Y hY n ω t ht X)
  have hp := probability_convergence_continuous_at μ _ _
    (fun t : Fin 1 → ℝ => t 0) hcp (continuous_apply 0).continuousAt
  exact (conditional_kl_mle_wrong_target_supporting μ A Y his hls).2.2.1 hp

end
end AronowAudit.P001.Wave1
