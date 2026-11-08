import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.P001_PrintedRefutations
import Mathlib.MeasureTheory.Measure.Support

namespace AronowAudit.P001.Wave1
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableRepairT120 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
universe u

/-- The recorded printed contract, with its fixed covariate restricted to the
covariate-law support. Every other binder is unchanged. The witness below has
positive singleton mass at both covariate values, so also meets the discrete
(positive-mass) reading of support. -/
def PrintedFixedCovariateKLMLESupported : Prop :=
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
   (x : Fin K → ℝ) (hx : x ∈ νX.support) (tstar : Fin τ → ℝ) (ht : tstar∈Θ)
   (hdom : ∀ t∈Θ,∀ᵐ y ∂κ,0 < f y x → 0 < g y x t)
   (hKL : ∀ t∈Θ,Integrable (fun y => f y x*Real.log (f y x/g y x t)) κ)
   (hunique : ∀ t∈Θ,conditionalKL κ f g x tstar ≤ conditionalKL κ f g x t ∧
     (conditionalKL κ f g x t=conditionalKL κ f g x tstar → t=tstar))
   (that : ℕ → Ω → Fin τ → ℝ) (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → (∏ i ∈ Finset.range n,g (Y i ω) (X i ω) t) ≤ 
     ∏ i ∈ Finset.range n,g (Y i ω) (X i ω) (that n ω)),
    CP μ that tstar

def RepairT120Target : Prop := ¬ PrintedFixedCovariateKLMLESupported.{u}

private def RepairT120_binary (p y : ℝ) : ℝ :=
  if y = 1 then p else if y = 0 then 1-p else 0
private def RepairT120_κ : Measure ℝ := Measure.dirac 0 + Measure.dirac 1
private instance RepairT120_κ_finite : IsFiniteMeasure RepairT120_κ := by
  unfold RepairT120_κ; infer_instance
private theorem RepairT120_binary_meas (p : ℝ) : Measurable (RepairT120_binary p) := by
  unfold RepairT120_binary
  exact measurable_const.ite (measurableSet_singleton 1)
    (measurable_const.ite (measurableSet_singleton 0) measurable_const)
private theorem RepairT120_binary_nonneg {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (y : ℝ) :
    0 ≤ RepairT120_binary p y := by
  unfold RepairT120_binary
  split_ifs <;> linarith only [hp.1,hp.2]
private theorem RepairT120_binary_norm {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∫⁻ y, ENNReal.ofReal (RepairT120_binary p y) ∂RepairT120_κ) = 1 := by
  simp only [RepairT120_κ, lintegral_add_measure, lintegral_dirac]
  norm_num [RepairT120_binary]
  rw [← ENNReal.ofReal_add (by linarith only [hp.2]) hp.1]
  norm_num

private def RepairT120_f (y : ℝ) (x : Fin 1 → ℝ) : ℝ :=
  RepairT120_binary (if x 0 = 0 then 1/4 else 3/4) y
private def RepairT120_g (y : ℝ) (_ : Fin 1 → ℝ) (t : Fin 1 → ℝ) : ℝ :=
  RepairT120_binary (t 0) y
private def RepairT120_Θ : Set (Fin 1 → ℝ) :=
  {t | t 0 ∈ Set.Icc (1/10 : ℝ) (9/10)}
private theorem RepairT120_f_meas :
    Measurable (fun xy : (Fin 1 → ℝ) × ℝ => RepairT120_f xy.2 xy.1) := by
  have hm : Measurable (fun xy : (Fin 1 → ℝ) × ℝ =>
      if xy.1 0 = 0 then (1/4 : ℝ) else 3/4) :=
    measurable_const.ite
      ((measurable_pi_apply 0).comp measurable_fst (measurableSet_singleton 0)) measurable_const
  unfold RepairT120_f RepairT120_binary
  exact hm.ite (measurable_snd (measurableSet_singleton _))
    ((measurable_const.sub hm).ite (measurable_snd (measurableSet_singleton _)) measurable_const)
private theorem RepairT120_kl (t : Fin 1 → ℝ) :
    conditionalKL RepairT120_κ RepairT120_f RepairT120_g (fun _ => 0) t =
      bernoulliKL (1/4) (t 0) := by
  unfold conditionalKL RepairT120_κ
  rw [integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top)]
  simp [RepairT120_f,RepairT120_g,RepairT120_binary,bernoulliKL]
  ring

/-- A finite alphabet makes every sample point binary, including null sample points. -/
private def RepairT120_law : Measure (Fin 4) :=
  (3/8 : ℝ≥0∞) • Measure.dirac 0 + (1/8 : ℝ≥0∞) • Measure.dirac 1 +
  (1/8 : ℝ≥0∞) • Measure.dirac 2 + (3/8 : ℝ≥0∞) • Measure.dirac 3
private instance RepairT120_law_probability : IsProbabilityMeasure RepairT120_law := by
  constructor
  norm_num [RepairT120_law,Measure.add_apply,Measure.smul_apply]
  rw [show (8 : ℝ≥0∞)⁻¹ = 1/8 from (one_div _).symm,
    ← ENNReal.add_div, ← ENNReal.add_div, ← ENNReal.add_div]
  norm_num
  exact ENNReal.div_self (a := 8) (by norm_num) (by simp)
private def RepairT120_a : Fin 4 → ℝ := ![0,0,1,1]
private def RepairT120_b : Fin 4 → ℝ := ![0,1,0,1]
private def RepairT120_ν : Measure (Fin 1 → ℝ) :=
  (1/2 : ℝ≥0∞) • Measure.dirac (fun _ => 0) +
  (1/2 : ℝ≥0∞) • Measure.dirac (fun _ => 1)
private instance RepairT120_ν_probability : IsProbabilityMeasure RepairT120_ν := by
  constructor
  norm_num [RepairT120_ν,Measure.add_apply,Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two
private theorem RepairT120_cell_masses :
    RepairT120_ν {fun _ => 0} = 1/2 ∧ RepairT120_ν {fun _ => 1} = 1/2 := by
  have hne : (fun _ : Fin 1 => (0 : ℝ)) ≠ (fun _ => 1) := by
    intro h; have := congrFun h 0; norm_num at this
  simp [RepairT120_ν,Measure.add_apply,Measure.smul_apply,hne,hne.symm]
private theorem RepairT120_supported : (fun _ => 0) ∈ RepairT120_ν.support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have hsub : {fun _ : Fin 1 => (0 : ℝ)} ⊆ U :=
    Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU)
  have hpos : 0 < RepairT120_ν {fun _ => 0} := by
    rw [RepairT120_cell_masses.1]; norm_num
  exact hpos.trans_le (measure_mono hsub)

private theorem RepairT120_scalar_law :
    RepairT120_law.map (fun j => (RepairT120_a j,RepairT120_b j)) =
      (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
      (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1) := by
  have hm := measurable_of_finite (fun j => (RepairT120_a j,RepairT120_b j))
  simp only [RepairT120_law,Measure.map_add _ _ hm,Measure.map_smul _ hm.aemeasurable,
    Measure.map_dirac]
  norm_num [RepairT120_a,RepairT120_b]
private theorem RepairT120_density :
    RepairT120_law.map (fun j => ((fun _ : Fin 1 => RepairT120_a j),RepairT120_b j)) =
      (RepairT120_ν.prod RepairT120_κ).withDensity
        (fun xy => ENNReal.ofReal (RepairT120_f xy.2 xy.1)) := by
  have hm := measurable_of_finite
    (fun j => ((fun _ : Fin 1 => RepairT120_a j),RepairT120_b j))
  simp only [RepairT120_law,Measure.map_add _ _ hm,Measure.map_smul _ hm.aemeasurable,
    Measure.map_dirac]
  norm_num [RepairT120_a,RepairT120_b,
    RepairT120_ν,RepairT120_κ,Measure.add_prod,Measure.prod_add,Measure.prod_smul_left,
    Measure.dirac_prod_dirac,withDensity_add_measure,withDensity_smul_measure,
    dirac_withDensity,RepairT120_f,RepairT120_binary,smul_smul]
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
    div_eq_mul_inv, ← mul_assoc, ← ENNReal.mul_inv]
  have hc (r : ℝ≥0∞) : (2 : ℝ≥0∞)⁻¹ * r * (4 : ℝ≥0∞)⁻¹ =
      r * (8 : ℝ≥0∞)⁻¹ := by
    calc
      _ = r * ((2 : ℝ≥0∞)⁻¹ * (4 : ℝ≥0∞)⁻¹) := by ac_rfl
      _ = _ := by rw [← ENNReal.mul_inv] <;> norm_num
  simp only [hc]
  ac_rfl

private theorem RepairT120_iid_comp {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] (μ : Measure Ω) (Z : ℕ → Ω → E)
    (hi : IID μ Z) (f : E → F) (hf : Measurable f) : IID μ (fun i ω => f (Z i ω)) :=
  ⟨fun i => hf.comp (hi.1 i),hi.2.1.comp (fun _ => f) (fun _ => hf),
    fun i => (hi.2.2 i).comp hf⟩

private theorem RepairT120_mle {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (hY : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (n : ℕ) (ω : Ω)
    (t : Fin 1 → ℝ) (ht : t ∈ RepairT120_Θ) (X : ℕ → Ω → Fin 1 → ℝ) :
    (∏ i ∈ Finset.range n,RepairT120_g (Y i ω) (X i ω) t) ≤
      ∏ i ∈ Finset.range n,RepairT120_g (Y i ω) (X i ω)
        (fun _ => clip (1/10) (9/10) (sampleMean Y n ω)) := by
  by_cases hn : n = 0
  · subst n; simp
  have hb (i : ℕ) (p : ℝ) : RepairT120_binary p (Y i ω) =
      if Y i ω = 1 then p else 1-p := by
    rcases hY i ω with h|h <;> simp [h,RepairT120_binary]
  simp only [RepairT120_g,hb]
  have hm := ((clipped_bernoulli_mle (Nat.pos_of_ne_zero hn)
    (fun i : Fin n => Y i.val ω) (fun i => hY i.val ω)).2 (t 0) ht).1
  rw [Fin.sum_univ_eq_sum_range (fun i => Y i ω) n] at hm
  rw [Fin.prod_univ_eq_prod_range (fun i => if Y i ω = 1 then t 0 else 1-t 0) n,
    Fin.prod_univ_eq_prod_range (fun i => if Y i ω = 1 then
      clip (1/10) (9/10) ((∑ i ∈ Finset.range n, Y i ω) / (n : ℝ)) else
      1-clip (1/10) (9/10) ((∑ i ∈ Finset.range n, Y i ω) / (n : ℝ))) n] at hm
  exact hm

/-- The supported four-atom example refutes the support-respecting printed claim. -/
theorem printed_fixed_covariate_kl_mle_supported_refuted :
    ¬ PrintedFixedCovariateKLMLESupported.{u} := by
  intro h
  let μ := PrintedConfidence.liftStreamLaw.{u} RepairT120_law
  let Z : ℕ → (ℕ → ULift.{u} (Fin 4)) → Fin 4 := PrintedConfidence.streamObservation
  let A := fun i ω => RepairT120_a (Z i ω)
  let Y := fun i ω => RepairT120_b (Z i ω)
  let X := fun i ω (_ : Fin 1) => A i ω
  have hi := (PrintedConfidence.lift_stream_iid.{u} RepairT120_law).1
  have hz : μ.map (Z 0) = RepairT120_law :=
    (PrintedConfidence.lift_stream_iid.{u} RepairT120_law).2
  have his : IID μ (fun i ω => (A i ω,Y i ω)) :=
    RepairT120_iid_comp μ Z hi (fun j => (RepairT120_a j,RepairT120_b j))
      (measurable_of_finite _)
  have hiv : IID μ (fun i ω => (X i ω,Y i ω)) :=
    RepairT120_iid_comp μ Z hi (fun j => ((fun _ : Fin 1 => RepairT120_a j),RepairT120_b j))
      (measurable_of_finite _)
  have hls : μ.map (fun ω => (A 0 ω,Y 0 ω)) =
      (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
      (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1) := by
    change μ.map ((fun j => (RepairT120_a j,RepairT120_b j)) ∘ Z 0) = _
    rw [← Measure.map_map (measurable_of_finite _) (hi.1 0),hz]
    exact RepairT120_scalar_law
  have hlv : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
      (RepairT120_ν.prod RepairT120_κ).withDensity
        (fun xy => ENNReal.ofReal (RepairT120_f xy.2 xy.1)) := by
    change μ.map ((fun j => ((fun _ : Fin 1 => RepairT120_a j),RepairT120_b j)) ∘ Z 0) = _
    rw [← Measure.map_map (measurable_of_finite _) (hi.1 0),hz]
    exact RepairT120_density
  have hY : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1 := by
    intro i ω
    dsimp [Y]
    generalize Z i ω = j
    fin_cases j <;> norm_num [RepairT120_b]
  have hcp := h μ X Y hiv RepairT120_κ RepairT120_ν RepairT120_f RepairT120_g hlv
    RepairT120_Θ
    (fun y x => RepairT120_binary_nonneg (by split_ifs <;> norm_num) y)
    (fun x => RepairT120_binary_norm (by split_ifs <;> norm_num)) RepairT120_f_meas
    (fun t ht => (RepairT120_binary_meas (t 0)).comp measurable_snd)
    (fun t ht y x => RepairT120_binary_nonneg
      ⟨by linarith only [ht.1],by linarith only [ht.2]⟩ y)
    (fun t ht x => RepairT120_binary_norm
      ⟨by linarith only [ht.1],by linarith only [ht.2]⟩)
    (fun _ => 0) RepairT120_supported (fun _ => 1/4) (by norm_num [RepairT120_Θ])
    (by
      intro t ht
      filter_upwards [] with y
      by_cases h1 : y = 1
      · subst y; norm_num [RepairT120_f,RepairT120_g,RepairT120_binary]
        linarith only [ht.1]
      · by_cases h0 : y = 0
        · subst y; norm_num [RepairT120_f,RepairT120_g,RepairT120_binary]
          linarith only [ht.2]
        · simp [RepairT120_f,RepairT120_g,RepairT120_binary,h1,h0])
    (by
      intro t ht
      unfold RepairT120_κ
      exact Integrable.add_measure (integrable_dirac enorm_lt_top)
        (integrable_dirac enorm_lt_top))
    (by
      intro t ht
      rw [RepairT120_kl,RepairT120_kl]
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
    (fun n ω t ht => RepairT120_mle Y hY n ω t ht X)
  have hp := probability_convergence_continuous_at μ _ _
    (fun t : Fin 1 → ℝ => t 0) hcp (continuous_apply 0).continuousAt
  exact (conditional_kl_mle_wrong_target_supporting μ A Y his hls).2.2.1 hp

example : RepairT120Target.{u} ↔ ¬ PrintedFixedCovariateKLMLESupported.{u} := Iff.rfl
example : RepairT120Target.{u} := printed_fixed_covariate_kl_mle_supported_refuted

end
end AronowAudit.P001.Wave1
