import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.P001_PrintedRefutations

namespace AronowAudit.P001.Wave1
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableWP001bB1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8192
universe u

private theorem fixed_iid_const {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : E) :
    IID μ (fun (_ : ℕ) (_ : Ω) => c) := by
  refine ⟨fun _ => measurable_const, ?_, fun _ => IdentDistrib.refl measurable_const.aemeasurable⟩
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hp (i : ℕ) : (fun _ : Ω => c) ⁻¹' sets i =
      if c ∈ sets i then Set.univ else ∅ := by
    split_ifs <;> ext ω <;> simp_all
  simp_rw [hp]
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    by_cases h : c ∈ sets a
    · simpa [ha, h] using ih (fun i hi => hsets i (Finset.mem_insert_of_mem hi))
    · simp [ha, h]

private theorem fixed_cp_const {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (c : E) : CP μ (fun _ _ => c) c := by
  intro ε hε
  simpa [prob, not_le.mpr hε] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

private def fixed_binary (p y : ℝ) : ℝ := if y=1 then p else if y=0 then 1-p else 0
private def fixed_κ : Measure ℝ := Measure.dirac 0 + Measure.dirac 1
private instance fixed_κ_finite : IsFiniteMeasure fixed_κ := by unfold fixed_κ; infer_instance
private theorem fixed_binary_meas (p : ℝ) : Measurable (fixed_binary p) := by
  unfold fixed_binary
  exact measurable_const.ite (measurableSet_singleton 1)
    (measurable_const.ite (measurableSet_singleton 0) measurable_const)
private theorem fixed_binary_nonneg {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (y : ℝ) :
    0 ≤ fixed_binary p y := by
  unfold fixed_binary
  split_ifs <;> linarith only [hp.1,hp.2]
private theorem fixed_binary_norm {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∫⁻ y, ENNReal.ofReal (fixed_binary p y) ∂fixed_κ)=1 := by
  simp only [fixed_κ, lintegral_add_measure, lintegral_dirac]
  norm_num [fixed_binary]
  rw [← ENNReal.ofReal_add (by linarith only [hp.2]) hp.1]
  norm_num

private def fixed_f (y : ℝ) (x : Fin 1 → ℝ) : ℝ :=
  fixed_binary (if x 0=0 then 3/4 else 0) y
private def fixed_g (y : ℝ) (_ : Fin 1 → ℝ) (t : Fin 1 → ℝ) : ℝ := fixed_binary (t 0) y
private def fixed_Θ : Set (Fin 1 → ℝ) := {t | t 0 ∈ Set.Icc (1/10 : ℝ) (9/10)}
private theorem fixed_f_meas : Measurable (fun xy : (Fin 1 → ℝ) × ℝ => fixed_f xy.2 xy.1) := by
  have hm : Measurable (fun xy : (Fin 1 → ℝ) × ℝ => if xy.1 0=0 then (3/4 : ℝ) else 0) :=
    measurable_const.ite ((measurable_pi_apply 0).comp measurable_fst (measurableSet_singleton 0)) measurable_const
  unfold fixed_f fixed_binary
  exact hm.ite (measurable_snd (measurableSet_singleton _)) ((measurable_const.sub hm).ite
    (measurable_snd (measurableSet_singleton _)) measurable_const)

private theorem fixed_kl (t : Fin 1 → ℝ) :
    conditionalKL fixed_κ fixed_f fixed_g (fun _ => 0) t = bernoulliKL (3/4) (t 0) := by
  unfold conditionalKL fixed_κ
  rw [integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top)]
  simp [fixed_f,fixed_g,fixed_binary,bernoulliKL]
  ring

theorem printed_fixed_covariate_kl_mle_refuted :
  ¬ (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
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
   (x : Fin K → ℝ) (tstar : Fin τ → ℝ) (ht : tstar∈Θ)
   (hdom : ∀ t∈Θ,∀ᵐ y ∂κ,0 < f y x → 0 < g y x t)
   (hKL : ∀ t∈Θ,Integrable (fun y => f y x*Real.log (f y x/g y x t)) κ)
   (hunique : ∀ t∈Θ,conditionalKL κ f g x tstar ≤ conditionalKL κ f g x t ∧
     (conditionalKL κ f g x t=conditionalKL κ f g x tstar → t=tstar))
   (that : ℕ → Ω → Fin τ → ℝ) (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → (∏ i ∈ Finset.range n,g (Y i ω) (X i ω) t) ≤ 
     ∏ i ∈ Finset.range n,g (Y i ω) (X i ω) (that n ω)),
    CP μ that tstar) := by
  intro h
  let μ : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  let X : ℕ → ULift.{u} Unit → Fin 1 → ℝ := fun _ _ _ => 1
  let Y : ℕ → ULift.{u} Unit → ℝ := fun _ _ => 0
  let ν : Measure (Fin 1 → ℝ) := Measure.dirac (fun _ => 1)
  have hf : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
      (ν.prod fixed_κ).withDensity (fun xy => ENNReal.ofReal (fixed_f xy.2 xy.1)) := by
    simp [μ,X,Y,ν,fixed_κ,Measure.map_const,Measure.prod_add,
      Measure.dirac_prod_dirac,withDensity_add_measure,dirac_withDensity,fixed_f,fixed_binary]
  have hcp := h μ X Y (fixed_iid_const μ ((fun _ => 1),0)) fixed_κ ν fixed_f fixed_g hf
    fixed_Θ
    (fun y x => fixed_binary_nonneg (by split_ifs <;> norm_num) y)
    (fun x => fixed_binary_norm (by split_ifs <;> norm_num)) fixed_f_meas
    (fun t ht => (fixed_binary_meas (t 0)).comp measurable_snd)
    (fun t ht y x => fixed_binary_nonneg ⟨by linarith only [ht.1],by linarith only [ht.2]⟩ y)
    (fun t ht x => fixed_binary_norm ⟨by linarith only [ht.1],by linarith only [ht.2]⟩)
    (fun _ => 0) (fun _ => 3/4) (by norm_num [fixed_Θ])
    (by
      intro t ht
      filter_upwards [] with y
      by_cases h1 : y=1
      · subst y; norm_num [fixed_f,fixed_g,fixed_binary]; linarith only [ht.1]
      · by_cases h0 : y=0
        · subst y; norm_num [fixed_f,fixed_g,fixed_binary]; linarith only [ht.2]
        · simp [fixed_f,fixed_g,fixed_binary,h1,h0])
    (by
      intro t ht
      unfold fixed_κ
      apply Integrable.add_measure
      · exact integrable_dirac enorm_lt_top
      · exact integrable_dirac enorm_lt_top)
    (by
      intro t ht
      rw [fixed_kl,fixed_kl]
      have hz : bernoulliKL (3/4) (3/4)=0 := by norm_num [bernoulliKL]
      rw [hz]
      have hk := bernoulli_kl_minimum (3/4) (t 0) (by norm_num) (by norm_num)
        (by linarith only [ht.1]) (by linarith only [ht.2])
      refine ⟨hk.1,fun he => ?_⟩
      ext j
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      exact hk.2.mp he)
    (fun _ _ _ => 1/10) (by intros; norm_num [fixed_Θ])
    (by
      intro n ω t ht
      apply Finset.prod_le_prod₀
      · intro i hi; exact fixed_binary_nonneg ⟨by linarith only [ht.1],by linarith only [ht.2]⟩ 0
      · intro i hi
        change fixed_binary (t 0) 0 ≤ fixed_binary (1/10) 0
        norm_num [fixed_binary]
        linarith only [ht.1])
  have he := probability_limit_unique μ (fun _ _ => (fun _ : Fin 1 => (1/10 : ℝ)))
    (fun _ => 1/10) (fun _ => 3/4) (fixed_cp_const μ _) hcp
  have he0 := congrFun he 0
  norm_num at he0

example : (type_of% @printed_fixed_covariate_kl_mle_refuted.{u}) ↔
    ¬ (type_of% @AronowAudit.P001.printed_fixed_covariate_kl_mle_target.{u}) := Iff.rfl


private def general_κ : Measure ℝ := fixed_κ + Measure.dirac 2 + Measure.dirac 3
private instance general_κ_finite : IsFiniteMeasure general_κ := by
  unfold general_κ; infer_instance
private def general_p (t : Fin 3 → ℝ) : Fin 2 → ℝ := ![t 0, 1-t 0]
private def general_g (m : Fin 2) (y : ℝ) (_ : Fin 0 → ℝ) (t : Fin 3 → ℝ) : ℝ :=
  if m=0 then fixed_binary (t 1) y else fixed_binary (t 2) (y-2)
private theorem general_box (t : Fin 3 → ℝ) :
    t ∈ disjointMixtureParameterSet ↔
    t 0 ∈ Set.Icc (0 : ℝ) 1 ∧ t 1 ∈ Set.Icc (0 : ℝ) 1 ∧
      t 2 ∈ Set.Icc (1/4 : ℝ) (3/4) := by
  constructor
  · intro h
    exact ⟨⟨h.1 0,h.2 0⟩,⟨h.1 1,h.2 1⟩,⟨h.1 2,h.2 2⟩⟩
  · rintro ⟨h0,h1,h2⟩
    constructor <;> intro j <;> fin_cases j <;> simp_all
private theorem general_g_norm (t : Fin 3 → ℝ) (ht : t ∈ disjointMixtureParameterSet)
    (m : Fin 2) (x : Fin 0 → ℝ) :
    (∫⁻ y, ENNReal.ofReal (general_g m y x t) ∂general_κ)=1 := by
  have hb := (general_box t).mp ht
  fin_cases m
  · simpa [general_g,general_κ,lintegral_add_measure,lintegral_dirac,fixed_binary]
      using fixed_binary_norm hb.2.1
  · simp only [general_κ,fixed_κ,lintegral_add_measure,lintegral_dirac]
    norm_num [general_g,fixed_binary]
    rw [← ENNReal.ofReal_add (by linarith only [hb.2.2.2]) (by linarith only [hb.2.2.1])]
    norm_num
private theorem general_g_meas (t : Fin 3 → ℝ) (m : Fin 2) :
    Measurable (fun xy : (Fin 0 → ℝ) × ℝ => general_g m xy.2 xy.1 t) := by
  fin_cases m
  · simpa [general_g,Function.comp_def] using (fixed_binary_meas (t 1)).comp measurable_snd
  · simpa [general_g,Function.comp_def] using (fixed_binary_meas (t 2)).comp (measurable_snd.sub_const 2)
private theorem general_density_zero (t : Fin 3 → ℝ) (x : Fin 0 → ℝ) :
    mixtureFamily general_p general_g 0 x t = t 0*(1-t 1) := by
  norm_num [mixtureFamily,general_p,general_g,Fin.sum_univ_succ,fixed_binary]
private theorem general_true :
    conditionalModelLaw (Measure.dirac (fun j : Fin 0 => Fin.elim0 j)) general_κ
      (mixtureFamily general_p general_g) (![1,0,1/4] : Fin 3 → ℝ) =
      Measure.dirac ((fun j : Fin 0 => Fin.elim0 j),(0 : ℝ)) := by
  simp [conditionalModelLaw,general_κ,fixed_κ,Measure.prod_add,Measure.dirac_prod_dirac,
    withDensity_add_measure,dirac_withDensity,mixtureFamily,general_p,general_g,
    Fin.sum_univ_succ,fixed_binary]

theorem printed_general_subset_mixture_refuted :
  ¬ (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
  (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (p : (Fin τ → ℝ) → Fin M → ℝ)
  (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (Θ : Set (Fin τ → ℝ)) (θ : Fin τ → ℝ) (hθ : θ ∈ Θ)
  (hp : ∀ t ∈ Θ, (∀ m, 0 ≤ p t m) ∧ (∑ m,p t m)=1)
  (hg : ∀ t ∈ Θ, ∀ m, Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
  (hgn : ∀ t ∈ Θ, ∀ m y x, 0 ≤ g m y x t)
  (hnorm : ∀ t ∈ Θ, ∀ m x, (∫⁻ y, ENNReal.ofReal (g m y x t) ∂κ)=1)
  (S : Finset (Fin M)) (hS : S.Nonempty) (hproper : S ≠ Finset.univ)
  (hsubset : ∀ m, m ∉ S → p θ m=0)
  (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=
    conditionalModelLaw νX κ (mixtureFamily p g) θ)
  (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n, Measurable (that n))
  (hthat : ∀ n ω, that n ω ∈ Θ)
  (hmax : ∀ n ω t, t ∈ Θ → sampleLikelihood X Y (mixtureFamily p g) n ω t ≤
    sampleLikelihood X Y (mixtureFamily p g) n ω (that n ω)),
    CP μ that θ ∧ EfficientInModel μ that (conditionalModelLaw νX κ (mixtureFamily p g)) θ) := by
  intro h
  let μ : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  let x : Fin 0 → ℝ := fun j => Fin.elim0 j
  let X : ℕ → ULift.{u} Unit → Fin 0 → ℝ := fun _ _ => x
  let Y : ℕ → ULift.{u} Unit → ℝ := fun _ _ => 0
  have hcp := (h μ X Y (fixed_iid_const μ (x,0)) (Measure.dirac x) general_κ
    general_p general_g disjointMixtureParameterSet ![1,0,1/4]
    (by apply (general_box _).mpr; norm_num)
    (by
      intro t ht
      have hb := (general_box t).mp ht
      constructor
      · intro m; fin_cases m <;> simp [general_p] <;> linarith only [hb.1.1,hb.1.2]
      · simp [general_p,Fin.sum_univ_succ])
    (fun t ht m => general_g_meas t m)
    (by
      intro t ht m y x
      have hb := (general_box t).mp ht
      fin_cases m
      · exact fixed_binary_nonneg hb.2.1 y
      · exact fixed_binary_nonneg ⟨by linarith only [hb.2.2.1],by linarith only [hb.2.2.2]⟩ (y-2))
    general_g_norm {0} (by simp)
    (by intro he; have := congrArg (fun S : Finset (Fin 2) => (1 : Fin 2) ∈ S) he; simp at this)
    (by intro m hm; fin_cases m <;> simp_all [general_p])
    (by simpa [μ,X,Y,x,Measure.map_const] using general_true.symm)
    (fun _ _ => ![1,0,3/4]) (fun _ => measurable_const)
    (by intros; apply (general_box _).mpr; norm_num)
    (by
      intro n ω t ht
      have hb := (general_box t).mp ht
      unfold sampleLikelihood
      apply Finset.prod_le_prod₀
      · intro i hi; rw [general_density_zero]; exact mul_nonneg hb.1.1 (sub_nonneg.mpr hb.2.1.2)
      · intro i hi
        simp only [Y,X,general_density_zero]
        norm_num
        exact mul_le_one₀ hb.1.2 (sub_nonneg.mpr hb.2.1.2) (by linarith only [hb.2.1.1]))).1
  have he := probability_limit_unique μ (fun _ _ => (![1,0,3/4] : Fin 3 → ℝ))
    ![1,0,3/4] ![1,0,1/4] (fixed_cp_const μ _) hcp
  have he2 := congrFun he 2
  norm_num at he2

example : (type_of% @printed_general_subset_mixture_refuted.{u}) ↔
    ¬ (type_of% @AronowAudit.P001.printed_general_subset_mixture_consistency_efficiency.{u}) := Iff.rfl


private def subset_mle (n : ℕ) (s : Fin n → Fin 4) : Fin 3 → ℝ :=
  Classical.choose ((finite_mixture_compact_attainment.2.2.2 n s).2)
private theorem subset_mle_spec (n : ℕ) (s : Fin n → Fin 4) :
    subset_mle n s ∈ disjointMixtureParameterSet ∧
    ∀ u ∈ disjointMixtureParameterSet,
      disjointMixtureLikelihood s u ≤ disjointMixtureLikelihood s (subset_mle n s) :=
  Classical.choose_spec ((finite_mixture_compact_attainment.2.2.2 n s).2)
private def subset_ν : Measure (Fin 4) :=
  ∑ j : Fin 4, ENNReal.ofReal (disjointMixture 1 (1/3) (1/4) j) • Measure.dirac j
private instance subset_ν_probability : IsProbabilityMeasure subset_ν := by
  constructor
  simp only [subset_ν,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply_of_mem,
    Set.mem_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => unused_component_nonidentification_supporting.2.2.1 j)]
  rw [unused_component_nonidentification_supporting.2.1]
  norm_num

theorem printed_subset_full_vector_consistency_refuted :
  ¬ (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → Fin 4) (hiid : IID μ X) (b0 : ℝ) (hb : b0∈Set.Icc (1/4 : ℝ) (3/4))
   (hlaw : μ.map (X 0)=∑ j : Fin 4,ENNReal.ofReal (disjointMixture 1 (1/3) b0 j) • Measure.dirac j)
   (that : ∀ n : ℕ,(Fin n → Fin 4) → Fin 3 → ℝ)
   (hvalid : ∀ n s,that n s 0∈Set.Icc (0 : ℝ) 1 ∧ that n s 1∈Set.Icc (0 : ℝ) 1 ∧
      that n s 2∈Set.Icc (1/4 : ℝ) (3/4))
   (hmax : ∀ n s p a b,p∈Set.Icc (0 : ℝ) 1 → a∈Set.Icc (0 : ℝ) 1 → b∈Set.Icc (1/4 : ℝ) (3/4) →
     (∏ i,disjointMixture p a b (s i)) ≤ 
       ∏ i,disjointMixture (that n s 0) (that n s 1) (that n s 2) (s i)),
    CP μ (fun n ω => that n (firstSample X n ω)) (![1,1/3,b0] : Fin 3 → ℝ)) := by
  intro h
  let μ := PrintedConfidence.liftStreamLaw.{u} subset_ν
  let X : ℕ → (ℕ → ULift.{u} (Fin 4)) → Fin 4 := PrintedConfidence.streamObservation
  have hiid : IID μ X := (PrintedConfidence.lift_stream_iid.{u} subset_ν).1
  have hlaw : μ.map (X 0)=subset_ν := (PrintedConfidence.lift_stream_iid.{u} subset_ν).2
  have hv : ∀ n s, subset_mle n s 0 ∈ Set.Icc (0 : ℝ) 1 ∧
      subset_mle n s 1 ∈ Set.Icc (0 : ℝ) 1 ∧
      subset_mle n s 2 ∈ Set.Icc (1/4 : ℝ) (3/4) := by
    intro n s
    exact (general_box _).mp (subset_mle_spec n s).1
  have hm : ∀ n s p a b, p ∈ Set.Icc (0 : ℝ) 1 → a ∈ Set.Icc (0 : ℝ) 1 →
      b ∈ Set.Icc (1/4 : ℝ) (3/4) →
      (∏ i, disjointMixture p a b (s i)) ≤
        ∏ i, disjointMixture (subset_mle n s 0) (subset_mle n s 1) (subset_mle n s 2) (s i) := by
    intro n s p a b hp ha hb
    simpa [disjointMixtureLikelihood] using
      (subset_mle_spec n s).2 ![p,a,b] ((general_box _).mpr (by simpa using And.intro hp (And.intro ha hb)))
  have ha := h μ X hiid (1/4) (by norm_num) hlaw subset_mle hv hm
  have hb := h μ X hiid (3/4) (by norm_num)
    (by rw [← unused_component_nonidentification_supporting.1]; exact hlaw) subset_mle hv hm
  have he := probability_limit_unique μ _ _ _ ha hb
  have he2 := congrFun he 2
  norm_num at he2

example : (type_of% @printed_subset_full_vector_consistency_refuted.{u}) ↔
    ¬ (type_of% @AronowAudit.P001.printed_subset_full_vector_consistency.{u}) := Iff.rfl

end
end AronowAudit.P001.Wave1
