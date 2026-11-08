import AronowAudit.P001.P001_Foundations

namespace AronowAudit.P001.ConfidenceInstances
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The exact four-atom distribution required by the two pooled-MLE counterexamples. -/
def klLaw : Measure (ℝ × ℝ) :=
  (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
  (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1)

instance klLaw_probability : IsProbabilityMeasure klLaw := by
  constructor
  norm_num [klLaw,Measure.add_apply,Measure.smul_apply]
  rw [show (8 : ℝ≥0∞)⁻¹=1/8 from (one_div _).symm,← ENNReal.add_div,← ENNReal.add_div,← ENNReal.add_div]
  norm_num
  exact ENNReal.div_self (a := 8) (by norm_num) (by simp)

abbrev KLStream := ℕ → ℝ × ℝ

def klStreamLaw : Measure KLStream := Measure.infinitePi (fun _ : ℕ => klLaw)
instance klStreamLaw_probability : IsProbabilityMeasure klStreamLaw := by
  dsimp [klStreamLaw]
  infer_instance

def klX (i : ℕ) (ω : KLStream) : ℝ := (ω i).1
def klY (i : ℕ) (ω : KLStream) : ℝ := (ω i).2

/-- This witnesses every probabilistic premise of both original T7 contracts. -/
theorem kl_original_premises :
    IID klStreamLaw (fun i ω => (klX i ω,klY i ω)) ∧
    klStreamLaw.map (fun ω => (klX 0 ω,klY 0 ω)) = klLaw := by
  have he (i : ℕ) : (fun ω : KLStream => (klX i ω,klY i ω))=(fun ω => ω i) := rfl
  have hm (i : ℕ) : Measurable (fun ω : KLStream => ω i) := measurable_pi_apply i
  have hlaw (i : ℕ) : klStreamLaw.map (fun ω : KLStream => ω i)=klLaw :=
    Measure.infinitePi_map_eval (fun _ : ℕ => klLaw) i
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro i
    exact hm i
  · change iIndepFun (fun i (ω : KLStream) => ω i) klStreamLaw
    exact iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
  · intro i
    exact ⟨(hm i).aemeasurable,(hm 0).aemeasurable,(hlaw i).trans (hlaw 0).symm⟩
  · exact hlaw 0

/-- Both complete counterexample declarations are instantiated on this actual iid law. -/
theorem kl_original_conclusions :
    CP klStreamLaw (fun n ω => clip (1/10) (9/10) (sampleMean klY n ω)) (1/2) ∧
    ¬ CP klStreamLaw (fun n ω => clip (1/10) (9/10) (sampleMean klY n ω)) (1/4) ∧
    ¬ CP klStreamLaw (fun n ω => clip (1/10) (9/10) (sampleMean klY n ω)) (3/4) := by
  have h := conditional_kl_mle_wrong_target_supporting klStreamLaw klX klY
    kl_original_premises.1 kl_original_premises.2
  exact h.2

/-- A genuine nondegenerate normal experiment: estimates shrink as one over root n. -/
def ciEstimate (n : ℕ) (ω : ℝ) : ℝ := ω / Real.sqrt n
def ciVariance (n : ℕ) (_ : ℝ) : ℝ := 1/(n : ℝ)
def ciAlpha : ℝ := 2*(1-prob (gaussianReal 0 1) (Set.Iic 1))

theorem ci_alpha_admissible : ciAlpha ∈ Set.Ioo (0 : ℝ) 1 := by
  have h0 : ProbabilityTheory.cdf (gaussianReal 0 1) 0=1/2 := by
    rw [ProbabilityTheory.cdf_eq_real]
    exact centered_gaussian_half_mass 1 (by norm_num)
  have h01 := P053.NormalCompletion.strictMono_normal_cdf (by norm_num : (0 : ℝ)<1)
  have h12 := P053.NormalCompletion.strictMono_normal_cdf (by norm_num : (1 : ℝ)<2)
  have h2 := ProbabilityTheory.cdf_le_one (gaussianReal 0 1) 2
  unfold ciAlpha prob
  rw [← measureReal_def,← ProbabilityTheory.cdf_eq_real]
  constructor <;> linarith

theorem ci_normal_limit :
    CD (gaussianReal 0 1) (fun n ω => Real.sqrt n*(ciEstimate n ω-0))
      (gaussianReal 0 ⟨(1 : ℝ)^2,sq_nonneg _⟩) := by
  have hv : (⟨(1 : ℝ)^2,sq_nonneg (1 : ℝ)⟩ : ℝ≥0)=1 := by ext; norm_num
  rw [hv]
  intro x hx
  have he : (fun n : ℕ => cdf (gaussianReal 0 1)
      (fun ω => Real.sqrt n*(ciEstimate n ω-0)) x) =ᶠ[atTop]
      (fun _ => prob (gaussianReal 0 1) (Set.Iic x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hs : Real.sqrt (n : ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
    have hf : (fun ω : ℝ => Real.sqrt n*(ciEstimate n ω-0))=id := by
      funext ω
      dsimp [ciEstimate]
      field_simp [hs]
      ring
    rw [hf]
    rfl
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => prob (gaussianReal 0 1) (Set.Iic x))
    atTop (nhds (prob (gaussianReal 0 1) (Set.Iic x)))).congr' he.symm

theorem ci_variance_consistent : VarianceConsistent (gaussianReal 0 1) ciVariance ((1 : ℝ)^2) := by
  intro ε hε
  have he : (fun n : ℕ => prob (gaussianReal 0 1)
      {ω | ε≤dist ((n : ℝ)*ciVariance n ω) ((1 : ℝ)^2)}) =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    simp [ciVariance,hn0,not_le_of_gt hε,prob]
  exact tendsto_const_nhds.congr' he.symm

/-- Every hypothesis of the original confidence-interval theorem has an actual witness. -/
theorem ci_original_premises :
    (∀ n,Measurable (ciEstimate n)) ∧ (∀ n,Measurable (ciVariance n)) ∧
    (∀ n ω,0≤ciVariance n ω) ∧ 0<(1 : ℝ) ∧ ciAlpha∈Set.Ioo (0 : ℝ) 1 ∧
    prob (gaussianReal 0 1) (Set.Iic (1 : ℝ))=1-ciAlpha/2 ∧
    CD (gaussianReal 0 1) (fun n ω => Real.sqrt n*(ciEstimate n ω-0))
      (gaussianReal 0 ⟨(1 : ℝ)^2,sq_nonneg _⟩) ∧
    VarianceConsistent (gaussianReal 0 1) ciVariance ((1 : ℝ)^2) := by
  refine ⟨?_,?_,?_,by norm_num,ci_alpha_admissible,?_,ci_normal_limit,ci_variance_consistent⟩
  · intro n
    fun_prop [ciEstimate]
  · intro n
    exact measurable_const
  · intro n ω
    exact div_nonneg (by norm_num) (Nat.cast_nonneg n)
  · unfold ciAlpha
    ring

/-- The original normal-coverage theorem applies to the concrete experiment. -/
theorem ci_original_conclusion :
    ∃ c : ℝ,1-ciAlpha≤c ∧
      Tendsto (fun n : ℕ => prob (gaussianReal 0 1) {ω | (0 : ℝ)∈Set.Ioo
        (ciEstimate n ω-Real.sqrt (ciVariance n ω))
        (ciEstimate n ω+Real.sqrt (ciVariance n ω))}) atTop (nhds c) := by
  rcases ci_original_premises with ⟨hthat,hvhat,hpos,hφ,hα,hz,hAN,hVC⟩
  simpa only [one_mul] using normal_approximation_confidence_interval (gaussianReal 0 1)
    ciEstimate ciVariance hthat hvhat hpos 0 1 ciAlpha 1 hφ hα hz hAN hVC

/-- A one-dimensional Gaussian covariate with an everywhere-positive vector PDF. -/
def pdaX (ω : ℝ) : Fin 1 → ℝ := fun _ => ω
def pdaDensity (x : Fin 1 → ℝ) : ℝ := gaussianPDFReal 0 1 (x 0)

theorem pda_vector_pdf : HasVectorPDF ((gaussianReal 0 1).map pdaX) pdaDensity := by
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hmp : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have hmeas : Measurable pdaDensity :=
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply 0)
  refine ⟨hmeas.aemeasurable,fun x => gaussianPDFReal_nonneg _ _ _,?_,?_⟩
  · exact hmp.integrable_comp_of_integrable (integrable_gaussianPDFReal 0 1)
  · ext A hA
    rw [Measure.map_apply (by fun_prop [pdaX]) hA,
      gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0)≠0),
      withDensity_apply _ ((by fun_prop [pdaX] : Measurable pdaX) hA),
      withDensity_apply _ hA]
    have hchange := hmp.symm.setLIntegral_comp_preimage_emb e.symm.measurableEmbedding
      (fun x : Fin 1 → ℝ => ENNReal.ofReal (pdaDensity x)) A
    change (∫⁻ a in pdaX ⁻¹' A, ENNReal.ofReal (gaussianPDFReal 0 1 a))=
      ∫⁻ x in A, ENNReal.ofReal (pdaDensity x) at hchange
    exact hchange

/-- Every premise of the original PDA uniqueness theorem holds in this nonempty,
positive-dimensional experiment, with zero outcomes and the genuine Gaussian density. -/
theorem pda_original_premises :
    Measurable pdaX ∧
    (∀ k : Fin 1,Integrable (fun ω => pdaX ω k) (gaussianReal 0 1)) ∧
    Integrable (fun _ : ℝ => (0 : ℝ)) (gaussianReal 0 1) ∧
    HasVectorPDF ((gaussianReal 0 1).map pdaX) pdaDensity ∧
    IsOpen (Set.univ : Set (Fin 1 → ℝ)) ∧
    (fun k : Fin 1 => mean (gaussianReal 0 1) (fun ω => pdaX ω k))∈Set.univ ∧
    (∀ x : Fin 1 → ℝ,x∈Set.univ → 0<pdaDensity x) ∧
    IsCEF (gaussianReal 0 1) pdaX (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) ∧
    ContinuousOn (fun _ : Fin 1 → ℝ => (0 : ℝ)) Set.univ ∧
    HasDerivAt (fun t : ℝ => (fun _ : Fin 1 → ℝ => (0 : ℝ))
      (Function.update (fun j => mean (gaussianReal 0 1) (fun ω => pdaX ω j)) 0
        (mean (gaussianReal 0 1) (fun ω => pdaX ω 0)+t))) 0 0 := by
  refine ⟨?_,?_,integrable_const 0 ,pda_vector_pdf,isOpen_univ,Set.mem_univ _,?_,?_,
    continuous_const.continuousOn,hasDerivAt_const _ _⟩
  · fun_prop [pdaX]
  · intro k
    exact (memLp_id_gaussianReal (2 : ℝ≥0)).integrable one_le_two
  · intro x hx
    exact gaussianPDFReal_pos _ _ _ (by norm_num)
  · exact ⟨measurable_const,integrable_const 0,integrable_const 0,by intros; simp⟩

#print axioms kl_original_premises
#print axioms kl_original_conclusions
#print axioms ci_original_premises
#print axioms ci_original_conclusion
#print axioms pda_original_premises
end
end AronowAudit.P001.ConfidenceInstances
