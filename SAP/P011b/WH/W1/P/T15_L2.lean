import SAP.P011b.WH.W1.Leaves
import AronowAudit.P011.Wave1.Gap.GLP011B4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W1.P.T15_L2

open MeasureTheory ProbabilityTheory SAP.P011b.WH.W1.P.T15_L2
open scoped BigOperators Classical

noncomputable section

lemma iIndepFun_map {ι : Type*} [DecidableEq ι] {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {μ : Measure Ω} {g : Ω → Ξ}
    (hg : Measurable g) {f : ∀ i, Ξ → β i}
    (hf : ∀ i, Measurable (f i))
    (h : iIndepFun (fun i => f i ∘ g) μ) :
    iIndepFun f (μ.map g) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have hmeas : MeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) :=
    Finset.measurableSet_biInter S (fun i hi => (hsets i hi).preimage (hf i))
  calc
    (μ.map g) (⋂ i ∈ S, f i ⁻¹' sets i) =
        μ (⋂ i ∈ S, (f i ∘ g) ⁻¹' sets i) := by
      rw [Measure.map_apply hg hmeas]
      congr 1
      ext x
      simp
    _ = ∏ i ∈ S, μ ((f i ∘ g) ⁻¹' sets i) := h S (sets := sets) hsets
    _ = ∏ i ∈ S, (μ.map g) (f i ⁻¹' sets i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Measure.map_apply hg ((hsets i hi).preimage (hf i))]
      congr 1

def blockVector (upper : Bool) (a : AronowAudit.P011.Wave1.star_Source) : Fin 4 → ℝ :=
  AronowAudit.P011.starBlock upper a.1 a.2

lemma blockIndex_at (K : ℕ) (b : Fin K) (r : Fin 4) :
    AronowAudit.P011.blockIndex (by decide) (SAP.P011b.w1StarAt K b r) = b := by
  apply Fin.ext
  simp [AronowAudit.P011.blockIndex, SAP.P011b.w1StarAt] <;> omega

lemma localIndex_at (K : ℕ) (b : Fin K) (r : Fin 4) :
    AronowAudit.P011.localIndex (by decide) (SAP.P011b.w1StarAt K b r) = r := by
  apply Fin.ext
  simp [AronowAudit.P011.localIndex, SAP.P011b.w1StarAt] <;> omega

lemma extract_source (upper : Bool) (K : ℕ) (b : Fin K) :
    (SAP.P011b.w1StarExtract K b) ∘ AronowAudit.P011.Wave1.star_source upper K =
      fun u => blockVector upper (u b) := by
  funext u r
  simp only [Function.comp_apply, SAP.P011b.w1StarExtract, blockVector,
    AronowAudit.P011.Wave1.star_source]
  rw [blockIndex_at, localIndex_at]

lemma one_block_law (upper : Bool) :
    (AronowAudit.P011.starModel upper 1).law =
      (PMF.uniformOfFintype AronowAudit.P011.Wave1.star_Source).toMeasure.map
        (blockVector upper) := by
  let e : (Fin 1 → AronowAudit.P011.Wave1.star_Source) ≃ AronowAudit.P011.Wave1.star_Source :=
    Equiv.funUnique (Fin 1) AronowAudit.P011.Wave1.star_Source
  have he : AronowAudit.P011.Wave1.star_source upper 1 = blockVector upper ∘ e := by
    funext u i
    fin_cases i
    all_goals norm_num [AronowAudit.P011.Wave1.star_source, blockVector,
      Equiv.funUnique, e, AronowAudit.P011.blockIndex, AronowAudit.P011.localIndex]
  change AronowAudit.P011.uniformLaw (AronowAudit.P011.Wave1.star_source upper 1) = _
  rw [he]
  calc
    AronowAudit.P011.uniformLaw (blockVector upper ∘ e) =
        AronowAudit.P011.uniformLaw (blockVector upper) :=
      AronowAudit.P011.NewFiniteCompletion.uniformLaw_equiv e (blockVector upper)
    _ = (PMF.uniformOfFintype AronowAudit.P011.Wave1.star_Source).toMeasure.map
          (blockVector upper) := by
      rw [AronowAudit.P011.uniformLaw]
      exact (PMF.toMeasure_map (blockVector upper) (PMF.uniformOfFintype _)
        (measurable_of_finite _)).symm

lemma measurable_extract (K : ℕ) (b : Fin K) :
    Measurable (SAP.P011b.w1StarExtract K b) := by
  rw [measurable_pi_iff]
  intro r
  exact measurable_pi_apply (SAP.P011b.w1StarAt K b r)

end
end SAP.P011b.WH.W1.P.T15_L2

open MeasureTheory ProbabilityTheory SAP.P011b.WH.W1.P.T15_L2

theorem SAP.P011b.WH.W1.T15_L2_proof : SAP.P011b.WH.W1.T15_L2 := by
  intro upper K hK
  let A := AronowAudit.P011.Wave1.star_Source
  let ν : Measure A := (PMF.uniformOfFintype A).toMeasure
  let μ : Measure (Fin K → A) := (PMF.uniformOfFintype (Fin K → A)).toMeasure
  have hpi : μ = Measure.pi (fun _ : Fin K => ν) := by
    dsimp [μ, ν, A]
    exact AronowAudit.P011.Wave1.star_uniform_pi
      (fun _ : Fin K => AronowAudit.P011.Wave1.star_Source)
  have hEval : iIndepFun (fun b : Fin K => fun u : Fin K → A => u b) μ := by
    rw [hpi]
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hBlock : iIndepFun (fun b : Fin K => fun u : Fin K → A => blockVector upper (u b)) μ := by
    simpa only [Function.comp_def] using
      hEval.comp (fun _ => blockVector upper) (fun _ => measurable_of_finite _)
  have hLaw : (AronowAudit.P011.starModel upper K).law =
      μ.map (AronowAudit.P011.Wave1.star_source upper K) := by
    change AronowAudit.P011.uniformLaw (AronowAudit.P011.Wave1.star_source upper K) = _
    rw [AronowAudit.P011.uniformLaw]
    dsimp [μ]
    exact (PMF.toMeasure_map (AronowAudit.P011.Wave1.star_source upper K)
      (PMF.uniformOfFintype _) (measurable_of_finite _)).symm
  have hSourceExtract : iIndepFun
      (fun b : Fin K => (SAP.P011b.w1StarExtract K b) ∘
        AronowAudit.P011.Wave1.star_source upper K) μ := by
    simpa only [extract_source] using hBlock
  have hInd : iIndepFun (fun b : Fin K => SAP.P011b.w1StarExtract K b)
      (AronowAudit.P011.starModel upper K).law := by
    rw [hLaw]
    exact SAP.P011b.WH.W1.P.T15_L2.iIndepFun_map (measurable_of_finite _)
      (fun b => SAP.P011b.WH.W1.P.T15_L2.measurable_extract K b) hSourceExtract
  refine ⟨hInd, ?_⟩
  intro b
  have hEvalMap : μ.map (fun u : Fin K → A => u b) = ν := by
    rw [hpi]
    exact (measurePreserving_eval (fun _ : Fin K => ν) b).map_eq
  calc
    (AronowAudit.P011.starModel upper K).law.map (SAP.P011b.w1StarExtract K b) =
        μ.map (SAP.P011b.w1StarExtract K b ∘ AronowAudit.P011.Wave1.star_source upper K) := by
      rw [hLaw, Measure.map_map (SAP.P011b.WH.W1.P.T15_L2.measurable_extract K b)
        (measurable_of_finite _)]
    _ = μ.map (blockVector upper ∘ fun u : Fin K → A => u b) := by
      simpa only [Function.comp_def] using
        congrArg (fun f => μ.map f) (extract_source upper K b)
    _ = (μ.map (fun u : Fin K → A => u b)).map (blockVector upper) := by
      rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    _ = ν.map (blockVector upper) := by rw [hEvalMap]
    _ = (AronowAudit.P011.starModel upper 1).law := (one_block_law upper).symm

