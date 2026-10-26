import AronowAudit.Shared.MapTailB.DensityQMD
import AronowAudit.P001.Wave1.Gap.DecideB

/-!
P001-T12: normal efficiency on a common measurable set of full model probability.
Score transport uses measurable versions on this set.
-/

open MeasureTheory ProbabilityTheory Filter AronowAudit.P001
open scoped BigOperators ENNReal NNReal Topology Matrix

namespace AronowAudit.P001.Wave1

noncomputable section
local instance instDecidableTailBRegularEfficiency (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false
set_option linter.unusedVariables false

theorem TailB_regular_local_alternative_score_identity {K τ : ℕ}
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
  (hg : ∀ t ∈ Metric.ball θ δ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hpos : ∀ t ∈ Metric.ball θ δ, ∀ y x, 0 ≤ g y x t)
  (hnorm : ∀ t ∈ Metric.ball θ δ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (hqm : QuadraticMeanModel νX κ g θ)
  (hs2 : ∀ j, MemLp (fun xy : (Fin K → ℝ) × ℝ => modelScore g xy.2 xy.1 θ j)
    2 (conditionalModelLaw νX κ g θ))
  (hs0 : ∀ j, mean (conditionalModelLaw νX κ g θ)
    (fun xy => modelScore g xy.2 xy.1 θ j)=0)
  (I : Matrix (Fin τ) (Fin τ) ℝ)
  (hI : ∀ j k, I j k=mean (conditionalModelLaw νX κ g θ)
    (fun xy => modelScore g xy.2 xy.1 θ j*modelScore g xy.2 xy.1 θ k))
  (hpd : I.PosDef)
  (T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ)
  (ψ : (Fin K → ℝ) × ℝ → Fin τ → ℝ)
  (hregular : RegularAL (conditionalModelLaw νX κ g) θ T ψ) :
  (∀ j k, mean (conditionalModelLaw νX κ g θ)
    (fun xy => ψ xy j*modelScore g xy.2 xy.1 θ k)=if j=k then 1 else 0) ∧
  ∀ a : Fin τ → ℝ, 0 ≤ ∑ j, ∑ k,
    a j*(covarianceMatrix (conditionalModelLaw νX κ g θ) ψ j k-I⁻¹ j k)*a k
 := by
  exact regular_local_alternative_score_identity_proof νX κ g θ δ hδ hg hpos hnorm hqm
    hs2 hs0 I hI hpd T ψ hregular


theorem identified_mixture_ml_normal_efficiency_common_regular_set {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ)
   (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
   (hinterior : Metric.ball θ δ⊆Θ)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ (mixtureFamily p g) θ)
   (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
   (hSfull : (μ.map (fun ω => (X 0 ω,Y 0 ω))) S = 1)
   (hpositive : ∀ xy ∈ S,∀ t∈Metric.ball θ δ,
     0 < mixtureFamily p g xy.2 xy.1 t)
   (hdiff : ∀ xy ∈ S,ContDiffOn ℝ 2
     (fun t => Real.log (mixtureFamily p g xy.2 xy.1 t)) (Metric.ball θ δ))
   (hs2 : ∀ j,MemLp (fun ω => modelScore (mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j) 2 μ)
   (hszero : ∀ j,mean μ (fun ω => modelScore (mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j)=0)
   (hinfo : (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ).PosDef)
   (hHinfo : populationHessian μ (X 0) (Y 0) (mixtureFamily p g) θ=
     -informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)
   (hHcont : ContinuousAt (populationHessian μ (X 0) (Y 0) (mixtureFamily p g)) θ)
   (hHi : ∀ t∈Metric.ball θ δ,∀ j k,
     Integrable (fun ω => modelHessian (mixtureFamily p g) (Y 0 ω) (X 0 ω) t j k) μ)
   (ΔH : ℕ → Ω → ℝ) (hHbound : ∀ n ω t,t∈Metric.ball θ δ → ∀ j k,
     |sampleHessian X Y (mixtureFamily p g) n ω t j k-
       populationHessian μ (X 0) (Y 0) (mixtureFamily p g) t j k| ≤ ΔH n ω)
   (hHlim : CP μ ΔH 0)
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLikelihood X Y (mixtureFamily p g) n ω t ≤ 
     sampleLikelihood X Y (mixtureFamily p g) n ω (that n ω))
   
  (hcompact : IsCompact Θ) (hθ : θ ∈ Θ)
  (hlog : ∀ t ∈ Θ, Integrable (fun ω =>
    Real.log (mixtureFamily p g (Y 0 ω) (X 0 ω) t)) μ)
  (hposAll : ∀ xy ∈ S, ∀ t ∈ Θ, 0 < mixtureFamily p g xy.2 xy.1 t)
  (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g)) Θ)
  (hunique : ∀ t ∈ Θ,
    expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t ≤
      expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ ∧
    (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t =
      expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ → t=θ))
  (Δ : ℕ → Ω → ℝ) (hΔ : CP μ Δ 0)
  (hbound : ∀ n ω t, t ∈ Θ →
    |sampleLogLikelihood X Y (mixtureFamily p g) n ω t-
      expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t| ≤ Δ n ω)
  (hqm : QuadraticMeanModel νX κ (mixtureFamily p g) θ) :
   CP μ that θ ∧ WeakLimit μ (fun n ω => Real.sqrt n • (that n ω-θ))
     (normalVectorLaw (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)⁻¹) ∧
  (∀ T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ,
    ∀ ψ : (Fin K → ℝ) × ℝ → Fin τ → ℝ,
    RegularAL (conditionalModelLaw νX κ (mixtureFamily p g)) θ T ψ →
    ∀ a : Fin τ → ℝ, 0 ≤ ∑ j, ∑ k, a j*
      (covarianceMatrix (conditionalModelLaw νX κ (mixtureFamily p g) θ) ψ j k-
       (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)⁻¹ j k)*a k) := by
  have hmixmeas (t : Fin τ → ℝ) (ht : t ∈ Θ) :
      Measurable (fun xy : (Fin K → ℝ) × ℝ => mixtureFamily p g xy.2 xy.1 t) := by
    exact Finset.measurable_sum Finset.univ (fun m _ => (hg t ht m).const_mul (p t m))
  have hmixnonneg (t : Fin τ → ℝ) (ht : t ∈ Θ) (y : ℝ) (x : Fin K → ℝ) :
      0 ≤ mixtureFamily p g y x t := by
    exact Finset.sum_nonneg (fun m _ => mul_nonneg ((hp t ht).1 m) (hnonneg t ht m y x))
  have hmixnorm (t : Fin τ → ℝ) (ht : t ∈ Θ) (x : Fin K → ℝ) :
      (∫⁻ y, ENNReal.ofReal (mixtureFamily p g y x t) ∂κ) = 1 := by
    have hnn (y : ℝ) (m : Fin M) : 0 ≤ p t m * g m y x t :=
      mul_nonneg ((hp t ht).1 m) (hnonneg t ht m y x)
    simp_rw [mixtureFamily, ENNReal.ofReal_sum_of_nonneg (fun m _ => hnn _ m),
      ENNReal.ofReal_mul ((hp t ht).1 _)]
    have hm (m : Fin M) : Measurable (fun y : ℝ => ENNReal.ofReal (g m y x t)) :=
      ((hg t ht m).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
    rw [lintegral_finsetSum Finset.univ
      (f := fun m (y : ℝ) => ENNReal.ofReal (p t m) * ENNReal.ofReal (g m y x t))
      (fun m _ => (hm m).const_mul _)]
    simp_rw [lintegral_const_mul _ (hm _), hnorm t ht, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => (hp t ht).1 m), (hp t ht).2]
    norm_num
  have hconsistent : CP μ that θ := DecideB_product_mle_consistency μ X Y hiid
    (mixtureFamily p g) Θ hcompact θ hθ S hS hSfull
    (fun xy hxy => hposAll xy hxy θ hθ) hM hunique that hthat hmax Δ hΔ hbound
  refine ⟨hconsistent, ?_, ?_⟩
  · exact product_identified_mixture_ml_normal_limit_common_regular_set μ X Y hiid
      νX κ p g Θ θ δ hδ hinterior hp hg hnonneg hnorm htrue S hS hSfull hpositive hdiff
      hs2 hszero hinfo hHinfo hHcont hHi ΔH hHbound hHlim that hmeas hthat hmax hconsistent
  · have hθball : θ ∈ Metric.ball θ δ := Metric.mem_ball_self hδ
    let v := DecideB_scoreVersion (mixtureFamily p g) S θ
    have hv : Measurable v := DecideB_scoreVersion_measurable (mixtureFamily p g)
      S hS (Metric.ball θ δ) Metric.isOpen_ball θ hθball
      (fun t ht => hmixmeas t (hinterior ht)) hdiff
    have hbaseS : ∀ᵐ xy ∂μ.map (fun ω => (X 0 ω, Y 0 ω)), xy ∈ S :=
      (mem_ae_iff_prob_eq_one hS).mpr hSfull
    have hvae (j : Fin τ) : (fun xy => v xy j) =ᵐ[μ.map (fun ω => (X 0 ω, Y 0 ω))]
        (fun xy => modelScore (mixtureFamily p g) xy.2 xy.1 θ j) := by
      filter_upwards [hbaseS] with xy hxy
      simp [v, DecideB_scoreVersion, hxy]
    have hsmeas (j : Fin τ) : AEStronglyMeasurable
        (fun xy : (Fin K → ℝ) × ℝ => modelScore (mixtureFamily p g) xy.2 xy.1 θ j)
        (μ.map (fun ω => (X 0 ω, Y 0 ω))) :=
      (((measurable_pi_apply j).comp hv).aestronglyMeasurable).congr (hvae j)
    have hsmodel (j : Fin τ) : MemLp
        (fun xy : (Fin K → ℝ) × ℝ => modelScore (mixtureFamily p g) xy.2 xy.1 θ j)
        2 (conditionalModelLaw νX κ (mixtureFamily p g) θ) := by
      rw [← htrue]
      exact (memLp_map_measure_iff (hsmeas j) (hiid.1 0).aemeasurable).2 (hs2 j)
    have hsmodel0 (j : Fin τ) : mean (conditionalModelLaw νX κ (mixtureFamily p g) θ)
        (fun xy => modelScore (mixtureFamily p g) xy.2 xy.1 θ j) = 0 := by
      rw [← htrue]
      exact (integral_map (hiid.1 0).aemeasurable (hsmeas j)).trans (hszero j)
    have hI (j k : Fin τ) : informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ j k =
        mean (conditionalModelLaw νX κ (mixtureFamily p g) θ)
          (fun xy => modelScore (mixtureFamily p g) xy.2 xy.1 θ j *
            modelScore (mixtureFamily p g) xy.2 xy.1 θ k) := by
      rw [← htrue]
      exact (integral_map (hiid.1 0).aemeasurable ((hsmeas j).mul (hsmeas k))).symm
    intro T ψ hregular
    exact (TailB_regular_local_alternative_score_identity νX κ (mixtureFamily p g) θ δ hδ
      (fun t ht => hmixmeas t (hinterior ht))
      (fun t ht => hmixnonneg t (hinterior ht))
      (fun t ht => hmixnorm t (hinterior ht)) hqm hsmodel hsmodel0
      (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ) hI hinfo T ψ hregular).2

end
end AronowAudit.P001.Wave1
