import AronowAudit.P061.P061_Foundations
import AronowAudit.P061.P061_Refutations
import AronowAudit.P061.P061_SamplingCompletion

/-! P061 statements with explicit statistical moment domains and design laws.
Printed false general existence assertions are refuted, never used as premises. -/
namespace AronowAudit.P061.PaperDomains
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

/-- T20 on the full atomic domain, with existence of the displayed signed
expectations made explicit, as required by the target's own definitions. -/
theorem covariate_adjustment_T20 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y F : OutcomeSchedule Ω N) (d : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hy : TargetedMoment D g y d)
    (hF : ∀ i, Integrable D (F i)) (hFd : TargetedMoment D g F d)
    (hc : ∀ i, expectation D (fun z => (if g i z=d then F i z else 0)/pi D g i d)=
      expectation D (F i)) :
    Integrable D (regressionEstimator D g y F d) ∧
      expectation D (regressionEstimator D g y F d)=aepo D g y d :=
  covariate_adjustment D g y F d hN hp hy hF hFd hc

/-- The corrected T16 first-moment statement retains positive population,
positive exposure probabilities and actual integrability of the estimator. -/
theorem ht_unbiased_T16_corrected {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hy : TargetedMoment D g y d) :
    Integrable D (ht D g y d) ∧ expectation D (ht D g y d)=aepo D g y d :=
  ⟨ht_integrable D g y d hy,ht_unbiased D g y d hy⟩

/-- Finite support, rather than finiteness of the feasible intervention type,
supplies the complete signed-mean and contrast conclusion of corrected T16. -/
theorem finite_support_ht_T16 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hp' : ∀ i, 0<pi D g i d')
    (hfin : {z : Ω | Support D z}.Finite) :
    Integrable D (ht D g y d) ∧ Integrable D (htContrast D g y d d') ∧
    expectation D (ht D g y d)=aepo D g y d ∧
    expectation D (htContrast D g y d d')=aeed D g y d d' := by
  have hd := finite_support_targeted_moment D hfin g y d
  have hd' := finite_support_targeted_moment D hfin g y d'
  exact ⟨ht_integrable D g y d hd,
    integrable_sub D (ht_integrable D g y d hd) (ht_integrable D g y d' hd'),
    ht_unbiased D g y d hd,ht_contrast_unbiased D g y d d' hd hd'
      (ht_integrable D g y d hd) (ht_integrable D g y d' hd')⟩

/-- T11's finite-support domain keeps every off-support feasible intervention.
The general printed positivity-only claim is handled separately by refutation. -/
theorem finite_support_targets_T11 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hp' : ∀ i, 0<pi D g i d')
    (hfin : {z : Ω | Support D z}.Finite) :
    TargetedMoment D g y d ∧ TargetedMoment D g y d' ∧
    (∀ i, epo D g y i d=conditionalMean D g y i d ∧
      epo D g y i d'=conditionalMean D g y i d') ∧
    aeed D g y d d'=(N:ℝ)⁻¹*∑ i,eed D g y i d d' := by
  have hd := finite_support_targeted_moment D hfin g y d
  have hd' := finite_support_targeted_moment D hfin g y d'
  exact ⟨hd,hd',fun i => ⟨epo_conditional D g y i d (hp i) (hd i),
    epo_conditional D g y i d' (hp' i) (hd' i)⟩,aeed_average_eed_algebra D g y d d'⟩


/-- General T17(b): actual SRS exposure-set law on arbitrary feasible raw
assignments, retaining sampling order and all zero-probability interventions. -/
theorem sample_mean_SRS_general_T17 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (n : ℕ)
    (hn : 0<n) (hn' : n≤N) (hd : SamplingCompletion.SimpleRandomExposure D g d n)
    (hfin : {z : Ω | Support D z}.Finite) :
    (∀ z, Support D z → (Finset.univ.filter (fun i => g i z=d)).card=n) ∧
    (∀ i, pi D g i d=(n:ℝ)/N) ∧
    expectation D (sampleMean g y d n)=aepo D g y d :=
  SamplingCompletion.SRS_unbiased D g y d n hn hn' hd hfin

/-- General T17(c): the actual treatment-set law is completely randomized;
the full raw assignment may carry information beyond its binary exposure mask. -/
theorem difference_in_means_CR_general_T17 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (n : ℕ)
    (hn : 0<n) (hn' : n<N) (hd : SamplingCompletion.SimpleRandomExposure D g 1 n)
    (hfin : {z : Ω | Support D z}.Finite) (hb : ∀ i z, Support D z → g i z=0 ∨ g i z=1) :
    (∀ i, pi D g i 1=(n:ℝ)/N ∧ pi D g i 0=((N-n:ℕ):ℝ)/N) ∧
    expectation D (fun z => sampleMean g y 1 n z-sampleMean g y 0 (N-n) z)=
      aeed D g y 1 0 :=
  SamplingCompletion.CR_unbiased D g y n hn hn' hd hfin hb

/-- Deterministic variance scaling on the ordinary first/second-moment
domain used by supplement Equations (5) and (9). -/
theorem variance_mul_T18 {Ω : Type} (D : Design Ω) (c : ℝ) (X : Ω → ℝ)
    (hX : Integrable D X) (h2 : Integrable D (fun z => (X z-expectation D X)^2)) :
    Integrable D (fun z => c*X z) ∧
    variance D (fun z => c*X z)=c^2*variance D X :=
  ⟨integrable_mul D hX c,variance_mul D c X⟩

theorem expectation_mul_T8 {Ω : Type} (D : Design Ω) (a : ℝ) (f : Ω → ℝ)
    (hf : Integrable D f) : Integrable D (fun z => a*f z) ∧
    expectation D (fun z => a*f z)=a*expectation D f :=
  ⟨integrable_mul D hf a,expectation_mul D a f hf⟩

theorem expectation_div_T8 {Ω : Type} (D : Design Ω) (f : Ω → ℝ) (a : ℝ)
    (hf : Integrable D f) (ha : a≠0) : Integrable D (fun z => f z/a) ∧
    expectation D (fun z => f z/a)=expectation D f/a :=
  ⟨integrable_div D hf a,expectation_div D f a hf ha⟩

/-- T6(ii) on the common finite assignment domain stipulated by the target. -/
theorem aeed_average_eed_T6 {Ω : Type} [Fintype Ω] {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ)
    (hN : 0<N) (hp : ∀ i, 0<pi D g i d ∧ 0<pi D g i d') :
    aeed D g y d d'=(N:ℝ)⁻¹*∑ i,eed D g y i d d' :=
  aeed_average_eed D g y d d' hN hp

theorem finite_support_targeted_moment_T8 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ)
    (hN : 0<N) (hp : ∀ i, 0<pi D g i d) (hfin : {z : Ω | Support D z}.Finite) :
    TargetedMoment D g y d := finite_support_targeted_moment D hfin g y d

/-- The automatic NURVA moment only requires stability at the targeted cell. -/
theorem targeted_nurva_moment_T8 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ)
    (hN : 0<N) (hp : ∀ i, 0<pi D g i d)
    (hn : ∀ i z z', Support D z → Support D z' → g i z=d → g i z'=d → y i z=y i z') :
    TargetedMoment D g y d ∧ ∀ i, ∃ a : ℝ,
      (∀ z, Support D z → g i z=d → y i z=a) ∧
      expectation D (fun z => |if g i z=d then y i z else 0|)=|a| * pi D g i d := by
  refine ⟨nurva_targeted_moment D g y d hp hn,?_⟩
  intro i
  obtain ⟨z,hz,hg⟩ := positive_cell_has_assignment D g i d (hp i)
  have hc : ∀ w, Support D w → g i w=d → y i w=y i z :=
    fun w hw he => hn i w z hw hz he hg
  exact ⟨y i z,hc,(constant_cell D g y i d (y i z) (hp i) hc).2.2⟩

theorem extended_expectation_T7 {A B : Type} (f : A → B) (hf : Function.Injective f)
    (D : Design A) (Y : B → ℝ) (hY : Integrable D (fun a => Y (f a))) :
    Integrable (extendDesign f hf D) Y ∧
    expectation (extendDesign f hf D) Y=expectation D (fun a => Y (f a)) := by
  constructor
  · change Summable (fun b => (extendDesign f hf D).p b*|Y b|)
    have hs : Function.support (fun b => (extendDesign f hf D).p b*|Y b|) ⊆ Set.range f := by
      intro b hb
      by_contra hn
      have hp : (extendDesign f hf D).p b=0 := Function.extend_apply' D.p (fun _ => 0) b hn
      exact hb (by simp [hp])
    rw [←hf.summable_iff (fun b hb => by
      by_contra hn
      exact hb (hs hn))]
    change Summable (fun a => (extendDesign f hf D).p (f a) * |Y (f a)|)
    simpa only [Integrable,Function.comp_apply,extendDesign,Function.Injective.extend_apply hf] using hY
  · exact extended_expectation f hf D Y hY

theorem expectation_support_congr_T8 {Ω : Type} (D : Design Ω) (f h : Ω → ℝ)
    (hf : Integrable D f) (he : ∀ z, Support D z → f z=h z) :
    Integrable D h ∧ expectation D f=expectation D h :=
  ⟨(integrable_support_congr D f h he).mp hf,expectation_support_congr D f h he⟩

theorem centered_ht_on_support_T18 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hn : NURVA D g y) (z : Ω) (hz : Support D z) :
    ht D g y d z-expectation D (ht D g y d)=
      (N:ℝ)⁻¹*∑ i,(epo D g y i d/pi D g i d)*centeredExposure D g i d z :=
  centered_ht_on_support D g y d hp hn z hz

theorem centered_ht_product_T18 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d e : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hp' : ∀ i, 0<pi D g i e) (hn : NURVA D g y)
    (z : Ω) (hz : Support D z) :
    (ht D g y d z-expectation D (ht D g y d))*(ht D g y e z-expectation D (ht D g y e))=
      (N:ℝ)⁻¹^2*∑ i,∑ j,((epo D g y i d/pi D g i d)*(epo D g y j e/pi D g j e))*
        (centeredExposure D g i d z*centeredExposure D g j e z) :=
  centered_ht_product D g y d e hp hp' hn z hz

theorem nurva_second_moment_T18 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d e : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hp' : ∀ i, 0<pi D g i e) (hn : NURVA D g y) :
    Integrable D (fun z => (ht D g y d z-expectation D (ht D g y d))*
      (ht D g y e z-expectation D (ht D g y e))) :=
  nurva_second_moment D g y d e hp hp' hn

theorem nurva_covariance_formula_T18 {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d e : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hp' : ∀ i, 0<pi D g i e) (hn : NURVA D g y) :
    covariance D (ht D g y d) (ht D g y e)=htCovarianceExpression D g y d e :=
  nurva_covariance_formula D g y d e hp hp' hn

theorem variance_eq_covariance_T18 {Ω : Type} (D : Design Ω) (X : Ω → ℝ)
    (hX : Integrable D X) (h2 : Integrable D (fun z => (X z-expectation D X)^2)) :
    variance D X=covariance D X X := variance_eq_covariance D X

/-- The printed general claim is false; on its corrected moment domain the
actual estimator is integrable and unbiased. -/
theorem ht_unbiased_T16_resolved {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hy : TargetedMoment D g y d) :
    ¬PrintedClaims.printed_general_ht_unbiased ∧
    Integrable D (ht D g y d) ∧ expectation D (ht D g y d)=aepo D g y d :=
  ⟨Refutations.printed_general_ht_unbiased_refuted,ht_unbiased_T16_corrected D g y d hN hp hy⟩

theorem finite_support_ht_T16_resolved {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hp' : ∀ i, 0<pi D g i d')
    (hfin : {z : Ω | Support D z}.Finite) :
    ¬PrintedClaims.printed_general_ht_unbiased ∧
    Integrable D (ht D g y d) ∧ Integrable D (htContrast D g y d d') ∧
    expectation D (ht D g y d)=aepo D g y d ∧
    expectation D (htContrast D g y d d')=aeed D g y d d' :=
  ⟨Refutations.printed_general_ht_unbiased_refuted,finite_support_ht_T16 D g y d d' hN hp hp' hfin⟩

theorem finite_support_targets_T11_resolved {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) (hN : 0<N)
    (hp : ∀ i, 0<pi D g i d) (hp' : ∀ i, 0<pi D g i d')
    (hfin : {z : Ω | Support D z}.Finite) :
    ¬PrintedClaims.printed_well_defined_claim ∧
    TargetedMoment D g y d ∧ TargetedMoment D g y d' ∧
    (∀ i, epo D g y i d=conditionalMean D g y i d ∧
      epo D g y i d'=conditionalMean D g y i d') ∧
    aeed D g y d d'=(N:ℝ)⁻¹*∑ i,eed D g y i d d' :=
  ⟨Refutations.printed_well_defined_claim_refuted,finite_support_targets_T11 D g y d d' hN hp hp' hfin⟩

end
end AronowAudit.P061.PaperDomains
