import SAP.P015b.Defs.WholeW2
import SAP.P015b.Bridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P015b.WH.W2
universe u
noncomputable section
open SAP.P015b Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal
open AronowAudit.P015 AronowAudit.P015.OLSCompletion
  AronowAudit.P015.PopulationMomentCompletion AronowAudit.P015.WeightedOLSCompletion
/-- Pull conditional expectations back through a measurable map. The source probability space is arbitrary, and the two codomain measurable spaces need no regular conditional probabilities. Prove this by uniqueness of conditional expectation: sets measurable for `comap (x ∘ T)` are preimages of sets measurable for `comap x`; use `setIntegral_map`, `Measure.restrict_map`, and `ae_eq_condExp_of_forall_setIntegral_eq`. Integrability and the measurable representative on the right are essential. Estimated size: 100-180 lines. -/
def T22_L1 : Prop :=
  ∀ {Ω : Type u} {E B : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace B] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → E) (_hT : Measurable T) (x : E → B) (_hx : Measurable x)
    (f : E → ℝ) (_hf : Measurable f) (_hi : Integrable f (P.map T)),
    P[(fun s => f (T s)) | MeasurableSpace.comap (fun s => x (T s)) inferInstance] =ᵐ[P]
      fun s => (P.map T)[f | MeasurableSpace.comap x inferInstance] (T s)
/-- Arbitrary-space unconfounded population identities. Use L1 to transfer the joint vector `(D,Y0,tau,X)` to its law on `R × R × R × R^K`. First transport event-factorization and the linear conditional mean, reflecting almost-sure equalities by `ae_map_iff`. On that standard Borel vector space, `condIndepFun_iff_condExp_inter_preimage_eq_mul` turns the event definition into `CondIndepFun`. Apply `AronowAudit.P015.unconfounded_zero_terms` to the coordinate maps and pull back its conditional and integral conclusions using L1 and `integral_map`. All seven integrability premises are given here, so this step is purely a one-unit law transfer. For the extra displayed factorization, derive E[r|X]=0 from `condExp_sub`, integrability of m=E[D|X], and `condExp_of_stronglyMeasurable`; combine with E[r*tau|X]=0. The supplied hCE is the preceding leaf, not an additional causal assumption. Estimated size: 200-350 lines. -/
def T22_L2 : Prop :=
  T22_L1.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℕ) (D Y₀ τ : Ω → ℝ) (X : Ω → Fin K → ℝ)
    (_hX : Measurable X) (_hD : Measurable D) (_hY : Measurable Y₀) (_hτ : Measurable τ)
    (_hunconf : WholeConditionalIndependent P X (fun s => (Y₀ s, τ s)) D)
    (ω : Fin (K+1) → ℝ)
    (_hlinear : P[D | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X s)) ω)
    (_hiD : Integrable D P) (_hiY : Integrable Y₀ P) (_hiτ : Integrable τ P)
    (_hiDY : Integrable (fun s => D s * Y₀ s) P)
    (_himY : Integrable (fun s => dotProduct (controlVector (X s)) ω * Y₀ s) P)
    (_hirτ : Integrable (fun s => (D s - dotProduct (controlVector (X s)) ω) * τ s) P)
    (_hirmτ : Integrable (fun s => (D s - dotProduct (controlVector (X s)) ω) *
      dotProduct (controlVector (X s)) ω * τ s) P),
    WholeMomentIdentities P K D Y₀ τ X ω
/-- Population identification on arbitrary probability spaces. This adapts the existing projection and Schur-complement proof, using the two identifying zero moments as inputs. No new population-identification leaf is required. -/
private theorem population_identification
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℕ) (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hX : Measurable (X 0)) (ω : Fin (K+1) → ℝ)
    (hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlRow (X 0 s)) ω)
    (hreg : RegressionRegularity P D Y₀ τ X)
    (hzeroBase : (∫ s, D 0 s * Y₀ 0 s ∂P) -
      (∫ s, dotProduct (controlRow (X 0 s)) ω * Y₀ 0 s ∂P) = 0)
    (hzeroMix : (∫ s, (D 0 s - dotProduct (controlRow (X 0 s)) ω) *
      dotProduct (controlRow (X 0 s)) ω * τ 0 s ∂P) = 0) :
    let W : Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun s =>
      Sum.elim (controlRow (X 0 s)) (fun _ => D 0 s)
    let G : Matrix (Fin (K+1) ⊕ Unit) (Fin (K+1) ⊕ Unit) ℝ :=
      fun j k => ∫ s, W s j * W s k ∂P
    let c := fun j => ∫ s, W s j * affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
    G.det ≠ 0 ∧ G⁻¹.mulVec c (Sum.inr ()) =
      (∫ s, populationWeight P (D 0) (X 0) s * τ 0 s ∂P) /
        (∫ s, populationWeight P (D 0) (X 0) s ∂P) := by
  change AronowAudit.P015.OLSRegularity P D Y₀ τ X at hreg
  rcases hreg with ⟨hVV,hVD,hD2,hDY,hVY,hD2T,hVDT,hVVT,hdet,hiw,hw⟩
  let V : Ω → Fin (K+1) → ℝ := fun s => controlRow (X 0 s)
  let M : Ω → ℝ := fun s => dotProduct (V s) ω
  let A : Matrix (Fin (K+1)) (Fin (K+1)) ℝ := fun j k => ∫ s, V s j*V s k ∂P
  let b : Fin (K+1) → ℝ := fun j => ∫ s, V s j*D 0 s ∂P
  let d : ℝ := ∫ s, D 0 s^2 ∂P
  let W : Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun s => Sum.elim (V s) (fun _ => D 0 s)
  let G : Matrix (Fin (K+1) ⊕ Unit) (Fin (K+1) ⊕ Unit) ℝ := fun j k => ∫ s, W s j*W s k ∂P
  let c : (Fin (K+1) ⊕ Unit) → ℝ := fun j => ∫ s, W s j*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
  change G.det ≠ 0 ∧ _
  have hiD : Integrable (D 0) P := by simpa [controlRow] using (hVD 0).1 0
  have hiDMT := linear_mul_integrable P V ω (fun s => D 0 s*τ 0 s) (fun j =>
    ((hVDT j).1 0).congr (Eventually.of_forall (fun s => by dsimp [V]; ring)))
  have hiMMT := linear_product_integrable P V ω (τ 0) (fun j k => (hVVT j k).1 0)
  have hproj : A.mulVec ω=b := projection_population_equations P (X 0) hX V
    (control_measurable (X 0)) (D 0) hiD ω hlinear
    (fun j => (hVD j).1 0) (fun j k => (hVV j k).1 0)
  have hsym : ∀ j k, A j k=A k j := by
    intro j k
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => mul_comm _ _)
  have hquad : (∑ j, ∑ k, ω j*ω k*A j k)=dotProduct ω (A.mulVec ω) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hwr : populationWeight P (D 0) (X 0) =ᵐ[P] fun s => (D 0 s-M s)^2 := by
    filter_upwards [hlinear] with s hs
    simp only [populationWeight,hs,M,V]
  have hEW : (∫ s, populationWeight P (D 0) (X 0) s ∂P)=
      d-dotProduct ω (A.mulVec ω) := by
    rw [integral_congr_ae hwr]
    have h := integral_residual_sq P V ω (D 0) (fun _ => 1)
      (by simpa using hD2.1 0) (fun j => by simpa using (hVD j).1 0)
      (fun j k => by simpa using (hVV j k).1 0)
    simp only [mul_one] at h
    change (∫ s, (D 0 s-M s)^2 ∂P)=d-2*dotProduct ω b+
      (∑ j, ∑ k, ω j*ω k*A j k) at h
    rw [hquad,←hproj] at h
    dsimp only [M]
    rw [h]
    ring
  have hs : 0<d-dotProduct ω (A.mulVec ω) := by rwa [hEW] at hw
  have hblock := SchurCompletion.block_ols_coefficient A hsym hdet ω d hs
  let B := Matrix.fromBlocks A (Matrix.replicateCol Unit (A.mulVec ω))
    (Matrix.replicateRow Unit (A.mulVec ω)) (fun (_ _ : Unit) => d)
  have hGB : G=B := by
    ext j k
    rcases j with j | u <;> rcases k with k | v
    · rfl
    · change b j=A.mulVec ω j
      exact (congrFun hproj j).symm
    · change (∫ s, D 0 s*V s k ∂P)=A.mulVec ω k
      rw [congrFun hproj k]
      exact integral_congr_ae (Eventually.of_forall (fun s => mul_comm _ _))
    · apply integral_congr_ae
      exact Eventually.of_forall (fun s => (pow_two _).symm)
  have hcV : ∀ j, c (Sum.inl j)=(∫ s, V s j*Y₀ 0 s ∂P)+(∫ s, V s j*D 0 s*τ 0 s ∂P) := by
    intro j
    have he : (fun s => V s j*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s)) =
        fun s => V s j*Y₀ 0 s+V s j*D 0 s*τ 0 s := by funext s; dsimp [affineOutcome]; ring
    change (∫ s, V s j*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P)=_
    rw [he,integral_add ((hVY j).1 0) ((hVDT j).1 0)]
  have hcD : c (Sum.inr ())=(∫ s, D 0 s*Y₀ 0 s ∂P)+(∫ s, D 0 s^2*τ 0 s ∂P) := by
    have he : (fun s => D 0 s*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s)) =
        fun s => D 0 s*Y₀ 0 s+D 0 s^2*τ 0 s := by funext s; dsimp [affineOutcome]; ring
    change (∫ s, D 0 s*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P)=_
    rw [he,integral_add (hDY.1 0) (hD2T.1 0)]
  have hvc : dotProduct ω (fun j => c (Sum.inl j))=
      (∫ s, M s*Y₀ 0 s ∂P)+(∫ s, M s*(D 0 s*τ 0 s) ∂P) := by
    simp_rw [hcV]
    change dotProduct ω ((fun j => ∫ s, V s j*Y₀ 0 s ∂P)+
      (fun j => ∫ s, V s j*D 0 s*τ 0 s ∂P))=_
    rw [dotProduct_add,integral_linear_mul P V ω (Y₀ 0) (fun j => (hVY j).1 0)]
    rw [integral_linear_mul P V ω (fun s => D 0 s*τ 0 s) (fun j =>
      ((hVDT j).1 0).congr (Eventually.of_forall (fun s => by dsimp [V]; ring)))]
    simp only [mul_assoc]
  have hmix : (∫ s, M s*(D 0 s*τ 0 s) ∂P)-
      (∫ s, M s*M s*τ 0 s ∂P)=0 := by
    have h := integral_sub hiDMT hiMMT
    change (∫ s, M s*(D 0 s*τ 0 s)-M s*M s*τ 0 s ∂P)=_ at h
    rw [←h]
    convert hzeroMix using 1
    congr 1
    funext s
    dsimp [M]
    ring
  have hR2T := integral_residual_sq P V ω (D 0) (τ 0) (hD2T.1 0)
    (fun j => (hVDT j).1 0) (fun j k => (hVVT j k).1 0)
  have hMDT := integral_linear_mul P V ω (fun s => D 0 s*τ 0 s) (fun j =>
    ((hVDT j).1 0).congr (Eventually.of_forall (fun s => by dsimp [V]; ring)))
  have hMMT := integral_linear_product P V ω (τ 0) (fun j k => (hVVT j k).1 0)
  have htarget : c (Sum.inr ())-dotProduct ω (fun j => c (Sum.inl j))=
      (∫ s, populationWeight P (D 0) (X 0) s*τ 0 s ∂P) := by
    have hwT : (∫ s, populationWeight P (D 0) (X 0) s*τ 0 s ∂P)=
        (∫ s, (D 0 s-M s)^2*τ 0 s ∂P) := by
      apply integral_congr_ae
      filter_upwards [hwr] with s hs
      rw [hs]
    rw [hwT,hcD,hvc]
    have hbase := hzeroBase
    change (∫ s, D 0 s*Y₀ 0 s ∂P)-(∫ s, M s*Y₀ 0 s ∂P)=0 at hbase
    try simp only [mul_assoc] at hMDT
    change (∫ s, M s*(D 0 s*τ 0 s) ∂P)=_ at hMDT
    change (∫ s, M s*M s*τ 0 s ∂P)=_ at hMMT
    change (∫ s, (D 0 s-M s)^2*τ 0 s ∂P)=_ at hR2T
    simp only [mul_assoc] at hbase hmix hR2T hMDT hMMT ⊢
    linarith [hbase,hmix,hR2T,hMDT,hMMT]
  refine ⟨by simpa only [hGB] using hblock.1, ?_⟩
  have hc : c=Sum.elim (fun j => c (Sum.inl j)) (fun _ : Unit => c (Sum.inr ())) := by
    funext j
    rcases j with j | u
    · rfl
    · cases u; rfl
  change G⁻¹.mulVec c (Sum.inr ())=_
  rw [hGB,hc]
  rw [hblock.2 (fun j => c (Sum.inl j)) (c (Sum.inr ())), htarget, ←hEW]
private theorem moment_integrability {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) {K : ℕ} (D Y₀ τ : ℕ → Ω → ℝ)
    (X : ℕ → Ω → Fin K → ℝ) (ω : Fin (K+1) → ℝ)
    (hreg : RegressionRegularity P D Y₀ τ X) :
    Integrable (D 0) P ∧ Integrable (Y₀ 0) P ∧ Integrable (τ 0) P ∧
    Integrable (fun s => D 0 s * Y₀ 0 s) P ∧
    Integrable (fun s => dotProduct (controlVector (X 0 s)) ω * Y₀ 0 s) P ∧
    Integrable (fun s => (D 0 s - dotProduct (controlVector (X 0 s)) ω) * τ 0 s) P ∧
    Integrable (fun s => (D 0 s - dotProduct (controlVector (X 0 s)) ω) *
      dotProduct (controlVector (X 0 s)) ω * τ 0 s) P ∧
    Integrable (fun s => (D 0 s - dotProduct (controlVector (X 0 s)) ω)^2 * τ 0 s) P := by
  rcases hreg with ⟨hVV, hVD, hD2, hDY, hVY, hD2T, hVDT, hVVT, _⟩
  let V := fun s => controlVector (X 0 s)
  let M := fun s => dotProduct (V s) ω
  have hiD : Integrable (D 0) P := by simpa [controlVector] using (hVD 0).1 0
  have hiY : Integrable (Y₀ 0) P := by simpa [controlVector] using (hVY 0).1 0
  have hiT : Integrable (τ 0) P := by simpa [controlVector] using (hVVT 0 0).1 0
  have hiDT : Integrable (fun s => D 0 s * τ 0 s) P := by
    simpa [controlVector] using (hVDT 0).1 0
  have hiVT : ∀ j, Integrable (fun s => V s j * τ 0 s) P := by
    intro j
    simpa [V, controlVector] using (hVVT j 0).1 0
  have hiMY := AronowAudit.P015.PopulationMomentCompletion.linear_mul_integrable
    P V ω (Y₀ 0) (fun j => (hVY j).1 0)
  have hiMT := AronowAudit.P015.PopulationMomentCompletion.linear_mul_integrable
    P V ω (τ 0) hiVT
  have hiRT : Integrable (fun s => (D 0 s - M s) * τ 0 s) P :=
    (hiDT.sub hiMT).congr (Eventually.of_forall (fun s => by dsimp [M]; ring))
  have hiDMT := AronowAudit.P015.PopulationMomentCompletion.linear_mul_integrable
    P V ω (fun s => D 0 s * τ 0 s) (fun j =>
      ((hVDT j).1 0).congr (Eventually.of_forall (fun s => by dsimp [V]; ring)))
  have hiMMT := AronowAudit.P015.PopulationMomentCompletion.linear_product_integrable
    P V ω (τ 0) (fun j k => (hVVT j k).1 0)
  have hiRMT : Integrable (fun s => (D 0 s - M s) * M s * τ 0 s) P :=
    (hiDMT.sub hiMMT).congr (Eventually.of_forall (fun s => by
      simp only [Pi.sub_apply]; dsimp [M]; ring))
  have hiR2T := AronowAudit.P015.PopulationMomentCompletion.residual_sq_integrable
    P V ω (D 0) (τ 0) (hD2T.1 0) (fun j => (hVDT j).1 0)
    (fun j k => (hVVT j k).1 0)
  exact ⟨hiD, hiY, hiT, hDY.1 0, hiMY, hiRT, hiRMT, hiR2T⟩
private theorem regularity_moments (h1 : T22_L1.{u}) (h2 : T22_L2.{u}) :
    WholeRegularityMoments.{u} := by
  intro Ω _ P _ K D Y₀ τ X hD hY hτ hX hunconf ω hlinear hreg
  obtain ⟨hiD, hiY, hiT, hiDY, hiMY, hiRT, hiRMT, _⟩ :=
    moment_integrability P D Y₀ τ X ω hreg
  exact h2 h1 P K (D 0) (Y₀ 0) (τ 0) (X 0) hX hD hY hτ hunconf ω
    hlinear hiD hiY hiT hiDY hiMY hiRT hiRMT
private theorem causal_convergence (h1 : T22_L1.{u}) (h2 : T22_L2.{u}) :
    WholeCausalOLSConvergence.{u} := by
  intro Ω _ P _ K D Y₀ τ X hD hY hτ hX _ _ hunconf ω hlinear hreg
  have hz := regularity_moments h1 h2 P K D Y₀ τ X (hD 0) (hY 0) (hτ 0)
    (hX 0) hunconf ω hlinear hreg
  have hiR2T := (moment_integrability P D Y₀ τ X ω hreg).2.2.2.2.2.2.2
  have hiWT : Integrable (fun s => squaredPopulationResidual P (D 0) (X 0) s * τ 0 s) P := by
    apply hiR2T.congr
    filter_upwards [hlinear] with s hs
    simp only [squaredPopulationResidual, hs]
  refine ⟨hiWT, ?_⟩
  let W : ℕ → Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun i s =>
    Sum.elim (controlVector (X i s)) (fun _ => D i s)
  let G : Matrix (Fin (K+1) ⊕ Unit) (Fin (K+1) ⊕ Unit) ℝ :=
    fun j k => ∫ s, W 0 s j * W 0 s k ∂P
  let c : (Fin (K+1) ⊕ Unit) → ℝ :=
    fun j => ∫ s, W 0 s j * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
  have hp := population_identification P K D Y₀ τ X (hX 0) ω hlinear hreg hz.2.2.2.2.1 hz.2.2.2.2.2
  change G.det ≠ 0 ∧ G⁻¹.mulVec c (Sum.inr ()) = _ at hp
  have hm := AronowAudit.P015.WeightedOLSCompletion.sum_design_moments P K D Y₀ τ X hreg
  have h := AronowAudit.P015.OLSCompletion.ols_moment_limit P W
    (fun i s => linearOutcome (Y₀ i s) (τ i s) (D i s)) G c hp.1
    (fun j k => (hm.1 j k).2) (fun j => (hm.2 j).2) (Sum.inr ())
  have hb : TendstoInMeasure P (treatmentEstimate D Y₀ τ X) atTop
      (fun _ => G⁻¹.mulVec c (Sum.inr ())) := by
    apply TendstoInMeasure.congr_left (fun n => Eventually.of_forall (fun s => ?_)) h
    exact (AronowAudit.P015.WeightedOLSCompletion.betaHat_reindex D Y₀ τ X n s).symm
  simpa only [hp.2, populationWeight, squaredPopulationResidual] using hb
private theorem coefficient_formula : WholeCoefficientFormula.{u} := by
  intro Ω K D Y₀ τ X Y hpot n s
  refine ⟨rfl, ?_⟩
  simp only [treatmentEstimate, linearOutcome, hpot]
private theorem confounding_witness : WholeConfoundingWitness := by
  dsimp only [WholeConfoundingWitness]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [IsFiniteLaw, Fin.sum_univ_two]
  · intro i d
    rfl
  · intro i
    norm_num [finiteCellMean, finiteMean, finiteMass, Fin.sum_univ_two]
  · norm_num [finiteMean, Fin.sum_univ_two]
  · norm_num [finiteMean, Fin.sum_univ_two]
  · intro i
    norm_num [finiteCellMean, finiteMean, finiteMass, Fin.sum_univ_two]
  · intro i
    norm_num [finiteCellMean, finiteMean, finiteMass, Fin.sum_univ_two]
  · intro h
    have hh := h () (0, 0) 0
    norm_num [finiteMass, Fin.sum_univ_two] at hh
  · have hG : (fun j k : Fin 2 => (1/2 : ℝ) * (![1, 0] j * ![1, 0] k) +
        1/2 * (![1, 1] j * ![1, 1] k)) = !![1, 1/2; 1/2, 1/2] := by
      ext j k
      fin_cases j <;> fin_cases k <;> norm_num
    have hi : (!![1, 1/2; 1/2, 1/2] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
        !![2, -2; -2, 4] := by
      apply Matrix.inv_eq_left_inv
      ext j k
      fin_cases j <;> fin_cases k <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    norm_num [populationCoefficients, finiteMean, linearOutcome, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct]
    rw [hG, hi]
    norm_num
  · norm_num [finiteMean, Fin.sum_univ_two]
  · norm_num [finiteMean, Fin.sum_univ_two]
/-- Theorem A.1 assembled from one-unit law transfer and population identification. Empirical-moment continuity is already proved in the project. -/
theorem T22_assembly (h1 : T22_L1.{u}) (h2 : T22_L2.{u}) :
    T22WholeStatement.{u} := by
  exact causal_convergence h1 h2
/-- Corrected expression (7), its two factorizations, the corrected coefficient formula, and the explicit confounding witness. The two leaves are shared with A.1; the finite arithmetic and redundant integrability are proved here. -/
theorem T15_assembly (h1 : T22_L1.{u}) (h2 : T22_L2.{u}) :
    T15WholeStatement.{u} := by
  exact ⟨causal_convergence h1 h2, regularity_moments h1 h2,
    coefficient_formula, confounding_witness⟩
end
end SAP.P015b.WH.W2
