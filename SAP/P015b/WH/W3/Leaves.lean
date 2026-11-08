import SAP.P015b.Defs.WholeW3
import SAP.P015b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015b.WH.W3

universe u

noncomputable section
open SAP.P015b Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

/-- Conditional-expectation pullback through a measurable map from an arbitrary
probability space. Prove by uniqueness of conditional expectation: a set
measurable for comap (x o T) is a preimage of an x-measurable set; use
`setIntegral_map` and `ae_eq_condExp_of_forall_setIntegral_eq`. The integrable
right-hand representative is essential. About 80-130 lines. -/
def T10_L1 : Prop :=
  ∀ {Ω : Type u} {E B : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace B] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → E) (_hT : Measurable T) (x : E → B) (_hx : Measurable x)
    (f : E → ℝ) (_hf : Measurable f) (_hi : Integrable f (P.map T)),
    P[(fun s => f (T s)) | MeasurableSpace.comap (fun s => x (T s)) inferInstance] =ᵐ[P]
      fun s => (P.map T)[f | MeasurableSpace.comap x inferInstance] (T s)

/-- The two causal cancellation moments on an arbitrary probability space.
Use L1 to transfer the measurable joint vector (D,Y0,tau,X) to its law on
R x R x R x R^K. Transport event factorization and the conditional treatment
mean using L1 and `ae_map_iff`. On that standard Borel vector space convert
event factorization with `condIndepFun_iff_condExp_inter_preimage_eq_mul`, apply
`AronowAudit.P015.unconfounded_zero_terms`, and pull the two integrals back by
`integral_map`. All seven required integrability premises are explicit; L1 is
a proof dependency, not a causal assumption. About 180-300 lines. -/
def T10_L2 : Prop :=
  T10_L1.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℕ) (D Y₀ τ : Ω → ℝ) (X : Ω → Fin K → ℝ)
    (_hX : Measurable X) (_hD : Measurable D) (_hY : Measurable Y₀) (_hτ : Measurable τ)
    (_hunconf : ConditionalIndependentW3 P X (fun s => (Y₀ s, τ s)) D)
    (ω : Fin (K+1) → ℝ)
    (_hlinear : P[D | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X s)) ω)
    (_hiD : Integrable D P) (_hiY : Integrable Y₀ P) (_hiτ : Integrable τ P)
    (_hiDY : Integrable (fun s => D s * Y₀ s) P)
    (_himY : Integrable (fun s => dotProduct (controlVector (X s)) ω * Y₀ s) P)
    (_hirτ : Integrable (fun s => (D s - dotProduct (controlVector (X s)) ω) * τ s) P)
    (_hirmτ : Integrable (fun s => (D s - dotProduct (controlVector (X s)) ω) *
      dotProduct (controlVector (X s)) ω * τ s) P),
    ((∫ s, D s * Y₀ s ∂P) -
      (∫ s, dotProduct (controlVector (X s)) ω * Y₀ s ∂P) = 0) ∧
    (∫ s, (D s - dotProduct (controlVector (X s)) ω) *
      dotProduct (controlVector (X s)) ω * τ s ∂P) = 0

/-- Population OLS identification from the two zero moments, with no ambient
standard-Borel restriction. Adapt `WeightedOLSCompletion.population_ols_identification`:
use `projection_population_equations` to identify the population control
projection; expand the residual square by `integral_residual_sq`; apply
`SchurCompletion.block_ols_coefficient`. Its Schur complement is E[w]>0,
and the two assumed cancellations identify the numerator with E[w*tau].
No conditional-independence result is being assumed in this algebraic leaf.
About 130-200 lines; all empirical LLNs remain in the already proved donor. -/
def T10_L3 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℕ) (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (_hX : Measurable (X 0)) (ω : Fin (K+1) → ℝ)
    (_hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X 0 s)) ω)
    (_hreg : RegressionRegularity P D Y₀ τ X)
    (_hzeroBase : (∫ s, D 0 s * Y₀ 0 s ∂P) -
      (∫ s, dotProduct (controlVector (X 0 s)) ω * Y₀ 0 s ∂P) = 0)
    (_hzeroMix : (∫ s, (D 0 s - dotProduct (controlVector (X 0 s)) ω) *
      dotProduct (controlVector (X 0 s)) ω * τ 0 s ∂P) = 0),
    let W : Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun s =>
      Sum.elim (controlVector (X 0 s)) (fun _ => D 0 s)
    let H : Matrix (Fin (K+1) ⊕ Unit) (Fin (K+1) ⊕ Unit) ℝ :=
      fun j k => ∫ s, W s j * W s k ∂P
    let c := fun j => ∫ s, W s j * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
    H.det ≠ 0 ∧ H⁻¹.mulVec c (Sum.inr ()) =
      (∫ s, squaredPopulationResidual P (D 0) (X 0) s * τ 0 s ∂P) /
        (∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P)

/-- The covariance assumptions ensure that none of the finite matrix inverses
in the whole statement is a singular-matrix completion. -/
private theorem pooling_covariances : PoolingCovariancesW3 := by
  intro G q hG _ n Z S σ₂ hS hσ hQ
  have : Nonempty (Fin G) := ⟨⟨0, by omega⟩⟩
  let P := fun g => precisionMatrix S ((Z g).transpose * Z g) (σ₂ g)
  have hΩ : ∀ g, (S + σ₂ g • ((Z g).transpose * Z g)⁻¹).PosDef := fun g =>
    Matrix.PosDef.posSemidef_add hS
      ((AronowAudit.P015.MatrixCompletion.gram_posDef (Z g) (hQ g)).inv.smul (hσ g))
  have hP : ∀ g, (P g).PosDef := fun g => (hΩ g).inv
  refine ⟨fun g => ⟨hΩ g, hP g, ?_⟩,
    Matrix.posDef_sum Finset.univ_nonempty (fun g _ => hP g)⟩
  apply Matrix.PosDef.posSemidef_add
  · simpa using hS.mul_mul_conjTranspose_same (Z g)
  · exact Matrix.PosDef.one.smul (hσ g)

/-- Prescribed-weight scalar pooling and both parts of its corrected entrywise
criterion. The universal coefficient-family quantifier precedes no weights. -/
private theorem scalar_row_criterion : ScalarRowCriterionW3 := by
  intro G q A a b
  have h := AronowAudit.P015.scalar_pooling_iff_algebra A a b
  constructor
  · simpa only [Finset.sum_apply, Matrix.mulVec, dotProduct, funext_iff] using h
  · constructor
    · intro hr
      refine ⟨fun g j hj => ?_, fun g => ?_⟩
      · simpa only [hj, ite_false] using congrFun (hr g) j
      · simpa using congrFun (hr g) b
    · rintro ⟨hoff, hdiag⟩ g
      funext j
      by_cases hj : j = b
      · subst j
        simpa using hdiag g
      · simpa only [hj, ite_false] using hoff g j hj

/-- A finite sum of vanishing off-treatment entries times uniformly bounded
inputs vanishes, with the exact same-index diagonal contribution subtracted. -/
private theorem bounded_input_approximation : BoundedInputApproximationW3 := by
  intro G q A b hvanish t hbounded
  obtain ⟨M, _, hM⟩ := hbounded
  have herr (k : ℕ) :
      (∑ g, (A k g).mulVec (t k g)) b - ∑ g, A k g b b * t k g b =
        ∑ g, ∑ j ∈ Finset.univ.erase b, A k g b j * t k g j := by
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin q))
      (fun j => A k g b j * t k g j) (Finset.mem_univ b)
    linarith
  simp_rw [herr]
  have hprod (g : Fin G) (j : Fin q) (hj : j ∈ Finset.univ.erase b) :
      Tendsto (fun k => A k g b j * t k g j) atTop (𝓝 0) := by
    have hne : j ≠ b := (Finset.mem_erase.mp hj).1
    simpa only [mul_comm] using bdd_le_mul_tendsto_zero' M
      (Eventually.of_forall (fun k => hM k g j)) (hvanish g j hne)
  have hsum := tendsto_finsetSum Finset.univ (fun g _ =>
    tendsto_finsetSum (Finset.univ.erase b) (fun j hj => hprod g j hj))
  simpa only [Finset.sum_const_zero] using hsum

/-- All integrability needed by the causal leaves follows from the eight
moment families already present in A.1(4); none is an added substantive premise. -/
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
  rcases hreg with ⟨_, hVD, _, hDY, hVY, hD2T, hVDT, hVVT, _⟩
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

/-- Apply the population leaves to one group, then use the project's proved
empirical-moment OLS continuity. Singular finite samples need no eventual
almost-sure nonsingularity assumption; the inverse formula is totalized there. -/
private theorem within_group_expression7
    (h1 : T10_L1.{u}) (h2 : T10_L2.{u}) (h3 : T10_L3.{u}) :
    WithinGroupExpression7W3.{u} := by
  intro Ω _ P _ K D Y₀ τ X hD hY hτ hX _ _ hunconf ω hlinear hreg
  obtain ⟨hiD, hiY, hiT, hiDY, hiMY, hiRT, hiRMT, hiR2T⟩ :=
    moment_integrability P D Y₀ τ X ω hreg
  have hz := h2 h1 P K (D 0) (Y₀ 0) (τ 0) (X 0) (hX 0) (hD 0) (hY 0)
    (hτ 0) hunconf ω hlinear hiD hiY hiT hiDY hiMY hiRT hiRMT
  have hiWT : Integrable (fun s => squaredPopulationResidual P (D 0) (X 0) s * τ 0 s) P := by
    apply hiR2T.congr
    filter_upwards [hlinear] with s hs
    simp only [squaredPopulationResidual, hs]
  refine ⟨hiWT, ?_⟩
  let W : ℕ → Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun i s =>
    Sum.elim (controlVector (X i s)) (fun _ => D i s)
  let H : Matrix (Fin (K+1) ⊕ Unit) (Fin (K+1) ⊕ Unit) ℝ :=
    fun j k => ∫ s, W 0 s j * W 0 s k ∂P
  let c : (Fin (K+1) ⊕ Unit) → ℝ :=
    fun j => ∫ s, W 0 s j * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
  have hp := h3 P K D Y₀ τ X (hX 0) ω hlinear hreg hz.1 hz.2
  change H.det ≠ 0 ∧ H⁻¹.mulVec c (Sum.inr ()) = _ at hp
  have hm := AronowAudit.P015.WeightedOLSCompletion.sum_design_moments P K D Y₀ τ X hreg
  have h := AronowAudit.P015.OLSCompletion.ols_moment_limit P W
    (fun i s => linearOutcome (Y₀ i s) (τ i s) (D i s)) H c hp.1
    (fun j k => (hm.1 j k).2) (fun j => (hm.2 j).2) (Sum.inr ())
  have hb : TendstoInMeasure P (treatmentEstimate D Y₀ τ X) atTop
      (fun _ => H⁻¹.mulVec c (Sum.inr ())) := by
    apply TendstoInMeasure.congr_left (fun n => Eventually.of_forall (fun s => ?_)) h
    exact (AronowAudit.P015.WeightedOLSCompletion.betaHat_reindex D Y₀ τ X n s).symm
  simpa only [hp.2] using hb

/-- The corrected whole claim. The three leaves concern only the extension of
within-group expression (7) to arbitrary ambient probability spaces. All finite
GLS clauses, the complete prescribed-row criterion, a mixing witness, and the
bounded-input limit are discharged by existing proofs and the arguments above. -/
theorem T10_assembly (h1 : T10_L1.{u}) (h2 : T10_L2.{u}) (h3 : T10_L3.{u}) :
    T10WholeStatement_W3.{u} := by
  exact ⟨SAP.P015b.Bridge.matrixPooling, pooling_covariances, scalar_row_criterion,
    bounded_input_approximation, within_group_expression7 h1 h2 h3,
    SAP.P015b.Bridge.rawPoolingCounterexample⟩

end
end SAP.P015b.WH.W3
