import SAP.P015b.Defs.WholeW1
import SAP.P015b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P015b.WH.W1

universe u

noncomputable section
open SAP.P015b Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- T23 needs no new mathematics: the existing donor has precisely the seven
moment families and already allows singular finite samples and zero finite
weight sums. All SAP definitions below are definitionally equal to its notation. -/
theorem T23_assembly : T23WholeStatement.{u} := by
  intro Ω _ P _ K D Z X hD hZ hX hiid hident ω hlinear hreg
  exact AronowAudit.P015.effective_covariate_mean_limit P K D Z X
    hD hZ hX hiid hident ω hlinear hreg

/-- The one-group counterexample is finite arithmetic. It retains the unit
intercept, positive error variance, and full column rank of the printed domain. -/
theorem T10_assembly : T10WholeStatement := by
  have hP : t10WitnessPrecision = t10WitnessDesign.transpose * t10WitnessDesign := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [t10WitnessPrecision, precisionMatrix, t10WitnessDesign,
        Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
        Matrix.mul_apply, Fin.sum_univ_succ]
  have hA : t10WitnessMap = 1 := by
    rw [t10WitnessMap, hP]
    apply Matrix.nonsing_inv_mul
    norm_num [t10WitnessDesign, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two]
  refine ⟨Matrix.PosSemidef.zero, by norm_num, ?_, ?_, ?_, hP, hA, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [t10WitnessDesign]
  · norm_num [t10WitnessDesign, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two]
  · ext j
    fin_cases j <;>
      norm_num [sampleCoefficients, t10WitnessDesign, Matrix.inv_def,
        Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · intro j hj
    fin_cases j <;> simp_all
  · norm_num [hA, Fin.sum_univ_succ, Matrix.one_apply, Fin.reduceFinMk]
  · intro h
    have hh := h ![0, 1]
    norm_num [hA, Fin.sum_univ_succ, Matrix.one_apply, Fin.reduceFinMk] at hh

/-- Model specification is unpacking a common existential parameter tuple;
the second conjunct is the existing unconditional misprint theorem. -/
theorem T14_assembly : T14WholeStatement.{u} := by
  constructor
  · intro Ω _ P _ K Y D X
    simp only [CommonLogisticModel, sigmoidMean, Real.sigmoid_def, one_div]
  · exact Bridge.unconditionalLogisticFailure

/-- Full differential of the finite logistic likelihood. Smoothness of the log
sum and the existing directional calculation identify the continuous linear
map, including for rank-deficient or empty designs. -/
theorem unrestrictedLogisticScore : UnrestrictedLogisticScore := by
  intro N K W Y hY θ
  let L := binaryLogLikelihood W (fun _ => 1) Y sigmoidMean
  have hd : DifferentiableAt ℝ L θ := by
    apply DifferentiableAt.fun_sum
    intro i hi
    have hw : DifferentiableAt ℝ (fun t : Fin (K + 2) → ℝ => W.mulVec t i) θ := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    have hs : DifferentiableAt ℝ
        (fun t : Fin (K + 2) → ℝ => sigmoidMean (W.mulVec t i)) θ :=
      differentiableAt_sigmoid.comp θ hw
    exact ((hs.log (Real.sigmoid_pos _).ne').const_mul (Y i)).add
      ((((differentiableAt_const (1 : ℝ)).sub hs).log
        (sub_pos.mpr (Real.sigmoid_lt_one _)).ne').const_mul (1 - Y i))
  have hdir (v : Fin (K + 2) → ℝ) : HasDerivAt
      (fun t => L (fun j => θ j + t * v j))
      (∑ i, (Y i - sigmoidMean (W.mulVec θ i)) * W.mulVec v i) 0 := by
    have hh := AronowAudit.P015.likelihood_directional_derivative_calculus W (fun _ => 1) Y
        AronowAudit.P015.logistic θ v (fun _ => differentiableAt_sigmoid)
        (fun _ => Real.sigmoid_pos _) (fun _ => Real.sigmoid_lt_one _)
    simp only [AronowAudit.P015.logistic_multiplier, one_mul] at hh
    exact hh
  have hmap : fderiv ℝ L θ = logisticScoreMap W Y θ := by
    ext v
    have hp : HasDerivAt (fun t : ℝ => fun j => θ j + t * v j) v 0 := by
      convert (hasDerivAt_const (0 : ℝ) θ).add ((hasDerivAt_id 0).smul_const v) using 1 <;>
        simp [funext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hd' : HasFDerivAt L (fderiv ℝ L θ) (fun j => θ j + 0 * v j) := by
      simpa using hd.hasFDerivAt
    have hh := hd'.comp_hasDerivAt 0 hp
    have he : (fderiv ℝ L θ) v =
        ∑ i, (Y i - sigmoidMean (W.mulVec θ i)) * W.mulVec v i :=
      hh.unique (hdir v)
    rw [he]
    simp only [logisticScoreMap, _root_.sum_apply,
      _root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      residualEquation, one_mul, Finset.sum_mul, Matrix.mulVec, dotProduct,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa only [hmap] using hd.hasFDerivAt

/-- Only the unique-root part uses full rank; the predictor identities use the
unit intercept alone and the likelihood differential has no rank hypothesis. -/
theorem T21_assembly : T21WholeStatement := by
  refine ⟨unrestrictedLogisticScore, Bridge.affinePredictor, ?_⟩
  intro N K W Y hY hW hQ b c hc
  exact (AronowAudit.P015.logistic_linearization N K W Y hY hW hQ b c hc).2

/-- Population OLS identification under common random assignment, on an
arbitrary measurable sampling space. Use the intercept coordinates of the eight
moment families to obtain integrability of D, Y₀, τ and Dτ. Independence gives
E[D Y₀] = E[D]E[Y₀], E[Dτ] = E[D]E[τ], and E[D²τ] = E[D²]E[τ]. Set
ω = (E[D],0,...,0); use condExp_indep_eq and projection_population_equations
for E[VD] = E[VV']ω. The Schur complement is Var(D) = E[w] > 0.
Apply block_ols_coefficient to the controls-first, treatment-last population
Gram, then simplify its numerator to Var(D) E[τ]. No conditional kernel or
regular conditional distribution on the sampling space is needed. Estimated
sample inverses do not occur in this leaf. Expected proof size: 150–220 lines. -/
def T24_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : Measurable (D 0)) (hY : Measurable (Y₀ 0))
    (hτ : Measurable (τ 0)) (hX : Measurable (X 0))
    (hrandom : IndepFun (D 0) (fun s => (Y₀ 0 s, τ 0 s, X 0 s)) P)
    (hreg : RegressionRegularity P D Y₀ τ X),
    let W : Ω → (Fin (K + 1) ⊕ Unit) → ℝ :=
      fun s => Sum.elim (controlVector (X 0 s)) (fun _ => D 0 s)
    let G : Matrix (Fin (K + 1) ⊕ Unit) (Fin (K + 1) ⊕ Unit) ℝ :=
      fun j k => ∫ s, W s j * W s k ∂P
    let z : (Fin (K + 1) ⊕ Unit) → ℝ :=
      fun j => ∫ s, W s j * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
    G.det ≠ 0 ∧ G⁻¹.mulVec z (Sum.inr ()) = ∫ s, τ 0 s ∂P

/-- Derive the seven fitted-weight moment families with Z = τ from the eight
OLS families under common assignment. Write m = E[D] and r = D-m. Expand
r²τ = D²τ - 2mDτ + m²τ, r² = D² - 2mD + m²,
rτV_j = DτV_j - mτV_j, and rV_j = DV_j - mV_j.
The intercept coordinates supply every lower-order family. Use momentLLN_add,
momentLLN_congr and scalar-multiple closure (from mul_limit and constant_limit)
for integrability and convergence together. Preserve the population control
determinant from RegressionRegularity. Independence makes E[D|X] = m; its
ae squared-residual identity transfers the positive mean weight to E[r²].
This leaf does not assume any additional LLN or positivity. Expected proof
size: 100–160 lines. -/
def T24_L2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : Measurable (D 0)) (hX : Measurable (X 0))
    (hrandom : IndepFun (D 0) (fun s => (Y₀ 0 s, τ 0 s, X 0 s)) P)
    (hreg : RegressionRegularity P D Y₀ τ X),
    EffectiveMeanRegularity P D τ X (randomAssignmentCenter P (D 0) K)

/-- The extra independence and existence assertions follow from the existing
centered-weight identity by measurable composition and ae congruence. -/
theorem randomizationWholePopulation : RandomizationWholePopulation.{u} := by
  intro Ω _ P _ K D Y₀ τ X hD hY hτ hX hrandom h₂ hτi hpos
  obtain ⟨hce, hw, hprod, hratio⟩ :=
    AronowAudit.P015.ProbabilityCompletion.randomization_population_weight_cancels
      P K D Y₀ τ X hD hY hτ hX hrandom h₂ hτi hpos
  change squaredPopulationResidual P D X =ᵐ[P] _ at hw
  have hDT : IndepFun D τ P := by
    convert hrandom.comp measurable_id (measurable_fst.comp measurable_snd) using 1 <;> rfl
  have hcenter : IndepFun (fun s => (D s - ∫ t, D t ∂P) ^ 2) τ P := by
    exact hDT.comp (by fun_prop : Measurable (fun d : ℝ => (d - ∫ t, D t ∂P) ^ 2))
      measurable_id
  have hind : IndepFun (squaredPopulationResidual P D X) τ P :=
    hcenter.congr hw.symm EventuallyEq.rfl
  have hwi : Integrable (squaredPopulationResidual P D X) P :=
    ((h₂.sub (memLp_const _)).integrable_sq).congr hw.symm
  have hwτi : Integrable (fun s => squaredPopulationResidual P D X s * τ s) P :=
    hind.integrable_mul hwi hτi
  have hvar : (∫ s, squaredPopulationResidual P D X s ∂P) = variance D P := by
    rw [integral_congr_ae hw, variance_eq_integral hD.aemeasurable]
  exact ⟨hce, hw, hind, hwi, hwτi, hvar, hvar.symm ▸ hpos, hprod, hratio⟩

/-- Assemble the actual OLS limit using the nonsingular population Gram and
existing continuous-mapping theorem, then apply T23 to the derived τ moments.
The separate population statement includes weight-effect independence. -/
theorem T24_assembly (h1 : T24_L1.{u}) (h2 : T24_L2.{u}) : T24WholeStatement.{u} := by
  refine ⟨?_, randomizationWholePopulation⟩
  intro Ω _ P _ K D Y₀ τ X hD hY hτ hX hiid hident hrandom hreg
  let W : ℕ → Ω → (Fin (K + 1) ⊕ Unit) → ℝ :=
    fun i s => Sum.elim (controlVector (X i s)) (fun _ => D i s)
  let G : Matrix (Fin (K + 1) ⊕ Unit) (Fin (K + 1) ⊕ Unit) ℝ :=
    fun j k => ∫ s, W 0 s j * W 0 s k ∂P
  let z : (Fin (K + 1) ⊕ Unit) → ℝ :=
    fun j => ∫ s, W 0 s j * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
  have hp := h1 P K D Y₀ τ X (hD 0) (hY 0) (hτ 0) (hX 0) hrandom hreg
  change G.det ≠ 0 ∧ G⁻¹.mulVec z (Sum.inr ()) = _ at hp
  have hm := AronowAudit.P015.WeightedOLSCompletion.sum_design_moments P K D Y₀ τ X hreg
  have hlim := AronowAudit.P015.OLSCompletion.ols_moment_limit P W
    (fun i s => linearOutcome (Y₀ i s) (τ i s) (D i s)) G z hp.1
      (fun j k => (hm.1 j k).2) (fun j => (hm.2 j).2) (Sum.inr ())
  have hβ : TendstoInMeasure P (treatmentEstimate D Y₀ τ X) atTop
      (fun _ => G⁻¹.mulVec z (Sum.inr ())) := by
    apply TendstoInMeasure.congr_left (fun n => Eventually.of_forall (fun s => ?_)) hlim
    exact (AronowAudit.P015.WeightedOLSCompletion.betaHat_reindex D Y₀ τ X n s).symm
  refine ⟨by simpa only [hp.2] using hβ, ?_⟩
  have hIX : IndepFun (D 0) (X 0) P := by
    convert hrandom.comp measurable_id (measurable_snd.comp measurable_snd) using 1 <;> rfl
  have hDm : Measurable[MeasurableSpace.comap (D 0) inferInstance] (D 0) :=
    measurable_iff_comap_le.mpr le_rfl
  have hce : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun _ => ∫ s, D 0 s ∂P :=
    condExp_indep_eq (hD 0).comap_le (hX 0).comap_le hDm.stronglyMeasurable
      ((IndepFun_iff_Indep (D 0) (X 0) P).mp hIX)
  have hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X 0 s)) (randomAssignmentCenter P (D 0) K) := by
    simpa [controlVector, randomAssignmentCenter, dotProduct, Fin.sum_univ_succ] using hce
  have hiid' : iIndepFun (fun i s => (D i s, τ i s, X i s)) P := by
    exact hiid.comp (fun _ t => (t.1, t.2.2.1, t.2.2.2)) (by intro i; fun_prop)
  have hident' : ∀ i, IdentDistrib (fun s => (D i s, τ i s, X i s))
      (fun s => (D 0 s, τ 0 s, X 0 s)) P P := by
    intro i
    exact (hident i).comp (by fun_prop : Measurable
      (fun t : ℝ × ℝ × ℝ × (Fin K → ℝ) => (t.1, t.2.2.1, t.2.2.2)))
  have heff := T23_assembly P K D τ X hD hτ hX hiid' hident'
    (randomAssignmentCenter P (D 0) K) hlinear
    (h2 P K D Y₀ τ X (hD 0) (hX 0) hrandom hreg)
  rcases hreg with ⟨hVV, hVD, hD2, hDY, hVY, hD2T, hVDT, hVVT, hdet, hwi, hwpos⟩
  have htwo : MemLp (D 0) 2 P :=
    (memLp_two_iff_integrable_sq (hD 0).aestronglyMeasurable).2 (hD2.1 0)
  have hτi : Integrable (τ 0) P := by simpa [controlVector] using (hVVT 0 0).1 0
  have hw : squaredPopulationResidual P (D 0) (X 0) =ᵐ[P]
      fun s => (D 0 s - ∫ t, D 0 t ∂P) ^ 2 := by
    filter_upwards [hce] with s hs
    simp only [squaredPopulationResidual, hs]
  have hpos : 0 < variance (D 0) P := by
    rw [variance_eq_integral (hD 0).aemeasurable, ← integral_congr_ae hw]
    exact hwpos
  have hcancel := AronowAudit.P015.ProbabilityCompletion.randomization_population_weight_cancels
    P K (D 0) (Y₀ 0) (τ 0) (X 0) (hD 0) (hY 0) (hτ 0) (hX 0)
    hrandom htwo hτi hpos
  have hc : (∫ s, squaredPopulationResidual P (D 0) (X 0) s * τ 0 s ∂P) /
      (∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P) = ∫ s, τ 0 s ∂P :=
    hcancel.2.2.2
  simpa only [hc] using heff

end
end SAP.P015b.WH.W1
