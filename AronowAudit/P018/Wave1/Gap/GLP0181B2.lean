import AronowAudit.P018.P018_Audit
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
P018-T17: the eight-type population, its positive leading covariance, and the
positive-probability full-rank sample with negative fitted dyadic variance.
All expectations below are integrals under the population law in P018_Audit.
-/

noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

local instance negative_population_instProbability : IsProbabilityMeasure finiteUnitLaw := by
  unfold finiteUnitLaw
  infer_instance

lemma negative_population_integrable {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsFiniteMeasure μ] (f : A → ℝ) :
    Integrable f μ := by
  exact ⟨(measurable_of_countable f).aestronglyMeasurable, HasFiniteIntegral.of_finite⟩

lemma negative_population_integral (f : Fin 4 × Bool → ℝ) :
    (∫ u, f u ∂finiteUnitLaw) = (1 / 8 : ℝ) * ∑ t : Fin 4, ∑ a : Bool, f (t,a) := by
  rw [finiteUnitLaw, PMF.integral_eq_sum]
  norm_num [PMF.uniformOfFintype_apply, Fintype.sum_prod_type, ← Finset.mul_sum]

lemma negative_population_pairIntegral (f : (Fin 4 × Bool) × (Fin 4 × Bool) → ℝ) :
    (∫ uv, f uv ∂finiteUnitLaw.prod finiteUnitLaw) =
      (1 / 8 : ℝ) * ∑ t : Fin 4, ∑ a : Bool,
        (1 / 8 : ℝ) * ∑ s : Fin 4, ∑ b : Bool, f ((t,a),(s,b)) := by
  rw [integral_prod _ (negative_population_integrable _ _)]
  simp_rw [negative_population_integral]

lemma negative_population_gram :
    populationGram finiteNegativeKernel = !![1,5/4;5/4,5/2] := by
  ext i j
  change (∫ uv, (outer (finiteNegativeKernel.X uv.1 uv.2)
    (finiteNegativeKernel.X uv.1 uv.2)) i j ∂finiteUnitLaw.prod finiteUnitLaw) = _
  rw [negative_population_pairIntegral]
  fin_cases i <;> fin_cases j <;>
    norm_num [finiteNegativeKernel, outer, Matrix.of_apply, Fin.sum_univ_succ,
      Fintype.sum_bool]

lemma negative_population_xy :
    meanVec (finiteUnitLaw.prod finiteUnitLaw)
      (fun uv => score (finiteNegativeKernel.X uv.1 uv.2)
        (finiteNegativeKernel.Y uv.1 uv.2)) = ![5/4,9/4] := by
  ext i
  change (∫ uv, (score (finiteNegativeKernel.X uv.1 uv.2)
    (finiteNegativeKernel.Y uv.1 uv.2)) i ∂finiteUnitLaw.prod finiteUnitLaw) = _
  rw [negative_population_pairIntegral]
  fin_cases i <;>
    norm_num [finiteNegativeKernel, heterogeneityTable, signValue, score,
      Matrix.of_apply, Fin.sum_univ_succ, Fintype.sum_bool]

lemma negative_population_gramInverse :
    (populationGram finiteNegativeKernel)⁻¹ = !![8/3,-4/3;-4/3,16/15] := by
  apply Matrix.inv_eq_left_inv
  rw [negative_population_gram]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Matrix.one_apply]

lemma negative_population_beta : populationBeta finiteNegativeKernel = ![1/3,11/15] := by
  unfold populationBeta
  rw [negative_population_gramInverse]
  change (!![8/3,-4/3;-4/3,16/15] : Mat 2).mulVec
    (meanVec (finiteUnitLaw.prod finiteUnitLaw) _) = _
  rw [negative_population_xy]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, funext_iff,
    Fin.forall_fin_succ]

lemma negative_population_tableSymmetry (t s : Fin 4) :
    heterogeneityTable t s = heterogeneityTable s t := by
  fin_cases t <;> fin_cases s <;> norm_num [heterogeneityTable, Matrix.of_apply]

lemma negative_population_standing : Standing finiteNegativeKernel := by
  refine ⟨negative_population_instProbability, measurable_of_countable _,
    measurable_of_countable _, ?_, ?_, ?_, ?_⟩
  · intro u v
    constructor
    · ext i
      fin_cases i <;> simp [finiteNegativeKernel, abs_sub_comm]
    · change |(u.1.val : ℝ) - (v.1.val : ℝ)| + heterogeneityTable u.1 v.1 +
          signValue u.2 + signValue v.2 =
        |(v.1.val : ℝ) - (u.1.val : ℝ)| + heterogeneityTable v.1 u.1 +
          signValue v.2 + signValue u.2
      rw [abs_sub_comm, negative_population_tableSymmetry u.1 v.1]
      ring
  · let f : (Fin 4 × Bool) × (Fin 4 × Bool) → Vec 2 :=
      fun uv => finiteNegativeKernel.X uv.1 uv.2
    let g : (Fin 4 × Bool) × (Fin 4 × Bool) → ℝ :=
      fun uv => finiteNegativeKernel.Y uv.1 uv.2
    refine ⟨‖f‖ + ‖g‖, add_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
    apply Filter.Eventually.of_forall
    intro uv
    constructor
    · exact (norm_le_pi_norm f uv).trans (le_add_of_nonneg_right (norm_nonneg g))
    · exact (show |g uv| ≤ ‖g‖ by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm g uv).trans
        (le_add_of_nonneg_left (norm_nonneg f))
  · exact ⟨0, fun _ _ => rfl⟩
  · rw [negative_population_gram]
    norm_num [Matrix.det_fin_two]

/-- The four label cases of the actual neighbor-integrated score. -/
lemma negative_population_projection (u : Fin 4 × Bool) :
    projection finiteNegativeKernel u =
      if u.1 = 0 ∨ u.1 = 3 then
        ![signValue u.2 + 1/15, (3/2)*signValue u.2 + 11/60]
      else ![signValue u.2 - 1/15, signValue u.2 - 11/60] := by
  ext i
  change (∫ v, (populationScore finiteNegativeKernel u v) i ∂finiteUnitLaw) = _
  rw [negative_population_integral]
  simp only [populationScore, populationResidual, negative_population_beta]
  rcases u with ⟨t,a⟩
  fin_cases t <;> cases a <;> fin_cases i <;>
    norm_num [finiteNegativeKernel, heterogeneityTable, signValue, score, dot,
      Matrix.of_apply, Fin.sum_univ_succ, Fintype.sum_bool]

lemma negative_population_gamma :
    projectionGamma finiteNegativeKernel = !![226/225,284/225;284/225,5971/3600] := by
  ext i j
  change (∫ u, (outer (projection finiteNegativeKernel u)
    (projection finiteNegativeKernel u)) i j ∂finiteUnitLaw) = _
  rw [negative_population_integral]
  simp_rw [negative_population_projection]
  fin_cases i <;> fin_cases j <;>
    norm_num [outer, Matrix.of_apply, signValue, Fin.sum_univ_succ, Fintype.sum_bool]

lemma negative_population_target :
    limitingTarget finiteNegativeKernel = !![1004/225,-48/125;-48/125,1856/5625] := by
  unfold limitingTarget
  rw [negative_population_gramInverse, negative_population_gamma]
  norm_num [sandwich, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ,
    funext_iff, Fin.forall_fin_succ]

lemma negative_population_targetPosDef : (limitingTarget finiteNegativeKernel).PosDef := by
  rw [negative_population_target]
  apply positive_definite_two <;> norm_num

lemma negative_population_singleton (u : Fin 4 × Bool) :
    finiteUnitLaw {u} = 1/8 := by
  rw [finiteUnitLaw, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  norm_num [PMF.uniformOfFintype_apply]

lemma negative_population_atom :
    (unitSampleLaw finiteNegativeKernel 4 {ω |
      ∀ i : Fin 4, ω i = (i,true)}).toReal = 1/4096 := by
  have he : {ω : Fin 4 → Fin 4 × Bool | ∀ i : Fin 4, ω i = (i,true)} =
      {fun i : Fin 4 => (i,true)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, funext_iff]
  rw [he]
  change ((Measure.pi (fun _ : Fin 4 => finiteUnitLaw)) _).toReal = _
  rw [Measure.pi_singleton]
  simp_rw [negative_population_singleton]
  norm_num [Fin.prod_univ_succ]

/-- The six dyads in exactly the order of the existing OLS certificate. -/
def negative_population_dyad (d : Fin 6) : Dyad 4 :=
  ⟨sixMembers d, by
    fin_cases d <;> norm_num [sixMembers, dyads]⟩

lemma negative_population_dyadInjective : Function.Injective negative_population_dyad := by
  decide

noncomputable def negative_population_dyadEquiv : Fin 6 ≃ Dyad 4 :=
  Equiv.ofBijective negative_population_dyad
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨negative_population_dyadInjective, by rw [number_of_dyads]; decide⟩)

lemma negative_population_members (d : Fin 6) :
    members (negative_population_dyadEquiv d) = sixMembers d := rfl

lemma negative_population_gramReindex {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) {k : ℕ} (X : F → Vec k) :
    sampleGram (fun d => X (e d)) = sampleGram X :=
  e.sum_comp (fun d => outer (X d) (X d))

lemma negative_population_olsReindex {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) {k : ℕ} (X : F → Vec k) (Y : F → ℝ) :
    sampleOLS (fun d => X (e d)) (fun d => Y (e d)) = sampleOLS X Y := by
  unfold sampleOLS
  rw [negative_population_gramReindex, e.sum_comp (fun d => score (X d) (Y d))]

lemma negative_population_meatReindex {V E F : Type*} [DecidableEq V]
    [Fintype E] [Fintype F] (e : E ≃ F) (s : F → Finset V) {k : ℕ} (q : F → Vec k) :
    meat (fun d => s (e d)) (fun d => q (e d)) = meat s q := by
  classical
  unfold meat
  calc
    _ = ∑ d : E, ∑ f : F,
        if (s (e d) ∩ s f).Nonempty then outer (q (e d)) (q f) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact e.sum_comp (fun f : F =>
        if (s (e d) ∩ s f).Nonempty then outer (q (e d)) (q f) else (0 : Mat k))
    _ = _ := e.sum_comp (fun d : F => ∑ f : F,
      if (s d ∩ s f).Nonempty then outer (q d) (q f) else (0 : Mat k))

lemma negative_population_varianceReindex {V E F : Type*} [DecidableEq V]
    [Fintype E] [Fintype F] (e : E ≃ F) (s : F → Finset V)
    {k : ℕ} (X : F → Vec k) (Y : F → ℝ) :
    sampleVariance (fun d => s (e d)) (fun d => X (e d)) (fun d => Y (e d)) =
      sampleVariance s X Y := by
  unfold sampleVariance
  rw [negative_population_gramReindex]
  simp only [fittedResidual, negative_population_olsReindex]
  exact congrArg (sandwich (sampleGram X)⁻¹)
    (negative_population_meatReindex e s
      (fun d => score (X d) (Y d - dot (X d) (sampleOLS X Y))))

lemma negative_population_eventDesign (ω : Fin 4 → Fin 4 × Bool)
    (hω : ∀ i : Fin 4, ω i = (i,true)) :
    (fun d : Fin 6 => design finiteNegativeKernel ω (negative_population_dyadEquiv d)) =
      negativeX := by
  funext d
  simp only [design, hω]
  fin_cases d <;>
    norm_num [negative_population_dyadEquiv, negative_population_dyad, firstUnit,
      secondUnit, members, sixMembers, finiteNegativeKernel, negativeX,
      Finset.min'_pair, Finset.max'_pair]

lemma negative_population_eventResponse (ω : Fin 4 → Fin 4 × Bool)
    (hω : ∀ i : Fin 4, ω i = (i,true)) :
    (fun d : Fin 6 => response finiteNegativeKernel ω (negative_population_dyadEquiv d)) =
      negativeY := by
  funext d
  simp only [response, hω]
  fin_cases d <;>
    norm_num [negative_population_dyadEquiv, negative_population_dyad, firstUnit,
      secondUnit, members, sixMembers, finiteNegativeKernel, negativeY,
      heterogeneityTable, signValue, Matrix.of_apply, Finset.min'_pair, Finset.max'_pair]

lemma negative_population_eventCertificate (ω : Fin 4 → Fin 4 × Bool)
    (hω : ∀ i : Fin 4, ω i = (i,true)) :
    (sampleGram (design finiteNegativeKernel ω)).det = 20 ∧
      sampleVariance members (design finiteNegativeKernel ω) (response finiteNegativeKernel ω) =
        (!![-17/50,21/125;21/125,-58/625] : Mat 2) := by
  have hg := negative_population_gramReindex negative_population_dyadEquiv
    (design finiteNegativeKernel ω)
  rw [negative_population_eventDesign ω hω] at hg
  have hv := negative_population_varianceReindex negative_population_dyadEquiv members
    (design finiteNegativeKernel ω) (response finiteNegativeKernel ω)
  have hm : (fun d : Fin 6 => members (negative_population_dyadEquiv d)) = sixMembers :=
    funext negative_population_members
  rw [hm, negative_population_eventDesign ω hω, negative_population_eventResponse ω hω] at hv
  rw [← hg, ← hv]
  exact ⟨negative_ols_certificate.2.1, negative_ols_certificate.2.2.2.2.2.1⟩

theorem negative_sample_population_proof :
    Standing finiteNegativeKernel ∧ populationGram finiteNegativeKernel = !![1,5/4;5/4,5/2] ∧
    populationBeta finiteNegativeKernel = ![1/3,11/15] ∧
    limitingTarget finiteNegativeKernel = !![1004/225,-48/125;-48/125,1856/5625] ∧
    (limitingTarget finiteNegativeKernel).PosDef ∧
    (unitSampleLaw finiteNegativeKernel 4 {ω |
      ∀ i : Fin 4, ω i = (i,true)}).toReal = 1/4096 ∧
    (∀ ω : Fin 4 → Fin 4 × Bool, (∀ i : Fin 4, ω i = (i,true)) →
      (sampleGram (design finiteNegativeKernel ω)).det = 20 ∧
      sampleVariance members (design finiteNegativeKernel ω) (response finiteNegativeKernel ω) =
        (!![-17/50,21/125;21/125,-58/625] : Mat 2)) := by
  exact ⟨negative_population_standing, negative_population_gram, negative_population_beta,
    negative_population_target, negative_population_targetPosDef, negative_population_atom,
    negative_population_eventCertificate⟩

end AronowAudit.P018.Wave1
