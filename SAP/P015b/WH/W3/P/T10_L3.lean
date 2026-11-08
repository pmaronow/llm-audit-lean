import SAP.P015b.WH.W3.Leaves
import Mathlib
import AronowAudit.P015.P015_OLSCompletion
import AronowAudit.P015.P015_PopulationMomentCompletion
import AronowAudit.P015.P015_SchurCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace SAP.P015b.WH.W3.P.T10_L3

noncomputable section
open SAP.P015b Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

private theorem control_measurable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (X : Ω → Fin K → ℝ) (j : Fin (K+1)) :
    Measurable[MeasurableSpace.comap X inferInstance] (fun s => controlVector (X s) j) := by
  have hX : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa [controlVector] using
      (measurable_const : Measurable[MeasurableSpace.comap X inferInstance]
        (fun _ : Ω => (1 : ℝ)))
  · simpa [controlVector, Function.comp_def] using (measurable_pi_apply k).comp hX

/-- The moment families in `RegressionRegularity` provide the integrability
needed to expand the population block moments. -/
private theorem moment_integrability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {K : ℕ} (D Y₀ τ : ℕ → Ω → ℝ)
    (X : ℕ → Ω → Fin K → ℝ) (ω : Fin (K+1) → ℝ)
    (hreg : RegressionRegularity P D Y₀ τ X) :
    Integrable (D 0) P ∧ Integrable (Y₀ 0) P ∧
    Integrable (fun s => D 0 s^2 * τ 0 s) P ∧
    Integrable (fun s => dotProduct (controlVector (X 0 s)) ω * Y₀ 0 s) P ∧
    Integrable (fun s => dotProduct (controlVector (X 0 s)) ω * (D 0 s * τ 0 s)) P ∧
    Integrable (fun s => (D 0 s - dotProduct (controlVector (X 0 s)) ω)^2 * τ 0 s) P ∧
    Integrable (fun s => (D 0 s - dotProduct (controlVector (X 0 s)) ω) *
      dotProduct (controlVector (X 0 s)) ω * τ 0 s) P := by
  rcases hreg with ⟨_, hVD, _, _, hVY, hD2T, hVDT, hVVT, _⟩
  let V := fun s => controlVector (X 0 s)
  have hiD : Integrable (D 0) P := by simpa [controlVector] using (hVD 0).1 0
  have hiY : Integrable (Y₀ 0) P := by simpa [controlVector] using (hVY 0).1 0
  have hiMY := AronowAudit.P015.PopulationMomentCompletion.linear_mul_integrable
    P V ω (Y₀ 0) (fun j => (hVY j).1 0)
  have hiD2T : Integrable (fun s => D 0 s^2 * τ 0 s) P := (hD2T.1 0).congr
    (Eventually.of_forall (fun s => by ring))
  have hiDMT := AronowAudit.P015.PopulationMomentCompletion.linear_mul_integrable
    P V ω (fun s => D 0 s * τ 0 s) (fun j =>
      ((hVDT j).1 0).congr (Eventually.of_forall (fun s => by dsimp [V]; ring)))
  have hiMMT := AronowAudit.P015.PopulationMomentCompletion.linear_product_integrable
    P V ω (τ 0) (fun j k => (hVVT j k).1 0)
  have hiRMT : Integrable (fun s => (D 0 s - dotProduct (V s) ω) *
      dotProduct (V s) ω * τ 0 s) P :=
    (hiDMT.sub hiMMT).congr (Eventually.of_forall (fun s => by
      simp only [Pi.sub_apply]; ring))
  have hiR2T := AronowAudit.P015.PopulationMomentCompletion.residual_sq_integrable
    P V ω (D 0) (τ 0) (hD2T.1 0) (fun j => (hVDT j).1 0)
    (fun j k => (hVVT j k).1 0)
  exact ⟨hiD, hiY, hiD2T, hiMY, hiDMT, hiR2T, hiRMT⟩

end
end SAP.P015b.WH.W3.P.T10_L3

open SAP.P015b Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

theorem SAP.P015b.WH.W3.T10_L3_proof : SAP.P015b.WH.W3.T10_L3 := by
  intro Ω _ P _ K D Y₀ τ X hX ω hlinear hreg hzeroBase hzeroMix
  obtain ⟨hiD, hiY, hiD2T, hiMY, hiDMT, hiR2T, hiRMT⟩ :=
    SAP.P015b.WH.W3.P.T10_L3.moment_integrability P D Y₀ τ X ω hreg
  rcases hreg with ⟨hVV, hVD, hD2, hDY, hVY, hD2T, hVDT, hVVT,
    hdet, hiw, hw⟩
  let V : Ω → Fin (K+1) → ℝ := fun s => controlVector (X 0 s)
  let M : Ω → ℝ := fun s => dotProduct (V s) ω
  let A : Matrix (Fin (K+1)) (Fin (K+1)) ℝ :=
    fun j k => ∫ s, V s j * V s k ∂P
  let b : Fin (K+1) → ℝ := fun j => ∫ s, V s j * D 0 s ∂P
  let d : ℝ := ∫ s, D 0 s^2 ∂P
  let W : Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun s =>
    Sum.elim (V s) (fun _ => D 0 s)
  let H : Matrix (Fin (K+1) ⊕ Unit) (Fin (K+1) ⊕ Unit) ℝ :=
    fun j k => ∫ s, W s j * W s k ∂P
  let c : (Fin (K+1) ⊕ Unit) → ℝ :=
    fun j => ∫ s, W s j * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
  change H.det ≠ 0 ∧ H⁻¹.mulVec c (Sum.inr ()) = _
  have hproj : A.mulVec ω = b :=
    AronowAudit.P015.OLSCompletion.projection_population_equations P (X 0) hX V
      (SAP.P015b.WH.W3.P.T10_L3.control_measurable (X 0)) (D 0) hiD ω hlinear
      (fun j => (hVD j).1 0) (fun j k => (hVV j k).1 0)
  have hsym : ∀ j k, A j k = A k j := by
    intro j k
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => mul_comm _ _)
  have hquad : (∑ j, ∑ k, ω j * ω k * A j k) = dotProduct ω (A.mulVec ω) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hwr : squaredPopulationResidual P (D 0) (X 0) =ᵐ[P]
      fun s => (D 0 s - M s)^2 := by
    filter_upwards [hlinear] with s hs
    simp only [squaredPopulationResidual, hs, M, V]
  have hEW : (∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P) =
      d - dotProduct ω (A.mulVec ω) := by
    rw [integral_congr_ae hwr]
    have h := AronowAudit.P015.PopulationMomentCompletion.integral_residual_sq
      P V ω (D 0) (fun _ => 1) (by simpa using (hD2.1 0))
      (fun j => by simpa using (hVD j).1 0)
      (fun j k => by simpa using (hVV j k).1 0)
    simp only [mul_one] at h
    change (∫ s, (D 0 s - dotProduct (V s) ω)^2 ∂P) =
      d - 2 * dotProduct ω b + (∑ j, ∑ k, ω j * ω k * A j k) at h
    rw [hquad, ← hproj] at h
    change (∫ s, (D 0 s - dotProduct (V s) ω)^2 ∂P) = _
    calc
      _ = d - 2 * dotProduct ω (A.mulVec ω) + dotProduct ω (A.mulVec ω) := h
      _ = _ := by ring
  have hs : 0 < d - dotProduct ω (A.mulVec ω) := by rwa [hEW] at hw
  have hblock := AronowAudit.P015.SchurCompletion.block_ols_coefficient
    A hsym hdet ω d hs
  let B := Matrix.fromBlocks A (Matrix.replicateCol Unit (A.mulVec ω))
    (Matrix.replicateRow Unit (A.mulVec ω)) (fun (_ _ : Unit) => d)
  have hGB : H = B := by
    ext j k
    rcases j with j | u <;> rcases k with k | v
    · rfl
    · change b j = A.mulVec ω j
      exact (congrFun hproj j).symm
    · change (∫ s, D 0 s * V s k ∂P) = A.mulVec ω k
      rw [congrFun hproj k]
      exact integral_congr_ae (Eventually.of_forall (fun s => mul_comm _ _))
    · apply integral_congr_ae
      exact Eventually.of_forall (fun s => (pow_two _).symm)
  have hcV : ∀ j, c (Sum.inl j) =
      (∫ s, V s j * Y₀ 0 s ∂P) + (∫ s, V s j * D 0 s * τ 0 s ∂P) := by
    intro j
    have he : (fun s => V s j * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s)) =
        fun s => V s j * Y₀ 0 s + V s j * D 0 s * τ 0 s := by
      funext s
      dsimp [linearOutcome]
      ring
    change (∫ s, V s j * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P) = _
    rw [he, integral_add ((hVY j).1 0) ((hVDT j).1 0)]
  have hcD : c (Sum.inr ()) =
      (∫ s, D 0 s * Y₀ 0 s ∂P) + (∫ s, D 0 s^2 * τ 0 s ∂P) := by
    have he : (fun s => D 0 s * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s)) =
        fun s => D 0 s * Y₀ 0 s + D 0 s^2 * τ 0 s := by
      funext s
      dsimp [linearOutcome]
      ring
    change (∫ s, D 0 s * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P) = _
    rw [he, integral_add (hDY.1 0) (hD2T.1 0)]
  have hvc : dotProduct ω (fun j => c (Sum.inl j)) =
      (∫ s, M s * Y₀ 0 s ∂P) + (∫ s, M s * (D 0 s * τ 0 s) ∂P) := by
    simp_rw [hcV]
    change dotProduct ω ((fun j => ∫ s, V s j * Y₀ 0 s ∂P) +
      (fun j => ∫ s, V s j * D 0 s * τ 0 s ∂P)) = _
    rw [dotProduct_add,
      AronowAudit.P015.PopulationMomentCompletion.integral_linear_mul P V ω (Y₀ 0)
        (fun j => (hVY j).1 0)]
    rw [AronowAudit.P015.PopulationMomentCompletion.integral_linear_mul P V ω
      (fun s => D 0 s * τ 0 s) (fun j =>
        ((hVDT j).1 0).congr (Eventually.of_forall (fun s => by dsimp [V]; ring)))]
    simp only [M, mul_assoc]
  have hdecomp :
      (∫ s, D 0 s^2 * τ 0 s ∂P) -
        (∫ s, M s * (D 0 s * τ 0 s) ∂P) =
      (∫ s, (D 0 s - M s)^2 * τ 0 s ∂P) +
        (∫ s, (D 0 s - M s) * M s * τ 0 s ∂P) := by
    calc
      _ = ∫ s, D 0 s^2 * τ 0 s - M s * (D 0 s * τ 0 s) ∂P :=
        (integral_sub hiD2T hiDMT).symm
      _ = ∫ s, (D 0 s - M s)^2 * τ 0 s +
          (D 0 s - M s) * M s * τ 0 s ∂P := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun s => by dsimp [M]; ring)
      _ = _ := integral_add hiR2T hiRMT
  have htarget : c (Sum.inr ()) - dotProduct ω (fun j => c (Sum.inl j)) =
      (∫ s, (D 0 s - M s)^2 * τ 0 s ∂P) := by
    rw [hcD, hvc]
    simp only [mul_assoc] at hzeroBase hzeroMix hdecomp ⊢
    linarith
  refine ⟨by simpa only [hGB] using hblock.1, ?_⟩
  have hc : c = Sum.elim (fun j => c (Sum.inl j)) (fun _ : Unit => c (Sum.inr ())) := by
    funext j
    rcases j with j | u
    · rfl
    · cases u
      rfl
  change H⁻¹.mulVec c (Sum.inr ()) = _
  rw [hGB, hc]
  rw [hblock.2 (fun j => c (Sum.inl j)) (c (Sum.inr ())), htarget, ← hEW]
  congr 1
  apply integral_congr_ae
  filter_upwards [hlinear] with s hs
  simp [squaredPopulationResidual, hs, M, V]
