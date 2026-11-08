import SAP.P015b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015b.WH.W1.P.T24_L1

noncomputable section
open Filter Matrix Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem population_ols_under_randomization : SAP.P015b.WH.W1.T24_L1 := by
  intro Ω _ P _ K D Y₀ τ X hD hY hτ hX hrandom hreg
  let V : Ω → Fin (K + 1) → ℝ := fun s => controlVector (X 0 s)
  let m : ℝ := ∫ s, D 0 s ∂P
  let ω : Fin (K + 1) → ℝ := Fin.cases m (fun _ => 0)
  let A : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ :=
    fun j k => ∫ s, V s j * V s k ∂P
  let b : Fin (K + 1) → ℝ := fun j => ∫ s, V s j * D 0 s ∂P
  let d : ℝ := ∫ s, (D 0 s) ^ 2 ∂P
  let W : Ω → (Fin (K + 1) ⊕ Unit) → ℝ :=
    fun s => Sum.elim (V s) (fun _ => D 0 s)
  let G : Matrix (Fin (K + 1) ⊕ Unit) (Fin (K + 1) ⊕ Unit) ℝ :=
    fun j k => ∫ s, W s j * W s k ∂P
  let z : (Fin (K + 1) ⊕ Unit) → ℝ :=
    fun j => ∫ s, W s j * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
  let B : Matrix (Fin (K + 1) ⊕ Unit) (Fin (K + 1) ⊕ Unit) ℝ :=
    Matrix.fromBlocks A (Matrix.replicateCol Unit (A.mulVec ω))
      (Matrix.replicateRow Unit (A.mulVec ω)) (fun _ _ => d)
  change G.det ≠ 0 ∧ G⁻¹.mulVec z (Sum.inr ()) = ∫ s, τ 0 s ∂P
  rcases hreg with ⟨hVV, hVD, hD2, hDY, hVY, hD2τ, hVDτ, hVVτ, hdet, hiw, hw⟩

  have hiD : Integrable (D 0) P := by
    simpa [controlVector] using (hVD 0).1 0
  have hiY : Integrable (Y₀ 0) P := by
    simpa [controlVector] using (hVY 0).1 0
  have hiτ : Integrable (τ 0) P := by
    simpa [controlVector] using (hVVτ 0 0).1 0
  have hiDτ : Integrable (fun s => D 0 s * τ 0 s) P := by
    simpa [controlVector] using (hVDτ 0).1 0
  have hiDY : Integrable (fun s => D 0 s * Y₀ 0 s) P := (hDY.1 0)
  have hiD2 : Integrable (fun s => (D 0 s)^2) P := (hD2.1 0)
  have hiD2τ : Integrable (fun s => (D 0 s)^2 * τ 0 s) P := (hD2τ.1 0)

  have hIX : IndepFun (D 0) (X 0) P := by
    convert hrandom.comp measurable_id (measurable_snd.comp measurable_snd) using 1 <;> rfl
  have hIY : IndepFun (D 0) (Y₀ 0) P := by
    convert hrandom.comp measurable_id measurable_fst using 1 <;> rfl
  have hIτ : IndepFun (D 0) (τ 0) P := by
    convert hrandom.comp measurable_id (measurable_fst.comp measurable_snd) using 1 <;> rfl
  have hID2τ : IndepFun (fun s => (D 0 s)^2) (τ 0) P := by
    exact hIτ.comp (show Measurable (fun x : ℝ => x^2) by fun_prop) measurable_id

  have hDm : Measurable[MeasurableSpace.comap (D 0) inferInstance] (D 0) :=
    measurable_iff_comap_le.mpr le_rfl
  have hce : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun _ => m := by
    simpa only [m] using
      (condExp_indep_eq (hD).comap_le (hX).comap_le hDm.stronglyMeasurable
        ((IndepFun_iff_Indep (D 0) (X 0) P).mp hIX))
  have hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (V s) ω := by
    filter_upwards [hce] with s hs
    simpa [V, ω, controlVector, dotProduct, Fin.sum_univ_succ] using hs
  have hVω (s : Ω) : dotProduct (V s) ω = m := by
    simp [V, ω, controlVector, dotProduct, Fin.sum_univ_succ]
  have hweight : squaredPopulationResidual P (D 0) (X 0) =ᵐ[P]
      fun s => (D 0 s - m)^2 := by
    filter_upwards [hce] with s hs
    simp [squaredPopulationResidual, hs, m]

  have hproj : A.mulVec ω = b := by
    exact AronowAudit.P015.OLSCompletion.projection_population_equations
      P (X 0) hX V (fun j => AronowAudit.P015.WeightedOLSCompletion.control_measurable
        (X 0) j) (D 0) hiD ω hlinear
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
  have hEW : (∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P) =
      d - dotProduct ω (A.mulVec ω) := by
    rw [integral_congr_ae hweight]
    have hres := AronowAudit.P015.PopulationMomentCompletion.integral_residual_sq
      P V ω (D 0) (fun _ => (1 : ℝ))
      ((hD2.1 0).congr (Eventually.of_forall (fun _ => by ring)))
      (fun j => ((hVD j).1 0).congr (Eventually.of_forall (fun _ => by ring)))
      (fun j k => ((hVV j k).1 0).congr (Eventually.of_forall (fun _ => by ring)))
    have hres' : (∫ s, (D 0 s - dotProduct (V s) ω)^2 ∂P) =
        d - 2 * dotProduct ω b + ∑ j, ∑ k, ω j * ω k * A j k := by
      simpa [d, b, A] using hres
    rw [hquad, ← hproj] at hres'
    have hresEq : (∫ s, (D 0 s - m)^2 ∂P) =
        (∫ s, (D 0 s - dotProduct (V s) ω)^2 ∂P) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s =>
        congrArg (fun x : ℝ => (D 0 s - x)^2) (hVω s).symm)
    rw [← hresEq] at hres'
    nlinarith

  have hschur : 0 < d - dotProduct ω (A.mulVec ω) := by
    rw [← hEW]
    exact hw
  have hgb : G = B := by
    ext j k
    rcases j with j | uj <;> rcases k with k | uk
    · rfl
    · cases uk
      change (∫ s, V s j * D 0 s ∂P) = A.mulVec ω j
      rw [congrFun hproj j]
    · cases uj
      change (∫ s, D 0 s * V s k ∂P) = A.mulVec ω k
      rw [congrFun hproj k]
      apply integral_congr_ae
      exact Eventually.of_forall (fun s => mul_comm _ _)
    · cases uj
      cases uk
      change (∫ s, D 0 s * D 0 s ∂P) = d
      exact integral_congr_ae (Eventually.of_forall (fun s => by simp [pow_two]))

  have hfacDY : (∫ s, D 0 s * Y₀ 0 s ∂P) = m * (∫ s, Y₀ 0 s ∂P) := by
    simpa [m] using hIY.integral_fun_mul_eq_mul_integral
      (hD).aestronglyMeasurable (hY).aestronglyMeasurable
  have hfacDτ : (∫ s, D 0 s * τ 0 s ∂P) = m * (∫ s, τ 0 s ∂P) := by
    simpa [m] using hIτ.integral_fun_mul_eq_mul_integral
      (hD).aestronglyMeasurable (hτ).aestronglyMeasurable
  have hfacD2τ : (∫ s, (D 0 s)^2 * τ 0 s ∂P) =
      (∫ s, (D 0 s)^2 ∂P) * (∫ s, τ 0 s ∂P) := by
    exact hID2τ.integral_fun_mul_eq_mul_integral (by fun_prop) (hτ).aestronglyMeasurable

  have hc0 : z (Sum.inl (0 : Fin (K + 1))) =
      (∫ s, Y₀ 0 s ∂P) + (∫ s, D 0 s * τ 0 s ∂P) := by
    change (∫ s, controlVector (X 0 s) 0 *
      linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P) = _
    have he : (fun s => controlVector (X 0 s) 0 *
        linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s)) =
        fun s => Y₀ 0 s + D 0 s * τ 0 s := by
      funext s
      simp [linearOutcome, controlVector]
      ring
    rw [he, integral_add hiY hiDτ]
  have hcD : z (Sum.inr ()) =
      (∫ s, D 0 s * Y₀ 0 s ∂P) + (∫ s, (D 0 s)^2 * τ 0 s ∂P) := by
    change (∫ s, D 0 s *
      linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P) = _
    have he : (fun s => D 0 s * linearOutcome (Y₀ 0 s) (τ 0 s) (D 0 s)) =
        fun s => D 0 s * Y₀ 0 s + (D 0 s)^2 * τ 0 s := by
      funext s
      simp [linearOutcome]
      ring
    rw [he, integral_add hiDY hiD2τ]
  have hdotc : dotProduct ω (fun j => z (Sum.inl j)) = m * z (Sum.inl 0) := by
    simp [ω, dotProduct, Fin.sum_univ_succ]
  have htarget : z (Sum.inr ()) - dotProduct ω (fun j => z (Sum.inl j)) =
      (d - dotProduct ω (A.mulVec ω)) * (∫ s, τ 0 s ∂P) := by
    rw [hcD, hdotc, hc0, hfacDY, hfacDτ, hfacD2τ]
    have hschurval : d - dotProduct ω (A.mulVec ω) =
        (∫ s, (D 0 s)^2 ∂P) - m^2 := by
      have hfirst : A.mulVec ω 0 = m := by
        calc
          A.mulVec ω 0 = b 0 := congrFun hproj 0
          _ = m := by simp [b, m, V, controlVector]
      have hquadm : dotProduct ω (A.mulVec ω) = m^2 := by
        simp [ω, dotProduct, Fin.sum_univ_succ, hfirst]
        ring
      dsimp [d]
      rw [hquadm]
    rw [hschurval]
    dsimp [d, m]
    ring

  have hblock := AronowAudit.P015.SchurCompletion.block_ols_coefficient
    A hsym hdet ω d hschur
  have hdetG : G.det ≠ 0 := by
    rw [hgb]
    exact hblock.1
  refine ⟨hdetG, ?_⟩
  rw [hgb]
  have hc : z = Sum.elim (fun j => z (Sum.inl j)) (fun _ : Unit => z (Sum.inr ())) := by
    funext j
    rcases j with j | u
    · rfl
    · cases u
      rfl
  rw [hc, hblock.2 (fun j => z (Sum.inl j)) (z (Sum.inr ())), htarget]
  field_simp [hschur.ne']

end
end SAP.P015b.WH.W1.P.T24_L1

theorem SAP.P015b.WH.W1.T24_L1_proof : SAP.P015b.WH.W1.T24_L1 :=
  SAP.P015b.WH.W1.P.T24_L1.population_ols_under_randomization
