import SAP.P015b.WH.W1.Leaves
import AronowAudit.P015.P015_ConvergenceCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015b.WH.W1.P.T24_L2

noncomputable section
open SAP.P015b MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

lemma moment_const_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : ℝ)
    {Z : ℕ → Ω → ℝ} (hZ : MomentConvergence P Z) :
    MomentConvergence P (fun i s => c * Z i s) := by
  refine ⟨fun i => (hZ.1 i).const_mul c, ?_⟩
  have h := AronowAudit.P015.ConvergenceCompletion.mul_limit P
    (AronowAudit.P015.ConvergenceCompletion.constant_limit P c) hZ.2
  have hsum : (fun n s => (∑ i : Fin n, c * Z i s) / (n : ℝ)) =
      fun n s => c * ((∑ i : Fin n, Z i s) / (n : ℝ)) := by
    funext n s
    rw [← Finset.mul_sum]
    ring
  rw [hsum, integral_const_mul]
  exact h

end

end SAP.P015b.WH.W1.P.T24_L2

open SAP.P015b MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

theorem SAP.P015b.WH.W1.T24_L2_proof : SAP.P015b.WH.W1.T24_L2 := by
  intro Ω hΩ P hP K D Y₀ τ X hD hX hrandom hreg
  let m : ℝ := ∫ s, D 0 s ∂P
  rcases hreg with ⟨hVV, hVD, hD2, hDY, hVY, hD2T, hVDT, hVVT,
    hdet, hwi, hwpos⟩

  have hdot (i : ℕ) (s : Ω) :
      dotProduct (controlVector (X i s)) (randomAssignmentCenter P (D 0) K) = m := by
    simp [dotProduct, controlVector, randomAssignmentCenter, m, Fin.sum_univ_succ]

  have hDmom : MomentConvergence P (fun i s => D i s) := by
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _ (fun i s => ?_)
      (hVD 0)
    simp [controlVector]

  have hτmom : MomentConvergence P (fun i s => τ i s) := by
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _ (fun i s => ?_)
      (hVVT 0 0)
    simp [controlVector]

  have hone : MomentConvergence P (fun i s => (1 : ℝ)) := by
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) (hVV 0 0)
    simp [controlVector]

  have hDtau : MomentConvergence P (fun i s => D i s * τ i s) := by
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) (hVDT 0)
    simp [controlVector]

  have hτV (j : Fin (K + 1)) :
      MomentConvergence P (fun i s => τ i s * controlVector (X i s) j) := by
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) (hVVT 0 j)
    simp [controlVector]
    ring

  have hDτV (j : Fin (K + 1)) :
      MomentConvergence P (fun i s => D i s * τ i s * controlVector (X i s) j) := by
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) (hVDT j)
    ring

  have hDV (j : Fin (K + 1)) :
      MomentConvergence P (fun i s => D i s * controlVector (X i s) j) := by
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) (hVD j)
    ring

  have hV (j : Fin (K + 1)) :
      MomentConvergence P (fun i s => controlVector (X i s) j) := by
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) (hVV 0 j)
    simp [controlVector]

  have hτVV (j k : Fin (K + 1)) :
      MomentConvergence P
        (fun i s => τ i s * controlVector (X i s) j * controlVector (X i s) k) := by
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) (hVVT j k)
    ring

  have hR2τ : MomentConvergence P (fun i s => (D i s - m) ^ 2 * τ i s) := by
    have hsum := AronowAudit.P015.WeightedOLSCompletion.momentLLN_add P _ _
      (AronowAudit.P015.WeightedOLSCompletion.momentLLN_add P _ _ hD2T
        (SAP.P015b.WH.W1.P.T24_L2.moment_const_mul P (-2 * m) hDtau))
      (SAP.P015b.WH.W1.P.T24_L2.moment_const_mul P (m ^ 2) hτmom)
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) hsum
    ring

  have hR2 : MomentConvergence P (fun i s => (D i s - m) ^ 2) := by
    have hsum := AronowAudit.P015.WeightedOLSCompletion.momentLLN_add P _ _
      (AronowAudit.P015.WeightedOLSCompletion.momentLLN_add P _ _ hD2
        (SAP.P015b.WH.W1.P.T24_L2.moment_const_mul P (-2 * m) hDmom))
      (SAP.P015b.WH.W1.P.T24_L2.moment_const_mul P (m ^ 2) hone)
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) hsum
    ring

  have hRτV (j : Fin (K + 1)) :
      MomentConvergence P
        (fun i s => (D i s - m) * τ i s * controlVector (X i s) j) := by
    have hsum := AronowAudit.P015.WeightedOLSCompletion.momentLLN_add P _ _
      (hDτV j)
      (SAP.P015b.WH.W1.P.T24_L2.moment_const_mul P (-m) (hτV j))
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) hsum
    ring

  have hRV (j : Fin (K + 1)) :
      MomentConvergence P (fun i s => (D i s - m) * controlVector (X i s) j) := by
    have hsum := AronowAudit.P015.WeightedOLSCompletion.momentLLN_add P _ _
      (hDV j)
      (SAP.P015b.WH.W1.P.T24_L2.moment_const_mul P (-m) (hV j))
    apply AronowAudit.P015.WeightedOLSCompletion.momentLLN_congr P _ _
      (fun i s => ?_) hsum
    ring

  have hDX : IndepFun (D 0) (X 0) P := by
    convert hrandom.comp measurable_id (measurable_snd.comp measurable_snd) using 1 <;> rfl
  have hDm : Measurable[MeasurableSpace.comap (D 0) inferInstance] (D 0) :=
    measurable_iff_comap_le.mpr le_rfl
  have hce : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun _ => m := by
    simpa [m] using
      (condExp_indep_eq (hD).comap_le (hX).comap_le hDm.stronglyMeasurable
        ((IndepFun_iff_Indep (D 0) (X 0) P).mp hDX))
  have hweight : squaredPopulationResidual P (D 0) (X 0) =ᵐ[P]
      fun s => (D 0 s - m) ^ 2 := by
    filter_upwards [hce] with s hs
    simp [squaredPopulationResidual, hs]
  have hmeanpos : 0 < ∫ s, (D 0 s - m) ^ 2 ∂P := by
    rw [← integral_congr_ae hweight]
    exact hwpos

  dsimp [EffectiveMeanRegularity]
  refine ⟨hVV, hVD, ?_, ?_, ?_, ?_, ?_, hdet, ?_⟩
  · simpa only [hdot] using hR2τ
  · simpa only [hdot] using hR2
  · intro j
    simpa only [hdot] using hRτV j
  · intro j
    simpa only [hdot] using hRV j
  · exact hτVV
  · simpa only [hdot] using hmeanpos
