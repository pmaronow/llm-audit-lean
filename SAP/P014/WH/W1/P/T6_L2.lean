import SAP.P014.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open MeasureTheory

theorem SAP.P014.WH.W1.T6_L2_proof : SAP.P014.WH.W1.T6_L2 := by
  classical
  intro Ω mΩ N μ hμ X hX H hH hdisc
  let A : FiniteDistribution (Fin N → ℝ) :=
    ⟨H, fun x => eventProbability μ (fun ω => X ω = x)⟩
  have hsupport : ∀ᵐ ω ∂μ, X ω ∈ H := by
    filter_upwards [hdisc] with ω hω
    exact (hH (X ω)).2 hω
  have hfiber_meas : ∀ x ∈ H, MeasurableSet (X ⁻¹' ({x} : Set (Fin N → ℝ))) := by
    intro x hx
    exact measurableSet_eq_fun hX measurable_const
  have hsumH :
      (∑ x ∈ H, eventProbability μ (fun ω => X ω = x)) = μ.real (X ⁻¹' (H : Set (Fin N → ℝ))) := by
    calc
      _ = ∑ x ∈ H, μ.real (X ⁻¹' ({x} : Set (Fin N → ℝ))) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [eventProbability, MeasureTheory.measureReal_def]
        congr 1
      _ = μ.real (X ⁻¹' (H : Set (Fin N → ℝ))) :=
        MeasureTheory.sum_measureReal_preimage_singleton H hfiber_meas
  have hsupport_set : X ⁻¹' (H : Set (Fin N → ℝ)) =ᵐ[μ] Set.univ := by
    filter_upwards [hsupport] with ω hω
    simp [hω]
  have hnorm : (∑ x ∈ H, eventProbability μ (fun ω => X ω = x)) = 1 := by
    calc
      _ = μ.real (X ⁻¹' (H : Set (Fin N → ℝ))) := hsumH
      _ = μ.real Set.univ := MeasureTheory.measureReal_congr hsupport_set
      _ = 1 := by simp [MeasureTheory.measureReal_def]
  have hdist : IsDistribution A := by
    change (∀ x ∈ H, 0 < eventProbability μ (fun ω => X ω = x)) ∧
      (∑ x ∈ H, eventProbability μ (fun ω => X ω = x)) = 1
    exact ⟨fun x hx => (hH x).mp hx, hnorm⟩
  refine ⟨hdist, ?_⟩
  intro P
  change probability A P = eventProbability μ (fun ω => P (X ω))
  have hprob_sum :
      probability A P = ∑ x ∈ H.filter P, eventProbability μ (fun ω => X ω = x) := by
    simp [probability, A, Finset.sum_filter]
  have hfiber_meas_P : ∀ x ∈ H.filter P,
      MeasurableSet (X ⁻¹' ({x} : Set (Fin N → ℝ))) := by
    intro x hx
    exact hfiber_meas x (Finset.mem_filter.mp hx).1
  have hsumP :
      (∑ x ∈ H.filter P, eventProbability μ (fun ω => X ω = x)) =
        μ.real (X ⁻¹' (H.filter P : Set (Fin N → ℝ))) := by
    calc
      _ = ∑ x ∈ H.filter P, μ.real (X ⁻¹' ({x} : Set (Fin N → ℝ))) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [eventProbability, MeasureTheory.measureReal_def]
        congr 1
      _ = μ.real (X ⁻¹' (H.filter P : Set (Fin N → ℝ))) :=
        MeasureTheory.sum_measureReal_preimage_singleton (H.filter P) hfiber_meas_P
  have hpreimage :
      X ⁻¹' (H.filter P : Set (Fin N → ℝ)) =ᵐ[μ] {ω | P (X ω)} := by
    filter_upwards [hsupport] with ω hω
    simp [hω]
  calc
    probability A P = ∑ x ∈ H.filter P, eventProbability μ (fun ω => X ω = x) := hprob_sum
    _ = μ.real (X ⁻¹' (H.filter P : Set (Fin N → ℝ))) := hsumP
    _ = μ.real {ω | P (X ω)} := MeasureTheory.measureReal_congr hpreimage
    _ = eventProbability μ (fun ω => P (X ω)) := rfl

