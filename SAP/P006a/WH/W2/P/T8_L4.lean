import SAP.P006a.WH.W2.Leaves
import AronowAudit.P006.Wave1.Gap.RepairT6T7

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

open SAP.P006a.WH.W2

theorem SAP.P006a.WH.W2.T8_L4_proof : SAP.P006a.WH.W2.T8_L4 := by
  unfold SAP.P006a.WH.W2.T8_L4 IndependentUnbiasedW2
  intro Ω X U _ _ _ n E PiSet hPiSet hS b0 hb0 hbi hu hI hR
  intro π hπ i
  let S := hS π hπ
  letI : IsProbabilityMeasure (E.law π) := S.law_probability
  rcases hI π hπ with ⟨A, mA, Z, f, hZ, hf⟩
  letI : MeasurableSpace A := mA
  have hπsingle : π ∈ ({π} : Set ((X × U) → ℝ)) := by simp
  obtain ⟨hfm, hrep, hi⟩ := hf π hπsingle
  let D := (Fin n → X × U) × (Fin n → Bool)
  let V : Ω → D := fun ω => ((fun j => E.X j ω), (fun j => E.T π j ω))
  let F : A × D → ℝ := fun z =>
    bit (z.2.2 i) * (f π z.1 (z.2.1 i) - b0 (z.2.1 i).1)
  have hV : Measurable V :=
    (measurable_pi_iff.mpr (fun j => (S.measurable_units j).1)).prodMk
      (measurable_pi_iff.mpr (fun j => (S.measurable_units j).2.2.2))
  have hx : Measurable (fun z : A × D => z.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have ht : Measurable (fun z : A × D => z.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  have hF : Measurable F :=
    ((measurable_of_countable bit).comp ht).mul
      ((hfm.comp (measurable_fst.prodMk hx)).sub
        (hb0.comp (measurable_fst.comp hx)))
  have heq : (fun ω => F (Z ω, V ω)) =
      TreatedResidualW2 E (fun c => b0 c.1) π i := by
    funext ω
    dsimp [F, V, TreatedResidualW2]
    rw [← hrep]
  have hFi : Integrable (fun ω => F (Z ω, V ω)) (E.law π) := by
    rw [heq]
    exact hR π hπ i
  have hmean (d : D) :
      (∫ z, F (z, d) ∂(E.law π).map Z) = (0 : ℝ) := by
    have hslice : Measurable (fun z : A => F (z, d)) :=
      hF.comp (measurable_id.prodMk measurable_const)
    rw [integral_map_of_stronglyMeasurable hZ hslice.stronglyMeasurable]
    calc
      (∫ ω, F (Z ω, d) ∂E.law π) =
          ∫ ω, bit (d.2 i) *
            (E.μhat π ω (d.1 i) - b0 (d.1 i).1) ∂E.law π := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by
          dsimp [F]
          rw [← hrep]
      _ = 0 := by
        have hu' := hu π hπ (d.1 i)
        rw [integral_const_mul, integral_sub hu'.1 (integrable_const _), hu'.2,
          integral_const]
        simp
  have hce := AronowAudit.P006.Wave1.RepairT6T7_auxiliary_condExp
    (E.law π) Z V hZ hV hi F (fun _ => 0) hF measurable_const hFi
    (integrable_const _) hmean
  rw [heq] at hce
  have hXv : Measurable[E.vectorSigma π] (E.X i) :=
    ((measurable_pi_apply i).comp measurable_fst).comp (comap_measurable V)
  have hsmall : E.covariateSigma i ≤ E.vectorSigma π := hXv.comap_le
  have hvle : E.vectorSigma π ≤ (inferInstance : MeasurableSpace Ω) := hV.comap_le
  have htower := condExp_condExp_of_le (μ := E.law π)
    (f := TreatedResidualW2 E (fun c => b0 c.1) π i) hsmall hvle
  exact htower.symm.trans ((condExp_congr_ae hce).trans (by simp))

