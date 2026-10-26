import AronowAudit.P001.Wave1.MarSelectionBlueprint
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.MarSelection

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n3_proof : N3.{u, v, w} := by
  intro _hN1 hN2 Ω E F _ _ _ μ _ X hX U R hU hR hbin hCI
  let P : Ω → E × F := fun ω => (X ω, U ω)
  let ρ : Ω → ℝ := μ[R | (MeasurableSpace.comap X inferInstance)]
  have hP : Measurable P := hX.prodMk hU
  have hG : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hH : (MeasurableSpace.comap P inferInstance) ≤ ‹MeasurableSpace Ω› := hP.comap_le
  have hGH : (MeasurableSpace.comap X inferInstance) ≤ (MeasurableSpace.comap P inferInstance) := by
    exact (measurable_fst.comp (comap_measurable P)).comap_le
  have hRb : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ (1 : ℝ) := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hRi : Integrable R μ := Integrable.of_bound hR.aestronglyMeasurable 1 hRb
  have hρi : Integrable ρ μ := integrable_condExp
  have hρm : StronglyMeasurable[(MeasurableSpace.comap P inferInstance)] ρ :=
    (stronglyMeasurable_condExp (μ := μ) (f := R) (m := (MeasurableSpace.comap X inferInstance))).mono hGH
  have htotal : (∫ ω, R ω ∂μ) = ∫ ω, ρ ω ∂μ := (integral_condExp hG).symm
  -- A direct π–λ proof for the two finite signed set integrals. This is the
  -- finite-measure uniqueness argument without constructing density measures.
  have htest : ∀ T : Set (E × F), MeasurableSet T →
      (∫ ω in P ⁻¹' T, R ω ∂μ) = ∫ ω in P ⁻¹' T, ρ ω ∂μ := by
    refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod
      ?_ ?_ ?_ ?_
    · simp
    · rintro _ ⟨C, hC, A, hA, rfl⟩
      exact hN2 μ X hX U R hU hR hbin hCI C A hC hA
    · intro T hT ih
      rw [Set.preimage_compl, setIntegral_compl (hT.preimage hP) hRi,
        setIntegral_compl (hT.preimage hP) hρi, htotal, ih]
    · intro T hd hT ih
      have hdP : Pairwise (fun i j => Disjoint (P ⁻¹' T i) (P ⁻¹' T j)) := by
        intro i j hij
        apply Set.disjoint_left.mpr
        intro ω hi hj
        exact Set.disjoint_left.mp (hd hij) hi hj
      simp only [Set.preimage_iUnion]
      rw [integral_iUnion (fun n => (hT n).preimage hP) hdP hRi.integrableOn,
        integral_iUnion (fun n => (hT n).preimage hP) hdP hρi.integrableOn]
      exact tsum_congr ih
  have hρeq : ρ =ᵐ[μ] μ[R | (MeasurableSpace.comap P inferInstance)] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hH hRi
      (fun _ _ _ => hρi.integrableOn) ?_ hρm.aestronglyMeasurable
    intro s hs _
    rcases hs with ⟨T, hT, rfl⟩
    exact (htest T hT).symm
  exact hρeq.symm

end

end AronowAudit.P001.Wave1.MarSelection
