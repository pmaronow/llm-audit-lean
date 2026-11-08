import SAP.P046.WH.W2.Leaves
import AronowAudit.P046.Wave1.Gap.GP046B4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W2.P.T8_L2

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

private theorem proofCore : SAP.P046.WH.W2.T8_L2 := by
  intro M hM n i H hHm hHi hInv
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    letI := hM.probability
    have hmultMeas : Measurable (fun a : Sample (n + 1) =>
        1 - X (a i) / M.pi (W (a i))) :=
      (AronowAudit.P046.Wave1.proposition4a_multiplier_measurable
        (Bridge.toStudy M) (Bridge.valid_to hM)).comp
        (measurable_pi_apply i)
    have hmultBound : ∀ᵐ a ∂sampleLaw M (n + 1),
        ‖1 - X (a i) / M.pi (W (a i))‖ ≤ 1 + M.delta⁻¹ := by
      exact (measurePreserving_eval (fun _ : Fin (n + 1) => M.law) i).quasiMeasurePreserving.ae
        (AronowAudit.P046.Wave1.proposition4a_multiplier_bound
          (Bridge.toStudy M) (Bridge.valid_to hM))
    have hprod : Integrable (fun a : Sample (n + 1) =>
        (1 - X (a i) / M.pi (W (a i))) * H a) (sampleLaw M (n + 1)) :=
      hHi.bdd_mul hmultMeas.aestronglyMeasurable hmultBound
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Unit) i
    have hpres := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => M.law) i).symm
    have hHcomp : Integrable (fun z : Unit × Sample n => H (e.symm z))
        (M.law.prod (sampleLaw M n)) :=
      hpres.integrable_comp_of_integrable hHi
    have hprodComp : Integrable (fun z : Unit × Sample n =>
        (1 - X (e.symm z i) / M.pi (W (e.symm z i))) * H (e.symm z))
        (M.law.prod (sampleLaw M n)) :=
      hpres.integrable_comp_of_integrable hprod
    have hzero : ∀ᵐ a ∂sampleLaw M n,
        (∫ o, (1 - X o / M.pi (W o)) *
          H (i.insertNth (α := fun _ : Fin (n + 1) => Unit) o a) ∂M.law) = 0 := by
      filter_upwards [hHcomp.prod_left_ae] with a ha
      let f : ℝ → ℝ := fun w =>
        H (i.insertNth (α := fun _ : Fin (n + 1) => Unit) (w, (false, (false, false))) a)
      have hinsertMeas : Measurable (fun w : ℝ =>
          i.insertNth (α := fun _ : Fin (n + 1) => Unit) (w, (false, (false, false))) a) := by
        apply measurable_pi_iff.mpr
        intro k
        by_cases hk : k = i
        · subst k
          simpa using (measurable_id.prodMk measurable_const :
            Measurable fun w : ℝ => (w, (false, (false, false))))
        · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
          simpa using (measurable_const : Measurable fun _ : ℝ => a j)
      have hfm : Measurable f := hHm.comp hinsertMeas
      have hsection : Integrable (fun o : Unit => H
          (i.insertNth (α := fun _ : Fin (n + 1) => Unit) o a)) M.law := by
        simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk] using ha
      have hfit (o : Unit) : H
          (i.insertNth (α := fun _ : Fin (n + 1) => Unit) o a) = f (W o) := by
        apply hInv
        · intro k hk
          obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
          simp [f]
        · simp [f, W]
      have hfint : Integrable (fun o : Unit => f (W o)) M.law :=
        hsection.congr (Filter.Eventually.of_forall hfit)
      calc
        (∫ o, (1 - X o / M.pi (W o)) * H
          (i.insertNth (α := fun _ : Fin (n + 1) => Unit) o a) ∂M.law) =
            ∫ o, (1 - X o / M.pi (W o)) * f (W o) ∂M.law := by
          apply integral_congr_ae
          filter_upwards [] with o
          rw [hfit]
        _ = 0 := AronowAudit.P046.Wave1.proposition4a_multiplier_cancel
          (Bridge.toStudy M) (Bridge.valid_to hM) f hfm hfint
    calc
      (∫ a, (1 - X (a i) / M.pi (W (a i))) * H a ∂sampleLaw M (n + 1)) =
          ∫ z : Unit × Sample n,
            (1 - X (e.symm z i) / M.pi (W (e.symm z i))) * H (e.symm z)
              ∂M.law.prod (sampleLaw M n) := (hpres.integral_comp' _).symm
      _ = ∫ a, ∫ o, (1 - X o / M.pi (W o)) * H
            (i.insertNth (α := fun _ : Fin (n + 1) => Unit) o a)
            ∂M.law ∂sampleLaw M n := by
        convert integral_prod_symm _ hprodComp using 1 <;>
          simp only [sampleLaw, Function.comp_def, e,
            MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Equiv.coe_fn_mk, Fin.insertNth_apply_same]
      _ = 0 := by rw [integral_congr_ae hzero, integral_zero]

end

end SAP.P046.WH.W2.P.T8_L2

theorem SAP.P046.WH.W2.T8_L2_proof : SAP.P046.WH.W2.T8_L2 :=
  SAP.P046.WH.W2.P.T8_L2.proofCore
