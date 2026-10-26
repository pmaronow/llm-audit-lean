import AronowAudit.P029.Wave1.LateIdentityBlueprint

namespace AronowAudit.P029.Wave1.LateIdentity

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

/-- Measurable maps of the potential-response tuple inherit assignment independence. -/
theorem n2_proof : N2.{u, v} := by
  intro Ω X _ _ μ _ U Z hiv
  rcases hiv with
    ⟨hx, hd0, hd1, hy0, hy1, hZ, hi0, hi1, hind, he0, he1, hdef, hrel⟩
  let R : Bool → (X × Bool × Bool × ℝ × ℝ) → Bool :=
    fun z t => if z then t.2.2.1 else t.2.1
  let Y : Bool → (X × Bool × Bool × ℝ × ℝ) → ℝ :=
    fun z t => if R z t then t.2.2.2.2 else t.2.2.2.1
  have hR (z : Bool) : Measurable (R z) := by
    cases z with
    | false =>
        simpa [R, Function.comp_def] using
          (measurable_fst.comp measurable_snd :
            Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.1))
    | true =>
        simpa [R, Function.comp_def] using
          (measurable_fst.comp (measurable_snd.comp measurable_snd) :
            Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.2.1))
  have hY0 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hY1 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hY (z : Bool) : Measurable (Y z) :=
    Measurable.ite ((measurableSet_singleton true).preimage (hR z)) hY1 hY0
  have hbit : Measurable bit := Measurable.of_discrete
  have hreceipt (z : Bool) : Measurable (fun ω => (U ω).receipt z) := by
    cases z with
    | false => simpa [PotentialUnit.receipt] using hd0
    | true => simpa [PotentialUnit.receipt] using hd1
  have houtcome (z : Bool) : Measurable (fun ω => (U ω).outcome z) :=
    Measurable.ite ((measurableSet_singleton true).preimage (hreceipt z)) hy1 hy0
  have hindD (z : Bool) : IndepFun Z (fun ω => bit ((U ω).receipt z)) μ := by
    simpa only [Function.comp_def, R, PotentialUnit.receipt, id_eq] using
      hind.comp (measurable_id : Measurable (id : Bool → Bool)) (hbit.comp (hR z))
  have hindY (z : Bool) : IndepFun Z (fun ω => (U ω).outcome z) μ := by
    convert hind.comp (measurable_id : Measurable (id : Bool → Bool)) (hY z) using 1 <;>
      rfl
  have hiD (z : Bool) : Integrable (fun ω => bit ((U ω).receipt z)) μ := by
    apply (integrable_const (μ := μ) (1 : ℝ)).mono'
      (hbit.comp (hreceipt z)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      cases hd : (U ω).receipt z <;> norm_num [bit, hd])
  have hiY (z : Bool) : Integrable (fun ω => (U ω).outcome z) μ := by
    apply (hi0.abs.add hi1.abs).mono' (houtcome z).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      cases hd : (U ω).receipt z <;>
        simp [PotentialUnit.outcome, hd, Real.norm_eq_abs] <;>
        linarith [abs_nonneg ((U ω).y0), abs_nonneg ((U ω).y1)])
  have hC : MeasurableSet {ω | (U ω).complier} := by
    change MeasurableSet ({ω | (U ω).d0 = false} ∩ {ω | (U ω).d1 = true})
    exact ((measurableSet_singleton false).preimage hd0).inter
      ((measurableSet_singleton true).preimage hd1)
  have hiTau : Integrable (fun ω => (U ω).tau) μ := hi1.sub hi0
  have hiCTau : Integrable (fun ω => if (U ω).complier then (U ω).tau else 0) μ := by
    have heq : (fun ω => if (U ω).complier then (U ω).tau else 0) =
        {ω | (U ω).complier}.indicator (fun ω => (U ω).tau) := funext (fun ω => rfl)
    rw [heq]
    exact hiTau.indicator hC
  refine ⟨?_, hiCTau, hC⟩
  intro z
  exact ⟨hiD z, hiY z, hindD z, hindY z, (measurableSet_singleton z).preimage hZ⟩

end

end AronowAudit.P029.Wave1.LateIdentity
