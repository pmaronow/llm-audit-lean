import AronowAudit.P047.Wave1.ImpossibilityBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem measurable_obsUnit : Measurable obsUnit :=
  measurable_covariate.prodMk (measurable_snd.fst.prodMk measurable_observed)

/-- Independence of all coordinates restricts to the injective list `Fin n → ℕ`. -/
theorem n6_proof : N6 := by
  intro μ _ n
  have hcoord : iIndepFun (fun i : ℕ => fun s : ℕ → UnitData => obsUnit (s i))
      (sampleLaw μ) := by
    exact iIndepFun_infinitePi (P := fun _ : ℕ => μ)
      (X := fun _ : ℕ => obsUnit) (fun _ => measurable_obsUnit)
  have hfin : iIndepFun (fun i : Fin n => fun s : ℕ → UnitData => obsUnit (s i.val))
      (sampleLaw μ) := hcoord.precomp (g := fun i : Fin n => i.val) Fin.val_injective
  have hm (i : Fin n) :
      Measurable (fun s : ℕ → UnitData => obsUnit (s i.val)) :=
    measurable_obsUnit.comp (measurable_pi_apply i.val)
  have hmargin (i : Fin n) :
      (sampleLaw μ).map (fun s : ℕ → UnitData => obsUnit (s i.val)) = μ.map obsUnit := by
    change (Measure.infinitePi (fun _ : ℕ => μ)).map (obsUnit ∘ Function.eval i.val) = _
    rw [← Measure.map_map measurable_obsUnit (measurable_pi_apply i.val),
      Measure.infinitePi_map_eval]
  change (sampleLaw μ).map (fun s (i : Fin n) => obsUnit (s i.val)) = _
  rw [hfin.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
  simp_rw [hmargin]

end

end AronowAudit.P047.Wave1.Impossibility
