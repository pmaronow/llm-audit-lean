import AronowAudit.P029.Wave1.IgnorabilityOrderingBlueprint

namespace AronowAudit.P029.Wave1.IgnorabilityOrdering

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- Transfer the closed six-atom certificate to the measure-valued witness. -/
theorem n1_proof : N1 := by
  classical
  intro hFM1 hFM2 hFM3 hFM6
  rcases ignorability_counterexample with
    ⟨hfiv, htyp, _hdt, _hdf, _hct, _hcf, hmean, hcomp, hscore, _hscorelb, _hw, _hww⟩
  have hp : ValidLaw sixMass := hfiv.1
  obtain ⟨hprob, _hIntegral, hMass, hCE⟩ := hFM1 sixMass hp
  have hiv : IVAssumptions (atomicMeasure sixMass) (liftUnit case1Unit) Prod.snd :=
    hFM3 hFM1 hFM2 sixMass (liftUnit case1Unit) Prod.snd hfiv
  have hX : ∀ i : Fin 3 × Bool, (liftUnit case1Unit i).x = () := by
    intro i
    exact Subsingleton.elim _ _
  have hprofile : mP (atomicMeasure sixMass)
      {i | (liftUnit case1Unit i).x = ()} = 1 := by
    rw [hMass]
    simpa only [fP, Set.mem_setOf_eq, hX, if_true] using hp.2
  have hscoreM : scoreAt (atomicMeasure sixMass) (liftUnit case1Unit) () = 1 / 2 :=
    ((hFM6 hFM1 sixMass hp (liftUnit case1Unit) Prod.snd).2 ()).trans hscore
  have htypM : typicalAt (atomicMeasure sixMass) (liftUnit case1Unit) Prod.snd () := by
    simpa only [typicalAt, fTypicalIgnorability, hCE, Set.mem_setOf_eq] using htyp
  have hfMean : fE sixMass (fun i => (liftUnit case1Unit i).tau) = 1 / 2 := hmean
  have hfComp : fCE sixMass (fun i => (liftUnit case1Unit i).tau)
      (fun i => (liftUnit case1Unit i).complier) = 1 := hcomp
  have hmeanX : mCE (atomicMeasure sixMass) (fun i => (liftUnit case1Unit i).tau)
      {i | (liftUnit case1Unit i).x = ()} = 1 / 2 := by
    rw [hCE]
    simpa only [Set.mem_setOf_eq, fCE, fP, hX, if_true, hp.2, div_one] using hfMean
  have hmeanC : mCE (atomicMeasure sixMass) (fun i => (liftUnit case1Unit i).tau)
      {i | (liftUnit case1Unit i).complier ∧ (liftUnit case1Unit i).x = ()} = 1 := by
    rw [hCE]
    simpa only [Set.mem_setOf_eq, hX, and_true] using hfComp
  refine ⟨hprob, hiv, ?_, ?_, htypM, ?_⟩
  · rw [hprofile]
    norm_num
  · rw [hscoreM]
    norm_num
  · intro hlatent
    unfold latentAt at hlatent
    have hbad : (1 / 2 : ℝ) = 1 :=
      hmeanX.symm.trans (hlatent.trans hmeanC)
    norm_num at hbad

end

end AronowAudit.P029.Wave1.IgnorabilityOrdering
