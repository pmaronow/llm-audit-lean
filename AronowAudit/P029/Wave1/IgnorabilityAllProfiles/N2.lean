import AronowAudit.P029.Wave1.IgnorabilityAllProfilesBlueprint

namespace AronowAudit.P029.Wave1.IgnorabilityAllProfiles

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- A genuine constant conditional kernel realizes the ordering counterexample. -/
theorem n2_proof : N2 := by
  classical
  intro hFM1 hFM2 hFM3 hLaw
  have ht : ValidLaw typeMass := by
    constructor
    · intro i
      unfold typeMass
      split <;> norm_num
    · norm_num [typeMass, Fin.sum_univ_succ]
  obtain ⟨hnuProb, hnuIntegral, hnuMass, hnuCE⟩ := hFM1 typeMass ht
  haveI : IsProbabilityMeasure nu := hnuProb
  have hmu : IsProbabilityMeasure muX := by
    change IsProbabilityMeasure (Measure.dirac ())
    infer_instance
  have hmarkov : IsMarkovKernel kappa := by
    change IsMarkovKernel (Kernel.const Unit nu)
    infer_instance
  have hprofile : ∀ x ∈ muX.support, ∀ᵐ i ∂kappa x, (case1Unit i).x = x := by
    intro x _hx
    exact Filter.Eventually.of_forall (fun _i => Subsingleton.elim _ _)
  have hsupp : () ∈ muX.support := by
    rw [Measure.mem_support_iff_forall ()]
    intro s hs
    have hmem : () ∈ s := mem_of_mem_nhds hs
    change 0 < (Measure.dirac ()) s
    rw [Measure.dirac_apply_of_mem hmem]
    exact zero_lt_one
  -- Insert the inert Unit coordinate before adjoining independent assignment.
  let p : Unit × Fin 3 → ℝ := fun l => typeMass l.2
  let u : Unit × Fin 3 → PotentialUnit Unit := fun l => case1Unit l.2
  have hp : ValidLaw p := by
    constructor
    · intro l
      exact ht.1 l.2
    · simpa only [p, Fintype.sum_prod_type, Fintype.sum_unique] using ht.2
  have hv : ValidLaw (randomized p (1 / 2)) :=
    randomized_valid p (1 / 2) hp (by norm_num) (by norm_num)
  have hind : FIndep (randomized p (1 / 2))
      (fun i => ((liftUnit u i).x, (liftUnit u i).d0, (liftUnit u i).d1,
        (liftUnit u i).y0, (liftUnit u i).y1)) Prod.snd :=
    randomized_independent p (1 / 2) hp
      (fun l => ((u l).x, (u l).d0, (u l).d1, (u l).y0, (u l).y1))
  have hfiv : FIV (randomized p (1 / 2)) (liftUnit u) Prod.snd := by
    refine ⟨hv, ?_, ?_, hind, ?_, ?_⟩
    all_goals norm_num [fCE, fE, fP, randomized, p, u, liftUnit, typeMass, case1Unit,
      bit, PotentialUnit.receipt, PotentialUnit.defier, Fintype.sum_prod_type,
      Fintype.sum_unique, Fintype.sum_bool, Fin.sum_univ_succ]
  have hglobal : IVAssumptions (kernelPopulationLaw muX kappa (1 / 2))
      (kernelPopulationUnit case1Unit) Prod.snd := by
    rw [hLaw.1]
    have hu : liftUnit u = kernelPopulationUnit case1Unit := rfl
    simpa only [p, hu] using
      hFM3 hFM1 hFM2 (randomized p (1 / 2)) (liftUnit u) Prod.snd hfiv
  have hy0 : Integrable (fun i => (case1Unit i).y0) (kappa ()) := by
    change Integrable (fun i => (case1Unit i).y0) nu
    exact Integrable.of_finite
  have hy1 : Integrable (fun i => (case1Unit i).y1) (kappa ()) := by
    change Integrable (fun i => (case1Unit i).y1) nu
    exact Integrable.of_finite
  have hc : mP (kappa ()) {i | (case1Unit i).complier} = 1 / 2 := by
    change mP (atomicMeasure typeMass) {i | (case1Unit i).complier} = 1 / 2
    rw [hnuMass]
    norm_num [Set.mem_setOf_eq, fP, typeMass, case1Unit, PotentialUnit.complier,
      Fin.sum_univ_succ]
  obtain ⟨_hSixProb, _hSixIntegral, _hSixMass, hSixCE⟩ :=
    hFM1 sixMass ignorability_counterexample.1.1
  have htyp : typicalAt ((kappa ()).prod (bernoulliMeasure (1 / 2)))
      (liftUnit case1Unit) Prod.snd () := by
    rw [hLaw.2]
    simpa only [typicalAt, fTypicalIgnorability, hSixCE, Set.mem_setOf_eq] using
      ignorability_counterexample.2.1
  have hmean : (∫ i, (case1Unit i).tau ∂(kappa ())) = 1 / 2 := by
    change (∫ i, (case1Unit i).tau ∂(atomicMeasure typeMass)) = 1 / 2
    rw [(hnuIntegral (fun i => (case1Unit i).tau)).2]
    norm_num [fE, typeMass, case1Unit, PotentialUnit.tau, Fin.sum_univ_succ]
  have hcomp : mCE (kappa ()) (fun i => (case1Unit i).tau)
      {i | (case1Unit i).complier} = 1 := by
    change mCE (atomicMeasure typeMass) (fun i => (case1Unit i).tau)
      {i | (case1Unit i).complier} = 1
    rw [hnuCE]
    norm_num [Set.mem_setOf_eq, fCE, fE, fP, typeMass, case1Unit,
      PotentialUnit.tau, PotentialUnit.complier, Fin.sum_univ_succ]
  refine ⟨hmu, hmarkov, hprofile, hglobal, hsupp, hy0, hy1, ?_, htyp, ?_⟩
  · rw [hc]
    norm_num
  · intro heq
    have hbad : (1 / 2 : ℝ) = 1 := hmean.symm.trans (heq.trans hcomp)
    norm_num at hbad

end

end AronowAudit.P029.Wave1.IgnorabilityAllProfiles
