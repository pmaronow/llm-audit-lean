import SAP.P029b.Defs.WholeW2
import SAP.P029b.Bridge
import AronowAudit.P029.Wave1.FiniteMeasure.N1
import AronowAudit.P029.Wave1.FiniteMeasure.N2
import AronowAudit.P029.Wave1.FiniteMeasure.N3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W2

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

def atomMass : CancelAtomW2 → ℝ := fun _ => 1/12
def profileTypeMass : Bool × Fin 3 → ℝ := fun _ => 1/6

theorem profileType_valid : ValidLaw profileTypeMass := by
  constructor
  · intro a
    norm_num [profileTypeMass]
  · norm_num [profileTypeMass, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]

theorem atom_randomized : atomMass = randomized profileTypeMass (1/2) := by
  funext a
  rcases a with ⟨⟨x,t⟩,z⟩
  cases z <;> norm_num [atomMass, randomized, profileTypeMass]

theorem atom_valid : ValidLaw atomMass := by
  rw [atom_randomized]
  exact AronowAudit.P029.randomized_valid profileTypeMass (1/2) profileType_valid
    (by norm_num) (by norm_num)

theorem atom_iv : FIV atomMass cancelUnitW2 Prod.snd := by
  refine ⟨atom_valid, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [fP, atomMass, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  · norm_num [fP, atomMass, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  · rw [atom_randomized]
    exact AronowAudit.P029.randomized_independent profileTypeMass (1/2) profileType_valid
      (fun a => let u := cancelUnitW2 (a,false); (u.x,u.d0,u.d1,u.y0,u.y1))
  · norm_num [fP, atomMass, cancelUnitW2, PotentialUnit.defier,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  · norm_num [fCE, fE, fP, atomMass, cancelUnitW2, PotentialUnit.receipt, bit,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]

theorem atom_measure : cancelLawW2 = atomicMeasure atomMass := by
  apply Measure.ext_of_singleton
  intro a
  simp [atomicMeasure, atomMass, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply', Pi.single_apply]

theorem cancellation_population : CancellationPopulationW2 := by
  have hN1 := n1_proof atomMass atom_valid
  have hP : ∀ S : Set CancelAtomW2,
      mP cancelLawW2 S = fP atomMass (fun a => a ∈ S) := by
    intro S
    rw [atom_measure]
    exact hN1.2.2.1 S
  have hCE : ∀ (v : CancelAtomW2 → ℝ) (S : Set CancelAtomW2),
      mCE cancelLawW2 v S = fCE atomMass v (fun a => a ∈ S) := by
    intro v S
    rw [atom_measure]
    exact hN1.2.2.2 v S
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [atom_measure]
    exact n3_proof n1_proof n2_proof atomMass (fun a => Bridge.toUnit (cancelUnitW2 a))
      Prod.snd atom_iv
  · intro x
    have hprofile : mP cancelLawW2 {a | (cancelUnitW2 a).x = x} = 1/2 := by
      rw [hP]
      cases x <;> norm_num [fP, atomMass, cancelUnitW2,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    have hc : scoreAt cancelLawW2 cancelUnitW2 x = 1/3 := by
      unfold scoreAt
      rw [hP, hP]
      cases x <;> norm_num [fP, atomMass, cancelUnitW2, PotentialUnit.complier,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    have hm : mCE cancelLawW2 (fun a => (cancelUnitW2 a).tau)
        {a | (cancelUnitW2 a).complier ∧ (cancelUnitW2 a).x = x} = 0 := by
      rw [hCE]
      cases x <;> norm_num [fCE, fE, fP, atomMass, cancelUnitW2, PotentialUnit.complier,
        PotentialUnit.tau, cancelSignW2, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    have ha : mCE cancelLawW2 (fun a => (cancelUnitW2 a).tau)
        {a | (cancelUnitW2 a).x = x} = if x then 4/3 else -4/3 := by
      rw [hCE]
      cases x <;> norm_num [fCE, fE, fP, atomMass, cancelUnitW2, PotentialUnit.tau,
        cancelSignW2, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    refine ⟨hprofile, hc, hm, ha, ?_⟩
    unfold latentAt
    rw [ha, hm]
    cases x <;> norm_num
  · intro x z
    rw [hCE]
    cases x <;> cases z <;>
      norm_num [fCE, fE, fP, atomMass, cancelUnitW2, PotentialUnit.receipt, bit,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  · rw [atom_measure, hN1.2.1 (fun a => (cancelUnitW2 a).tau) |>.2]
    norm_num [AronowAudit.P029.fE, atomMass, cancelUnitW2, PotentialUnit.tau,
      cancelSignW2, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  · rintro ⟨⟨x,t⟩,z⟩
    fin_cases t <;> cases x <;> cases z <;>
      norm_num [cancelUnitW2, cancelSignW2, PotentialUnit.outcome, PotentialUnit.receipt]

end
end SAP.P029b.WH.W2
