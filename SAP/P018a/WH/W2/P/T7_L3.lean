import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.P018_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018a.WH.W2.P.T7_L3

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open SAP.P018a

def enumDyad (d : Fin 28) : Dyad 8 :=
  ⟨eightMembers d, by
    fin_cases d <;> norm_num [eightMembers, dyads]⟩

lemma enumDyad_injective : Function.Injective enumDyad := by
  decide

noncomputable def enumDyadEquiv : Fin 28 ≃ Dyad 8 :=
  Equiv.ofBijective enumDyad
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨enumDyad_injective, by decide⟩)

lemma enumDyadEquiv_apply (d : Fin 28) : enumDyadEquiv d = enumDyad d := rfl

lemma enum_sum {α : Type*} [AddCommMonoid α] (f : Dyad 8 → α) :
    (∑ d : Dyad 8, f d) = ∑ d : Fin 28, f (enumDyad d) := by
  rw [← enumDyadEquiv.sum_comp f]
  simp only [enumDyadEquiv_apply]

lemma enumDyad_members (d : Fin 28) : members (enumDyad d) = eightMembers d := rfl

lemma enumDyad_data (d : Fin 28) :
    design signPairKernel wholeDegeneracyAtom (enumDyad d) = degeneracyX d ∧
    response signPairKernel wholeDegeneracyAtom (enumDyad d) = degeneracyY d := by
  fin_cases d <;>
    norm_num [enumDyad, design, response, firstUnit, secondUnit, members,
      signPairKernel, wholeDegeneracyAtom, signValue, degeneracyX, degeneracyY,
      degeneracyZ, degeneracyW, eightMembers]

lemma enumDyad_design (d : Fin 28) :
    design signPairKernel wholeDegeneracyAtom (enumDyad d) = degeneracyX d :=
  (enumDyad_data d).1

lemma enumDyad_response (d : Fin 28) :
    response signPairKernel wholeDegeneracyAtom (enumDyad d) = degeneracyY d :=
  (enumDyad_data d).2

lemma atom_gram :
    sampleGram (design signPairKernel wholeDegeneracyAtom) = sampleGram degeneracyX := by
  unfold sampleGram
  rw [enum_sum]
  simp_rw [enumDyad_design]

lemma atom_score_sum :
    (∑ d : Dyad 8, score (design signPairKernel wholeDegeneracyAtom d)
      (response signPairKernel wholeDegeneracyAtom d)) =
    ∑ d : Fin 28, score (degeneracyX d) (degeneracyY d) := by
  rw [enum_sum]
  simp_rw [enumDyad_design, enumDyad_response]

lemma table_meat :
    meat eightMembers (fun d => score (degeneracyX d)
      (fittedResidual degeneracyX degeneracyY d)) = !![240,160;160,64] := by
  have hs : ∀ d : Fin 28, (eightMembers d).card = 2 := by decide
  have hi : Function.Injective eightMembers := by decide
  have hfit : sampleOLS degeneracyX degeneracyY = 0 :=
    AronowAudit.P018.degenerate_numeric_certificate.2.2.1
  have hres : ∀ d, fittedResidual degeneracyX degeneracyY d = degeneracyY d := by
    intro d
    simp [fittedResidual, hfit, dot]
  change AronowAudit.P018.meat eightMembers
      (fun d => score (degeneracyX d) (fittedResidual degeneracyX degeneracyY d)) = _
  rw [AronowAudit.P018.overlap_meat_identity eightMembers hs hi]
  simp_rw [hres]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitScore, dyadMeat, AronowAudit.P018.unitScore,
      AronowAudit.P018.dyadMeat, AronowAudit.P018.outer, outer, score, degeneracyX, degeneracyY,
      degeneracyZ, degeneracyW, eightMembers, Matrix.of_apply, Fin.sum_univ_succ,
      funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]

lemma atom_meat (hfit : sampleOLS (design signPairKernel wholeDegeneracyAtom)
    (response signPairKernel wholeDegeneracyAtom) = 0) :
    meat members (fun d => score (design signPairKernel wholeDegeneracyAtom d)
      (fittedResidual (design signPairKernel wholeDegeneracyAtom)
        (response signPairKernel wholeDegeneracyAtom) d)) =
    meat eightMembers (fun d => score (degeneracyX d)
      (fittedResidual degeneracyX degeneracyY d)) := by
  have hres (d : Dyad 8) :
      fittedResidual (design signPairKernel wholeDegeneracyAtom)
        (response signPairKernel wholeDegeneracyAtom) d =
      response signPairKernel wholeDegeneracyAtom d := by
    simp [fittedResidual, hfit, dot]
  have hresTable (d : Fin 28) :
      fittedResidual degeneracyX degeneracyY d = degeneracyY d := by
    have hfitTable : sampleOLS degeneracyX degeneracyY = 0 :=
      AronowAudit.P018.degenerate_numeric_certificate.2.2.1
    simp [fittedResidual, hfitTable, dot]
  unfold meat
  rw [enum_sum (fun d : Dyad 8 =>
    ∑ f : Dyad 8, if (members d ∩ members f).Nonempty then
      outer (score (design signPairKernel wholeDegeneracyAtom d)
        (fittedResidual (design signPairKernel wholeDegeneracyAtom)
          (response signPairKernel wholeDegeneracyAtom) d))
        (score (design signPairKernel wholeDegeneracyAtom f)
          (fittedResidual (design signPairKernel wholeDegeneracyAtom)
            (response signPairKernel wholeDegeneracyAtom) f)) else 0)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [enum_sum (fun f : Dyad 8 =>
    if (members (enumDyad d) ∩ members f).Nonempty then
      outer (score (design signPairKernel wholeDegeneracyAtom (enumDyad d))
        (fittedResidual (design signPairKernel wholeDegeneracyAtom)
          (response signPairKernel wholeDegeneracyAtom) (enumDyad d)))
        (score (design signPairKernel wholeDegeneracyAtom f)
          (fittedResidual (design signPairKernel wholeDegeneracyAtom)
            (response signPairKernel wholeDegeneracyAtom) f)) else 0)]
  apply Finset.sum_congr rfl
  intro f hf
  simp only [enumDyad_members, enumDyad_design,
    enumDyad_response, hres, hresTable]

lemma atom_variance (hfit : sampleOLS (design signPairKernel wholeDegeneracyAtom)
    (response signPairKernel wholeDegeneracyAtom) = 0) :
    sampleVariance members (design signPairKernel wholeDegeneracyAtom)
      (response signPairKernel wholeDegeneracyAtom) =
    sampleVariance eightMembers degeneracyX degeneracyY := by
  unfold sampleVariance
  rw [atom_gram, atom_meat hfit]

lemma fairLaw_singleton (b : Bool) :
    fairLaw {b} = ENNReal.ofReal ((2 : ℝ)⁻¹) := by
  letI : IsProbabilityMeasure fairLaw := AronowAudit.P018.Wave1.printed_fair_probability
  rw [fairLaw, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton b)]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num [PMF.uniformOfFintype_apply]

lemma signPairLaw_singleton (z : Bool × Bool) :
    signPairKernel.μ {z} = ENNReal.ofReal ((4 : ℝ)⁻¹) := by
  letI : IsProbabilityMeasure fairLaw := AronowAudit.P018.Wave1.printed_fair_probability
  change (fairLaw.prod fairLaw) {z} = _
  rw [show ({z} : Set (Bool × Bool)) = ({z.1} : Set Bool) ×ˢ ({z.2} : Set Bool) by
    ext x
    simp]
  rw [Measure.prod_prod, fairLaw_singleton, fairLaw_singleton,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1 <;> norm_num

lemma atom_mass :
    unitSampleLaw signPairKernel 8 {wholeDegeneracyAtom} =
      ENNReal.ofReal ((4 : ℝ)⁻¹^8) := by
  letI : IsProbabilityMeasure fairLaw := AronowAudit.P018.Wave1.printed_fair_probability
  letI : IsProbabilityMeasure signPairKernel.μ := by
    change IsProbabilityMeasure (fairLaw.prod fairLaw)
    infer_instance
  change Measure.pi (fun _ : Fin 8 => signPairKernel.μ) {wholeDegeneracyAtom} = _
  rw [Measure.pi_singleton]
  simp_rw [signPairLaw_singleton]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

end SAP.P018a.WH.W2.P.T7_L3

theorem SAP.P018a.WH.W2.T7_L3_proof : SAP.P018a.WH.W2.T7_L3 := by
  obtain ⟨hGramTable, _, hFitTable, hVarianceTable, _⟩ :=
    AronowAudit.P018.degenerate_numeric_certificate
  have hScoreTable :
      (∑ d : Fin 28, SAP.P018a.score (SAP.P018a.degeneracyX d)
        (SAP.P018a.degeneracyY d)) = 0 := by
    ext i
    fin_cases i <;>
      norm_num [SAP.P018a.score, SAP.P018a.degeneracyX, SAP.P018a.degeneracyY,
      SAP.P018a.degeneracyZ, SAP.P018a.degeneracyW, SAP.P018a.eightMembers,
      Fin.sum_univ_succ]
  have hGramAtom :
      SAP.P018a.sampleGram (SAP.P018a.design SAP.P018a.signPairKernel
        SAP.P018a.wholeDegeneracyAtom) = !![28,24;24,48] := by
    rw [SAP.P018a.WH.W2.P.T7_L3.atom_gram]
    exact hGramTable
  have hFitAtom :
      SAP.P018a.sampleOLS (SAP.P018a.design SAP.P018a.signPairKernel
        SAP.P018a.wholeDegeneracyAtom)
        (SAP.P018a.response SAP.P018a.signPairKernel SAP.P018a.wholeDegeneracyAtom) = 0 := by
    unfold SAP.P018a.sampleOLS
    rw [hGramAtom, SAP.P018a.WH.W2.P.T7_L3.atom_score_sum, hScoreTable]
    simp
  have hMeatAtom :
      SAP.P018a.meat SAP.P018a.members (fun d => SAP.P018a.score
        (SAP.P018a.design SAP.P018a.signPairKernel SAP.P018a.wholeDegeneracyAtom d)
        (SAP.P018a.fittedResidual (SAP.P018a.design SAP.P018a.signPairKernel
          SAP.P018a.wholeDegeneracyAtom)
          (SAP.P018a.response SAP.P018a.signPairKernel SAP.P018a.wholeDegeneracyAtom) d)) =
      !![240,160;160,64] := by
    rw [SAP.P018a.WH.W2.P.T7_L3.atom_meat hFitAtom]
    exact SAP.P018a.WH.W2.P.T7_L3.table_meat
  have hVarianceAtom :
      SAP.P018a.sampleVariance SAP.P018a.members
        (SAP.P018a.design SAP.P018a.signPairKernel SAP.P018a.wholeDegeneracyAtom)
        (SAP.P018a.response SAP.P018a.signPairKernel SAP.P018a.wholeDegeneracyAtom) =
      !![3/8,-1/48;-1/48,-13/288] := by
    rw [SAP.P018a.WH.W2.P.T7_L3.atom_variance hFitAtom]
    exact hVarianceTable
  have hMass := SAP.P018a.WH.W2.P.T7_L3.atom_mass
  have hMassPos : 0 < SAP.P018a.unitSampleLaw SAP.P018a.signPairKernel 8
      {SAP.P018a.wholeDegeneracyAtom} := by
    rw [hMass]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  exact ⟨SAP.P018a.WH.W2.P.T7_L3.table_meat, hMass, hMassPos,
    hGramAtom, hFitAtom, hMeatAtom, hVarianceAtom⟩
