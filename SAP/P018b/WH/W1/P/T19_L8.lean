import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018b.WH.W1.P.T19_L8

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

abbrev AuxUnit := AronowAudit.P018.RareUnit × ℝ

def auxUniform : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

def auxUnitLaw : Measure AuxUnit := rareModel.μ.prod auxUniform

lemma auxUniform_nullSingleton : NullSingletonClass auxUniform := by
  dsimp [auxUniform]
  infer_instance

lemma auxUnitLaw_snd_ae_ne (c : ℝ) : ∀ᵐ z ∂auxUnitLaw, z.2 ≠ c := by
  letI : IsProbabilityMeasure rareModel.μ := rareModel_law.1
  haveI : SigmaFinite auxUniform := by
    dsimp [auxUniform]
    infer_instance
  letI : NullSingletonClass auxUniform := auxUniform_nullSingleton
  change ∀ᵐ z ∂rareModel.μ.prod auxUniform, z.2 ≠ c
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  exact Filter.Eventually.of_forall (fun _ => Measure.ae_ne auxUniform c)

lemma measurableSet_inj_snd (N : ℕ) :
    MeasurableSet {ω : Fin N → AuxUnit | Function.Injective (fun i => (ω i).2)} := by
  classical
  have hEq :
      {ω : Fin N → AuxUnit | Function.Injective (fun i => (ω i).2)} =
        ⋂ i : Fin N, ⋂ j : Fin N, {ω | (ω i).2 = (ω j).2 → i = j} := by
    ext ω
    simp [Function.Injective]
  rw [hEq]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i = j
  · simp [hij]
  · have hfi : Measurable (fun ω : Fin N → AuxUnit => (ω i).2) :=
      (measurable_pi_apply i).snd
    have hfj : Measurable (fun ω : Fin N → AuxUnit => (ω j).2) :=
      (measurable_pi_apply j).snd
    have heq : MeasurableSet {ω : Fin N → AuxUnit | (ω i).2 = (ω j).2} :=
      measurableSet_eq_fun hfi hfj
    have hne : Measurable fun ω : Fin N → AuxUnit => ¬ (ω i).2 = (ω j).2 := by
      apply measurableSet_setOfPred.mp
      simpa only [Set.compl_setOf] using heq.compl
    simpa [hij] using hne

lemma auxLabels_injective_ae (N : ℕ) :
    ∀ᵐ ω : Fin N → AuxUnit ∂ Measure.pi (fun _ : Fin N => auxUnitLaw),
      Function.Injective (fun i => (ω i).2) := by
  classical
  letI : IsProbabilityMeasure rareModel.μ := rareModel_law.1
  haveI : SigmaFinite auxUniform := by
    dsimp [auxUniform]
    infer_instance
  haveI : SigmaFinite auxUnitLaw := by
    dsimp [auxUnitLaw]
    infer_instance
  induction N with
  | zero =>
      filter_upwards [] with ω
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      let e : MeasurableEquiv (Fin (n+1) → AuxUnit)
          (AuxUnit × (Fin n → AuxUnit)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => AuxUnit) 0
      let μtail : Measure (Fin n → AuxUnit) := Measure.pi (fun _ : Fin n => auxUnitLaw)
      have hsplit := MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ : Fin (n+1) => auxUnitLaw) 0
      have hdiff (x : AuxUnit) :
          ∀ᵐ y : Fin n → AuxUnit ∂ μtail, ∀ j, (y j).2 ≠ x.2 := by
        rw [ae_all_iff]
        intro j
        exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => auxUnitLaw)
          (i := j)).eventually (auxUnitLaw_snd_ae_ne x.2)
      have hprod :
          ∀ᵐ z : AuxUnit × (Fin n → AuxUnit) ∂ auxUnitLaw.prod μtail,
            Function.Injective (fun i => (e.symm z i).2) := by
        apply (Measure.ae_prod_iff_ae_ae
          (measurableSet_inj_snd (n+1) |>.preimage e.symm.measurable)).2
        filter_upwards [] with x
        filter_upwards [ih, hdiff x] with y hy hd
        intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => rfl
            | succ j =>
                have heq : x.2 = (y j).2 := by
                  simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
                    Fin.insertNthEquiv, Fin.insertNth_zero] using hij
                exact (hd j heq.symm).elim
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                have heq : (y i).2 = x.2 := by
                  simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
                    Fin.insertNthEquiv, Fin.insertNth_zero] using hij
                exact (hd i heq).elim
            | succ j =>
                have heq : (y i).2 = (y j).2 := by
                  simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
                    Fin.insertNthEquiv, Fin.insertNth_zero] using hij
                exact congrArg Fin.succ (hy heq)
      have hmap :
          ∀ᵐ z ∂ Measure.map e (Measure.pi (fun _ : Fin (n+1) => auxUnitLaw)),
            Function.Injective (fun i => (e.symm z i).2) := by
        rw [hsplit.map_eq]
        simpa [μtail] using hprod
      have hmeas : MeasurableSet
          {z : AuxUnit × (Fin n → AuxUnit) |
            Function.Injective (fun i => (e.symm z i).2)} :=
        (measurableSet_inj_snd (n+1)).preimage e.symm.measurable
      have hpi := (MeasureTheory.ae_map_iff e.measurable.aemeasurable hmeas).mp hmap
      simpa using hpi

lemma sum_fin_two_reverse {α : Type*} [AddCommMonoid α] (f : Fin 2 → α) :
    (∑ t : Fin 2, f (Fin.rev t)) = ∑ t : Fin 2, f t := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Fin.rev, add_comm]

lemma sum_fin_two_reindexed {α : Type*} [AddCommMonoid α]
    (a b : ℝ) (hne : a ≠ b) (f : Fin 2 → α) :
    (∑ t : Fin 2, f (if a = b then 0 else if a < b then t else Fin.rev t)) =
      ∑ t : Fin 2, f t := by
  have hne' : ¬ a = b := hne
  simp only [if_neg hne']
  by_cases hlt : a < b
  · simp [hlt]
  · simp only [if_neg hlt]
    exact sum_fin_two_reverse f

lemma first_ne_second {N : ℕ} (d : Dyad N) : firstUnit d ≠ secondUnit d := by
  exact (Finset.min'_lt_max'_of_card (members d) (by rw [members_card]; omega)).ne

lemma directed_sum_eq {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) (d : Dyad N)
    (f : Fin 2 → Vec 2) :
    (∑ t : Fin 2,
      f (if (ω (firstUnit d)).2 = (ω (secondUnit d)).2 then 0
        else if (ω (firstUnit d)).2 < (ω (secondUnit d)).2 then t else Fin.rev t)) =
      ∑ t : Fin 2, f t := by
  apply sum_fin_two_reindexed
  intro h
  exact first_ne_second d (hω h)

def recordIndex {N : ℕ} (ω : Fin N → AuxUnit) (d : Dyad N) (t : Fin 2) : Fin 2 :=
  if (ω (firstUnit d)).2 = (ω (secondUnit d)).2 then 0
  else if (ω (firstUnit d)).2 < (ω (secondUnit d)).2 then t else Fin.rev t

lemma endpoint_aux_ne {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) (d : Dyad N) :
    (ω (firstUnit d)).2 ≠ (ω (secondUnit d)).2 := by
  intro h
  exact first_ne_second d (hω h)

lemma sum_recordIndex {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) (d : Dyad N)
    {α : Type*} [AddCommMonoid α] (f : Fin 2 → α) :
    (∑ t : Fin 2, f (recordIndex ω d t)) = ∑ t : Fin 2, f t := by
  exact sum_fin_two_reindexed (ω (firstUnit d)).2 (ω (secondUnit d)).2
    (endpoint_aux_ne ω hω d) f

lemma directed_recordX {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) (d : Dyad N) (t : Fin 2) :
    repeatedX (wholeRareDirected rareModel) ω d t =
      repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d (recordIndex ω d t) := by
  simp [repeatedX, wholeRareDirected, wholeRareKernel, recordIndex,
    endpoint_aux_ne ω hω d]

lemma directed_recordY {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) (d : Dyad N) (t : Fin 2) :
    repeatedY (wholeRareDirected rareModel) ω d t =
      repeatedY (wholeRareKernel rareModel) (fun i => (ω i).1) d (recordIndex ω d t) := by
  simp [repeatedY, wholeRareDirected, wholeRareKernel, recordIndex,
    endpoint_aux_ne ω hω d]

lemma weightedGram_eq {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) :
    wholeWeightedGram (wholeRareDirected rareModel) (fun _ _ => 1) ω =
      repeatedGram (wholeRareKernel rareModel) (fun i => (ω i).1) := by
  change (∑ d : Dyad N, ∑ t : Fin 2,
      (1 : ℝ) • outer (repeatedX (wholeRareDirected rareModel) ω d t)
        (repeatedX (wholeRareDirected rareModel) ω d t)) =
    ∑ d : Dyad N, ∑ t : Fin 2,
      outer (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t)
        (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t)
  simp only [one_smul]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    (∑ t : Fin 2, outer (repeatedX (wholeRareDirected rareModel) ω d t)
        (repeatedX (wholeRareDirected rareModel) ω d t)) =
      ∑ t : Fin 2, outer
        (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d (recordIndex ω d t))
        (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d (recordIndex ω d t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [directed_recordX ω hω d t]
    _ = ∑ t : Fin 2, outer
        (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t)
        (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t) :=
          sum_recordIndex ω hω d
            (fun t => outer
              (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t)
              (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t))

lemma weightedXY_eq {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) :
    wholeWeightedXY (wholeRareDirected rareModel) (fun _ _ => 1) ω =
      ∑ d : Dyad N, ∑ t : Fin 2,
        score (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t)
          (repeatedY (wholeRareKernel rareModel) (fun i => (ω i).1) d t) := by
  change (∑ d : Dyad N, ∑ t : Fin 2,
      score (repeatedX (wholeRareDirected rareModel) ω d t)
        ((1 : ℝ) * repeatedY (wholeRareDirected rareModel) ω d t)) = _
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    (∑ t : Fin 2, score (repeatedX (wholeRareDirected rareModel) ω d t)
        (repeatedY (wholeRareDirected rareModel) ω d t)) =
      ∑ t : Fin 2, score
        (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d (recordIndex ω d t))
        (repeatedY (wholeRareKernel rareModel) (fun i => (ω i).1) d (recordIndex ω d t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [directed_recordX ω hω d t, directed_recordY ω hω d t]
    _ = ∑ t : Fin 2, score
        (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t)
        (repeatedY (wholeRareKernel rareModel) (fun i => (ω i).1) d t) :=
          sum_recordIndex ω hω d
            (fun t => score
              (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t)
              (repeatedY (wholeRareKernel rareModel) (fun i => (ω i).1) d t))

lemma weightedBlockScore_eq {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) (β : Vec 2) (d : Dyad N) :
    wholeWeightedBlockScore (wholeRareDirected rareModel) (fun _ _ => 1) β ω d =
      repeatedBlockScore (wholeRareKernel rareModel) β (fun i => (ω i).1) d := by
  change (∑ t : Fin 2, score (repeatedX (wholeRareDirected rareModel) ω d t)
      ((1 : ℝ) * (repeatedY (wholeRareDirected rareModel) ω d t -
        dot (repeatedX (wholeRareDirected rareModel) ω d t) β))) = _
  simp only [one_mul]
  calc
    (∑ t : Fin 2, score (repeatedX (wholeRareDirected rareModel) ω d t)
        (repeatedY (wholeRareDirected rareModel) ω d t -
          dot (repeatedX (wholeRareDirected rareModel) ω d t) β)) =
      ∑ t : Fin 2, score
        (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d (recordIndex ω d t))
        (repeatedY (wholeRareKernel rareModel) (fun i => (ω i).1) d (recordIndex ω d t) -
          dot (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d (recordIndex ω d t)) β) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [directed_recordX ω hω d t, directed_recordY ω hω d t]
    _ = ∑ t : Fin 2, score
        (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t)
        (repeatedY (wholeRareKernel rareModel) (fun i => (ω i).1) d t -
          dot (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t) β) :=
            sum_recordIndex ω hω d
              (fun t => score
                (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t)
                (repeatedY (wholeRareKernel rareModel) (fun i => (ω i).1) d t -
                  dot (repeatedX (wholeRareKernel rareModel) (fun i => (ω i).1) d t) β))

lemma directed_ols_eq {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) :
    wholeWeightedOLS (wholeRareDirected rareModel) (fun _ _ => 1) ω =
      repeatedOLS (wholeRareKernel rareModel) (fun i => (ω i).1) := by
  rw [wholeWeightedOLS, repeatedOLS, weightedGram_eq ω hω, weightedXY_eq ω hω]
  rfl

lemma directed_variance_eq {N : ℕ} (ω : Fin N → AuxUnit)
    (hω : Function.Injective (fun i => (ω i).2)) :
    wholeWeightedVariance (wholeRareDirected rareModel) (fun _ _ => 1) ω =
      repeatedVariance (wholeRareKernel rareModel) (fun i => (ω i).1) := by
  have hgram := weightedGram_eq ω hω
  have hols := directed_ols_eq ω hω
  have hblock :
      wholeWeightedBlockScore (wholeRareDirected rareModel) (fun _ _ => 1)
        (wholeWeightedOLS (wholeRareDirected rareModel) (fun _ _ => 1) ω) ω =
      repeatedBlockScore (wholeRareKernel rareModel)
        (repeatedOLS (wholeRareKernel rareModel) (fun i => (ω i).1)) (fun i => (ω i).1) := by
    funext d
    rw [hols]
    exact weightedBlockScore_eq ω hω _ d
  simp only [wholeWeightedVariance, repeatedVariance, hgram, hblock]

end SAP.P018b.WH.W1.P.T19_L8

open SAP.P018b.WH.W1.P.T19_L8

theorem SAP.P018b.WH.W1.T19_L8_proof : SAP.P018b.WH.W1.T19_L8 := by
  intro N
  have hdistinct := auxLabels_injective_ae N
  filter_upwards [hdistinct] with ω hω
  exact ⟨hω, directed_ols_eq ω hω, directed_variance_eq ω hω⟩

