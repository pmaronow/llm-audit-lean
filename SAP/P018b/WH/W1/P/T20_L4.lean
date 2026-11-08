import SAP.P018b.WH.W1.Leaves
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.WH.W1.P.T20_L4

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal Matrix.Norms.Elementwise
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def auxUniform : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

local instance auxUniform_probability : IsProbabilityMeasure auxUniform := by
  constructor
  norm_num [auxUniform]

local instance auxUniform_noAtoms : NullSingletonClass auxUniform :=
  inferInstanceAs (NullSingletonClass (volume.restrict (Set.Icc (0 : ℝ) 1)))

private theorem measurableSet_pairwise_ne {ι : Type} [Fintype ι] :
    MeasurableSet {x : ι → ℝ | Pairwise (fun i j => x i ≠ x j)} := by
  classical
  have hset : {x : ι → ℝ | Pairwise (fun i j => x i ≠ x j)} =
      ⋂ i, ⋂ j, if i = j then Set.univ else {x | x i ≠ x j} := by
    ext x
    simp [Pairwise]
  rw [hset]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    by_cases hij : i = j
    · simp [hij]
    · have hs : {x : ι → ℝ | x i ≠ x j} =
          {x | x i < x j} ∪ {x | x j < x i} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_union]
        constructor
        · exact lt_or_gt_of_ne
        · rintro (h | h)
          · exact ne_of_lt h
          · exact Ne.symm (ne_of_lt h)
      rw [hs]
      have h₁ : Measurable (fun x : ι → ℝ => x i) := by fun_prop
      have h₂ : Measurable (fun x : ι → ℝ => x j) := by fun_prop
      simpa [hij] using (measurableSet_lt h₁ h₂).union (measurableSet_lt h₂ h₁)

private theorem pairwise_ne_uniform_succ (n : ℕ) :
    ∀ᵐ x : Fin (n+1) → ℝ ∂ Measure.pi (fun _ : Fin (n+1) => auxUniform),
      Pairwise (fun i j => x i ≠ x j) := by
  induction n with
  | zero =>
      filter_upwards [] with x
      intro i j hij
      fin_cases i
      fin_cases j
      exact (hij rfl).elim
  | succ n ih =>
      let α : Fin (n+1+1) → Type := fun _ => ℝ
      let e := MeasurableEquiv.piFinSuccAbove α (0 : Fin (n+1+1))
      have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1+1) => auxUniform)
        (0 : Fin (n+1+1))
      have hcrossMeas : MeasurableSet
          {z : ℝ × (Fin (n+1) → ℝ) | ∀ j, z.1 ≠ z.2 j} := by
        classical
        rw [Set.setOf_forall]
        exact MeasurableSet.iInter fun j => by
          have hs : {z : ℝ × (Fin (n+1) → ℝ) | z.1 ≠ z.2 j} =
              {z | z.1 < z.2 j} ∪ {z | z.2 j < z.1} := by
            ext z
            simp only [Set.mem_setOf_eq, Set.mem_union]
            constructor
            · exact lt_or_gt_of_ne
            · rintro (h | h)
              · exact ne_of_lt h
              · exact Ne.symm (ne_of_lt h)
          rw [hs]
          have h₁ : Measurable (fun z : ℝ × (Fin (n+1) → ℝ) => z.1) := by fun_prop
          have h₂ : Measurable (fun z : ℝ × (Fin (n+1) → ℝ) => z.2 j) := by fun_prop
          exact (measurableSet_lt h₁ h₂).union (measurableSet_lt h₂ h₁)
      have hcross : ∀ᵐ z : ℝ × (Fin (n+1) → ℝ)
          ∂ auxUniform.prod (Measure.pi (fun _ : Fin (n+1) => auxUniform)),
          ∀ j, z.1 ≠ z.2 j := by
        rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hcrossMeas]
        exact Filter.Eventually.of_forall fun x =>
          Filter.eventually_all.2 (fun j =>
            (MeasureTheory.Measure.ae_eval_ne (fun _ : Fin (n+1) => auxUniform) j x).mono
              (fun y hy => hy.symm))
      have hpairMeas : MeasurableSet
          {y : Fin (n+1) → ℝ | Pairwise (fun i j => y i ≠ y j)} :=
        measurableSet_pairwise_ne
      have hrestMeas : MeasurableSet
          {z : ℝ × (Fin (n+1) → ℝ) | Pairwise (fun i j => z.2 i ≠ z.2 j)} :=
        hpairMeas.preimage measurable_snd
      have hrest : ∀ᵐ z : ℝ × (Fin (n+1) → ℝ)
          ∂ auxUniform.prod (Measure.pi (fun _ : Fin (n+1) => auxUniform)),
          Pairwise (fun i j => z.2 i ≠ z.2 j) := by
        rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hrestMeas]
        exact Filter.Eventually.of_forall fun _ => ih
      have hprod := hcross.and hrest
      have hpairMeas' : MeasurableSet
          {x : Fin (n+1+1) → ℝ | Pairwise (fun i j => x i ≠ x j)} :=
        measurableSet_pairwise_ne
      have hpropMeas : MeasurableSet {z : ℝ × (Fin (n+1) → ℝ) |
          Pairwise (fun i j : Fin (n+1+1) => (e.symm z) i ≠ (e.symm z) j)} :=
        hpairMeas'.preimage e.symm.measurable
      have hcomb : ∀ᵐ z : ℝ × (Fin (n+1) → ℝ)
          ∂ auxUniform.prod (Measure.pi (fun _ : Fin (n+1) => auxUniform)),
          Pairwise (fun i j : Fin (n+1+1) => (e.symm z) i ≠ (e.symm z) j) := by
        filter_upwards [hprod] with z hz
        intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j =>
            simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hz.1 j
        | succ i =>
          cases j using Fin.cases with
          | zero =>
            simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using (hz.1 i).symm
          | succ j =>
            have hh := hz.2 (by
              intro h
              exact hij (congrArg Fin.succ h))
            simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hh
      have hmap : ∀ᵐ z : ℝ × (Fin (n+1) → ℝ)
          ∂ Measure.map e (Measure.pi (fun _ : Fin (n+1+1) => auxUniform)),
          Pairwise (fun i j : Fin (n+1+1) => (e.symm z) i ≠ (e.symm z) j) := by
        rw [mp.map_eq]
        exact hcomb
      have hback := (MeasureTheory.ae_map_iff e.measurable.aemeasurable hpropMeas).mp hmap
      filter_upwards [hback] with x hx
      have hx' : Pairwise (fun i j => x i ≠ x j) := by
        change Pairwise (fun i j => (e.symm (e x)) i ≠ (e.symm (e x)) j) at hx
        simpa only [e.symm_apply_apply] using hx
      intro i j hij
      by_contra heq
      exact (hx' hij) heq

private theorem sum_fin2_rev {α : Type} [AddCommMonoid α] (f : Fin 2 → α) :
    (∑ t : Fin 2, f (Fin.rev t)) = ∑ t : Fin 2, f t := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Fin.rev, add_comm]

private theorem sum_fin2_if_rev {α : Type} [AddCommMonoid α] (f : Fin 2 → α) (b : Prop)
    [Decidable b] : (∑ t : Fin 2, f (if b then t else Fin.rev t)) = ∑ t : Fin 2, f t := by
  by_cases hb : b
  · simp [hb]
  · simpa [hb] using sum_fin2_rev f

private theorem sum_dyad_fin2_if_rev {N : ℕ} {α : Type} [AddCommMonoid α]
    (f : Dyad N → Fin 2 → α) (b : Dyad N → Prop) [DecidablePred b] :
    (∑ d : Dyad N, ∑ t : Fin 2, f d (if b d then t else Fin.rev t)) =
      ∑ d : Dyad N, ∑ t : Fin 2, f d t := by
  apply Finset.sum_congr rfl
  intro d hd
  exact sum_fin2_if_rev (f d) (b d)

private theorem directed_labels_pairwise (N : ℕ) (hN : 0 < N) :
    ∀ᵐ ω : Fin N → AronowAudit.P018.RareUnit × ℝ
      ∂ repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N,
      Pairwise (fun i j => (ω i).2 ≠ (ω j).2) := by
  have hN' : N - 1 + 1 = N := by omega
  have hp : ∀ᵐ y : Fin N → ℝ ∂ Measure.pi (fun _ : Fin N => auxUniform),
      Pairwise (fun i j => y i ≠ y j) := by
    have h := pairwise_ne_uniform_succ (N - 1)
    rw [hN'] at h
    exact h
  letI : IsProbabilityMeasure SAP.P018b.WH.W1.rareModel.μ :=
    SAP.P018b.WH.W1.rareModel_law.1
  have hsnd : MeasurePreserving Prod.snd
      (SAP.P018b.WH.W1.rareModel.μ.prod auxUniform) auxUniform := measurePreserving_snd
  have hpi := MeasureTheory.measurePreserving_pi
    (fun _ : Fin N => SAP.P018b.WH.W1.rareModel.μ.prod auxUniform)
    (fun _ : Fin N => auxUniform) (f := fun _ => Prod.snd) (fun _ => hsnd)
  have hmap : ∀ᵐ y : Fin N → ℝ
      ∂ Measure.map (fun ω : Fin N → AronowAudit.P018.RareUnit × ℝ => fun i => (ω i).2)
        (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N),
      Pairwise (fun i j => y i ≠ y j) := by
    change ∀ᵐ y : Fin N → ℝ
      ∂ Measure.map (fun ω : Fin N → AronowAudit.P018.RareUnit × ℝ => fun i => (ω i).2)
        (Measure.pi (fun _ : Fin N => SAP.P018b.WH.W1.rareModel.μ.prod auxUniform)),
      Pairwise (fun i j => y i ≠ y j)
    rw [hpi.map_eq]
    exact hp
  exact (MeasureTheory.ae_map_iff hpi.aemeasurable measurableSet_pairwise_ne).mp hmap

private theorem directed_projection_mp (N : ℕ) :
    MeasurePreserving
      (fun ω : Fin N → AronowAudit.P018.RareUnit × ℝ => fun i => (ω i).1)
      (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N)
      (repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N) := by
  letI : IsProbabilityMeasure auxUniform := auxUniform_probability
  letI : IsProbabilityMeasure SAP.P018b.WH.W1.rareModel.μ :=
    SAP.P018b.WH.W1.rareModel_law.1
  have hfst : MeasurePreserving Prod.fst
      (SAP.P018b.WH.W1.rareModel.μ.prod auxUniform) SAP.P018b.WH.W1.rareModel.μ :=
    measurePreserving_fst
  let μ : Fin N → Measure (AronowAudit.P018.RareUnit × ℝ) :=
    fun _ => SAP.P018b.WH.W1.rareModel.μ.prod auxUniform
  let ν : Fin N → Measure AronowAudit.P018.RareUnit := fun _ =>
    SAP.P018b.WH.W1.rareModel.μ
  exact MeasureTheory.measurePreserving_pi
    μ ν (f := fun _ => Prod.fst) (fun _ => hfst)

private theorem directed_sample_gram_xy_eq {N : ℕ}
    (ω : Fin N → AronowAudit.P018.RareUnit × ℝ)
    (hlab : Function.Injective (fun i => (ω i).2)) :
    wholeWeightedGram (wholeRareDirected SAP.P018b.WH.W1.rareModel)
        (fun _ _ => 1) ω =
        repeatedGram (wholeRareKernel SAP.P018b.WH.W1.rareModel) (fun i => (ω i).1) ∧
      wholeWeightedXY (wholeRareDirected SAP.P018b.WH.W1.rareModel)
        (fun _ _ => 1) ω =
        (∑ d : Dyad N, ∑ t : Fin 2,
          score (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel)
            (fun i => (ω i).1) d t)
            (repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel)
              (fun i => (ω i).1) d t)) := by
  let R := wholeRareDirected SAP.P018b.WH.W1.rareModel
  let K := wholeRareKernel SAP.P018b.WH.W1.rareModel
  let ω₀ : Fin N → AronowAudit.P018.RareUnit := fun i => (ω i).1
  have hrecX (d : Dyad N) (t : Fin 2) :
      R.X N d t (ω (firstUnit d)) (ω (secondUnit d)) =
        K.X N d (if (ω (firstUnit d)).2 < (ω (secondUnit d)).2
          then t else Fin.rev t) (ω₀ (firstUnit d)) (ω₀ (secondUnit d)) := by
    have hne : (ω (firstUnit d)).2 ≠ (ω (secondUnit d)).2 := by
      intro h
      have hidx : firstUnit d = secondUnit d := hlab (by simpa using h)
      have hlt : firstUnit d < secondUnit d := by
        exact (members d).min'_lt_max'_of_card (by rw [members_card]; norm_num)
      exact hlt.ne hidx
    change K.X N d (if (ω (firstUnit d)).2 = (ω (secondUnit d)).2
        then (0 : Fin 2) else
        if (ω (firstUnit d)).2 < (ω (secondUnit d)).2 then t else Fin.rev t)
        (ω₀ (firstUnit d)) (ω₀ (secondUnit d)) = _
    simp [hne]
  have hrecY (d : Dyad N) (t : Fin 2) :
      R.Y N d t (ω (firstUnit d)) (ω (secondUnit d)) =
        K.Y N d (if (ω (firstUnit d)).2 < (ω (secondUnit d)).2
          then t else Fin.rev t) (ω₀ (firstUnit d)) (ω₀ (secondUnit d)) := by
    have hne : (ω (firstUnit d)).2 ≠ (ω (secondUnit d)).2 := by
      intro h
      have hidx : firstUnit d = secondUnit d := hlab (by simpa using h)
      have hlt : firstUnit d < secondUnit d := by
        exact (members d).min'_lt_max'_of_card (by rw [members_card]; norm_num)
      exact hlt.ne hidx
    change K.Y N d (if (ω (firstUnit d)).2 = (ω (secondUnit d)).2
        then (0 : Fin 2) else
        if (ω (firstUnit d)).2 < (ω (secondUnit d)).2 then t else Fin.rev t)
        (ω₀ (firstUnit d)) (ω₀ (secondUnit d)) = _
    simp [hne]
  constructor
  · change (∑ d : Dyad N, ∑ t : Fin 2, (1 : ℝ) • outer
        (R.X N d t (ω (firstUnit d)) (ω (secondUnit d)))
        (R.X N d t (ω (firstUnit d)) (ω (secondUnit d)))) =
      ∑ d : Dyad N, ∑ t : Fin 2, outer
        (K.X N d t (ω₀ (firstUnit d)) (ω₀ (secondUnit d)))
        (K.X N d t (ω₀ (firstUnit d)) (ω₀ (secondUnit d)))
    simp only [one_smul]
    let f : Dyad N → Fin 2 → Mat 2 := fun d t =>
      outer (K.X N d t (ω₀ (firstUnit d)) (ω₀ (secondUnit d)))
        (K.X N d t (ω₀ (firstUnit d)) (ω₀ (secondUnit d)))
    let b : Dyad N → Prop := fun d => (ω (firstUnit d)).2 < (ω (secondUnit d)).2
    calc
      (∑ d : Dyad N, ∑ t : Fin 2, outer
          (R.X N d t (ω (firstUnit d)) (ω (secondUnit d)))
          (R.X N d t (ω (firstUnit d)) (ω (secondUnit d))))
          = ∑ d : Dyad N, ∑ t : Fin 2, f d (if b d then t else Fin.rev t) := by
                apply Finset.sum_congr rfl
                intro d hd
                apply Finset.sum_congr rfl
                intro t ht
                simp only [f, b, hrecX]
                rfl
      _ = ∑ d : Dyad N, ∑ t : Fin 2, f d t := sum_dyad_fin2_if_rev f b
  · change (∑ d : Dyad N, ∑ t : Fin 2, score
        (R.X N d t (ω (firstUnit d)) (ω (secondUnit d)))
        ((1 : ℝ) * R.Y N d t (ω (firstUnit d)) (ω (secondUnit d)))) =
      ∑ d : Dyad N, ∑ t : Fin 2, score
        (K.X N d t (ω₀ (firstUnit d)) (ω₀ (secondUnit d)))
        (K.Y N d t (ω₀ (firstUnit d)) (ω₀ (secondUnit d)))
    simp only [one_mul]
    let f : Dyad N → Fin 2 → Vec 2 := fun d t =>
      score (K.X N d t (ω₀ (firstUnit d)) (ω₀ (secondUnit d)))
        (K.Y N d t (ω₀ (firstUnit d)) (ω₀ (secondUnit d)))
    let b : Dyad N → Prop := fun d => (ω (firstUnit d)).2 < (ω (secondUnit d)).2
    calc
      (∑ d : Dyad N, ∑ t : Fin 2, score
          (R.X N d t (ω (firstUnit d)) (ω (secondUnit d)))
          (R.Y N d t (ω (firstUnit d)) (ω (secondUnit d))))
          = ∑ d : Dyad N, ∑ t : Fin 2, f d (if b d then t else Fin.rev t) := by
                apply Finset.sum_congr rfl
                intro d hd
                apply Finset.sum_congr rfl
                intro t ht
                simp only [f, b, hrecX, hrecY]
                rfl
      _ = ∑ d : Dyad N, ∑ t : Fin 2, f d t := sum_dyad_fin2_if_rev f b

private theorem directed_coefficient_eq_ae (N : ℕ) (hN : 0 < N) :
    (fun ω : Fin N → AronowAudit.P018.RareUnit × ℝ =>
      wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1) =ᵐ[
        repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N]
      (fun ω => repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel)
        (fun i => (ω i).1) 1) := by
  filter_upwards [directed_labels_pairwise N hN] with ω hpair
  have hlabels : Function.Injective (fun i => (ω i).2) := by
    intro i j hij
    by_contra hne
    exact (hpair hne) hij
  obtain ⟨hG, hXY⟩ := directed_sample_gram_xy_eq ω hlabels
  have hvec : wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel)
      (fun _ _ => 1) ω =
        repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (fun i => (ω i).1) := by
    unfold wholeWeightedOLS repeatedOLS
    rw [hG, hXY]
    rfl
  exact congrFun hvec 1

private theorem directed_square_integral_eq (N : ℕ) (hN : 0 < N) :
    (∫⁻ ω, ENNReal.ofReal ((wholeWeightedOLS
      (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1)^2)
        ∂ repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) =
    (∫⁻ ω, ENNReal.ofReal ((repeatedOLS
      (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω 1)^2)
        ∂ repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N) := by
  let π : (Fin N → AronowAudit.P018.RareUnit × ℝ) → (Fin N → AronowAudit.P018.RareUnit) :=
    fun ω i => (ω i).1
  let μ := repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N
  let ν := repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N
  have hmp := directed_projection_mp N
  have hEq := directed_coefficient_eq_ae N hN
  have hm : Measurable (fun ω : Fin N → AronowAudit.P018.RareUnit =>
      ENNReal.ofReal ((repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω 1)^2)) := by
    fun_prop
  calc
    _ = ∫⁻ ω, ENNReal.ofReal
        ((repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (π ω) 1)^2) ∂ μ := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [hEq] with ω hω
          simpa [π] using congrArg (fun x : ℝ => ENNReal.ofReal (x^2)) hω
    _ = _ := hmp.lintegral_comp hm

private theorem directed_abs_integral_eq (N : ℕ) (hN : 0 < N) :
    (∫⁻ ω, ENNReal.ofReal |wholeWeightedOLS
      (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1|
        ∂ repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) =
    (∫⁻ ω, ENNReal.ofReal |repeatedOLS
      (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω 1|
        ∂ repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N) := by
  let π : (Fin N → AronowAudit.P018.RareUnit × ℝ) → (Fin N → AronowAudit.P018.RareUnit) :=
    fun ω i => (ω i).1
  let μ := repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N
  have hmp := directed_projection_mp N
  have hEq := directed_coefficient_eq_ae N hN
  have hm : Measurable (fun ω : Fin N → AronowAudit.P018.RareUnit =>
      ENNReal.ofReal |repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω 1|) := by
    fun_prop
  calc
    _ = ∫⁻ ω, ENNReal.ofReal
        |repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (π ω) 1| ∂ μ := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [hEq] with ω hω
          simpa [π] using congrArg (fun x : ℝ => ENNReal.ofReal |x|) hω
    _ = _ := hmp.lintegral_comp hm

private theorem wholeRareKernel_toRepeated_eq_rareRepeated :
    SAP.P018b.Bridge.toRepeated (wholeRareKernel SAP.P018b.WH.W1.rareModel) =
      AronowAudit.P018.rareRepeated := by
  rfl

private theorem source_square_integral_top (N : ℕ) (hN : 3 ≤ N) :
    (∫⁻ ω, ENNReal.ofReal ((repeatedOLS
      (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω 1)^2)
        ∂ repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N) = ∞ := by
  rw [SAP.P018b.Bridge.repeatedOLS_eq, SAP.P018b.Bridge.repeatedLaw_eq,
    wholeRareKernel_toRepeated_eq_rareRepeated]
  exact (AronowAudit.P018.Wave1.TailB_rare_coefficient_integrals N hN).1

private theorem source_abs_integral_top (N : ℕ) (hN : 3 ≤ N) :
    (∫⁻ ω, ENNReal.ofReal |repeatedOLS
      (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω 1|
        ∂ repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N) = ∞ := by
  rw [SAP.P018b.Bridge.repeatedOLS_eq, SAP.P018b.Bridge.repeatedLaw_eq,
    wholeRareKernel_toRepeated_eq_rareRepeated]
  exact (AronowAudit.P018.Wave1.TailB_rare_coefficient_integrals N hN).2

private theorem no_memLp_sub_of_square_top {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (b : ℝ)
    (htop : (∫⁻ ω, ENNReal.ofReal ((f ω)^2) ∂ μ) = ⊤) :
    ¬ MemLp (fun ω => f ω - b) 2 μ := by
  intro h
  have hb : MemLp (fun _ : Ω => b) 2 μ :=
    MemLp.of_bound measurable_const.aestronglyMeasurable |b|
      (ae_of_all _ fun _ => by simp [Real.norm_eq_abs])
  have hf : MemLp f 2 μ := by
    have h' := h.add hb
    have heq : (fun ω => (f ω - b) + b) = f := by
      funext ω
      ring
    exact heq ▸ h'
  have hi := hf.integrable_sq
  have hfi := (MeasureTheory.hasFiniteIntegral_iff_enorm).1 hi.hasFiniteIntegral
  have hfin : (∫⁻ ω, ENNReal.ofReal ((f ω)^2) ∂ μ) < ∞ := by
    have heq : (fun ω : Ω => ‖(f ω)^2‖ₑ) =
        fun ω => ENNReal.ofReal ((f ω)^2) := by
      funext ω
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg (f ω))]
    rw [heq] at hfi
    exact hfi
  rw [htop] at hfin
  simp at hfin

private theorem no_integrable_sub_of_abs_top {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (b : ℝ)
    (htop : (∫⁻ ω, ENNReal.ofReal |f ω| ∂ μ) = ⊤) :
    ¬ Integrable (fun ω => f ω - b) μ := by
  intro h
  have hb : Integrable (fun _ : Ω => b) μ := integrable_const b
  have hf : Integrable f μ := by
    have h' := h.add hb
    have heq : (fun ω => (f ω - b) + b) = f := by
      funext ω
      ring
    exact heq ▸ h'
  have hn := hf.norm
  have hfi := (MeasureTheory.hasFiniteIntegral_iff_enorm).1 hn.hasFiniteIntegral
  have hfin : (∫⁻ ω, ENNReal.ofReal |f ω| ∂ μ) < ∞ := by
    simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs, abs_abs] using hfi
  rw [htop] at hfin
  simp at hfin

private theorem no_memLp_of_square_top {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (htop : (∫⁻ ω, ENNReal.ofReal ((f ω)^2) ∂ μ) = ⊤) :
    ¬ MemLp f 2 μ := by
  intro h
  have h0 : MemLp (fun ω => f ω - 0) 2 μ := by simpa using h
  exact no_memLp_sub_of_square_top μ f 0 htop h0

end SAP.P018b.WH.W1.P.T20_L4

namespace SAP.P018b.WH.W1
open SAP.P018b
open SAP.P018b.WH.W1.P.T20_L4
open MeasureTheory

theorem T20_L4_proof : SAP.P018b.WH.W1.T20_L4 := by
  change SAP.P018b.wholeDirectedMomentFailure SAP.P018b.WH.W1.rareModel
  dsimp [SAP.P018b.wholeDirectedMomentFailure]
  constructor
  · intro N hN
    letI : IsProbabilityMeasure SAP.P018b.WH.W1.rareModel.μ :=
      SAP.P018b.WH.W1.rareModel_law.1
    letI : IsProbabilityMeasure auxUniform := auxUniform_probability
    letI : IsProbabilityMeasure
      (SAP.P018b.WH.W1.rareModel.μ.prod auxUniform) := inferInstance
    have hμ : IsProbabilityMeasure
        (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) := by
      change IsProbabilityMeasure
        (Measure.pi (fun _ : Fin N =>
          SAP.P018b.WH.W1.rareModel.μ.prod auxUniform))
      infer_instance
    have hsquare :
        (∫⁻ ω, ENNReal.ofReal ((wholeWeightedOLS
          (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1)^2)
            ∂ repeatedLaw (wholeRareDirected rareModel) N) = ⊤ := by
      rw [directed_square_integral_eq N (by omega)]
      exact source_square_integral_top N hN
    have habs :
        (∫⁻ ω, ENNReal.ofReal |wholeWeightedOLS
          (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1|
            ∂ repeatedLaw (wholeRareDirected rareModel) N) = ⊤ := by
      rw [directed_abs_integral_eq N (by omega)]
      exact source_abs_integral_top N hN
    refine ⟨?_, ?_⟩
    · exact no_memLp_sub_of_square_top
        (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N)
        (fun ω => wholeWeightedOLS
          (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1)
        (wholeWeightedBeta (N := N) (wholeRareDirected SAP.P018b.WH.W1.rareModel)
          (fun _ _ => 1) 1) hsquare
    · exact no_integrable_sub_of_abs_top
        (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N)
        (fun ω => wholeWeightedOLS
          (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1)
        (wholeWeightedBeta (N := N) (wholeRareDirected SAP.P018b.WH.W1.rareModel)
          (fun _ _ => 1) 1) habs
  · intro hui
    dsimp only [SAP.P018b.uiSquares] at hui
    have hscaled := hui.1 3 1
    have hμ : IsProbabilityMeasure
        (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) 3) := by
      letI : IsProbabilityMeasure SAP.P018b.WH.W1.rareModel.μ :=
        SAP.P018b.WH.W1.rareModel_law.1
      letI : IsProbabilityMeasure auxUniform := auxUniform_probability
      letI : IsProbabilityMeasure
        (SAP.P018b.WH.W1.rareModel.μ.prod auxUniform) := inferInstance
      change IsProbabilityMeasure
        (Measure.pi (fun _ : Fin 3 =>
          SAP.P018b.WH.W1.rareModel.μ.prod auxUniform))
      infer_instance
    letI : IsProbabilityMeasure
        (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) 3) := hμ
    have hsquare :
        (∫⁻ ω, ENNReal.ofReal ((wholeWeightedOLS
          (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1)^2)
            ∂ repeatedLaw (wholeRareDirected rareModel) 3) = ⊤ := by
      rw [directed_square_integral_eq 3 (by norm_num)]
      exact source_square_integral_top 3 (by norm_num)
    have hroot : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    have herr : MemLp
        (fun ω : Fin 3 → AronowAudit.P018.RareUnit × ℝ =>
          wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel)
            (fun _ _ => 1) ω 1 -
          wholeWeightedBeta (N := 3) (wholeRareDirected SAP.P018b.WH.W1.rareModel)
            (fun _ _ => 1) 1) 2
        (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) 3) := by
      have hscaled' : MemLp
          (fun ω : Fin 3 → AronowAudit.P018.RareUnit × ℝ =>
            Real.sqrt 3 * (wholeWeightedOLS
              (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1 -
              wholeWeightedBeta (N := 3) (wholeRareDirected SAP.P018b.WH.W1.rareModel)
                (fun _ _ => 1) 1)) 2
          (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) 3) := by
        change MemLp
          (fun ω : Fin 3 → AronowAudit.P018.RareUnit × ℝ =>
            (Real.sqrt 3 • (wholeWeightedOLS
              (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω -
              wholeWeightedBeta (N := 3) (wholeRareDirected SAP.P018b.WH.W1.rareModel)
                (fun _ _ => 1))) 1) 2
          (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) 3) at hscaled
        simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] using hscaled
      have hcancel := hscaled'.const_mul (Real.sqrt 3)⁻¹
      convert hcancel using 1 <;> ext ω <;> field_simp [hroot]
    exact (no_memLp_sub_of_square_top
      (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) 3)
      (fun ω => wholeWeightedOLS
        (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω 1)
      (wholeWeightedBeta (N := 3) (wholeRareDirected SAP.P018b.WH.W1.rareModel)
        (fun _ _ => 1) 1) hsquare) herr

end SAP.P018b.WH.W1
