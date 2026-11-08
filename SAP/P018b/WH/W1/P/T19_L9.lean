import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018b.WH.W1.P.T19_L9

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction ENNReal Matrix.Norms.Elementwise

local instance rareUnitCountable : Countable AronowAudit.P018.RareUnit := by
  apply (Function.Injective.countable (f :=
    fun u : AronowAudit.P018.RareUnit => (u.m, u.label.val, u.A, u.B)))
  intro u v huv
  cases u with
  | mk m c a b =>
    cases v with
    | mk n d e f =>
      simp only [Prod.mk.injEq] at huv
      rcases huv with ⟨hm, hc, ha, hb⟩
      subst n
      subst e
      subst f
      have hcd : c = d := Fin.ext hc
      subst d
      rfl

local instance rareUnitMeasurableSingleton : MeasurableSingletonClass AronowAudit.P018.RareUnit := by
  constructor
  intro u
  change True
  trivial

private abbrev U := AronowAudit.P018.RareUnit
private abbrev μ₀ : Measure U := SAP.P018b.WH.W1.rareModel.μ
private abbrev μaux : Measure (U × ℝ) :=
  μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))
private def proj (N : ℕ) (ω : Fin N → U × ℝ) : Fin N → U := fun i => (ω i).1

private theorem uniform01_probability : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ (Set.Icc (0 : ℝ) 1), Real.volume_Icc]
  norm_num

private theorem projection_mp (N : ℕ) :
    MeasurePreserving
      (proj N)
      (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N)
      (repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N) := by
  letI : IsProbabilityMeasure μ₀ := SAP.P018b.WH.W1.rareModel_law.1
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := uniform01_probability
  have hfst : MeasurePreserving Prod.fst μaux μ₀ := MeasureTheory.measurePreserving_fst
  exact MeasureTheory.measurePreserving_pi
    (μ := fun _ : Fin N => μaux) (ν := fun _ => μ₀)
    (f := fun _ => Prod.fst) (fun _ => hfst)

private theorem proj_measurable (N : ℕ) :
    Measurable (proj N : (Fin N → U × ℝ) → (Fin N → U)) := by
  exact (projection_mp N).measurable

private theorem source_measurable {N : ℕ} {β : Type*} [MeasurableSpace β]
    (f : (Fin N → U) → β) : Measurable f := measurable_of_countable f

private theorem source_lintegral_map {N : ℕ} {f : (Fin N → U) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ ω, f (proj N ω) ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) =
      ∫⁻ x, f x ∂repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N := by
  rw [← (projection_mp N).map_eq]
  exact (lintegral_map hf (proj_measurable N)).symm

private theorem source_integral_map {N : ℕ} {f : (Fin N → U) → ℝ}
    (hf : AEStronglyMeasurable f
      (Measure.map (proj N) (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N))) :
    (∫ ω, f (proj N ω) ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) =
      ∫ x, f x ∂repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N := by
  rw [← (projection_mp N).map_eq]
  exact (integral_map (proj_measurable N).aemeasurable hf).symm

private theorem source_event_measure {N : ℕ} {s : Set (Fin N → U)}
    (hs : MeasurableSet s) :
    repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N ((proj N) ⁻¹' s) =
      repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N s := by
  calc
    _ = Measure.map (proj N) (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) s :=
      (Measure.map_apply (proj_measurable N) hs).symm
    _ = _ := by rw [(projection_mp N).map_eq]

private theorem source_beta_zero (N : ℕ) :
    repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N = 0 := by
  have hEq : SAP.P018b.repeatedBeta
      (wholeRareKernel SAP.P018b.WH.W1.rareModel) N =
      AronowAudit.P018.repeatedBeta AronowAudit.P018.rareRepeated N := by
    rfl
  rw [hEq]
  exact AronowAudit.P018.Wave1.tb09_rare_population_beta N

private theorem source_event_measurable {N : ℕ} (s : Set (Fin N → U)) : MeasurableSet s := by
  exact (Set.to_countable s).measurableSet

private abbrev ν₀ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

private instance uniform01_nullSingleton : NullSingletonClass ν₀ where
  measure_singleton x := by
    simp [ν₀, Measure.restrict_apply, Real.volume_singleton]

private theorem label_pair_ne_ae (N : ℕ) {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ ω ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N,
      (ω i).2 ≠ (ω j).2 := by
  letI : IsProbabilityMeasure μ₀ := SAP.P018b.WH.W1.rareModel_law.1
  letI : IsProbabilityMeasure ν₀ := uniform01_probability
  letI : IsProbabilityMeasure μaux := inferInstance
  let μ := repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => μaux))
    infer_instance
  let f : (Fin N → U × ℝ) → ℝ := fun ω => (ω i).2
  let g : (Fin N → U × ℝ) → ℝ := fun ω => (ω j).2
  have hI : f ⟂ᵢ[μ] g := by
    change f ⟂ᵢ[Measure.pi (fun _ : Fin N => μaux)] g
    have hcoords := iIndepFun_pi (μ := fun _ : Fin N => μaux)
      (X := fun _ (z : U × ℝ) => z.2)
      (fun _ => measurable_snd.aemeasurable)
    exact hcoords.indepFun hij
  have hlabel : MeasurePreserving Prod.snd μaux ν₀ := by
    exact MeasureTheory.measurePreserving_snd
  have hcoord (i : Fin N) : MeasurePreserving (fun ω : Fin N → U × ℝ => (ω i).2) μ ν₀ := by
    have heval : MeasurePreserving (fun ω : Fin N → U × ℝ => ω i) μ μaux :=
      MeasureTheory.measurePreserving_eval (fun _ : Fin N => μaux) i
    exact hlabel.comp heval
  have hpair : μ.map (fun ω => (f ω, g ω)) = ν₀.prod ν₀ := by
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map
      (by fun_prop : AEMeasurable f μ) (by fun_prop : AEMeasurable g μ)).mp hI
    rw [hmap, (hcoord i).map_eq, (hcoord j).map_eq]
  have hdiag : ν₀.prod ν₀ {z : ℝ × ℝ | z.1 = z.2} = 0 := by
    calc
      ν₀.prod ν₀ {z : ℝ × ℝ | z.1 = z.2} =
          ∫⁻ x, ν₀ {y | (x, y) ∈ Set.diagonal ℝ} ∂ν₀ := by
        rw [show {z : ℝ × ℝ | z.1 = z.2} = Set.diagonal ℝ by ext z; simp]
        exact Measure.prod_apply measurableSet_diagonal
      _ = 0 := by simp
  have hzero : μ {ω | f ω = g ω} = 0 := by
    calc
      μ {ω | f ω = g ω} = μ ((fun ω => (f ω, g ω)) ⁻¹' {z : ℝ × ℝ | z.1 = z.2}) := by
        congr 1
      _ = μ.map (fun ω => (f ω, g ω)) {z : ℝ × ℝ | z.1 = z.2} :=
        (Measure.map_apply (by fun_prop) measurableSet_diagonal).symm
      _ = 0 := by simpa [hpair] using hdiag
  have hae : ∀ᵐ ω ∂μ, ¬ f ω = g ω := by
    rw [ae_iff]
    simpa [Set.preimage, Set.mem_setOf_eq] using hzero
  simpa [μ, f, g] using hae

private theorem tie_free_ae (N : ℕ) :
    ∀ᵐ ω ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N,
      Function.Injective (fun i => (ω i).2) := by
  classical
  change ∀ᵐ ω ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N,
    ∀ i j, (ω i).2 = (ω j).2 → i = j
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · simp [hij]
  · filter_upwards [label_pair_ne_ae N hij] with ω hω
    intro he
    exact (hω he).elim

private def directedIndex (a b : ℝ) (t : Fin 2) : Fin 2 :=
  if a = b then 0 else if a < b then t else Fin.rev t

private theorem sum_directedIndex {α : Type*} [AddCommMonoid α]
    (a b : ℝ) (hab : a ≠ b) (f : Fin 2 → α) :
    (∑ t : Fin 2, f (directedIndex a b t)) = ∑ t, f t := by
  by_cases hlt : a < b
  · simp [directedIndex, hab, hlt]
  · simp [directedIndex, hab, hlt, Fin.sum_univ_two, add_comm]

private theorem directedX_record {N : ℕ} (ω : Fin N → U × ℝ) (d : Dyad N)
    (t : Fin 2) :
    repeatedX (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t =
      repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d
        (directedIndex ((ω (firstUnit d)).2) ((ω (secondUnit d)).2) t) := by
  simp [repeatedX, wholeRareDirected, wholeRareKernel, directedIndex, proj]

private theorem directedY_record {N : ℕ} (ω : Fin N → U × ℝ) (d : Dyad N)
    (t : Fin 2) :
    repeatedY (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t =
      repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d
        (directedIndex ((ω (firstUnit d)).2) ((ω (secondUnit d)).2) t) := by
  simp [repeatedY, wholeRareDirected, wholeRareKernel, directedIndex, proj]

private theorem endpoint_label_ne {N : ℕ} (ω : Fin N → U × ℝ)
    (hinj : Function.Injective (fun i => (ω i).2)) (d : Dyad N) :
    (ω (firstUnit d)).2 ≠ (ω (secondUnit d)).2 := by
  intro he
  have hcard : 1 < (members d).card := by rw [members_card]; omega
  have hlt : firstUnit d < secondUnit d := by
    change (members d).min' _ < (members d).max' _
    exact Finset.min'_lt_max'_of_card (members d) hcard
  have hne : firstUnit d ≠ secondUnit d := ne_of_lt hlt
  exact hne (hinj he)

private theorem directed_gram_eq {N : ℕ} (ω : Fin N → U × ℝ)
    (hinj : Function.Injective (fun i => (ω i).2)) :
    wholeWeightedGram (wholeRareDirected SAP.P018b.WH.W1.rareModel)
      (fun _ _ => 1) ω =
    repeatedGram (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) := by
  change (∑ d : Dyad N, ∑ t : Fin 2, (1 : ℝ) •
      outer (repeatedX (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)
        (repeatedX (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)) =
    ∑ d : Dyad N, ∑ t : Fin 2,
      outer (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
  apply Finset.sum_congr rfl
  intro d hd
  have hne := endpoint_label_ne ω hinj d
  calc
    (∑ t : Fin 2, (1 : ℝ) • outer
        (repeatedX (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)
        (repeatedX (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)) =
      ∑ t : Fin 2, outer
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d
          (directedIndex ((ω (firstUnit d)).2) ((ω (secondUnit d)).2) t))
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d
          (directedIndex ((ω (firstUnit d)).2) ((ω (secondUnit d)).2) t)) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [one_smul]
        rw [directedX_record]
    _ = ∑ t : Fin 2, outer
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t) :=
      sum_directedIndex _ _ hne (fun t => outer
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t))

private theorem directed_xy_eq {N : ℕ} (ω : Fin N → U × ℝ)
    (hinj : Function.Injective (fun i => (ω i).2)) :
    wholeWeightedXY (wholeRareDirected SAP.P018b.WH.W1.rareModel)
      (fun _ _ => 1) ω =
    ∑ d : Dyad N, ∑ t : Fin 2, score
      (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
      (repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t) := by
  change (∑ d : Dyad N, ∑ t : Fin 2,
      score (repeatedX (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)
        (1 * repeatedY (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)) = _
  apply Finset.sum_congr rfl
  intro d hd
  have hne := endpoint_label_ne ω hinj d
  calc
    (∑ t : Fin 2, score
        (repeatedX (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)
        (1 * repeatedY (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)) =
      ∑ t : Fin 2, score
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d
          (directedIndex ((ω (firstUnit d)).2) ((ω (secondUnit d)).2) t))
        (repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d
          (directedIndex ((ω (firstUnit d)).2) ((ω (secondUnit d)).2) t)) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [one_mul]
        rw [directedX_record, directedY_record]
    _ = ∑ t : Fin 2, score
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
        (repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t) :=
      sum_directedIndex _ _ hne (fun t => score
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
        (repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t))

private theorem directed_ols_eq {N : ℕ} (ω : Fin N → U × ℝ)
    (hinj : Function.Injective (fun i => (ω i).2)) :
    wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel)
      (fun _ _ => 1) ω =
    repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) := by
  unfold wholeWeightedOLS repeatedOLS
  rw [directed_gram_eq ω hinj, directed_xy_eq ω hinj]
  rfl

private theorem directed_blockscore_eq {N : ℕ} (ω : Fin N → U × ℝ)
    (hinj : Function.Injective (fun i => (ω i).2)) (d : Dyad N) :
    wholeWeightedBlockScore (wholeRareDirected SAP.P018b.WH.W1.rareModel)
      (fun _ _ => 1)
      (wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω)
      ω d =
    repeatedBlockScore (wholeRareKernel SAP.P018b.WH.W1.rareModel)
      (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω)) (proj N ω) d := by
  unfold wholeWeightedBlockScore repeatedBlockScore
  rw [directed_ols_eq ω hinj]
  calc
    (∑ t : Fin 2, score
        (repeatedX (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)
        (1 * (repeatedY (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t -
          dot (repeatedX (wholeRareDirected SAP.P018b.WH.W1.rareModel) ω d t)
            (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω))))) =
      ∑ t : Fin 2, score
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d
          (directedIndex ((ω (firstUnit d)).2) ((ω (secondUnit d)).2) t))
        (repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d
            (directedIndex ((ω (firstUnit d)).2) ((ω (secondUnit d)).2) t) -
          dot (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d
            (directedIndex ((ω (firstUnit d)).2) ((ω (secondUnit d)).2) t))
            (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω))) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [one_mul]
        rw [directedX_record, directedY_record]
    _ = ∑ t : Fin 2, score
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
        (repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t -
          dot (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
            (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω))) :=
      sum_directedIndex _ _ (endpoint_label_ne ω hinj d) (fun t => score
        (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
        (repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t -
          dot (repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) d t)
            (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω))))

private theorem directed_variance_eq {N : ℕ} (ω : Fin N → U × ℝ)
    (hinj : Function.Injective (fun i => (ω i).2)) :
    wholeWeightedVariance (wholeRareDirected SAP.P018b.WH.W1.rareModel)
      (fun _ _ => 1) ω =
    repeatedVariance (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) := by
  unfold wholeWeightedVariance repeatedVariance
  rw [directed_gram_eq ω hinj]
  rw [directed_ols_eq ω hinj]
  congr 1
  unfold meat
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hov : (members d ∩ members f).Nonempty
  · simp only [if_pos hov]
    have hds := directed_blockscore_eq ω hinj d
    have hfs := directed_blockscore_eq ω hinj f
    rw [directed_ols_eq ω hinj] at hds hfs
    rw [hds, hfs]
  · simp only [if_neg hov]

private theorem ols_ae (N : ℕ) :
    ∀ᵐ ω ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N,
      wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω =
        repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) := by
  filter_upwards [tie_free_ae N] with ω hω
  exact directed_ols_eq ω hω

private theorem variance_ae (N : ℕ) :
    ∀ᵐ ω ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N,
      wholeWeightedVariance (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω =
        repeatedVariance (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) := by
  filter_upwards [tie_free_ae N] with ω hω
  exact directed_variance_eq ω hω

theorem directed_moments :
    wholeRareDirectedMoments SAP.P018b.WH.W1.rareModel := by
  constructor
  · intro N hN
    rcases SAP.P018b.WH.W1.rareModel_moments.1 N hN with ⟨hsq, habs⟩
    constructor
    · calc
        (∫⁻ ω, ENNReal.ofReal
            ((wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel)
              (fun _ _ => 1) ω 1)^2)
            ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) =
          ∫⁻ ω, ENNReal.ofReal
            ((repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) 1)^2)
            ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N := by
              apply lintegral_congr_ae
              filter_upwards [ols_ae N] with ω hω
              rw [hω]
        _ = ∫⁻ x, ENNReal.ofReal
            ((repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) x 1)^2)
            ∂repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N := by
              exact source_lintegral_map (f := fun x => ENNReal.ofReal
                ((repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) x 1)^2))
                (source_measurable _)
        _ = ∞ := hsq
    · calc
        (∫⁻ ω, ENNReal.ofReal |wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel)
            (fun _ _ => 1) ω 1|
            ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) =
          ∫⁻ ω, ENNReal.ofReal
            |repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) 1|
            ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N := by
              apply lintegral_congr_ae
              filter_upwards [ols_ae N] with ω hω
              rw [hω]
        _ = ∫⁻ x, ENNReal.ofReal
            |repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) x 1|
            ∂repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N := by
              exact source_lintegral_map (f := fun x => ENNReal.ofReal
                |repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) x 1|)
                (source_measurable _)
        _ = ∞ := habs
  · intro N hN
    rcases SAP.P018b.WH.W1.rareModel_moments.2 N hN with ⟨hpos, hneg⟩
    constructor
    · calc
        (∫⁻ ω, ENNReal.ofReal
            (max (wholeWeightedVariance (wholeRareDirected SAP.P018b.WH.W1.rareModel)
              (fun _ _ => 1) ω 1 1) 0)
            ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) =
          ∫⁻ ω, ENNReal.ofReal
            (max (repeatedVariance (wholeRareKernel SAP.P018b.WH.W1.rareModel)
              (proj N ω) 1 1) 0)
            ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N := by
              apply lintegral_congr_ae
              filter_upwards [variance_ae N] with ω hω
              rw [hω]
        _ = ∫⁻ x, ENNReal.ofReal
            (max (repeatedVariance (wholeRareKernel SAP.P018b.WH.W1.rareModel) x 1 1) 0)
            ∂repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N := by
              exact source_lintegral_map (f := fun x => ENNReal.ofReal
                (max (repeatedVariance (wholeRareKernel SAP.P018b.WH.W1.rareModel) x 1 1) 0))
                (source_measurable _)
        _ = ∞ := hpos
    · calc
        (∫⁻ ω, ENNReal.ofReal
            (max (-wholeWeightedVariance (wholeRareDirected SAP.P018b.WH.W1.rareModel)
              (fun _ _ => 1) ω 1 1) 0)
            ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) =
          ∫⁻ ω, ENNReal.ofReal
            (max (-repeatedVariance (wholeRareKernel SAP.P018b.WH.W1.rareModel)
              (proj N ω) 1 1) 0)
            ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N := by
              apply lintegral_congr_ae
              filter_upwards [variance_ae N] with ω hω
              rw [hω]
        _ = ∫⁻ x, ENNReal.ofReal
            (max (-repeatedVariance (wholeRareKernel SAP.P018b.WH.W1.rareModel) x 1 1) 0)
            ∂repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N := by
              exact source_lintegral_map (f := fun x => ENNReal.ofReal
                (max (-repeatedVariance (wholeRareKernel SAP.P018b.WH.W1.rareModel) x 1 1) 0))
                (source_measurable _)
        _ < ∞ := hneg

theorem directed_limits :
    wholeRareDirectedLimits SAP.P018b.WH.W1.rareModel := by
  rcases SAP.P018b.WH.W1.rareModel_limits with ⟨hv, hpd, hdet, hprob, hweak⟩
  constructor
  · intro ε hε
    have hevent (N : ℕ) :
        repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N
          {ω | ε ≤ ‖(N : ℝ) • wholeWeightedVariance
            (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω -
            wholeRareLimitMatrix SAP.P018b.WH.W1.rareModel‖} =
        repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N
          {x | ε ≤ ‖(N : ℝ) • repeatedVariance
            (wholeRareKernel SAP.P018b.WH.W1.rareModel) x -
            wholeRareLimitMatrix SAP.P018b.WH.W1.rareModel‖} := by
      have hSet :
          {ω | ε ≤ ‖(N : ℝ) • wholeWeightedVariance
              (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω -
              wholeRareLimitMatrix SAP.P018b.WH.W1.rareModel‖} =ᵐ[
            repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N]
          {ω | ε ≤ ‖(N : ℝ) • repeatedVariance
              (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) -
              wholeRareLimitMatrix SAP.P018b.WH.W1.rareModel‖} := by
        filter_upwards [variance_ae N] with ω hω
        rw [hω]
      calc
        _ = repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N
              {ω | ε ≤ ‖(N : ℝ) • repeatedVariance
                (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) -
                wholeRareLimitMatrix SAP.P018b.WH.W1.rareModel‖} :=
          MeasureTheory.measure_congr hSet
        _ = _ := source_event_measure (N := N)
          (s := {x | ε ≤ ‖(N : ℝ) •
            repeatedVariance (wholeRareKernel SAP.P018b.WH.W1.rareModel) x -
            wholeRareLimitMatrix SAP.P018b.WH.W1.rareModel‖})
          (source_event_measurable _)
    have hsrc := hprob ε hε
    apply Tendsto.congr' (f₁ := fun N =>
      (repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N
        {x | ε ≤ ‖(N : ℝ) • repeatedVariance
          (wholeRareKernel SAP.P018b.WH.W1.rareModel) x -
          wholeRareLimitMatrix SAP.P018b.WH.W1.rareModel‖}).toReal)
    · exact Filter.Eventually.of_forall fun N => congrArg ENNReal.toReal (hevent N).symm
    · exact hsrc
  · rcases hweak with ⟨ν, hnormal, hweak⟩
    refine ⟨ν, hnormal, ?_⟩
    rcases hweak with ⟨hmeas, hν, htest⟩
    refine ⟨?_, hν, ?_⟩
    · intro N
      have hcomp : AEMeasurable
          (fun ω : Fin N → U => Real.sqrt N •
            (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω -
              repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N))
          (repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N) := hmeas N
      have hcompMap : AEMeasurable
          (fun x : Fin N → U => Real.sqrt N •
            (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) x -
              repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N))
          (Measure.map (proj N)
            (repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N)) := by
        rw [(projection_mp N).map_eq]
        exact hcomp
      have hcompose := hcompMap.comp_aemeasurable (proj_measurable N).aemeasurable
      have hbeta : repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N = 0 := by
        exact source_beta_zero N
      have hAE :
          (fun ω : Fin N → U × ℝ => Real.sqrt N •
            wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel)
              (fun _ _ => 1) ω) =ᵐ[
            repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N]
          (fun ω => Real.sqrt N •
            (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) -
              repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N)) := by
        filter_upwards [ols_ae N] with ω hω
        simp [hω, hbeta]
      exact hcompose.congr hAE.symm
    · intro g
      have hInt (N : ℕ) :
          (∫ ω, g (Real.sqrt N • wholeWeightedOLS
            (wholeRareDirected SAP.P018b.WH.W1.rareModel) (fun _ _ => 1) ω)
            ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N) =
          ∫ x, g (Real.sqrt N • (repeatedOLS
            (wholeRareKernel SAP.P018b.WH.W1.rareModel) x -
            repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N))
            ∂repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N := by
        have hbeta : repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N = 0 := by
          exact source_beta_zero N
        have hAE :
            (fun ω : Fin N → U × ℝ => g (Real.sqrt N •
              wholeWeightedOLS (wholeRareDirected SAP.P018b.WH.W1.rareModel)
                (fun _ _ => 1) ω)) =ᵐ[
              repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N]
            (fun ω => g (Real.sqrt N •
              (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) -
                repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N))) := by
          filter_upwards [ols_ae N] with ω hω
          simp [hω, hbeta]
        calc
          _ = ∫ ω, g (Real.sqrt N •
                (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) (proj N ω) -
                  repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N))
                ∂repeatedLaw (wholeRareDirected SAP.P018b.WH.W1.rareModel) N :=
            integral_congr_ae hAE
          _ = _ := by
            exact source_integral_map (N := N)
              (f := fun x => g (Real.sqrt N •
                (repeatedOLS (wholeRareKernel SAP.P018b.WH.W1.rareModel) x -
                  repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N))) (by
                rw [(projection_mp N).map_eq]
                exact ((g.measurable.comp (source_measurable _)).stronglyMeasurable).aestronglyMeasurable)
      apply Tendsto.congr' (f₁ := fun N =>
        ∫ x, g (Real.sqrt N • (repeatedOLS
          (wholeRareKernel SAP.P018b.WH.W1.rareModel) x -
          repeatedBeta (wholeRareKernel SAP.P018b.WH.W1.rareModel) N))
          ∂repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N)
      · exact Filter.Eventually.of_forall fun N => (hInt N).symm
      · exact htest g

end SAP.P018b.WH.W1.P.T19_L9

theorem SAP.P018b.WH.W1.T19_L9_proof : SAP.P018b.WH.W1.T19_L9 := by
  exact ⟨SAP.P018b.WH.W1.P.T19_L9.directed_moments,
    SAP.P018b.WH.W1.P.T19_L9.directed_limits⟩
