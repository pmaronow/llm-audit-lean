import SAP.P011b.WH.W1.Leaves
import AronowAudit.P011.P011_BlockOLSCompletion
import AronowAudit.P011.Wave1.Gap.GLP011B4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W1.P.T15_L1

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

abbrev StarSource := AronowAudit.P011.Wave1.star_Source
abbrev StarFlat := AronowAudit.P011.Wave1.star_Flat 1
abbrev StarAxis := AronowAudit.P011.Wave1.star_Axis 1

def leafThreshold (upper : Bool) (j : Fin 3) : ℕ :=
  if upper then (![3, 1, 2] : Fin 3 → ℕ) j else 1

def leafPrimitive (upper : Bool) (j : Fin 3) (a : Fin 4) : ℝ :=
  if a.val < leafThreshold upper j then 1 else 0

def sourceObs (upper : Bool) (a : StarSource) : Fin 4 → ℝ :=
  fun r => AronowAudit.P011.starBlock upper a.1 a.2 r

lemma source_law (upper : Bool) :
    (SAP.P011b.starModel upper 1).law =
      AronowAudit.P011.uniformLaw (sourceObs upper) := by
  classical
  let e : (Fin 1 → StarSource) ≃ StarSource := Equiv.funUnique (Fin 1) StarSource
  change AronowAudit.P011.uniformLaw (fun u : Fin 1 → StarSource =>
    fun i => AronowAudit.P011.starBlock upper
      (u (AronowAudit.P011.blockIndex (by decide) i)).1
      (u (AronowAudit.P011.blockIndex (by decide) i)).2
    (AronowAudit.P011.localIndex (by decide) i)) =
      AronowAudit.P011.uniformLaw (sourceObs upper)
  have he : (fun u : Fin 1 → StarSource =>
      fun i => AronowAudit.P011.starBlock upper
        (u (AronowAudit.P011.blockIndex (by decide) i)).1
        (u (AronowAudit.P011.blockIndex (by decide) i)).2
        (AronowAudit.P011.localIndex (by decide) i)) = sourceObs upper ∘ e := by
    funext u i
    have hb : AronowAudit.P011.blockIndex (by decide : 0 < 4) i = 0 := by
      apply Fin.ext
      simp [AronowAudit.P011.blockIndex]
    have hl : AronowAudit.P011.localIndex (by decide : 0 < 4) i = i := by
      apply Fin.ext
      simp [AronowAudit.P011.localIndex]
    rw [hb, hl]
    rfl
  rw [he]
  exact AronowAudit.P011.NewFiniteCompletion.uniformLaw_equiv e (sourceObs upper)

lemma sourceObs_leaf (upper : Bool) (a : StarSource) (j : Fin 3) :
    sourceObs upper a j.succ = AronowAudit.P011.starLeaves upper a.1 j := by
  fin_cases j <;> rfl

def leafMatches (upper : Bool) (s : Fin 3 → Bool) (u : Fin 3 → Fin 4) : Prop :=
  ∀ j, AronowAudit.P011.starLeaves upper u j = if s j then 1 else 0

lemma source_leaf_event_iff (upper : Bool) (s : Fin 3 → Bool) (a : StarSource) :
    sourceObs upper a ∈ SAP.P011b.w1LeafEvent s ↔ leafMatches upper s a.1 := by
  simp [SAP.P011b.w1LeafEvent, sourceObs_leaf, leafMatches]

def flatObs (upper : Bool) (a : StarFlat) : Fin 4 → ℝ :=
  AronowAudit.P011.Wave1.star_source upper 1 (AronowAudit.P011.Wave1.star_flatEquiv 1 a)

lemma flatObs_leaf (upper : Bool) (a : StarFlat) (j : Fin 3) :
    flatObs upper a j.succ = leafPrimitive upper j (a (0, Sum.inl j)) := by
  have hb : AronowAudit.P011.blockIndex (by decide : 0 < 4) (blocks := 1) j.succ = 0 := by
    apply Fin.ext
    simp [AronowAudit.P011.blockIndex]
  have hl : AronowAudit.P011.localIndex (by decide : 0 < 4) (blocks := 1) j.succ = j.succ := by
    apply Fin.ext
    simp [AronowAudit.P011.localIndex]
    omega
  simp [flatObs, AronowAudit.P011.Wave1.star_source, hb, hl,
    AronowAudit.P011.Wave1.star_flatEquiv, AronowAudit.P011.starBlock,
    AronowAudit.P011.starLeaves, leafPrimitive, leafThreshold]
  fin_cases j <;> simp [AronowAudit.P011.starLeaves, leafPrimitive, leafThreshold] <;> rfl

lemma flatObs_law (upper : Bool) :
    ((PMF.uniformOfFintype StarFlat).toMeasure).map (flatObs upper) =
      (SAP.P011b.starModel upper 1).law := by
  have h := AronowAudit.P011.Wave1.star_source_map upper 1
  have hm : (SAP.P011b.starModel upper 1).law =
      (AronowAudit.P011.starModel upper 1).law := by rfl
  rw [hm]
  exact h

lemma indepFun_map {ι Ω Ω' β : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace β]
    (μ : Measure Ω) (g : Ω → Ω') (hg : Measurable g)
    (f : ι → Ω' → β) (hf : ∀ i, Measurable (f i))
    (h : iIndepFun (fun i => f i ∘ g) μ) :
    iIndepFun f (μ.map g) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  have hset : MeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) := by
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
      (hf i) (hs i hi)
  rw [Measure.map_apply hg hset]
  have hsrc := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp h)
    S (sets := sets) hs
  have hleft : g ⁻¹' (⋂ i ∈ S, f i ⁻¹' sets i) =
      ⋂ i ∈ S, (f i ∘ g) ⁻¹' sets i := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iInter]
    constructor
    · intro hx i hi
      exact (hx i hi)
    · intro hx
      intro i hi
      exact hx i hi
  have hm (i : ι) (hi : i ∈ S) :
      (μ.map g) (f i ⁻¹' sets i) = μ ((f i ∘ g) ⁻¹' sets i) :=
    Measure.map_apply hg ((hf i) (hs i hi))
  calc
    μ (g ⁻¹' (⋂ i ∈ S, f i ⁻¹' sets i)) =
        μ (⋂ i ∈ S, (f i ∘ g) ⁻¹' sets i) := by rw [hleft]
    _ = ∏ i ∈ S, μ ((f i ∘ g) ⁻¹' sets i) := hsrc
    _ = ∏ i ∈ S, (μ.map g) (f i ⁻¹' sets i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (hm i hi).symm

lemma flat_leaves_indep (upper : Bool) :
    iIndepFun (fun j : Fin 3 => fun a : StarFlat =>
      leafPrimitive upper j (a (0, Sum.inl j)))
      ((PMF.uniformOfFintype StarFlat).toMeasure) := by
  classical
  let A : StarAxis → Type := fun p => AronowAudit.P011.Wave1.star_Atom p.2
  have hpi : (PMF.uniformOfFintype StarFlat).toMeasure =
      Measure.pi (fun p : StarAxis =>
        (PMF.uniformOfFintype (A p)).toMeasure) := by
    simpa [StarFlat, StarAxis, A] using
      (AronowAudit.P011.Wave1.star_uniform_pi
        (fun p : StarAxis => AronowAudit.P011.Wave1.star_Atom p.2))
  have hbase : iIndepFun (fun p : StarAxis => fun a : StarFlat => a p)
      (Measure.pi (fun p : StarAxis =>
        (PMF.uniformOfFintype (A p)).toMeasure)) := by
    exact iIndepFun_pi (X := fun p : StarAxis => id)
      (fun _ => aemeasurable_id)
  rw [hpi]
  have hinj : Function.Injective
      (fun j : Fin 3 => ((0 : Fin 1), Sum.inl j) : Fin 3 → StarAxis) := by
    intro i j h
    exact (Sum.inl.inj (congrArg Prod.snd h))
  have hcoords := hbase.precomp (g := fun j : Fin 3 => ((0 : Fin 1), Sum.inl j)) hinj
  exact hcoords.comp (fun j a => leafPrimitive upper j a)
    (fun j => measurable_of_finite _)

lemma observed_leaf_indep (upper : Bool) :
    iIndepFun (fun j : Fin 3 => fun y : Fin 4 → ℝ => y j.succ)
      (SAP.P011b.starModel upper 1).law := by
  classical
  let μ := (PMF.uniformOfFintype StarFlat).toMeasure
  have hflat := flat_leaves_indep upper
  have hcomp : iIndepFun
      (fun j : Fin 3 => (fun y : Fin 4 → ℝ => y j.succ) ∘ flatObs upper) μ := by
    apply (iIndepFun_congr (μ := μ) (f := fun j a =>
      (fun y : Fin 4 → ℝ => y j.succ) (flatObs upper a))
      (g := fun j a => leafPrimitive upper j (a (0, Sum.inl j))) ?_).2 hflat
    intro j
    filter_upwards with a
    exact flatObs_leaf upper a j
  have hmap := indepFun_map μ (flatObs upper) (measurable_of_finite _)
    (fun (j : Fin 3) (y : Fin 4 → ℝ) => y j.succ)
    (fun j => measurable_pi_apply j.succ) hcomp
  rw [flatObs_law] at hmap
  exact hmap

lemma uniformLaw_real_count {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
    (f : A → Fin n → ℝ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    (AronowAudit.P011.uniformLaw f).real E =
      (Fintype.card A : ℝ)⁻¹ * ∑ a, if f a ∈ E then (1 : ℝ) else 0 := by
  change ((AronowAudit.P011.uniformLaw f) E).toReal = _
  rw [AronowAudit.P011.Wave1.uci_uniform_apply f E hE]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (by
        intro a ha
        split_ifs <;> simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : f a ∈ E <;> simp [h]

lemma probability_count (upper : Bool) (E : Set (Fin 4 → ℝ)) (hE : MeasurableSet E) :
    SAP.P011b.probability (SAP.P011b.starModel upper 1) E =
      (Fintype.card StarSource : ℝ)⁻¹ *
        ∑ a : StarSource, if sourceObs upper a ∈ E then (1 : ℝ) else 0 := by
  unfold SAP.P011b.probability
  rw [source_law upper]
  exact uniformLaw_real_count (sourceObs upper) E hE

lemma leafPattern_count (upper : Bool) (s : Fin 3 → Bool) :
    (∑ a : StarSource,
      if sourceObs upper a ∈ SAP.P011b.w1LeafEvent s then (1 : ℝ) else 0) =
      48 * ∑ u : Fin 3 → Fin 4,
        if leafMatches upper s u then (1 : ℝ) else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [source_leaf_event_iff]
  have hv (u : Fin 3 → Fin 4) :
      (∑ v : Fin 48, if leafMatches upper s u then (1 : ℝ) else 0) =
        48 * (if leafMatches upper s u then (1 : ℝ) else 0) := by
    by_cases h : leafMatches upper s u <;> simp [h, Fintype.card_fin]
  simp_rw [hv]
  rw [← Finset.mul_sum]

lemma leafMarginal_count (upper : Bool) (j : Fin 3) :
    (∑ a : StarSource,
      if sourceObs upper a j.succ = 1 then (1 : ℝ) else 0) =
      48 * ∑ u : Fin 3 → Fin 4, AronowAudit.P011.starLeaves upper u j := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [sourceObs_leaf]
  have hb (u : Fin 3 → Fin 4) :
      (if AronowAudit.P011.starLeaves upper u j = 1 then (1 : ℝ) else 0) =
        AronowAudit.P011.starLeaves upper u j := by
    simp [AronowAudit.P011.starLeaves]
  simp_rw [hb]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  norm_num

lemma marginal_probability (upper : Bool) (j : Fin 3) :
    SAP.P011b.probability (SAP.P011b.starModel upper 1)
      {y | y j.succ = 1} =
      if upper then (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j else 1/4 := by
  have hE : MeasurableSet {y : Fin 4 → ℝ | y j.succ = 1} := by measurability
  rw [probability_count upper _ hE]
  change (Fintype.card StarSource : ℝ)⁻¹ *
      (∑ a : StarSource, if sourceObs upper a j.succ = 1 then (1 : ℝ) else 0) = _
  rw [leafMarginal_count]
  have hc : (Fintype.card StarSource : ℝ) = 3072 := by
    norm_num [StarSource, Fintype.card_prod, Fintype.card_fun]
  rw [hc, AronowAudit.P011.BlockOLSCompletion.star_leaves_mean]
  cases upper <;> fin_cases j <;> norm_num [Fintype.card_fin] <;> ring

lemma leafThreshold_pos (upper : Bool) (j : Fin 3) : 0 < leafThreshold upper j := by
  cases upper <;> fin_cases j <;> norm_num [leafThreshold]

lemma leafThreshold_lt_four (upper : Bool) (j : Fin 3) : leafThreshold upper j < 4 := by
  cases upper <;> fin_cases j <;> norm_num [leafThreshold]

end
end SAP.P011b.WH.W1.P.T15_L1
