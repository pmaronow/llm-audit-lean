import AronowAudit.P006.P006_CounterfactualMetrics
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Analysis.Real.Cardinality

/-! Counterexample to the unrestricted marginal/maximal comparison in T17(d). -/
namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

local instance DecideE_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p

open Set Cardinal

/-- Choose distinct representatives along an initial cardinal. -/
lemma DecideE_distinct_selection (κ : Cardinal.{0})
    (F : κ.ord.ToType → Set ℝ) (hF : ∀ i, κ ≤ #(F i)) :
    ∃ g : κ.ord.ToType → ℝ, Function.Injective g ∧ ∀ i, g i ∈ F i := by
  have fresh (i : κ.ord.ToType) (g : Set.Iio i → ℝ) :
      (F i \ Set.range g).Nonempty := by
    apply Cardinal.sdiff_nonempty_of_mk_lt_mk
    exact (Cardinal.mk_range_le (f := g)).trans_lt
      ((show #(Set.Iio i) < κ by simpa using Cardinal.mk_Iio_lt i (by simp)).trans_le (hF i))
  let g : κ.ord.ToType → ℝ := WellFounded.fix wellFounded_lt
    (fun i g => (fresh i (fun j => g j.1 (Set.mem_Iio.mp j.2))).choose)
  have hg (i : κ.ord.ToType) :
      g i ∈ F i ∧ g i ∉ Set.range (fun j : Set.Iio i => g j.1) := by
    change g i ∈ F i \ Set.range (fun j : Set.Iio i => g j.1)
    have hfix : g i = (fresh i (fun j => g j.1)).choose :=
      WellFounded.fix_eq wellFounded_lt _ i
    rw [hfix]
    exact (fresh i (fun j => g j.1)).choose_spec
  refine ⟨g, ?_, fun i => (hg i).1⟩
  apply Function.Injective.of_lt_imp_ne
  intro i j hij heq
  exact (hg j).2 ⟨⟨i, hij⟩, heq⟩

/-- A continuum-sized family of continuum-sized sets can be split simultaneously. -/
lemma DecideE_split_family {ι : Type} (F : ι → Set ℝ)
    (hι : #ι ≤ 𝔠) (hF : ∀ i, 𝔠 ≤ #(F i)) :
    ∃ A : Set ℝ, ∀ i, (F i ∩ A).Nonempty ∧ (F i \ A).Nonempty := by
  have hcard : #(ι × Bool) ≤ #((𝔠 : Cardinal.{0}).ord.ToType) := by
    rw [Cardinal.mk_prod, Cardinal.mk_fintype Bool, Fintype.card_bool, Cardinal.mk_ord_toType]
    simp only [Cardinal.lift_id]
    exact (mul_le_mul' hι le_rfl).trans_eq (Cardinal.continuum_mul_nat (by decide : 2 ≠ 0))
  let e : (ι × Bool) ↪ (𝔠 : Cardinal.{0}).ord.ToType :=
    Classical.choice hcard
  let G : (𝔠 : Cardinal.{0}).ord.ToType → Set ℝ := fun j =>
    if h : ∃ i, e i = j then F (Classical.choose h).1 else Set.univ
  have hG (j) : 𝔠 ≤ #(G j) := by
    dsimp [G]
    split_ifs
    · exact hF _
    · simp [Cardinal.mk_real]
  obtain ⟨g, hginj, hg⟩ := DecideE_distinct_selection 𝔠 G hG
  have he (i : ι × Bool) : G (e i) = F i.1 := by
    dsimp [G]
    rw [dif_pos ⟨i, rfl⟩]
    congr 1
    exact congrArg Prod.fst (e.injective (Classical.choose_spec (show ∃ k, e k = e i from ⟨i, rfl⟩)))
  refine ⟨Set.range (fun i : ι => g (e (i, false))), fun i => ?_⟩
  constructor
  · exact ⟨g (e (i, false)), by simpa [he] using hg (e (i, false)), ⟨i, rfl⟩⟩
  · refine ⟨g (e (i, true)), by simpa [he] using hg (e (i, true)), ?_⟩
    rintro ⟨j, hj⟩
    have := congrArg Prod.snd (e.injective (hginj hj))
    cases this

/-- The bounded ambient probability, with the ordinary Borel structure on the reals. -/
def DecideE_uniform : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance DecideE_uniform_probability : IsProbabilityMeasure DecideE_uniform where
  measure_univ := by norm_num [DecideE_uniform]

instance DecideE_uniform_noAtoms : NullSingletonClass DecideE_uniform :=
  inferInstanceAs (NullSingletonClass (volume.restrict (Set.Icc (0 : ℝ) 1)))

lemma DecideE_compact_card {K : Set ℝ} (hK : IsCompact K)
    (hpos : DecideE_uniform K ≠ 0) : 𝔠 ≤ #K := by
  have hunc : ¬ K.Countable := fun h => hpos (h.measure_zero DecideE_uniform)
  obtain ⟨f, hfK, _, hfinj⟩ :=
    hK.isClosed.exists_nat_bool_injection_of_not_countable hunc
  have : #(ℕ → Bool) ≤ #K :=
    Cardinal.mk_le_of_injective (f := fun x => (⟨f x, hfK ⟨x, rfl⟩⟩ : K))
      (fun x y h => hfinj (congrArg Subtype.val h))
  simpa [Cardinal.mk_arrow] using this

/-- Both parts of the partition have inner measure zero. -/
lemma DecideE_partition : ∃ A : Set ℝ,
    (∀ H : Set ℝ, MeasurableSet H → H ⊆ A → DecideE_uniform H = 0) ∧
    (∀ H : Set ℝ, MeasurableSet H → H ⊆ Aᶜ → DecideE_uniform H = 0) := by
  let ι := {K : Set ℝ // IsCompact K ∧ DecideE_uniform K ≠ 0}
  have hι : #ι ≤ 𝔠 := by
    have hsub : #ι ≤ #{s : Set ℝ | MeasurableSet s} :=
      Cardinal.mk_le_of_injective
        (f := fun K : ι => (⟨K.1, K.2.1.measurableSet⟩ : {s : Set ℝ | MeasurableSet s}))
        (by intro x y h; exact Subtype.ext (congrArg (fun z : {s : Set ℝ | MeasurableSet s} => z.1) h))
    apply hsub.trans
    have hb := (TopologicalSpace.isBasis_countableBasis ℝ).borel_eq_generateFrom
    change #{s : Set ℝ | MeasurableSet[borel ℝ] s} ≤ 𝔠
    rw [hb]
    apply MeasurableSpace.cardinal_measurableSet_le_continuum
    exact (Cardinal.mk_le_aleph0_iff.mpr (TopologicalSpace.countable_countableBasis ℝ).to_subtype).trans
      Cardinal.aleph0_le_continuum
  obtain ⟨A, hA⟩ := DecideE_split_family (fun K : ι => K.1) hι
    (fun K => DecideE_compact_card K.2.1 K.2.2)
  have hzero (H : Set ℝ) (hm : MeasurableSet H) (hdisj :
      ∀ K : ι, ¬ K.1 ⊆ H) : DecideE_uniform H = 0 := by
    by_contra hpos
    obtain ⟨K, hKH, hK, hKpos⟩ := hm.exists_lt_isCompact_of_ne_top
      (measure_ne_top _ _) (pos_iff_ne_zero.mpr hpos)
    exact hdisj ⟨K, hK, ne_of_gt hKpos⟩ hKH
  refine ⟨A, ?_, ?_⟩
  · intro H hm hHA
    apply hzero H hm
    intro K hKH
    obtain ⟨x, hxK, hxA⟩ := (hA K).2
    exact hxA (hHA (hKH hxK))
  · intro H hm hHA
    apply hzero H hm
    intro K hKH
    obtain ⟨x, hxK, hxA⟩ := (hA K).1
    exact hHA (hKH hxK) hxA

/-- Trace-measurable sets satisfy Carathéodory's criterion for the pulled-back outer measure. -/
lemma DecideE_trace_caratheodory (A : Set ℝ) :
    (inferInstance : MeasurableSpace A) ≤
      (OuterMeasure.comap (Subtype.val : A → ℝ) DecideE_uniform.toOuterMeasure).caratheodory := by
  intro s hs T
  obtain ⟨H, hH, rfl⟩ := hs
  have hi : Subtype.val '' (T ∩ Subtype.val ⁻¹' H) = Subtype.val '' T ∩ H := by
    ext x
    simp only [mem_image, mem_inter_iff, mem_preimage]
    aesop
  have hd : Subtype.val '' (T \ Subtype.val ⁻¹' H) = Subtype.val '' T \ H := by
    ext x
    simp only [mem_image, Set.mem_sdiff, mem_preimage]
    aesop
  simpa only [OuterMeasure.comap_apply, Measure.coe_toOuterMeasure, hi, hd] using
    (measure_inter_add_sdiff (μ := DecideE_uniform) (Subtype.val '' T) hH).symm

/-- The trace law uses outer measure on the inclusion image, then trims to the trace sigma-algebra. -/
def DecideE_trace (A : Set ℝ) : Measure A :=
  (OuterMeasure.comap (Subtype.val : A → ℝ) DecideE_uniform.toOuterMeasure).toMeasure
    (DecideE_trace_caratheodory A)

lemma DecideE_trace_apply (A : Set ℝ) (s : Set A) (hs : MeasurableSet s) :
    DecideE_trace A s = DecideE_uniform (Subtype.val '' s) := by
  rw [DecideE_trace, toMeasure_apply _ _ hs, OuterMeasure.comap_apply, Measure.coe_toOuterMeasure]

lemma DecideE_outer_inter (A : Set ℝ)
    (hA : ∀ H : Set ℝ, MeasurableSet H → H ⊆ Aᶜ → DecideE_uniform H = 0)
    (H : Set ℝ) (hH : MeasurableSet H) :
    DecideE_uniform (H ∩ A) = DecideE_uniform H := by
  apply le_antisymm (measure_mono inter_subset_left)
  let T := toMeasurable DecideE_uniform (H ∩ A)
  have hT : MeasurableSet T := measurableSet_toMeasurable _ _
  have hnull : DecideE_uniform (H \ T) = 0 := by
    apply hA _ (hH.diff hT)
    intro x hx hxA
    exact hx.2 (subset_toMeasurable DecideE_uniform (H ∩ A) ⟨hx.1, hxA⟩)
  calc
    DecideE_uniform H ≤ DecideE_uniform (T ∪ (H \ T)) := measure_mono (by
      intro x hx
      by_cases hxT : x ∈ T
      · exact Or.inl hxT
      · exact Or.inr ⟨hx, hxT⟩)
    _ ≤ DecideE_uniform T + DecideE_uniform (H \ T) := measure_union_le _ _
    _ = DecideE_uniform (H ∩ A) := by rw [hnull, add_zero, measure_toMeasurable]

lemma DecideE_trace_map (A : Set ℝ)
    (hA : ∀ H : Set ℝ, MeasurableSet H → H ⊆ Aᶜ → DecideE_uniform H = 0) :
    (DecideE_trace A).map Subtype.val = DecideE_uniform := by
  ext H hH
  rw [Measure.map_apply measurable_subtype_coe hH,
    DecideE_trace_apply A _ (measurable_subtype_coe hH),
    image_preimage_eq_inter_range]
  simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using DecideE_outer_inter A hA H hH

def DecideE_A : Set ℝ := DecideE_partition.choose

lemma DecideE_A_inner : ∀ H : Set ℝ, MeasurableSet H → H ⊆ DecideE_A → DecideE_uniform H = 0 :=
  DecideE_partition.choose_spec.1

lemma DecideE_B_inner : ∀ H : Set ℝ, MeasurableSet H → H ⊆ DecideE_Aᶜ → DecideE_uniform H = 0 :=
  DecideE_partition.choose_spec.2

lemma DecideE_trace_probability (A : Set ℝ)
    (hA : ∀ H : Set ℝ, MeasurableSet H → H ⊆ Aᶜ → DecideE_uniform H = 0) :
    IsProbabilityMeasure (DecideE_trace A) := by
  have : IsProbabilityMeasure ((DecideE_trace A).map Subtype.val) := by
    rw [DecideE_trace_map A hA]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable

instance DecideE_traceA_probability : IsProbabilityMeasure (DecideE_trace DecideE_A) :=
  DecideE_trace_probability _ DecideE_B_inner

instance DecideE_traceB_probability : IsProbabilityMeasure (DecideE_trace DecideE_Aᶜ) :=
  DecideE_trace_probability _ (by simpa only [compl_compl] using DecideE_A_inner)

abbrev DecideE_U := Sum {x : ℝ // x ∈ DecideE_A} {x : ℝ // x ∉ DecideE_A}

def DecideE_j : DecideE_U → ℝ := Sum.elim Subtype.val Subtype.val

def DecideE_tag : DecideE_U → ℝ := Sum.elim (fun _ => 0) (fun _ => 2)

lemma DecideE_j_measurable : Measurable DecideE_j :=
  measurable_subtype_coe.sumElim measurable_subtype_coe

lemma DecideE_tag_measurable : Measurable DecideE_tag :=
  measurable_const.sumElim measurable_const

def DecideE_eta : Measure DecideE_U :=
  (3 / 4 : ℝ≥0) • (DecideE_trace DecideE_A).map Sum.inl +
  (1 / 4 : ℝ≥0) • (DecideE_trace DecideE_Aᶜ).map Sum.inr

instance DecideE_eta_probability : IsProbabilityMeasure DecideE_eta where
  measure_univ := by
    simp only [DecideE_eta, Measure.add_apply, Measure.smul_apply, measure_univ]
    rw [← add_smul]
    norm_num

lemma DecideE_j_map : DecideE_eta.map DecideE_j = DecideE_uniform := by
  rw [DecideE_eta, Measure.map_add _ _ DecideE_j_measurable,
    Measure.map_smul _ DecideE_j_measurable.aemeasurable,
    Measure.map_smul _ DecideE_j_measurable.aemeasurable,
    Measure.map_map DecideE_j_measurable measurable_inl,
    Measure.map_map DecideE_j_measurable measurable_inr]
  change (3 / 4 : ℝ≥0) • (DecideE_trace DecideE_A).map Subtype.val +
    (1 / 4 : ℝ≥0) • (DecideE_trace DecideE_Aᶜ).map Subtype.val = DecideE_uniform
  rw [DecideE_trace_map DecideE_A DecideE_B_inner,
    DecideE_trace_map DecideE_Aᶜ (by simpa only [compl_compl] using DecideE_A_inner), ← add_smul]
  norm_num

lemma DecideE_bounded_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) (K : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ K) : Integrable f μ :=
  (integrable_const K).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)

lemma DecideE_eta_integral (f : DecideE_U → ℝ) (hf : Measurable f) (K : ℝ)
    (hb : ∀ u, ‖f u‖ ≤ K) :
    (∫ u, f u ∂DecideE_eta) =
      (3 / 4 : ℝ) * (∫ a, f (Sum.inl a) ∂DecideE_trace DecideE_A) +
      (1 / 4 : ℝ) * (∫ b, f (Sum.inr b) ∂DecideE_trace DecideE_Aᶜ) := by
  have h0 := DecideE_bounded_integrable ((DecideE_trace DecideE_A).map Sum.inl) hf K hb
  have h1 := DecideE_bounded_integrable ((DecideE_trace DecideE_Aᶜ).map Sum.inr) hf K hb
  rw [DecideE_eta, integral_add_measure (h0.smul_measure_nnreal) (h1.smul_measure_nnreal),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_map measurable_inl.aemeasurable hf.aestronglyMeasurable,
    integral_map measurable_inr.aemeasurable hf.aestronglyMeasurable]
  norm_num [NNReal.smul_def, smul_eq_mul] <;> rfl

lemma DecideE_tag_values (u : DecideE_U) : DecideE_tag u = 0 ∨ DecideE_tag u = 2 := by
  cases u <;> simp [DecideE_tag]

lemma DecideE_tag_integrable : Integrable DecideE_tag DecideE_eta :=
  DecideE_bounded_integrable _ DecideE_tag_measurable 2 (by
    intro u; rcases DecideE_tag_values u with h | h <;> norm_num [h])

lemma DecideE_tag_integral : (∫ u, DecideE_tag u ∂DecideE_eta) = 1 / 2 := by
  rw [DecideE_eta_integral DecideE_tag DecideE_tag_measurable 2 (by
    intro u; rcases DecideE_tag_values u with h | h <;> norm_num [h])]
  norm_num [DecideE_tag]

lemma DecideE_deviation_integral :
    (∫ u, |(1 / 2 : ℝ) - DecideE_tag u| ∂DecideE_eta) = 3 / 4 := by
  rw [DecideE_eta_integral (fun u => |(1 / 2 : ℝ) - DecideE_tag u|)
    (by exact (measurable_const.sub DecideE_tag_measurable).abs) 2 (by
    intro u; rcases DecideE_tag_values u with h | h <;> norm_num [h])]
  norm_num [DecideE_tag]

def DecideE_graph : Set (ℝ × DecideE_U) := {c | c.1 = DecideE_j c.2}

lemma DecideE_graph_measurable : MeasurableSet DecideE_graph :=
  measurableSet_eq_fun measurable_fst (DecideE_j_measurable.comp measurable_snd)

def DecideE_m : (ℝ × DecideE_U) → ℝ :=
  DecideE_graph.indicator (fun c => DecideE_tag c.2)

lemma DecideE_m_measurable : Measurable DecideE_m :=
  (DecideE_tag_measurable.comp measurable_snd).indicator DecideE_graph_measurable

lemma DecideE_m_values (c : ℝ × DecideE_U) : DecideE_m c = 0 ∨ DecideE_m c = 2 := by
  by_cases hc : c ∈ DecideE_graph
  · simpa [DecideE_m, hc] using DecideE_tag_values c.2
  · simp [DecideE_m, hc]

lemma DecideE_m_graph (u : DecideE_U) : DecideE_m (DecideE_j u, u) = DecideE_tag u := by
  simp [DecideE_m, DecideE_graph]

lemma DecideE_m_inl (x : ℝ) (a : DecideE_A) : DecideE_m (x, Sum.inl a) = 0 := by
  by_cases h : (x, Sum.inl a) ∈ DecideE_graph <;> simp [DecideE_m, DecideE_tag, h]

lemma DecideE_m_on_A {x : ℝ} (hx : x ∈ DecideE_A) (u : DecideE_U) :
    DecideE_m (x, u) = 0 := by
  cases u with
  | inl a => exact DecideE_m_inl x a
  | inr b =>
    have hn : (x, Sum.inr b) ∉ DecideE_graph := by
      change x ≠ (b : ℝ)
      intro he
      exact b.2 (he ▸ hx)
    simp [DecideE_m, hn]

def DecideE_a : DecideE_A :=
  (nonempty_of_measure_ne_zero (μ := DecideE_trace DecideE_A)
    (s := Set.univ) (by simp)).choose

lemma DecideE_maximum_eq (c : ℝ × DecideE_U) :
    maximumDeviation DecideE_m c = if c.1 ∈ DecideE_A then 0 else 2 := by
  have hsup (v : DecideE_U) (hv : ∀ u, |DecideE_m c - DecideE_m (c.1, u)| ≤
      |DecideE_m c - DecideE_m (c.1, v)|) :
      maximumDeviation DecideE_m c = |DecideE_m c - DecideE_m (c.1, v)| := by
    apply IsLUB.csSup_eq (s := Set.range (fun u => |DecideE_m c - DecideE_m (c.1, u)|))
      (IsGreatest.isLUB ⟨⟨v, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hv u⟩)
      ⟨_, ⟨v, rfl⟩⟩
  by_cases hx : c.1 ∈ DecideE_A
  · have hcur : DecideE_m c = 0 := by simpa using DecideE_m_on_A hx c.2
    have he := hsup c.2 (by intro u; simp [hcur, DecideE_m_on_A hx u])
    simpa [hx] using he
  · let b : {x : ℝ // x ∉ DecideE_A} := ⟨c.1, hx⟩
    have hm2 : DecideE_m (c.1, Sum.inr b) = 2 := by
      simpa [DecideE_j, DecideE_tag, b] using DecideE_m_graph (Sum.inr b)
    rcases DecideE_m_values c with hc | hc
    · have he := hsup (Sum.inr b) (by
        intro u
        rcases DecideE_m_values (c.1, u) with h | h <;> norm_num [hc, hm2, h])
      simpa [hx, hc, hm2] using he
    · have he := hsup (Sum.inl DecideE_a) (by
        intro u
        rcases DecideE_m_values (c.1, u) with h | h <;>
          norm_num [hc, DecideE_m_inl, h])
      simpa [hx, hc, DecideE_m_inl] using he

lemma DecideE_maximum_attained (c : ℝ × DecideE_U) :
    ∃ v, ∀ u, |DecideE_m c - DecideE_m (c.1, u)| ≤
      |DecideE_m c - DecideE_m (c.1, v)| := by
  by_cases hx : c.1 ∈ DecideE_A
  · refine ⟨c.2, fun u => ?_⟩
    have hcur : DecideE_m c = 0 := by simpa using DecideE_m_on_A hx c.2
    simp [hcur, DecideE_m_on_A hx u]
  · let b : {x : ℝ // x ∉ DecideE_A} := ⟨c.1, hx⟩
    have hm2 : DecideE_m (c.1, Sum.inr b) = 2 := by
      simpa [DecideE_j, DecideE_tag, b] using DecideE_m_graph (Sum.inr b)
    rcases DecideE_m_values c with hc | hc
    · refine ⟨Sum.inr b, fun u => ?_⟩
      rcases DecideE_m_values (c.1, u) with h | h <;> norm_num [hc, hm2, h]
    · refine ⟨Sum.inl DecideE_a, fun u => ?_⟩
      rcases DecideE_m_values (c.1, u) with h | h <;> norm_num [hc, DecideE_m_inl, h]

lemma DecideE_maximum_graph (u : DecideE_U) :
    maximumDeviation DecideE_m (DecideE_j u, u) = DecideE_tag u := by
  rw [DecideE_maximum_eq]
  cases u with
  | inl a => simp [DecideE_j, DecideE_tag, a.2]
  | inr b => simp [DecideE_j, DecideE_tag, b.2]

def DecideE_embed (u : DecideE_U) : ℝ × DecideE_U := (DecideE_j u, u)

lemma DecideE_embed_measurable : Measurable DecideE_embed :=
  DecideE_j_measurable.prodMk measurable_id

def DecideE_PX : Measure (ℝ × DecideE_U) := DecideE_eta.map DecideE_embed

instance DecideE_PX_probability : IsProbabilityMeasure DecideE_PX :=
  inferInstanceAs (IsProbabilityMeasure (DecideE_eta.map DecideE_embed))

lemma DecideE_maximum_ae : maximumDeviation DecideE_m =ᵐ[DecideE_PX]
    (fun c => DecideE_tag c.2) := by
  have hG : ∀ᵐ c ∂DecideE_PX, c ∈ DecideE_graph :=
    (ae_map_iff DecideE_embed_measurable.aemeasurable DecideE_graph_measurable).mpr
      (Eventually.of_forall (by intro u; rfl))
  filter_upwards [hG] with c hc
  rcases c with ⟨x, u⟩
  change x = DecideE_j u at hc
  subst x
  exact DecideE_maximum_graph u

lemma DecideE_maximum_integrable : Integrable (maximumDeviation DecideE_m) DecideE_PX := by
  apply (DecideE_bounded_integrable DecideE_PX
    (DecideE_tag_measurable.comp measurable_snd) 2 (by
      intro c; rcases DecideE_tag_values c.2 with h | h <;> norm_num [h])).congr
  exact DecideE_maximum_ae.symm

lemma DecideE_maximum_integral :
    (∫ c, maximumDeviation DecideE_m c ∂DecideE_PX) = 1 / 2 := by
  rw [integral_congr_ae DecideE_maximum_ae]
  rw [DecideE_PX, integral_map (f := fun c => DecideE_tag c.2) DecideE_embed_measurable.aemeasurable
    (DecideE_tag_measurable.comp measurable_snd).aestronglyMeasurable]
  exact DecideE_tag_integral

lemma DecideE_marginal_integral :
    (∫ c, |(1 / 2 : ℝ) - DecideE_m c| ∂DecideE_PX) = 3 / 4 := by
  rw [DecideE_PX, integral_map (f := fun c => |(1 / 2 : ℝ) - DecideE_m c|)
    DecideE_embed_measurable.aemeasurable
    (measurable_const.sub DecideE_m_measurable).abs.aestronglyMeasurable]
  simpa only [DecideE_embed, DecideE_m_graph] using DecideE_deviation_integral

lemma DecideE_condExp_fst {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α × ℝ → ℝ) (g : α → ℝ)
    (hf : Integrable f (μ.prod DecideE_uniform)) (hg : Measurable g) (hgi : Integrable g μ)
    (hinner : ∀ a, (∫ r, f (a, r) ∂DecideE_uniform) = g a) :
    (μ.prod DecideE_uniform)[f | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.prod DecideE_uniform]
      (fun ω => g ω.1) := by
  have hm : MeasurableSpace.comap (Prod.fst : α × ℝ → α) inferInstance ≤
      (inferInstance : MeasurableSpace (α × ℝ)) :=
    measurable_fst.comap_le
  have hgprod := hgi.comp_fst DecideE_uniform
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun _ _ _ => hgprod.integrableOn) ?_
    (hg.comp (comap_measurable Prod.fst)).stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs _
  obtain ⟨H, hH, rfl⟩ := hs
  rw [← integral_indicator (measurable_fst hH), ← integral_indicator (measurable_fst hH),
    integral_prod _ (hgprod.indicator (measurable_fst hH)),
    integral_prod _ (hf.indicator (measurable_fst hH))]
  apply integral_congr_ae (Eventually.of_forall (fun a => ?_))
  by_cases ha : a ∈ H <;> simp [Set.indicator_apply, ha, hinner]

abbrev DecideE_Omega := DecideE_U × ℝ

def DecideE_law : Measure DecideE_Omega := DecideE_eta.prod DecideE_uniform

instance DecideE_law_probability : IsProbabilityMeasure DecideE_law :=
  inferInstanceAs (IsProbabilityMeasure (DecideE_eta.prod DecideE_uniform))

def DecideE_C (ω : DecideE_Omega) : ℝ × DecideE_U := DecideE_embed ω.1

lemma DecideE_C_measurable : Measurable DecideE_C :=
  DecideE_embed_measurable.comp measurable_fst

lemma DecideE_covariateSigma : MeasurableSpace.comap DecideE_C inferInstance =
    MeasurableSpace.comap (Prod.fst : DecideE_Omega → DecideE_U) inferInstance := by
  apply le_antisymm
  · exact (DecideE_embed_measurable.comp (comap_measurable Prod.fst)).comap_le
  · exact (measurable_snd.comp (comap_measurable DecideE_C)).comap_le

def DecideE_treatment (π : (ℝ × DecideE_U) → ℝ) (ω : DecideE_Omega) : Bool :=
  if ω.2 ≤ π (DecideE_C ω) then true else false

lemma DecideE_treatment_measurable {π : (ℝ × DecideE_U) → ℝ} (hπ : Admissible π) :
    Measurable (DecideE_treatment π) :=
  Measurable.ite (measurableSet_le measurable_snd (hπ.1.comp DecideE_C_measurable))
    measurable_const measurable_const

lemma DecideE_bit_treatment {π : (ℝ × DecideE_U) → ℝ} (hπ : Admissible π) :
    Measurable (fun ω => bit (DecideE_treatment π ω)) :=
  (measurable_of_countable bit).comp (DecideE_treatment_measurable hπ)

lemma DecideE_bit_bound (b : Bool) : ‖bit b‖ ≤ 1 := by
  cases b <;> norm_num [bit]

lemma DecideE_uniform_threshold {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) :
    (∫ r, (if r ≤ q then (1 : ℝ) else 0) ∂DecideE_uniform) = q := by
  have he : Set.Iic q ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 q := by
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hrq, hr0, _⟩; exact ⟨hr0, hrq⟩
    · rintro ⟨hr0, hrq⟩; exact ⟨hrq, hr0, hrq.trans hq.2⟩
  change (∫ r, (Set.Iic q).indicator (fun _ => (1 : ℝ)) r ∂DecideE_uniform) = q
  rw [integral_indicator_const 1 measurableSet_Iic]
  simp only [smul_eq_mul, mul_one, measureReal_def, DecideE_uniform,
    Measure.restrict_apply measurableSet_Iic, he, Real.volume_Icc, sub_zero]
  exact ENNReal.toReal_ofReal hq.1

lemma DecideE_bernoulli {π : (ℝ × DecideE_U) → ℝ} (hπ : Admissible π) :
    DecideE_law[(fun ω => bit (DecideE_treatment π ω)) |
      MeasurableSpace.comap DecideE_C inferInstance] =ᵐ[DecideE_law]
      (fun ω => π (DecideE_C ω)) := by
  rw [DecideE_covariateSigma]
  apply DecideE_condExp_fst DecideE_eta _ (fun u => π (DecideE_embed u))
    (DecideE_bounded_integrable _ (DecideE_bit_treatment hπ) 1
      (fun ω => DecideE_bit_bound _))
    (hπ.1.comp DecideE_embed_measurable)
    (DecideE_bounded_integrable _ (hπ.1.comp DecideE_embed_measurable) 1 (by
      intro u; rw [Real.norm_eq_abs, abs_of_nonneg (hπ.2 _).1]; exact (hπ.2 _).2))
  intro u
  convert DecideE_uniform_threshold (hπ.2 (DecideE_embed u)) using 1
  congr 1
  funext r
  by_cases h : r ≤ π (DecideE_embed u) <;> simp [DecideE_treatment, DecideE_C, bit, h]

def DecideE_Y (ω : DecideE_Omega) : ℝ := DecideE_tag ω.1

lemma DecideE_Y_measurable : Measurable DecideE_Y :=
  DecideE_tag_measurable.comp measurable_fst

lemma DecideE_Y_integrable : Integrable DecideE_Y DecideE_law :=
  DecideE_tag_integrable.comp_fst DecideE_uniform


lemma DecideE_C_law : IdentDistrib DecideE_C (fun c : ℝ × DecideE_U => c)
    DecideE_law DecideE_PX := by
  refine ⟨DecideE_C_measurable.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id']
  change DecideE_law.map (DecideE_embed ∘ Prod.fst) = DecideE_PX
  rw [← Measure.map_map DecideE_embed_measurable measurable_fst,
    DecideE_law, Measure.map_fst_prod, measure_univ, one_smul]
  rfl


lemma DecideE_tag_setIntegral (H : Set ℝ) (hH : MeasurableSet H) :
    (∫ u in DecideE_j ⁻¹' H, DecideE_tag u ∂DecideE_eta) =
      (1 / 2 : ℝ) * DecideE_uniform.real H := by
  let f : DecideE_U → ℝ := (DecideE_j ⁻¹' H).indicator DecideE_tag
  have hf : Measurable f := DecideE_tag_measurable.indicator (DecideE_j_measurable hH)
  have hfb (u) : ‖f u‖ ≤ 2 := by
    by_cases hu : DecideE_j u ∈ H
    · rcases DecideE_tag_values u with h | h <;> norm_num [f, hu, h]
    · simp [f, hu]
  rw [← integral_indicator (DecideE_j_measurable hH)]
  change (∫ u, f u ∂DecideE_eta) = _
  rw [DecideE_eta_integral f hf 2 hfb]
  have h0 : (fun a : DecideE_A => f (Sum.inl a)) = (fun _ => 0) := by
    funext a
    by_cases ha : (a : ℝ) ∈ H <;> simp [f, DecideE_tag, DecideE_j, ha]
  have h1 : (fun b : {x : ℝ // x ∉ DecideE_A} => f (Sum.inr b)) =
      (fun b : {x : ℝ // x ∉ DecideE_A} => H.indicator (fun _ => (2 : ℝ)) (b : ℝ)) := by
    funext b
    by_cases hb : (b : ℝ) ∈ H <;> simp [f, DecideE_tag, DecideE_j, hb]
  rw [h0, integral_zero, mul_zero, zero_add]
  have hi1 : (∫ b, f (Sum.inr b) ∂DecideE_trace (DecideE_Aᶜ)) =
      ∫ b : {x : ℝ // x ∉ DecideE_A}, H.indicator (fun _ => (2 : ℝ)) (b : ℝ)
        ∂DecideE_trace (DecideE_Aᶜ) :=
    integral_congr_ae (Eventually.of_forall (fun b => congrFun h1 b))
  rw [hi1]
  have he := integral_map (μ := DecideE_trace (DecideE_Aᶜ))
    (φ := Subtype.val) (f := H.indicator (fun _ => (2 : ℝ)))
    measurable_subtype_coe.aemeasurable (measurable_const.indicator hH).aestronglyMeasurable
  rw [DecideE_trace_map (DecideE_Aᶜ) (by simpa only [compl_compl] using DecideE_A_inner)] at he
  have he' : (∫ b : {x : ℝ // x ∉ DecideE_A}, H.indicator (fun _ => (2 : ℝ)) (b : ℝ)
        ∂DecideE_trace (DecideE_Aᶜ)) = ∫ x, H.indicator (fun _ => (2 : ℝ)) x ∂DecideE_uniform := by
    convert he.symm using 1 <;> rfl
  rw [he', integral_indicator_const 2 hH, smul_eq_mul]
  ring

lemma DecideE_marginal_conditional :
    DecideE_law[(fun ω => DecideE_m (DecideE_C ω)) |
      MeasurableSpace.comap (fun ω => (DecideE_C ω).1) inferInstance] =ᵐ[DecideE_law]
      (fun _ => (1 / 2 : ℝ)) := by
  have hfun : (fun ω => DecideE_m (DecideE_C ω)) = DecideE_Y :=
    funext fun ω => DecideE_m_graph ω.1
  rw [hfun]
  have hm : MeasurableSpace.comap (fun ω => (DecideE_C ω).1) inferInstance ≤
      (inferInstance : MeasurableSpace DecideE_Omega) :=
    (measurable_fst.comp DecideE_C_measurable).comap_le
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm DecideE_Y_integrable
    (fun _ _ _ => (integrable_const (1 / 2 : ℝ)).integrableOn) ?_
    stronglyMeasurable_const.aestronglyMeasurable).symm
  intro s hs _
  obtain ⟨H, hH, rfl⟩ := hs
  have hSH : MeasurableSet ((fun ω => (DecideE_C ω).1) ⁻¹' H) :=
    (measurable_fst.comp DecideE_C_measurable) hH
  rw [← integral_indicator hSH, ← integral_indicator hSH]
  change (∫ ω, ((DecideE_j ⁻¹' H).indicator (fun _ => (1 / 2 : ℝ))) ω.1
      ∂DecideE_eta.prod DecideE_uniform) =
    ∫ ω, ((DecideE_j ⁻¹' H).indicator DecideE_tag) ω.1 ∂DecideE_eta.prod DecideE_uniform
  rw [integral_fun_fst, integral_fun_fst]
  simp only [probReal_univ, one_smul]
  rw [integral_indicator (DecideE_j_measurable hH),
    integral_indicator (DecideE_j_measurable hH), setIntegral_const, DecideE_tag_setIntegral H hH]
  have he : DecideE_eta.real (DecideE_j ⁻¹' H) = DecideE_uniform.real H := by
    rw [measureReal_def, ← Measure.map_apply DecideE_j_measurable hH, DecideE_j_map]
    rfl
  rw [he, smul_eq_mul, mul_comm]


/-- Conditional moments are unchanged by a measurable equivalence of sample spaces. -/
lemma DecideE_condExp_transport {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (e : α ≃ᵐ β) (μ : Measure α) [IsProbabilityMeasure μ]
    (Z : α → γ) (hZ : Measurable Z) (f : α → ℝ) (hf : Integrable f μ)
    (k : γ → ℝ) (hk : Measurable k) (hki : Integrable (fun a => k (Z a)) μ)
    (hc : μ[f | MeasurableSpace.comap Z inferInstance] =ᵐ[μ] (fun a => k (Z a))) :
    (μ.map e)[(fun b => f (e.symm b)) |
      MeasurableSpace.comap (fun b => Z (e.symm b)) inferInstance] =ᵐ[μ.map e]
      (fun b => k (Z (e.symm b))) := by
  have hZ' : Measurable (fun b => Z (e.symm b)) := hZ.comp e.symm.measurable
  have hfi : Integrable (fun b => f (e.symm b)) (μ.map e) :=
    e.measurableEmbedding.integrable_map_iff.mpr (by simpa only [Function.comp_def,
      e.symm_apply_apply] using hf)
  have hgi : Integrable (fun b => k (Z (e.symm b))) (μ.map e) :=
    e.measurableEmbedding.integrable_map_iff.mpr (by simpa only [Function.comp_def,
      e.symm_apply_apply] using hki)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hZ'.comap_le hfi
    (fun _ _ _ => hgi.integrableOn) ?_
    (hk.comp (comap_measurable (fun b => Z (e.symm b)))).stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs _
  obtain ⟨H, hH, rfl⟩ := hs
  rw [e.measurableEmbedding.setIntegral_map, e.measurableEmbedding.setIntegral_map]
  have hpre : e ⁻¹' ((fun b => Z (e.symm b)) ⁻¹' H) = Z ⁻¹' H := by
    ext a; simp
  simp only [e.symm_apply_apply, hpre]
  exact (setIntegral_congr_ae (hZ hH) (hc.symm.mono (fun a ha _ => ha))).trans
    (setIntegral_condExp hZ.comap_le hf ⟨H, hH, rfl⟩)

lemma DecideE_deterministic_ignorability {α C : Type*} [MeasurableSpace α] [MeasurableSpace C]
    (μ : Measure α) [IsProbabilityMeasure μ] (Z : α → C) (hZ : Measurable Z)
    (Y : α → ℝ) (hY : Measurable[MeasurableSpace.comap Z inferInstance] Y)
    (T : α → Bool) (hT : Measurable T) (π : C → ℝ)
    (hbern : μ[(fun a => bit (T a)) | MeasurableSpace.comap Z inferInstance] =ᵐ[μ]
      (fun a => π (Z a))) (B : Set (ℝ × ℝ)) (hB : MeasurableSet B) :
    μ[(fun a => bit (T a) * B.indicator (fun _ => (1 : ℝ)) (Y a, Y a)) |
      MeasurableSpace.comap Z inferInstance] =ᵐ[μ]
      (fun a => π (Z a) * μ[(fun b => B.indicator (fun _ => (1 : ℝ)) (Y b, Y b)) |
        MeasurableSpace.comap Z inferInstance] a) := by
  let v : α → ℝ := fun a => B.indicator (fun _ => (1 : ℝ)) (Y a, Y a)
  have hv : Measurable[MeasurableSpace.comap Z inferInstance] v :=
    (measurable_const.indicator hB).comp (hY.prodMk hY)
  have hv' : Measurable v := hv.mono hZ.comap_le le_rfl
  have hvb (a) : ‖v a‖ ≤ 1 := by
    by_cases ha : (Y a, Y a) ∈ B <;> simp [v, ha]
  have hvi := DecideE_bounded_integrable μ hv' 1 hvb
  have hb := (measurable_of_countable bit).comp hT
  have hbi := DecideE_bounded_integrable μ hb 1 (fun a => DecideE_bit_bound (T a))
  have hpi : Integrable ((fun a => bit (T a)) * v) μ :=
    DecideE_bounded_integrable μ (hb.mul hv') 1 (fun a => by
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_one₀ (DecideE_bit_bound _) (norm_nonneg _) (hvb a))
  have hpull := condExp_mul_of_stronglyMeasurable_right hv.stronglyMeasurable hpi hbi
  have hvCE := condExp_of_stronglyMeasurable hZ.comap_le hv.stronglyMeasurable hvi
  change μ[((fun a => bit (T a)) * v) | MeasurableSpace.comap Z inferInstance] =ᵐ[μ]
    (fun a => π (Z a) * μ[v | MeasurableSpace.comap Z inferInstance] a)
  rw [hvCE]
  filter_upwards [hpull, hbern] with a hp hb
  simpa only [Pi.mul_apply, hb] using hp

section UniverseTransport

variable {Ω' X' U' : Type*} [MeasurableSpace Ω'] [MeasurableSpace X'] [MeasurableSpace U']
    (eΩ : Ω' ≃ᵐ DecideE_Omega) (eX : X' ≃ᵐ ℝ) (eU : U' ≃ᵐ DecideE_U)

def DecideE_upC : (ℝ × DecideE_U) ≃ᵐ (X' × U') := (eX.prodCongr eU).symm

def DecideE_upLaw : Measure Ω' := DecideE_law.map eΩ.symm

instance DecideE_upLaw_probability : IsProbabilityMeasure (DecideE_upLaw eΩ) :=
  inferInstanceAs (IsProbabilityMeasure (DecideE_law.map eΩ.symm))

def DecideE_upPX : Measure (X' × U') := DecideE_PX.map (DecideE_upC eX eU)

instance DecideE_upPX_probability : IsProbabilityMeasure (DecideE_upPX eX eU) :=
  inferInstanceAs (IsProbabilityMeasure (DecideE_PX.map (DecideE_upC eX eU)))

def DecideE_upMean (c : X' × U') : ℝ := DecideE_m (eX c.1, eU c.2)

def DecideE_upCovariate (ω : Ω') : X' × U' := DecideE_upC eX eU (DecideE_C (eΩ ω))

def DecideE_upY (ω : Ω') : ℝ := DecideE_Y (eΩ ω)

def DecideE_upTreatment (π : X' × U' → ℝ) (ω : Ω') : Bool :=
  DecideE_treatment (fun c => π (DecideE_upC eX eU c)) (eΩ ω)

lemma DecideE_upMean_measurable : Measurable (DecideE_upMean eX eU) :=
  DecideE_m_measurable.comp (eX.measurable.prodMap eU.measurable)

lemma DecideE_upCovariate_measurable : Measurable (DecideE_upCovariate eΩ eX eU) :=
  (DecideE_upC eX eU).measurable.comp (DecideE_C_measurable.comp eΩ.measurable)

lemma DecideE_upY_measurable : Measurable (DecideE_upY eΩ) :=
  DecideE_Y_measurable.comp eΩ.measurable

lemma DecideE_upPolicy {π : X' × U' → ℝ} (hπ : Admissible π) :
    Admissible (fun c => π (DecideE_upC eX eU c)) :=
  ⟨hπ.1.comp (DecideE_upC eX eU).measurable, fun c => hπ.2 _⟩

lemma DecideE_up_covSigma : MeasurableSpace.comap
    (fun ω => DecideE_upC eX eU (DecideE_C ω)) inferInstance =
      MeasurableSpace.comap DecideE_C inferInstance := by
  change MeasurableSpace.comap ((DecideE_upC eX eU) ∘ DecideE_C) _ = _
  rw [← MeasurableSpace.comap_comp, (DecideE_upC eX eU).measurableEmbedding.comap_eq]

lemma DecideE_up_bernoulli {π : X' × U' → ℝ} (hπ : Admissible π) :
    (DecideE_upLaw eΩ)[(fun ω => bit (DecideE_upTreatment eΩ eX eU π ω)) |
      MeasurableSpace.comap (DecideE_upCovariate eΩ eX eU) inferInstance] =ᵐ[DecideE_upLaw eΩ]
      (fun ω => π (DecideE_upCovariate eΩ eX eU ω)) := by
  apply DecideE_condExp_transport eΩ.symm DecideE_law
    (fun ω => DecideE_upC eX eU (DecideE_C ω))
    ((DecideE_upC eX eU).measurable.comp DecideE_C_measurable)
    (fun ω => bit (DecideE_treatment (fun c => π (DecideE_upC eX eU c)) ω))
    (DecideE_bounded_integrable _ (DecideE_bit_treatment (DecideE_upPolicy eX eU hπ)) 1
      (fun _ => DecideE_bit_bound _)) π hπ.1
    (DecideE_bounded_integrable _
      (hπ.1.comp ((DecideE_upC eX eU).measurable.comp DecideE_C_measurable)) 1 (by
        intro ω; rw [Real.norm_eq_abs, abs_of_nonneg (hπ.2 _).1]; exact (hπ.2 _).2))
  rw [DecideE_up_covSigma]
  exact DecideE_bernoulli (DecideE_upPolicy eX eU hπ)

lemma DecideE_upMean_up (c : ℝ × DecideE_U) :
    DecideE_upMean eX eU (DecideE_upC eX eU c) = DecideE_m c := by
  change DecideE_m ((eX.prodCongr eU) ((eX.prodCongr eU).symm c)) = _
  rw [MeasurableEquiv.apply_symm_apply]

lemma DecideE_upMean_covariate (ω : Ω') :
    DecideE_upMean eX eU (DecideE_upCovariate eΩ eX eU ω) = DecideE_upY eΩ ω := by
  rw [DecideE_upCovariate, DecideE_upMean_up]
  exact DecideE_m_graph (eΩ ω).1

lemma DecideE_upY_covmeasurable :
    Measurable[MeasurableSpace.comap (DecideE_upCovariate eΩ eX eU) inferInstance]
      (DecideE_upY eΩ) := by
  have he : DecideE_upY eΩ = fun ω => DecideE_upMean eX eU (DecideE_upCovariate eΩ eX eU ω) :=
    funext fun ω => (DecideE_upMean_covariate eΩ eX eU ω).symm
  rw [he]
  exact (DecideE_upMean_measurable eX eU).comp (comap_measurable _)

def DecideE_upExperiment : Experiment Ω' (X' × U') 1 where
  hn := by decide
  PX := DecideE_upPX eX eU
  μ0 := DecideE_upMean eX eU
  μ1 := DecideE_upMean eX eU
  law := fun _ => DecideE_upLaw eΩ
  X := fun _ => DecideE_upCovariate eΩ eX eU
  Y0 := fun _ => DecideE_upY eΩ
  Y1 := fun _ => DecideE_upY eΩ
  T := fun π _ => DecideE_upTreatment eΩ eX eU π
  μhat := fun _ _ _ => 0

lemma DecideE_upStanding : Standing (DecideE_upExperiment eΩ eX eU) := by
  have hm := DecideE_upMean_measurable eX eU
  have hC := DecideE_upCovariate_measurable eΩ eX eU
  have hY := DecideE_upY_measurable eΩ
  have hiY : Integrable (DecideE_upY eΩ) (DecideE_upLaw eΩ) :=
    DecideE_bounded_integrable _ hY 2 (by
      intro ω; rcases DecideE_tag_values (eΩ ω).1 with h | h <;> norm_num [DecideE_upY, DecideE_Y, h])
  have hiM : Integrable (DecideE_upMean eX eU) (DecideE_upPX eX eU) :=
    DecideE_bounded_integrable _ hm 2 (by
      intro c; rcases DecideE_m_values (eX c.1, eU c.2) with h | h <;> norm_num [DecideE_upMean, h])
  have hT (π) (hπ : Admissible π) : Measurable (DecideE_upTreatment eΩ eX eU π) :=
    (DecideE_treatment_measurable (DecideE_upPolicy eX eU hπ)).comp eΩ.measurable
  have hCE : (DecideE_upLaw eΩ)[DecideE_upY eΩ |
      MeasurableSpace.comap (DecideE_upCovariate eΩ eX eU) inferInstance] =ᵐ[DecideE_upLaw eΩ]
      (fun ω => DecideE_upMean eX eU (DecideE_upCovariate eΩ eX eU ω)) := by
    rw [condExp_of_stronglyMeasurable hC.comap_le
      (DecideE_upY_covmeasurable eΩ eX eU).stronglyMeasurable hiY]
    exact Eventually.of_forall (fun ω => (DecideE_upMean_covariate eΩ eX eU ω).symm)
  have hCLaw : IdentDistrib (DecideE_upCovariate eΩ eX eU) (fun c : X' × U' => c)
      (DecideE_upLaw eΩ) (DecideE_upPX eX eU) := by
    refine ⟨hC.aemeasurable, measurable_id.aemeasurable, ?_⟩
    rw [Measure.map_id']
    change (DecideE_law.map eΩ.symm).map (DecideE_upCovariate eΩ eX eU) = _
    rw [Measure.map_map hC eΩ.symm.measurable]
    have he : (DecideE_upCovariate eΩ eX eU) ∘ eΩ.symm =
        (DecideE_upC eX eU) ∘ DecideE_C := by
      funext ω; simp [DecideE_upCovariate]
    rw [he, ← Measure.map_map (DecideE_upC eX eU).measurable DecideE_C_measurable,
      DecideE_C_law.map_eq, Measure.map_id']
    rfl
  refine {
    px_probability := DecideE_upPX_probability eX eU
    means_measurable := ⟨hm, hm⟩
    means_integrable := ⟨hiM, hiM⟩
    law_probability := fun _ _ => DecideE_upLaw_probability eΩ
    measurable_units := fun π hπ _ => ⟨hC, hY, hY, hT π hπ⟩
    integrable_units := fun _ _ _ => ⟨hiY, hiY,
      (show Integrable (fun _ : Ω' => (0 : ℝ)) (DecideE_upLaw eΩ) from integrable_const 0)⟩
    covariate_law := fun _ _ _ => hCLaw
    potential_law_fixed := fun _ _ _ _ _ => IdentDistrib.refl (hC.prodMk (hY.prodMk hY)).aemeasurable
    iid_independent := fun π _ => (show iIndepFun (fun _ : Fin 1 => fun ω =>
      (DecideE_upCovariate eΩ eX eU ω, DecideE_upY eΩ ω, DecideE_upY eΩ ω,
        DecideE_upTreatment eΩ eX eU π ω)) (DecideE_upLaw eΩ) from iIndepFun.of_subsingleton)
    iid_identical := fun π hπ _ _ => IdentDistrib.refl (hC.prodMk (hY.prodMk (hY.prodMk (hT π hπ)))).aemeasurable
    conditional_means := fun _ _ _ => ⟨hCE, hCE⟩
    bernoulli := fun _ hπ _ => DecideE_up_bernoulli eΩ eX eU hπ
    ignorability := fun π hπ _ B hB => DecideE_deterministic_ignorability (DecideE_upLaw eΩ)
      _ hC _ (DecideE_upY_covmeasurable eΩ eX eU) _ (hT π hπ) π
      (DecideE_up_bernoulli eΩ eX eU hπ) B hB }

lemma DecideE_upBaseline : MarginalBaseline (DecideE_upExperiment eΩ eX eU)
    (fun _ => (1 / 2 : ℝ)) := by
  refine ⟨measurable_const,
    (show Integrable (fun _ : X' × U' => (1 / 2 : ℝ)) (DecideE_upPX eX eU) from integrable_const _), ?_⟩
  intro π hπ i
  change (DecideE_upLaw eΩ)[(fun ω => DecideE_upMean eX eU (DecideE_upCovariate eΩ eX eU ω)) |
    MeasurableSpace.comap (fun ω => (DecideE_upCovariate eΩ eX eU ω).1) inferInstance]
    =ᵐ[DecideE_upLaw eΩ] (fun _ => (1 / 2 : ℝ))
  simp only [DecideE_upMean_covariate]
  have ht := DecideE_condExp_transport eΩ.symm DecideE_law
    (fun ω => eX.symm (DecideE_C ω).1)
    (eX.symm.measurable.comp (measurable_fst.comp DecideE_C_measurable))
    DecideE_Y DecideE_Y_integrable (fun _ => (1 / 2 : ℝ)) measurable_const (integrable_const _) ?_
  · convert ht using 1 <;> rfl
  · have he : MeasurableSpace.comap (fun ω => eX.symm (DecideE_C ω).1) inferInstance =
        MeasurableSpace.comap (fun ω => (DecideE_C ω).1) inferInstance := by
      change MeasurableSpace.comap (eX.symm ∘ (fun ω => (DecideE_C ω).1)) _ = _
      rw [← MeasurableSpace.comap_comp, eX.symm.measurableEmbedding.comap_eq]
    rw [he]
    have hfun : (fun ω => DecideE_m (DecideE_C ω)) = DecideE_Y :=
      funext fun ω => DecideE_m_graph ω.1
    have hh := DecideE_marginal_conditional
    rw [hfun] at hh
    exact hh

lemma DecideE_upMaximum (c : X' × U') :
    maximumDeviation (DecideE_upMean eX eU) c = maximumDeviation DecideE_m (eX c.1, eU c.2) := by
  unfold maximumDeviation DecideE_upMean
  change sSup (Set.range ((fun u => |DecideE_m (eX c.1, eU c.2) - DecideE_m (eX c.1, u)|) ∘ eU)) = _
  rw [eU.surjective.range_comp]

lemma DecideE_upAttained (c : X' × U') :
    ∃ v, ∀ u, |DecideE_upMean eX eU c - DecideE_upMean eX eU (c.1, u)| ≤
      |DecideE_upMean eX eU c - DecideE_upMean eX eU (c.1, v)| := by
  obtain ⟨v, hv⟩ := DecideE_maximum_attained (eX c.1, eU c.2)
  refine ⟨eU.symm v, fun u => ?_⟩
  simpa only [DecideE_upMean, MeasurableEquiv.apply_symm_apply] using hv (eU u)

lemma DecideE_upMaximum_up (c : ℝ × DecideE_U) :
    maximumDeviation (DecideE_upMean eX eU) (DecideE_upC eX eU c) = maximumDeviation DecideE_m c := by
  rw [DecideE_upMaximum]
  change maximumDeviation DecideE_m ((eX.prodCongr eU) ((eX.prodCongr eU).symm c)) = _
  rw [MeasurableEquiv.apply_symm_apply]

lemma DecideE_upMaximum_integrable : Integrable (maximumDeviation (DecideE_upMean eX eU))
    (DecideE_upPX eX eU) := by
  apply (integrable_map_equiv (DecideE_upC eX eU) _).mpr
  simpa only [Function.comp_def, DecideE_upMaximum_up] using DecideE_maximum_integrable

lemma DecideE_upMaximum_integral :
    (∫ c, maximumDeviation (DecideE_upMean eX eU) c ∂DecideE_upPX eX eU) = 1 / 2 := by
  rw [DecideE_upPX, (DecideE_upC eX eU).measurableEmbedding.integral_map]
  simpa only [DecideE_upMaximum_up] using DecideE_maximum_integral

lemma DecideE_upMarginal_integral :
    marginalHeterogeneity (DecideE_upExperiment eΩ eX eU) (fun _ => (1 / 2 : ℝ)) = 3 / 4 := by
  change (∫ c, |(1 / 2 : ℝ) - DecideE_upMean eX eU c| ∂DecideE_upPX eX eU) = _
  rw [DecideE_upPX, (DecideE_upC eX eU).measurableEmbedding.integral_map]
  simpa only [DecideE_upMean_up] using DecideE_marginal_integral

end UniverseTransport

/-- The printed unrestricted marginal/maximal inequality fails on trace-Borel private types. -/
theorem T17_maximum_dominates_marginal_printed_false :
  ¬ (∀ {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (hS : Standing E) (b0 : X → ℝ)
    (hM : MarginalBaseline E b0)
    (hmax : ∀ c : X × U, ∃ v, ∀ u, |E.μ0 c-E.μ0 (c.1,u)| ≤
      |E.μ0 c-E.μ0 (c.1,v)|)
    (hint : Integrable (maximumDeviation E.μ0) E.PX),
    marginalHeterogeneity E b0 ≤ (∫ c, maximumDeviation E.μ0 c ∂E.PX)) := by
  intro h
  let eΩ : ULift DecideE_Omega ≃ᵐ DecideE_Omega := MeasurableEquiv.ulift
  let eX : ULift ℝ ≃ᵐ ℝ := MeasurableEquiv.ulift
  let eU : ULift DecideE_U ≃ᵐ DecideE_U := MeasurableEquiv.ulift
  have hbad := h (DecideE_upExperiment eΩ eX eU) (DecideE_upStanding eΩ eX eU)
    (fun _ => (1 / 2 : ℝ)) (DecideE_upBaseline eΩ eX eU) (DecideE_upAttained eX eU)
    (DecideE_upMaximum_integrable eX eU)
  rw [DecideE_upMarginal_integral eΩ eX eU] at hbad
  change (3 / 4 : ℝ) ≤ ∫ c, maximumDeviation (DecideE_upMean eX eU) c ∂DecideE_upPX eX eU at hbad
  rw [DecideE_upMaximum_integral eX eU] at hbad
  norm_num at hbad

end
end AronowAudit.P006.Wave1
