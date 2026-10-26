import AronowAudit.P001.P001_Foundations
import Mathlib.Data.Fintype.Vector
import Mathlib.Topology.Connected.Clopen

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0012B5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-- The common length of a level-n component, in a form suited to the recursion. -/
private def t31B5_width (n : ℕ) : ℝ := ((1/2 : ℝ)^n + (1/4 : ℝ)^n)/2

private lemma t31B5_width_pos (n : ℕ) : 0 < t31B5_width n := by
  unfold t31B5_width
  positivity

private lemma t31B5_width_succ (n : ℕ) :
    t31B5_width (n+1) = (t31B5_width n - (1/4 : ℝ)^(n+1))/2 := by
  simp only [t31B5_width, pow_succ]
  ring

private lemma t31B5_interval_width (w : List Bool) :
    (fatInterval w).2 - (fatInterval w).1 = t31B5_width w.length := by
  induction w with
  | nil => norm_num [fatInterval, t31B5_width]
  | cons b w ih =>
    rw [List.length_cons, t31B5_width_succ]
    cases b <;> simp only [fatInterval, Bool.false_eq_true, ↓reduceIte] <;>
      linarith

private lemma t31B5_interval_order (w : List Bool) :
    (fatInterval w).1 < (fatInterval w).2 := by
  have := t31B5_interval_width w
  have := t31B5_width_pos w.length
  linarith

private lemma t31B5_child_subset (b : Bool) (w : List Bool) :
    Set.Icc (fatInterval (b::w)).1 (fatInterval (b::w)).2 ⊆
      Set.Icc (fatInterval w).1 (fatInterval w).2 := by
  have ho := t31B5_interval_order w
  have hg : 0 < (1/4 : ℝ)^(w.length+1) := by positivity
  intro x hx
  cases b <;> simp only [fatInterval, Bool.false_eq_true, ↓reduceIte,
    Set.mem_Icc] at hx <;> constructor <;> linarith [hx.1, hx.2]

private lemma t31B5_siblings_disjoint (w : List Bool) :
    Disjoint (Set.Icc (fatInterval (false::w)).1 (fatInterval (false::w)).2)
      (Set.Icc (fatInterval (true::w)).1 (fatInterval (true::w)).2) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hg : 0 < (1/4 : ℝ)^(w.length+1) := by positivity
  simp only [fatInterval, Bool.false_eq_true, ↓reduceIte,
    Set.mem_Icc] at hx hy
  linarith [hx.2, hy.1]

private lemma t31B5_intervals_disjoint (u v : List Bool) (hlen : u.length = v.length)
    (hne : u ≠ v) :
    Disjoint (Set.Icc (fatInterval u).1 (fatInterval u).2)
      (Set.Icc (fatInterval v).1 (fatInterval v).2) := by
  induction u generalizing v with
  | nil =>
    have : v = [] := List.length_eq_zero_iff.mp hlen.symm
    exact (hne this.symm).elim
  | cons b u ih =>
    cases v with
    | nil => simp at hlen
    | cons c v =>
      have hl : u.length = v.length := by simpa using hlen
      by_cases huv : u = v
      · subst v
        cases b <;> cases c
        · exact (hne rfl).elim
        · exact t31B5_siblings_disjoint u
        · exact (t31B5_siblings_disjoint u).symm
        · exact (hne rfl).elim
      · exact (ih v hl huv).mono (t31B5_child_subset b u) (t31B5_child_subset c v)

private lemma t31B5_stage_union (n : ℕ) :
    fatStage n = ⋃ w : List.Vector Bool n,
      Set.Icc (fatInterval w.val).1 (fatInterval w.val).2 := by
  ext x
  simp only [fatStage, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨w, hw, hx⟩
    exact ⟨⟨w, hw⟩, hx⟩
  · rintro ⟨w, hx⟩
    exact ⟨w.val, w.property, hx⟩

private lemma t31B5_stage_closed (n : ℕ) : IsClosed (fatStage n) := by
  rw [t31B5_stage_union]
  exact isClosed_iUnion_of_finite (fun _ => isClosed_Icc)

private lemma t31B5_stage_zero : fatStage 0 = Set.Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨w, hw, hx⟩
    have : w = [] := List.length_eq_zero_iff.mp hw
    simpa [this, fatInterval] using hx
  · intro hx
    exact ⟨[], rfl, by simpa [fatInterval] using hx⟩

private lemma t31B5_stage_succ_subset (n : ℕ) : fatStage (n+1) ⊆ fatStage n := by
  rintro x ⟨w, hw, hx⟩
  cases w with
  | nil => simp at hw
  | cons b w =>
    exact ⟨w, by simpa using hw, t31B5_child_subset b w hx⟩

private lemma t31B5_stage_antitone : Antitone fatStage :=
  antitone_nat_of_succ_le t31B5_stage_succ_subset

private lemma t31B5_vector_card (n : ℕ) : Fintype.card (List.Vector Bool n) = 2^n := by
  rw [Fintype.card_congr (Equiv.vectorEquivFin Bool n)]
  simp

private lemma t31B5_mass_algebra (n : ℕ) :
    (2 : ℝ)^n * t31B5_width n = 1/2 + (1/2 : ℝ)^(n+1) := by
  unfold t31B5_width
  rw [← mul_div_assoc, mul_add, ← mul_pow, ← mul_pow]
  norm_num
  rw [pow_succ]
  ring

private lemma t31B5_stage_volume (n : ℕ) :
    volume (fatStage n) = ENNReal.ofReal (1/2 + (1/2 : ℝ)^(n+1)) := by
  rw [t31B5_stage_union, measure_iUnion]
  · simp only [Real.volume_Icc]
    have hw (w : List.Vector Bool n) :
        ENNReal.ofReal ((fatInterval w.val).2 - (fatInterval w.val).1) =
          ENNReal.ofReal (t31B5_width n) := by
      rw [t31B5_interval_width, w.property]
    simp only [hw, tsum_fintype, Finset.sum_const, Finset.card_univ, t31B5_vector_card]
    rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    push_cast
    exact t31B5_mass_algebra n
  · intro u v huv
    apply t31B5_intervals_disjoint u.val v.val (u.property.trans v.property.symm)
    exact fun h => huv (Subtype.ext h)
  · intro w
    exact measurableSet_Icc

private lemma t31B5_cantor_closed : IsClosed fatCantor :=
  isClosed_iInter t31B5_stage_closed

private lemma t31B5_half_pow_limit :
    Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private lemma t31B5_cantor_volume : volume fatCantor = 1/2 := by
  have hlim : Tendsto (fun n : ℕ => 1/2 + (1/2 : ℝ)^(n+1)) atTop (𝓝 (1/2 : ℝ)) := by
    simpa only [pow_succ, zero_mul, add_zero] using
      (tendsto_const_nhds.add (t31B5_half_pow_limit.mul_const (1/2 : ℝ)))
  have hlim' : Tendsto (volume ∘ fatStage) atTop (𝓝 (1/2 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, t31B5_stage_volume,
      ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.tendsto_ofReal hlim
  have hcontinuity := tendsto_measure_iInter_atTop
    (fun n => (t31B5_stage_closed n).measurableSet.nullMeasurableSet)
    t31B5_stage_antitone
    (show ∃ n, volume (fatStage n) ≠ ∞ from
      ⟨0, by rw [t31B5_stage_zero, Real.volume_Icc]; norm_num⟩)
  exact tendsto_nhds_unique hcontinuity hlim'

/-- A real interval in a stage lies in a single component. Separate one component
from the finite closed union of the others, and use preconnectedness of the interval. -/
private lemma t31B5_interval_in_component (n : ℕ) (a b : ℝ) (hab : a ≤ b)
    (hs : Set.Icc a b ⊆ fatStage n) :
    ∃ w : List.Vector Bool n,
      Set.Icc a b ⊆ Set.Icc (fatInterval w.val).1 (fatInterval w.val).2 := by
  have ha := hs (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)
  rw [t31B5_stage_union] at ha
  obtain ⟨w, haw⟩ := Set.mem_iUnion.mp ha
  let V : Set ℝ := ⋃ v ∈ (Finset.univ.erase w),
    Set.Icc (fatInterval v.val).1 (fatInterval v.val).2
  have hV : IsClosed V := isClosed_biUnion_finset (fun _ _ => isClosed_Icc)
  have hd : Disjoint (Set.Icc (fatInterval w.val).1 (fatInterval w.val).2) V := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hxV
    have hne : w ≠ v := (Finset.mem_erase.mp hv).1.symm
    exact Set.disjoint_left.mp
      (t31B5_intervals_disjoint w.val v.val (w.property.trans v.property.symm)
        (fun h => hne (Subtype.ext h))) hx hxv
  have hcover : Set.Icc a b ⊆ Set.Icc (fatInterval w.val).1 (fatInterval w.val).2 ∪ V := by
    intro x hx
    have hxstage := hs hx
    rw [t31B5_stage_union] at hxstage
    obtain ⟨v, hxv⟩ := Set.mem_iUnion.mp hxstage
    by_cases hvw : v = w
    · exact Or.inl (hvw ▸ hxv)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨v, Finset.mem_erase.mpr ⟨hvw,
        Finset.mem_univ _⟩, hxv⟩)
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_Icc).mp
      isPreconnected_Icc _ _ isClosed_Icc hV hcover hd with h | h
  · exact ⟨w, h⟩
  · exact (Set.disjoint_left.mp hd haw (h ⟨le_rfl, hab⟩)).elim

private lemma t31B5_width_limit : Tendsto t31B5_width atTop (𝓝 0) := by
  have hq : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Tendsto (fun n => ((1/2 : ℝ)^n + (1/4 : ℝ)^n)/2) atTop (𝓝 0)
  simpa only [add_zero, zero_div] using
    (t31B5_half_pow_limit.add hq).div_const 2

private lemma t31B5_cantor_no_interval :
    ∀ a b : ℝ, a < b → ¬ Set.Icc a b ⊆ fatCantor := by
  intro a b hab hsub
  obtain ⟨n, hn⟩ := ((tendsto_order.mp t31B5_width_limit).2 (b-a) (sub_pos.mpr hab)).exists
  have hstage : Set.Icc a b ⊆ fatStage n := by
    intro x hx
    exact Set.mem_iInter.mp (hsub hx) n
  obtain ⟨w, hw⟩ := t31B5_interval_in_component n a b hab.le hstage
  have ha := hw (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)
  have hb := hw (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩)
  have hwidth := t31B5_interval_width w.val
  rw [w.property] at hwidth
  linarith [ha.1, hb.2]

private lemma t31B5_subtype_probability (C : Set ℝ) (hC : MeasurableSet C)
    (hm : volume C = 1/2) :
    IsProbabilityMeasure ((2 : ℝ≥0∞) • volume.comap (fun x : C => x.val)) := by
  constructor
  rw [Measure.smul_apply, comap_subtype_coe_apply hC, Set.image_univ,
    Subtype.range_coe, smul_eq_mul, hm]
  simp only [one_div]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

private lemma t31B5_subtype_pdf (C : Set ℝ) (hC : MeasurableSet C)
    (hm : volume C = 1/2) :
    HasPDF (((2 : ℝ≥0∞) • volume.comap (fun x : C => x.val)).map
      (fun x : C => x.val)) (fun x => if x ∈ C then 2 else 0) := by
  have hf : (fun x : ℝ => if x ∈ C then (2 : ℝ) else 0) =
      C.indicator (fun _ : ℝ => (2 : ℝ)) := by
    funext x
    by_cases hx : x ∈ C <;> simp [hx, Set.indicator]
  have hmeas : Measurable (fun x : ℝ => if x ∈ C then (2 : ℝ) else 0) := by
    rw [hf]
    exact measurable_const.indicator hC
  have hi : IntegrableOn (fun _ : ℝ => (2 : ℝ)) C volume :=
    integrableOn_const (by rw [hm]; norm_num)
  refine ⟨hmeas.aemeasurable, ?_, ?_, ?_⟩
  · intro x
    dsimp only
    split_ifs <;> norm_num
  · rw [hf]
    exact hi.integrable_indicator hC
  · rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable, map_comap_subtype_coe hC]
    have hd : (fun x : ℝ => ENNReal.ofReal (if x ∈ C then (2 : ℝ) else 0)) =
        C.indicator (fun _ => (2 : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ C <;> simp [hx, Set.indicator]
    rw [hd, withDensity_indicator hC, withDensity_const]

/-- The fat Cantor construction, with its literal subtype range and normalized law. -/
theorem fat_cantor_continuous_range_counterexample_proof : IsClosed fatCantor ∧ volume fatCantor=1/2 ∧ IsProbabilityMeasure fatSampleMeasure ∧
   HasPDF (fatSampleMeasure.map (fun x : fatCantor => x.val)) fatPDF ∧
   Set.range (fun x : fatCantor => x.val)=fatCantor ∧
   ∀ a b : ℝ,a < b → ¬ Set.Icc a b ⊆ fatCantor := by
  exact ⟨t31B5_cantor_closed, t31B5_cantor_volume,
    t31B5_subtype_probability fatCantor t31B5_cantor_closed.measurableSet t31B5_cantor_volume,
    t31B5_subtype_pdf fatCantor t31B5_cantor_closed.measurableSet t31B5_cantor_volume,
    Subtype.range_coe, t31B5_cantor_no_interval⟩

end
end AronowAudit.P001.Wave1
