import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectSampling
import Mathlib.Logic.Equiv.Fintype

/-! Exact ordered distinct-recipient sampling, including all three donor counts
needed by the original, one-replica and shared-site two-replica squares. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectPairSampling (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- A measurable moving donor count, with an arbitrary measurable query. -/
theorem marked_query_count_measurable {E : Type*} [MeasurableSpace E] (n : ℕ) (p : ℝ)
    (q : E → ℝ) (z : E → Fin n → MatchUnit) (hq : Measurable q) (hz : Measurable z) :
    Measurable (fun y => markedWindowCount (markedCloserDonors p (q y)) (z y)) := by
  simp only [markedWindowCount,Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  have hi := (measurable_pi_apply i).comp hz
  exact Measurable.ite
    ((measurableSet_eq_fun hi.snd.fst measurable_const).inter
      (measurableSet_lt (continuous_abs.measurable.comp (hi.fst.sub hq))
        (continuous_abs.measurable.comp (measurable_const.sub hq))))
    measurable_const measurable_const

/-- The union count is measurable jointly in both recipient positions. -/
theorem marked_query_union_count_measurable {E : Type*} [MeasurableSpace E] (n : ℕ) (p : ℝ)
    (q r : E → ℝ) (z : E → Fin n → MatchUnit)
    (hq : Measurable q) (hr : Measurable r) (hz : Measurable z) :
    Measurable (fun y => markedWindowCount
      (markedCloserDonors p (q y) ∪ markedCloserDonors p (r y)) (z y)) := by
  simp only [markedWindowCount,Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  have hi := (measurable_pi_apply i).comp hz
  have hm (s : E → ℝ) (hs : Measurable s) : MeasurableSet
      {y | z y i ∈ markedCloserDonors p (s y)} :=
    (measurableSet_eq_fun hi.snd.fst measurable_const).inter
      (measurableSet_lt (continuous_abs.measurable.comp (hi.fst.sub hs))
        (continuous_abs.measurable.comp (measurable_const.sub hs)))
  exact Measurable.ite ((hm q hq).union (hm r hr)) measurable_const measurable_const

/-- Two recipient flags, and the individual and union donor counts. -/
def markedRecipientPairCountTest {n : ℕ} (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (z : Fin n → MatchUnit) (i j : Fin n) : ℝ :=
  if (z i).2.1 = false ∧ (z j).2.1 = false then
    K (markedWindowCount (markedCloserDonors p (z i).1) z)
      (markedWindowCount (markedCloserDonors p (z j).1) z)
      (markedWindowCount (markedCloserDonors p (z i).1 ∪ markedCloserDonors p (z j).1) z)
    else 0

theorem marked_recipient_pair_test_equiv {n : ℕ} (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (z : Fin n → MatchUnit) (e : Fin n ≃ Fin n) (i j : Fin n) :
    markedRecipientPairCountTest p K (z ∘ e) i j =
      markedRecipientPairCountTest p K z (e i) (e j) := by
  simp only [markedRecipientPairCountTest,Function.comp_apply,marked_window_count_equiv]

theorem marked_recipient_pair_test_measurable {n : ℕ} (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (i j : Fin n) : Measurable (fun z => markedRecipientPairCountTest p K z i j) := by
  have hK : Measurable (fun c : ℕ × ℕ × ℕ => K c.1 c.2.1 c.2.2) := measurable_of_countable _
  have hi := marked_query_count_measurable n p (fun z : Fin n → MatchUnit => (z i).1)
    id (measurable_pi_apply i).fst measurable_id
  have hj := marked_query_count_measurable n p (fun z : Fin n → MatchUnit => (z j).1)
    id (measurable_pi_apply j).fst measurable_id
  have hu := marked_query_union_count_measurable n p
    (fun z : Fin n → MatchUnit => (z i).1) (fun z => (z j).1) id
    (measurable_pi_apply i).fst (measurable_pi_apply j).fst measurable_id
  exact Measurable.ite
    ((measurableSet_eq_fun (measurable_pi_apply i).snd.fst measurable_const).inter
      (measurableSet_eq_fun (measurable_pi_apply j).snd.fst measurable_const))
    (hK.comp (hi.prodMk (hj.prodMk hu))) measurable_const

theorem marked_recipient_pair_test_integrable {n : ℕ} (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (i j : Fin n) {C : ℝ} (hC : 0 ≤ C) (hK : ∀ a b c, |K a b c| ≤ C) :
    Integrable (fun z => markedRecipientPairCountTest p K z i j) (MatchProduct n) := by
  apply Integrable.of_bound (marked_recipient_pair_test_measurable p K i j).aestronglyMeasurable C
  apply ae_of_all
  intro z
  simp only [markedRecipientPairCountTest,Real.norm_eq_abs]
  split_ifs
  · exact hK _ _ _
  · simpa only [abs_zero] using hC

/-- All ordered distinct pairs have exactly the same expectation. -/
theorem marked_recipient_pair_test_integral_eq {n : ℕ} (p : ℝ)
    (K : ℕ → ℕ → ℕ → ℝ) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) :
    mean (MatchProduct n) (fun z => markedRecipientPairCountTest p K z i j) =
      mean (MatchProduct n) (fun z => markedRecipientPairCountTest p K z k l) := by
  have hf (a b : Fin n) (hab : a ≠ b) : Function.Injective (fun t : Bool => if t then a else b) := by
    intro x y h
    cases x <;> cases y <;> simp_all
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair
    (fun t : Bool => if t then i else j) (fun t : Bool => if t then k else l)
    (hf i j hij) (hf k l hkl)
  have hei : e i = k := by simpa using he true
  have hej : e j = l := by simpa using he false
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => matchingUnitLaw) e.symm
  have hh := hp.integral_comp' (fun z => markedRecipientPairCountTest p K z i j)
  have heq (z : Fin n → MatchUnit) :
      markedRecipientPairCountTest p K
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => MatchUnit) e.symm) z) i j =
          markedRecipientPairCountTest p K z k l := by
    have hmap : ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => MatchUnit) e.symm) z) =
        z ∘ e := by
      funext v
      simp only [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast,
        Equiv.symm_symm,cast_eq,Function.comp_apply]
    rw [hmap,marked_recipient_pair_test_equiv,hei,hej]
  simpa only [mean,MatchProduct,heq] using hh.symm

/-- Exact factor for the double sum: two recipients remove two iid sites. -/
theorem marked_recipient_pair_sum_integral (n : ℕ) (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hK : ∀ a b c, |K a b c| ≤ C) :
    mean (MatchProduct (n+2)) (fun z => ∑ i, ∑ j,
      if i = j then 0 else markedRecipientPairCountTest p K z i j) =
      ((n+2 : ℕ) : ℝ)*(n+1 : ℕ)*mean (MatchProduct (n+2))
        (fun z => markedRecipientPairCountTest p K z 0 1) := by
  have hi (i j : Fin (n+2)) : Integrable (fun z =>
      if i = j then 0 else markedRecipientPairCountTest p K z i j) (MatchProduct (n+2)) := by
    by_cases h : i = j
    · simp only [if_pos h]; exact integrable_const _
    · simp only [if_neg h]; exact marked_recipient_pair_test_integrable p K i j hC hK
  rw [mean,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  have he (i j : Fin (n+2)) :
      (∫ z, (if i = j then 0 else markedRecipientPairCountTest p K z i j) ∂MatchProduct (n+2)) =
        if i = j then 0 else mean (MatchProduct (n+2))
          (fun z => markedRecipientPairCountTest p K z 0 1) := by
    by_cases h : i = j
    · simp [h]
    · simp only [if_neg h]
      exact marked_recipient_pair_test_integral_eq p K i j 0 1 h (by intro hh; have hv := congrArg Fin.val hh; simp at hv)
  simp_rw [he]
  have hs (i : Fin (n+2)) (a : ℝ) : (∑ j : Fin (n+2), if i = j then 0 else a) =
      (n+1 : ℕ)*a := by
    simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const,
      Finset.filter_ne,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,Fintype.card_fin,show n+2-1 = n+1 by omega,nsmul_eq_mul]
  simp_rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Two nonresponding observations do not enter any closer-donor count. -/
theorem marked_recipient_pair_test_cons (n : ℕ) (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (u v : MatchUnit) (z : Fin n → MatchUnit) :
    markedRecipientPairCountTest p K (Fin.cons u (Fin.cons v z)) 0 1 =
      if u.2.1 = false ∧ v.2.1 = false then
        K (markedWindowCount (markedCloserDonors p u.1) z)
          (markedWindowCount (markedCloserDonors p v.1) z)
          (markedWindowCount (markedCloserDonors p u.1 ∪ markedCloserDonors p v.1) z)
      else 0 := by
  simp only [markedRecipientPairCountTest,Fin.cons_zero,Fin.cons_one]
  by_cases h : u.2.1 = false ∧ v.2.1 = false
  · have hu (E : Set MatchUnit) (hE : ∀ w ∈ E, w.2.1 = true) : u ∉ E ∧ v ∉ E := by
      constructor
      · intro hu; have := hE u hu; simp_all
      · intro hv; have := hE v hv; simp_all
    have h1 := hu (markedCloserDonors p u.1) (fun _ hw => hw.1)
    have h2 := hu (markedCloserDonors p v.1) (fun _ hw => hw.1)
    have h3 := hu (markedCloserDonors p u.1 ∪ markedCloserDonors p v.1)
      (by intro w hw; rcases hw with hw | hw <;> exact hw.1)
    simp only [if_pos h,marked_window_count_cons,if_neg h1.1,if_neg h1.2,
      if_neg h2.1,if_neg h2.2,if_neg h3.1,if_neg h3.2,zero_add]
  · simp only [if_neg h]

/-- Ordered distinct-recipient disintegration into two independent actual
observations and the actual remaining iid sample. -/
theorem marked_recipient_pair_test_disintegration (n : ℕ) (p : ℝ)
    (K : ℕ → ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hK : ∀ a b c, |K a b c| ≤ C) :
    mean (MatchProduct (n+2)) (fun z => markedRecipientPairCountTest p K z 0 1) =
      ∫ u, ∫ v, ∫ z, (if u.2.1 = false ∧ v.2.1 = false then
        K (markedWindowCount (markedCloserDonors p u.1) z)
          (markedWindowCount (markedCloserDonors p v.1) z)
          (markedWindowCount (markedCloserDonors p u.1 ∪ markedCloserDonors p v.1) z)
        else 0) ∂MatchProduct n ∂matchingUnitLaw ∂matchingUnitLaw := by
  let F := fun z : Fin (n+2) → MatchUnit => markedRecipientPairCountTest p K z 0 1
  have hF : Integrable F (MatchProduct (n+2)) :=
    marked_recipient_pair_test_integrable p K 0 1 hC hK
  have hsplit (m : ℕ) (f : (Fin (m+1) → MatchUnit) → ℝ)
      (hf : Integrable f (MatchProduct (m+1))) :
      (∫ z, f z ∂MatchProduct (m+1)) =
        ∫ u, ∫ z, f (Fin.cons u z) ∂MatchProduct m ∂matchingUnitLaw := by
    have hm := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (m+1) => matchingUnitLaw) 0).symm
    have hh := hm.integral_comp' f
    have hc (y : MatchUnit × (Fin m → MatchUnit)) :
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => MatchUnit) 0).symm y =
          Fin.cons y.1 y.2 := by
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
        Fin.insertNth_zero,Equiv.coe_fn_mk,cast_eq]
    have hi := (hm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hf
    simp only [Function.comp_def,hc] at hh hi
    simp only [MatchProduct]
    rw [← hh,integral_prod _ hi]
  rw [mean,hsplit (n+1) F hF]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  have hm : Measurable (fun z : Fin (n+1) → MatchUnit => F (Fin.cons u z)) :=
    (marked_recipient_pair_test_measurable p K 0 1).comp (by
      apply measurable_pi_lambda
      intro i
      exact Fin.cases measurable_const (fun j => measurable_pi_apply j) i)
  have hi : Integrable (fun z : Fin (n+1) → MatchUnit => F (Fin.cons u z)) (MatchProduct (n+1)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable C
    apply ae_of_all
    intro z
    simp only [F,markedRecipientPairCountTest,Real.norm_eq_abs]
    split_ifs
    · exact hK _ _ _
    · simpa only [abs_zero] using hC
  beta_reduce
  rw [hsplit n _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  apply integral_congr_ae
  exact ae_of_all _ (fun z => marked_recipient_pair_test_cons n p K u v z)

end AronowAudit.P001.TailA
