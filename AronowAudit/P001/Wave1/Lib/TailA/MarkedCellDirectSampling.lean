import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectOriginal
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectTruncated

/-! Finite iid recipient-sampling identities for the direct count kernels. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectSampling (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Counts depend on the original multiset, without a choice of label ordering. -/
theorem marked_window_count_equiv {n : ℕ} (E : Set MatchUnit)
    (z : Fin n → MatchUnit) (e : Fin n ≃ Fin n) :
    markedWindowCount E (z ∘ e) = markedWindowCount E z := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,e.apply_symm_apply j⟩
    simpa only [Function.comp_apply,e.apply_symm_apply] using (Finset.mem_filter.mp hj).2

/-- A general one-recipient kernel, with its response still observed in the
actual iid sample and all other original sites counted as donors. -/
def markedRecipientCountTest {n : ℕ} (p : ℝ) (K : ℕ → ℝ)
    (z : Fin n → MatchUnit) (i : Fin n) : ℝ :=
  if (z i).2.1 = false then K (markedWindowCount (markedCloserDonors p (z i).1) z) else 0

theorem marked_recipient_count_test_equiv {n : ℕ} (p : ℝ) (K : ℕ → ℝ)
    (z : Fin n → MatchUnit) (e : Fin n ≃ Fin n) (i : Fin n) :
    markedRecipientCountTest p K (z ∘ e) i = markedRecipientCountTest p K z (e i) := by
  simp only [markedRecipientCountTest,Function.comp_apply,marked_window_count_equiv]

theorem marked_recipient_count_test_measurable {n : ℕ} (p : ℝ) (K : ℕ → ℝ) (i : Fin n) :
    Measurable (fun z => markedRecipientCountTest p K z i) := by
  have hc : Measurable (fun z : Fin n → MatchUnit =>
      markedWindowCount (markedCloserDonors p (z i).1) z) := by
    simp only [markedWindowCount,Finset.card_filter]
    apply Finset.measurable_sum
    intro j _
    have hdist1 : Measurable (fun z : Fin n → MatchUnit => |(z j).1-(z i).1|) :=
      continuous_abs.measurable.comp ((measurable_pi_apply j).fst.sub (measurable_pi_apply i).fst)
    have hdist2 : Measurable (fun z : Fin n → MatchUnit => |p-(z i).1|) :=
      continuous_abs.measurable.comp (measurable_const.sub (measurable_pi_apply i).fst)
    exact Measurable.ite
      ((measurableSet_eq_fun (measurable_pi_apply j).snd.fst measurable_const).inter
        (measurableSet_lt hdist1 hdist2)) measurable_const measurable_const
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i).snd.fst measurable_const)
    ((measurable_of_countable K).comp hc) measurable_const

theorem marked_recipient_count_test_integrable {n : ℕ} (p : ℝ) (K : ℕ → ℝ) (i : Fin n)
    {C : ℝ} (hC : 0 ≤ C) (hK : ∀ c, |K c| ≤ C) :
    Integrable (fun z => markedRecipientCountTest p K z i) (MatchProduct n) := by
  apply Integrable.of_bound (marked_recipient_count_test_measurable p K i).aestronglyMeasurable C
  apply ae_of_all
  intro z
  simp only [markedRecipientCountTest,Real.norm_eq_abs]
  split_ifs
  · exact hK _
  · simpa only [abs_zero] using hC

/-- Exchangeability holds for the explicit count kernel, without any claim
about permutation-equivariance of a selector on tied configurations. -/
theorem marked_recipient_count_test_integral_eq {n : ℕ} (p : ℝ) (K : ℕ → ℝ) (i j : Fin n) :
    mean (MatchProduct n) (fun z => markedRecipientCountTest p K z i) =
      mean (MatchProduct n) (fun z => markedRecipientCountTest p K z j) := by
  let e : Fin n ≃ Fin n := Equiv.swap i j
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => matchingUnitLaw) e
  have hh := hp.integral_comp' (fun z => markedRecipientCountTest p K z i)
  have heq (z : Fin n → MatchUnit) :
      markedRecipientCountTest p K ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => MatchUnit) e) z) i =
        markedRecipientCountTest p K z j := by
    have hmap : ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => MatchUnit) e) z) =
        z ∘ e.symm := by
      funext v
      simp only [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast,cast_eq,
        Function.comp_apply]
    rw [hmap,marked_recipient_count_test_equiv]
    simp only [e,Equiv.symm_swap,Equiv.swap_apply_left]
  simpa only [mean,MatchProduct,heq] using hh.symm

/-- The complete one-recipient sum is an exact iid sampling factor. -/
theorem marked_recipient_count_sum_integral (n : ℕ) (p : ℝ) (K : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hK : ∀ c, |K c| ≤ C) :
    mean (MatchProduct (n+1)) (fun z => ∑ i, markedRecipientCountTest p K z i) =
      (n+1 : ℕ)*mean (MatchProduct (n+1)) (fun z => markedRecipientCountTest p K z 0) := by
  rw [mean,integral_finsetSum _ (fun i _ => marked_recipient_count_test_integrable p K i hC hK)]
  change (∑ i, mean (MatchProduct (n+1)) (fun z => markedRecipientCountTest p K z i)) = _
  simp only [marked_recipient_count_test_integral_eq p K _ (0 : Fin (n+1)),
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem marked_window_count_cons (n : ℕ) (E : Set MatchUnit) (u : MatchUnit)
    (z : Fin n → MatchUnit) :
    markedWindowCount E (Fin.cons u z) = (if u ∈ E then 1 else 0)+markedWindowCount E z := by
  simp only [markedWindowCount,Finset.card_filter,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

/-- Fixing the first recipient removes precisely that recipient from the
closer-donor count. -/
theorem marked_recipient_count_test_cons (n : ℕ) (p : ℝ) (K : ℕ → ℝ)
    (u : MatchUnit) (z : Fin n → MatchUnit) :
    markedRecipientCountTest p K (Fin.cons u z) 0 =
      if u.2.1 = false then K (markedWindowCount (markedCloserDonors p u.1) z) else 0 := by
  simp only [markedRecipientCountTest,Fin.cons_zero,marked_window_count_cons]
  by_cases hu : u.2.1 = false
  · have hnot : u ∉ markedCloserDonors p u.1 := by
      intro h
      simp only [markedCloserDonors,Set.mem_setOf_eq,hu,Bool.false_eq_true,false_and] at h
    simp only [if_pos hu,if_neg hnot,zero_add]
  · simp only [if_neg hu]

/-- Exact one-recipient disintegration before any asymptotic calculation.
The inner law is the actual product law of the other original observations. -/
theorem marked_recipient_count_test_disintegration (n : ℕ) (p : ℝ) (K : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hK : ∀ c, |K c| ≤ C) :
    mean (MatchProduct (n+1)) (fun z => markedRecipientCountTest p K z 0) =
      ∫ u, (∫ z, (if u.2.1 = false then
        K (markedWindowCount (markedCloserDonors p u.1) z) else 0) ∂MatchProduct n) ∂matchingUnitLaw := by
  have hm := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => matchingUnitLaw) 0).symm
  have hh := hm.integral_comp' (fun z => markedRecipientCountTest p K z 0)
  have hcomp (y : MatchUnit × (Fin n → MatchUnit)) :
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => MatchUnit) 0).symm y =
        Fin.cons y.1 y.2 := by
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Fin.insertNth_zero,Equiv.coe_fn_mk,cast_eq]
  have hi := (hm.integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).mpr
      (marked_recipient_count_test_integrable p K (0 : Fin (n+1)) hC hK)
  simp only [Function.comp_def,hcomp] at hi hh
  simp only [mean,MatchProduct]
  rw [← hh]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  apply integral_congr_ae
  exact ae_of_all _ (fun z => marked_recipient_count_test_cons n p K u z)

end AronowAudit.P001.TailA
