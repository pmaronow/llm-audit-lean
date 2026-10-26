import AronowAudit.P009.P009_FullBiasCompletion
import Mathlib.Order.Interval.Finset.Fin

namespace AronowAudit.P009.Wave1

open scoped BigOperators
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

/-- The two exceptional outcomes have disjoint incoming sets of odd equal size. -/
lemma t9_halfA_card (r : ℕ) (hr : 1 ≤ r) : (halfA r).card = 2*r+1 := by
  let a : Fin (4*r+2) := ⟨2, by omega⟩
  let b : Fin (4*r+2) := ⟨2*r+1, by omega⟩
  have he : halfA r = insert 0 (Finset.Icc a b) := by
    ext i
    simp only [halfA, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_Icc]
    change (i.val = 0 ∨ (2 ≤ i.val ∧ i.val ≤ 2*r+1)) ↔
      (i = 0 ∨ (2 ≤ i.val ∧ i.val ≤ 2*r+1))
    simp only [Fin.ext_iff, Fin.val_zero]
  rw [he, Finset.card_insert_of_notMem]
  · simp only [Fin.card_Icc, a, b]
    omega
  · simp [a, b, Fin.le_iff_val_le_val]

@[simp] lemma t9_zero_mem_halfA (r : ℕ) : (0 : Fin (4*r+2)) ∈ halfA r := by
  simp [halfA]

@[simp] lemma t9_one_not_mem_halfA (r : ℕ) : (1 : Fin (4*r+2)) ∉ halfA r := by
  simp [halfA]

lemma t9_halfB_card (r : ℕ) (hr : 1 ≤ r) :
    (Finset.univ \ halfA r).card = 2*r+1 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, t9_halfA_card r hr]
  omega

def t9_parents (r : ℕ) (i : Fin (4*r+2)) : Finset (Fin (4*r+2)) :=
  if i = 0 then halfA r else if i = 1 then Finset.univ \ halfA r else {i}

lemma t9_self_parent (r : ℕ) (i : Fin (4*r+2)) : i ∈ t9_parents r i := by
  by_cases h0 : i = 0
  · subst i; simp [t9_parents]
  · by_cases h1 : i = 1
    · subst i; simp [t9_parents]
    · simp [t9_parents, h0, h1]

lemma t9_interferes_div_sum {n : ℕ} (E : Experiment n) (i j : Fin n)
    (G : Finset (Fin n)) (c : ℝ) (hc : c ≠ 0) (hj : j ∈ G)
    (hy : ∀ z, E.outcome j z = (∑ l ∈ G, bit (z l))/c) :
    Interferes E i j ↔ i ∈ G := by
  constructor
  · rintro (h | ⟨z, z', hagree, hne⟩)
    · simpa [h] using hj
    · by_contra hi
      apply hne
      rw [hy z, hy z']
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      rw [hagree l (by intro he; subst l; exact hi hl)]
  · intro hi
    refine Or.inr ⟨(fun _ => false), Function.update (fun _ => false) i true, ?_, ?_⟩
    · intro l hl
      simp [Function.update_of_ne hl]
    · rw [hy, hy]
      simp [bit, Function.update, hi, hc, Ne.symm hc]

lemma t9_interferes (r : ℕ) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (i j : Fin (4*r+2)) :
    Interferes E i j ↔ i ∈ t9_parents r j := by
  apply t9_interferes_div_sum E i j (t9_parents r j)
    (if j = 0 ∨ j = 1 then ((2*r+1 : ℕ) : ℝ) else 1)
  · split_ifs <;> positivity
  · exact t9_self_parent r j
  · intro z
    rw [hy]
    by_cases h0 : j = 0
    · subst j; simp [halfOutcome, t9_parents]
    · by_cases h1 : j = 1
      · subst j; simp [halfOutcome, t9_parents]
      · have h0v : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using h0
        have h1v : j.val ≠ 1 := by simpa only [Fin.ext_iff, Fin.val_one] using h1
        simp [halfOutcome, t9_parents, h0, h1, h0v, h1v]

lemma t9_dependent_zero (r : ℕ) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (j : Fin (4*r+2)) :
    Dependent E 0 j ↔ j ∈ halfA r := by
  simp only [Dependent, t9_interferes r E hy]
  by_cases h0 : j = 0
  · subst j
    simp [t9_parents]
    exact ⟨0, by simp⟩
  · by_cases h1 : j = 1
    · subst j; simp [t9_parents]
    · simp [t9_parents, h0, h1]

lemma t9_dependent_one (r : ℕ) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (j : Fin (4*r+2)) :
    Dependent E 1 j ↔ j ∉ halfA r := by
  simp only [Dependent, t9_interferes r E hy]
  by_cases h0 : j = 0
  · subst j; simp [t9_parents]
  · by_cases h1 : j = 1
    · subst j
      simp [t9_parents]
      exact ⟨1, by simp⟩
    · simp [t9_parents, h0, h1]

lemma t9_dependent_ordinary (r : ℕ) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (i j : Fin (4*r+2))
    (h0 : i ≠ 0) (h1 : i ≠ 1) :
    Dependent E i j ↔ i ∈ t9_parents r j := by
  simp [Dependent, t9_interferes r E hy, t9_parents, h0, h1]

lemma t9_degree_zero (r : ℕ) (hr : 1 ≤ r) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) : degree E 0 = (2*r+1 : ℕ) := by
  simp only [degree, d, t9_dependent_zero r E hy]
  rw [Finset.sum_boole]
  simp [t9_halfA_card r hr]

lemma t9_degree_one (r : ℕ) (hr : 1 ≤ r) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) : degree E 1 = (2*r+1 : ℕ) := by
  simp only [degree, d, t9_dependent_one r E hy]
  rw [Finset.sum_boole]
  have he : Finset.univ.filter (fun j : Fin (4*r+2) => j ∉ halfA r) =
      Finset.univ \ halfA r := by ext j; simp
  rw [he, t9_halfB_card r hr]

lemma t9_degree_ordinary (r : ℕ) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (i : Fin (4*r+2))
    (h0 : i ≠ 0) (h1 : i ≠ 1) : degree E i = 2 := by
  have hd (j : Fin (4*r+2)) : d E i j =
      (if j = i then (1:ℝ) else 0) +
      (if j = 0 then (if i ∈ halfA r then 1 else 0) else 0) +
      (if j = 1 then (if i ∉ halfA r then 1 else 0) else 0) := by
    simp only [d, t9_dependent_ordinary r E hy i j h0 h1]
    by_cases hj0 : j = 0
    · subst j; simp [t9_parents, Ne.symm h0]
    · by_cases hj1 : j = 1
      · subst j; simp [t9_parents, Ne.symm h1]
      · simp [t9_parents, hj0, hj1, eq_comm]
  simp only [degree, hd, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hi : i ∈ halfA r <;> norm_num [hi]

lemma t9_outgoing (r : ℕ) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (i : Fin (4*r+2)) :
    outgoing E i = 2 - (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0) := by
  have hI (j : Fin (4*r+2)) : I E i j =
      (if j = 0 then (if i ∈ halfA r then (1:ℝ) else 0) else 0) +
      (if j = 1 then (if i ∉ halfA r then 1 else 0) else 0) +
      (if j = i then (if i ≠ 0 ∧ i ≠ 1 then 1 else 0) else 0) := by
    simp only [I, t9_interferes r E hy]
    by_cases hj0 : j = 0
    · subst j
      by_cases hi : i = 0 <;> simp [t9_parents, hi, eq_comm]
    · by_cases hj1 : j = 1
      · subst j
        by_cases hi : i = 1 <;> simp [t9_parents, hi, eq_comm]
      · simp [t9_parents, hj0, hj1]
        by_cases hi : i = j
        · subst i; simp [hj0, hj1]
        · simp [hi, Ne.symm hi]
  simp only [outgoing, hI, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    by_cases hA : i ∈ halfA r <;> simp_all <;> norm_num

lemma t9_graph_statistics (r : ℕ) (hr : 1 ≤ r) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) :
    d E 0 1 = 0 ∧ dAvg E = 3 - 4/(4*r+2:ℕ) ∧ dAvg E < 3 ∧
      C1 E = 2 - 2/(4*r+2:ℕ) ∧ Cinf E = 2 := by
  have hn : (0:ℝ) < (4*r+2:ℕ) := by positivity
  have hs : (∑ i, degree E i) = 3*((4*r+2:ℕ):ℝ)-4 := by
    have hd (i : Fin (4*r+2)) : degree E i = 2 +
        (if i = 0 then ((2*r+1:ℕ):ℝ)-2 else 0) +
        (if i = 1 then ((2*r+1:ℕ):ℝ)-2 else 0) := by
      by_cases h0 : i = 0
      · subst i; rw [t9_degree_zero r hr E hy]; norm_num
      · by_cases h1 : i = 1
        · subst i; rw [t9_degree_one r hr E hy]; norm_num
        · rw [t9_degree_ordinary r E hy i h0 h1]
          simp [h0, h1]
    simp only [hd, Finset.sum_add_distrib]
    simp
    push_cast
    ring
  have havg : dAvg E = 3 - 4/(4*r+2:ℕ) := by
    unfold dAvg
    rw [hs]
    field_simp
  have hout : (∑ i, outgoing E i) = 2*((4*r+2:ℕ):ℝ)-2 := by
    simp only [t9_outgoing r E hy, Finset.sum_sub_distrib]
    simp
    ring
  have hC1 : C1 E = 2 - 2/(4*r+2:ℕ) := by
    unfold C1
    rw [hout]
    field_simp
  have hmax : Cinf E = 2 := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨i, rfl⟩
      rw [t9_outgoing r E hy i]
      split_ifs <;> norm_num
    · let i : Fin (4*r+2) := ⟨2, by omega⟩
      have hi : outgoing E i = 2 := by
        rw [t9_outgoing r E hy i]
        norm_num [i, Fin.ext_iff]
      rw [← hi]
      exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
  refine ⟨?_, havg, ?_, hC1, hmax⟩
  · simp [d, t9_dependent_zero r E hy]
  · rw [havg]
    exact sub_lt_self _ (div_pos (by norm_num) hn)

lemma t9_outcome_bounds (r : ℕ) (hr : 1 ≤ r) (i : Fin (4*r+2))
    (z : Assignment (4*r+2)) : 0 ≤ halfOutcome r i z ∧ halfOutcome r i z ≤ 1 := by
  have hh : (0:ℝ) < (2*r+1:ℕ) := by positivity
  have hA := CompleteConditional.mask_count_bounds (halfA r) z
  have hB := CompleteConditional.mask_count_bounds (Finset.univ \ halfA r) z
  rw [t9_halfA_card r hr] at hA
  rw [t9_halfB_card r hr] at hB
  unfold halfOutcome
  split_ifs
  · exact ⟨div_nonneg hA.1 hh.le, (div_le_one hh).mpr hA.2⟩
  · exact ⟨div_nonneg hB.1 hh.le, (div_le_one hh).mpr hB.2⟩
  · exact CompleteConditional.bit_bounds _

lemma t9_regular (r : ℕ) (hr : 1 ≤ r) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (hCR : Complete E (2*r+1)) :
    Regular E 2 4 1 := by
  have hm (i : Fin (4*r+2)) : marginal E i true = 1/2 := by
    rw [CompleteConditional.complete_marginal_true E (2*r+1) hCR i]
    push_cast
    field_simp
    ring
  have hb (i : Fin (4*r+2)) (z : Assignment (4*r+2)) : |E.outcome i z| ≤ 1 := by
    rw [hy, abs_of_nonneg (t9_outcome_bounds r hr i z).1]
    exact (t9_outcome_bounds r hr i z).2
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro i; rw [hm]; norm_num
  · intro i
    have hp (x : ℝ) : Real.rpow x 4 = x^4 := by simpa using Real.rpow_natCast x 4
    simp only [hp]
    calc
      _ ≤ mean E.design (fun _ => (1:ℝ)) := by
        apply CompleteConditional.mean_mono
        intro z
        calc
          _ ≤ (1:ℝ)^4 := by gcongr; exact hb i z
          _ = 1 := by norm_num
      _ ≤ _ := by rw [mean_const]; norm_num
  · intro i b
    simp only [Real.rpow_eq_pow, Real.rpow_one]
    calc
      _ ≤ mean E.design (fun _ => (1:ℝ)) := by
        apply CompleteConditional.mean_mono
        intro z
        exact hb i (Function.update z i b)
      _ ≤ _ := by rw [mean_const]; norm_num

/-- The standard sharp universal upper bound for the finite event supremum. -/
lemma t9_alpha_le_quarter {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) : alpha P X Y ≤ 1/4 := by
  have hv (F : Ω → Prop) : var P (fun w => if F w then 1 else 0) ≤ 1/4 := by
    rw [variance_second_moment]
    have hs : (fun w => (if F w then (1:ℝ) else 0)^2) =
        (fun w => if F w then (1:ℝ) else 0) := by
      funext w; split_ifs <;> norm_num
    rw [hs]
    nlinarith [sq_nonneg (mean P (fun w => if F w then (1:ℝ) else 0)-1/2)]
  apply MixingBasics.alpha_le_of_event_bound
  intro S T
  let f : Ω → ℝ := fun w => if X w ∈ S then 1 else 0
  let g : Ω → ℝ := fun w => if Y w ∈ T then 1 else 0
  have he : cov P f g = prob P (fun w => X w ∈ S ∧ Y w ∈ T) -
      prob P (fun w => X w ∈ S) * prob P (fun w => Y w ∈ T) := by
    rw [BernoulliCompletion.covariance_product_formula]
    congr 1
    apply congrArg (mean P)
    funext w
    by_cases h : X w ∈ S <;> by_cases h' : Y w ∈ T <;> simp [f, g, h, h']
  rw [← he]
  calc
    _ ≤ Real.sqrt (var P f * var P g) := covariance_cauchy_schwarz P f g
    _ ≤ Real.sqrt ((1/4:ℝ)*(1/4)) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (hv _) (hv _) (variance_nonnegative P g) (by norm_num)
    _ = 1/4 := by norm_num

/-- Integer treated counts are useful for avoiding ties in the odd half. -/
def t9_count {n : ℕ} (H : Finset (Fin n)) (z : Assignment n) : ℕ :=
  ∑ j ∈ H, if z j then 1 else 0

lemma t9_count_flip {n : ℕ} (H : Finset (Fin n)) (z : Assignment n) :
    t9_count H (fun j => !(z j)) + t9_count H z = H.card := by
  unfold t9_count
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _j ∈ H, (1:ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      cases hj : z j <;> simp [hj]
    _ = _ := by simp

lemma t9_count_partition {n : ℕ} (H : Finset (Fin n)) (z : Assignment n) :
    t9_count H z + t9_count (Finset.univ \ H) z = t9_count Finset.univ z := by
  unfold t9_count
  exact Finset.sum_add_sum_compl H _

lemma t9_prob_support_congr {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A B : Ω → Prop) (h : ∀ w, 0 < P.mass w → (A w ↔ B w)) :
    prob P A = prob P B := by
  apply CompleteConditional.mean_support_congr
  intro w hw
  exact if_congr (h w hw) rfl rfl

lemma t9_count_support (r : ℕ) (E : Experiment (4*r+2))
    (hCR : Complete E (2*r+1)) (z : Assignment (4*r+2))
    (hz : 0 < E.design.mass z) : t9_count Finset.univ z = 2*r+1 := by
  by_contra hn
  have hmass : E.design.mass z = 0 := by
    rw [hCR.2.2 z]
    exact if_neg hn
  linarith

lemma t9_mass_flip (r : ℕ) (E : Experiment (4*r+2))
    (hCR : Complete E (2*r+1)) (z : Assignment (4*r+2)) :
    E.design.mass (fun j => !(z j)) = E.design.mass z := by
  have hs := t9_count_flip Finset.univ z
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  have he : t9_count Finset.univ (fun j => !(z j)) = 2*r+1 ↔
      t9_count Finset.univ z = 2*r+1 := by omega
  rw [hCR.2.2, hCR.2.2]
  exact if_congr he rfl rfl

lemma t9_prob_flip (r : ℕ) (E : Experiment (4*r+2))
    (hCR : Complete E (2*r+1)) (A : Assignment (4*r+2) → Prop) :
    prob E.design (fun z => A (fun j => !(z j))) = prob E.design A := by
  let e : Assignment (4*r+2) ≃ Assignment (4*r+2) :=
    { toFun := fun z j => !(z j)
      invFun := fun z j => !(z j)
      left_inv := by intro z; funext j; simp
      right_inv := by intro z; funext j; simp }
  unfold prob mean
  apply Fintype.sum_equiv e
  intro z
  change E.design.mass z * (if A (e z) then 1 else 0) =
    E.design.mass (e z) * (if A (e z) then 1 else 0)
  have hm : E.design.mass (e z) = E.design.mass z := t9_mass_flip r E hCR z
  rw [hm]

lemma t9_majority_half (r : ℕ) (hr : 1 ≤ r) (E : Experiment (4*r+2))
    (hCR : Complete E (2*r+1)) :
    prob E.design (fun z => r+1 ≤ t9_count (halfA r) z) = 1/2 ∧
    prob E.design (fun z => t9_count (Finset.univ \ halfA r) z ≤ r) = 1/2 ∧
    prob E.design (fun z => r+1 ≤ t9_count (halfA r) z ∧
      t9_count (Finset.univ \ halfA r) z ≤ r) = 1/2 := by
  let G := fun z : Assignment (4*r+2) => r+1 ≤ t9_count (halfA r) z
  let H := fun z : Assignment (4*r+2) => t9_count (Finset.univ \ halfA r) z ≤ r
  have hflip (z : Assignment (4*r+2)) : G (fun j => !(z j)) ↔ ¬ G z := by
    have hc := t9_count_flip (halfA r) z
    rw [t9_halfA_card r hr] at hc
    dsimp [G]
    omega
  have hsymm : prob E.design (fun z => ¬ G z) = prob E.design G := by
    rw [← t9_prob_flip r E hCR G]
    apply congrArg (prob E.design)
    funext z
    exact propext (hflip z).symm
  have hG : prob E.design G = 1/2 := by
    rw [probability_complement] at hsymm
    linarith
  have heq (z : Assignment (4*r+2)) (hz : 0 < E.design.mass z) : H z ↔ G z := by
    have hs := t9_count_partition (halfA r) z
    rw [t9_count_support r E hCR z hz] at hs
    dsimp [G, H]
    omega
  refine ⟨hG, ?_, ?_⟩
  · exact (t9_prob_support_congr E.design H G heq).trans hG
  · apply Eq.trans (t9_prob_support_congr E.design (fun z => G z ∧ H z) G ?_) hG
    intro z hz
    rw [heq z hz, and_self]

lemma t9_count_mask_zero (r : ℕ) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (z : Assignment (4*r+2)) :
    t9_count (halfA r) (masked E 0 z) = t9_count (halfA r) z := by
  apply Finset.sum_congr rfl
  intro j hj
  have hI : Interferes E j 0 := (t9_interferes r E hy j 0).mpr (by
    simpa [t9_parents] using hj)
  simp only [masked, if_pos hI]

lemma t9_count_mask_one (r : ℕ) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (z : Assignment (4*r+2)) :
    t9_count (Finset.univ \ halfA r) (masked E 1 z) =
      t9_count (Finset.univ \ halfA r) z := by
  apply Finset.sum_congr rfl
  intro j hj
  have hI : Interferes E j 1 := (t9_interferes r E hy j 1).mpr (by
    simpa [t9_parents] using hj)
  simp only [masked, if_pos hI]

lemma t9_mask_alpha (r : ℕ) (hr : 1 ≤ r) (E : Experiment (4*r+2))
    (hy : E.outcome = halfOutcome r) (hCR : Complete E (2*r+1)) :
    alpha E.design (masked E 0) (masked E 1) = 1/4 := by
  apply le_antisymm (t9_alpha_le_quarter _ _ _)
  have h := MixingBasics.event_abs_le_alpha E.design (masked E 0) (masked E 1)
    {w | r+1 ≤ t9_count (halfA r) w}
    {w | t9_count (Finset.univ \ halfA r) w ≤ r}
  simp only [Set.mem_setOf_eq, t9_count_mask_zero r E hy, t9_count_mask_one r E hy] at h
  obtain ⟨hG, hH, hGH⟩ := t9_majority_half r hr E hCR
  rw [hG, hH, hGH] at h
  norm_num at h
  exact h

/-- The exceptional masks retain exact quarter mixing although their incoming
interference sets are disjoint and the average dependence degree stays below three. -/
theorem exceptional_pair_counterexample_proof (r : ℕ) (hr : 1 ≤ r) :
    ∃ E : Experiment (4*r+2), Complete E (2*r+1) ∧ E.outcome = halfOutcome r ∧
      Regular E 2 4 1 ∧ d E 0 1 = 0 ∧
      dAvg E = 3 - 4/(4*r+2:ℕ) ∧ dAvg E < 3 ∧
      C1 E = 2 - 2/(4*r+2:ℕ) ∧ Cinf E = 2 ∧
      alpha E.design (masked E 0) (masked E 1) = 1/4 := by
  let E := FullBiasCompletion.completeExperiment (4*r+2) (2*r+1) (by omega) (halfOutcome r)
  have hCR : Complete E (2*r+1) :=
    FullBiasCompletion.complete_certificate _ _ (by omega) (by omega) _
  have hy : E.outcome = halfOutcome r := rfl
  obtain ⟨hd, havg, hlt, hC1, hinf⟩ := t9_graph_statistics r hr E hy
  exact ⟨E, hCR, hy, t9_regular r hr E hy hCR, hd, havg, hlt, hC1, hinf,
    t9_mask_alpha r hr E hy hCR⟩

end
end AronowAudit.P009.Wave1
