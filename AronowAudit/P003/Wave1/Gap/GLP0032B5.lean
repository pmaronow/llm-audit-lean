import AronowAudit.P003.P003_Audit
import AronowAudit.P003.Wave1.Gap.GP0032B1
import AronowAudit.P037.P037_FiniteDesign
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Powerset

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! Finite four-block counting. All sums below are over whole assignments;
no independence of units within one assignment is asserted. -/

abbrev ab5_Blocks (v : Counts) :=
  Fin v.a ⊕ (Fin v.b ⊕ (Fin v.c ⊕ Fin v.d))
abbrev ab5_Sets (v : Counts) :=
  Finset (Fin v.a) × (Finset (Fin v.b) × (Finset (Fin v.c) × Finset (Fin v.d)))

def ab5_labels (v : Counts) : ab5_Blocks v ≃ Fin v.total :=
  ((Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
    finSumFinEquiv)).trans finSumFinEquiv).trans
      (finCongr (by simp [Counts.total, Nat.add_assoc]))

def ab5_sets (v : Counts) : ab5_Sets v ≃ Finset (Fin v.total) :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _)
    Finset.sumEquiv.toEquiv.symm).trans Finset.sumEquiv.toEquiv.symm)).trans
      (Finset.sumEquiv.toEquiv.symm.trans (ab5_labels v).finsetCongr)

lemma ab5_sets_apply (v : Counts) (s : ab5_Sets v) :
    ab5_sets v s = (s.1.disjSum (s.2.1.disjSum
      (s.2.2.1.disjSum s.2.2.2))).map (ab5_labels v).toEmbedding := rfl

lemma ab5_pairs (v : Counts) :
    (∀ i : Fin v.a, canonicalPair v (ab5_labels v (.inl i)).val = (true,true)) ∧
    (∀ i : Fin v.b, canonicalPair v (ab5_labels v (.inr (.inl i))).val = (true,false)) ∧
    (∀ i : Fin v.c, canonicalPair v (ab5_labels v (.inr (.inr (.inl i)))).val = (false,true)) ∧
    (∀ i : Fin v.d, canonicalPair v (ab5_labels v (.inr (.inr (.inr i)))).val = (false,false)) := by
  repeat' apply And.intro
  all_goals
    intro i
    have hi := i.isLt
    simp only [ab5_labels, Equiv.trans_apply, Equiv.sumCongr_apply,
      Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      finCongr_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd]
    unfold canonicalPair
    split_ifs <;> simp_all <;> omega

lemma ab5_card (v : Counts) (s : ab5_Sets v) :
    (ab5_sets v s).card = s.1.card+s.2.1.card+s.2.2.1.card+s.2.2.2.card := by
  simp [ab5_sets_apply, Finset.card_disjSum, Nat.add_assoc]

lemma ab5_observed (v : Counts) (s : ab5_Sets v) :
    canonicalObserved v (ab5_sets v s) =
      observed v ⟨s.1.card,s.2.1.card,s.2.2.1.card,s.2.2.2.card⟩ := by
  have hs (P : Fin v.total → Prop) :
      (Finset.univ.filter P).card =
        ∑ i : ab5_Blocks v, if P (ab5_labels v i) then (1:ℕ) else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact (Equiv.sum_comp (ab5_labels v) _).symm
  have hnot {n : ℕ} (t : Finset (Fin n)) :
      (∑ i : Fin n, if i ∉ t then (1:ℕ) else 0) = n-t.card := by
    classical
    have he : Finset.univ.filter (fun i : Fin n => i ∉ t) = tᶜ := by ext; simp
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, one_nsmul, he, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]
  ext <;> simp only [canonicalObserved, observed]
  all_goals
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Equiv.sum_comp (ab5_labels v)]
    simp only [Fintype.sum_sum_type, ab5_sets_apply, Finset.mem_map_equiv,
      Equiv.symm_apply_apply, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum,
      (ab5_pairs v).1, (ab5_pairs v).2.1, (ab5_pairs v).2.2.1,
      (ab5_pairs v).2.2.2, Bool.true_eq_false, Bool.false_eq_true,
      and_true, and_false, ite_false, Finset.sum_const_zero, add_zero, zero_add,
      hnot]
    simp
    all_goals have h := Finset.card_le_univ s.2.2.1; have h' := Finset.card_le_univ s.2.2.2
    all_goals simp only [Fintype.card_fin] at h h'; omega

lemma ab5_sum_card {R : Type*} [CommSemiring R] (n : ℕ) (f : ℕ → R) :
    (∑ s : Finset (Fin n), f s.card) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : R)*f k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Finset (Fin n))))
    (t := Finset.range (n+1)) (g := Finset.card)
    (by intro s hs; have := Finset.card_le_univ s; simpa using Nat.lt_succ_of_le this)]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑ s ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card=k), f k := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ = _ := by simp

lemma ab5_sum_assignment {R : Type*} [CommSemiring R] (v : Counts) (m : ℕ) (f : Counts → R) :
    (∑ z : Assignment v.total m, f (canonicalObserved v z.val)) =
      ∑ a ∈ Finset.range (v.a+1), ∑ b ∈ Finset.range (v.b+1),
        ∑ c ∈ Finset.range (v.c+1), ∑ d ∈ Finset.range (v.d+1),
          (v.a.choose a : R)*(v.b.choose b : R)*(v.c.choose c : R)*(v.d.choose d : R)*
            if a+b+c+d=m then f (observed v ⟨a,b,c,d⟩) else 0 := by
  classical
  have ht : (∑ z : Assignment v.total m, f (canonicalObserved v z.val)) =
      ∑ z : Finset (Fin v.total), if z.card=m then f (canonicalObserved v z) else 0 := by
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_subtype (Finset.univ.filter (fun z : Finset (Fin v.total) => z.card=m))
    intro z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ht, ← Equiv.sum_comp (ab5_sets v)]
  simp_rw [ab5_card, ab5_observed]
  simp only [Fintype.sum_prod_type]
  rw [ab5_sum_card v.a (fun a => ∑ b : Finset (Fin v.b),
    ∑ c : Finset (Fin v.c), ∑ d : Finset (Fin v.d),
      if a+b.card+c.card+d.card=m then f (observed v ⟨a,b.card,c.card,d.card⟩) else 0)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [ab5_sum_card v.b (fun b => ∑ c : Finset (Fin v.c),
    ∑ d : Finset (Fin v.d),
      if a+b+c.card+d.card=m then f (observed v ⟨a,b,c.card,d.card⟩) else 0), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [ab5_sum_card v.c (fun c => ∑ d : Finset (Fin v.d),
      if a+b+c+d.card=m then f (observed v ⟨a,b,c,d.card⟩) else 0),
      Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [ab5_sum_card v.d (fun d =>
      if a+b+c+d=m then f (observed v ⟨a,b,c,d⟩) else 0),
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring


lemma ab5_sum_assignment_n {R : Type*} [CommSemiring R] (n : ℕ)
    (v : Counts) (hn : v.total=n) (m : ℕ) (f : Counts → R) :
    (∑ z : Assignment n m, f (canonicalObserved v z.val)) =
      ∑ a ∈ Finset.range (v.a+1), ∑ b ∈ Finset.range (v.b+1),
        ∑ c ∈ Finset.range (v.c+1), ∑ d ∈ Finset.range (v.d+1),
          (v.a.choose a : R)*(v.b.choose b : R)*(v.c.choose c : R)*(v.d.choose d : R)*
            if a+b+c+d=m then f (observed v ⟨a,b,c,d⟩) else 0 := by
  subst n
  exact ab5_sum_assignment v m f

/-! The finite uniform law and its independent product coordinates. The
moment theorem reused below is the proved finite-sum theorem from P037. -/

noncomputable def ab5_uniform (A : Type*) [Fintype A] [Nonempty A] :
    AronowAudit.P037.FiniteDesign A where
  weight := fun _ => (Fintype.card A : ℝ)⁻¹
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma ab5_law_ext {A : Type*} [Fintype A]
    (d e : AronowAudit.P037.FiniteDesign A) (h : d.weight=e.weight) : d=e := by
  cases d; cases e; cases h; rfl

lemma ab5_product_uniform {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] :
    AronowAudit.P037.productDesign (fun _ : I => ab5_uniform A) = ab5_uniform (I → A) := by
  apply ab5_law_ext
  funext w
  simp only [AronowAudit.P037.productDesign, ab5_uniform, Fintype.card_pi,
    Nat.cast_prod, Finset.prod_inv_distrib]

lemma ab5_mean {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    AronowAudit.P037.designMean (ab5_uniform A) f = (∑ a, f a)/Fintype.card A := by
  simp [AronowAudit.P037.designMean, ab5_uniform, div_eq_mul_inv, Finset.sum_mul, mul_comm]

lemma ab5_probability {A : Type*} [Fintype A] [Nonempty A] (E : A → Prop) :
    AronowAudit.P037.designProbability (ab5_uniform A) E = uniformProb E := by
  rw [AronowAudit.P037.designProbability, ab5_mean]
  unfold uniformProb
  congr 1
  simp

lemma ab5_probability_mono {A : Type*} [Fintype A] {E F : A → Prop}
    (h : ∀ a, E a → F a) : uniformProb E ≤ uniformProb F := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hs : Finset.univ.filter E ⊆ Finset.univ.filter F := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact h a ha
  exact_mod_cast Finset.card_le_card hs

lemma ab5_probability_compl {A : Type*} [Fintype A] [Nonempty A] (E : A → Prop) :
    uniformProb (fun a => ¬E a) = 1-uniformProb E := by
  calc
    _ = AronowAudit.P037.designMean (ab5_uniform A)
        (fun a => 1-(if E a then (1:ℝ) else 0)) := by
      rw [← ab5_probability, AronowAudit.P037.designProbability]
      congr 1
      funext a
      by_cases h : E a <;> simp [h]
    _ = _ := by
      rw [AronowAudit.P037.designMean_sub, AronowAudit.P037.designMean_const]
      exact congrArg (1-·) (ab5_probability E)

lemma ab5_probability_pair {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] (i j : I) (hij : i≠j) (E F : A → Prop) :
    uniformProb (fun w : I → A => E (w i) ∧ F (w j)) = uniformProb E*uniformProb F := by
  calc
    _ = AronowAudit.P037.designMean
        (AronowAudit.P037.productDesign (fun _ : I => ab5_uniform A))
        (fun w => (if E (w i) then (1:ℝ) else 0)*(if F (w j) then (1:ℝ) else 0)) := by
      rw [← ab5_probability, ← ab5_product_uniform, AronowAudit.P037.designProbability]
      congr 1
      funext w
      split_ifs <;> simp_all
    _ = _ := by
      rw [AronowAudit.P037.product_design_coordinate_pair
        (fun _ : I => ab5_uniform A) i j hij
        (fun a => if E a then (1:ℝ) else 0) (fun a => if F a then (1:ℝ) else 0)]
      exact congrArg₂ (·*·) (ab5_probability E) (ab5_probability F)

lemma ab5_mean_coordinate {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] (i : I) (f : A → ℝ) :
    AronowAudit.P037.designMean (ab5_uniform (I → A)) (fun w => f (w i)) =
      AronowAudit.P037.designMean (ab5_uniform A) f := by
  rw [← ab5_product_uniform]
  exact AronowAudit.P037.product_design_coordinate_mean (fun _ : I => ab5_uniform A) i f

lemma ab5_bernoulli_variance {A : Type*} [Fintype A] [Nonempty A]
    (K : ℕ) (hK : 0<K) (T : A → Prop) :
    let p := uniformProb T
    let S := fun w : Fin K → A => (∑ i, if T (w i) then (1:ℝ) else 0)/K
    AronowAudit.P037.designMean (ab5_uniform (Fin K → A)) S = p ∧
    AronowAudit.P037.designVariance (ab5_uniform (Fin K → A)) S = p*(1-p)/K := by
  dsimp only
  have h := AronowAudit.P037.monte_carlo_frequency_moments
    (ab5_uniform (Fin K → A)) K hK
    (fun i w => if T (w i) then (1:ℝ) else 0) (uniformProb T)
    (by intro i w; split_ifs <;> simp)
    (by
      intro i
      rw [ab5_mean_coordinate i (fun a => if T a then (1:ℝ) else 0)]
      exact ab5_probability T)
    (by
      intro i j hij
      rw [← ab5_product_uniform,
        AronowAudit.P037.product_design_coordinate_pair (fun _ : Fin K => ab5_uniform A) i j hij
          (fun a => if T a then (1:ℝ) else 0) (fun a => if T a then (1:ℝ) else 0)]
      change AronowAudit.P037.designProbability (ab5_uniform A) T *
        AronowAudit.P037.designProbability (ab5_uniform A) T = _
      rw [ab5_probability]; ring)
  exact ⟨h.1,h.2.1⟩

lemma ab5_chebyshev_event {A : Type*} [Fintype A] [Nonempty A]
    (X : A → ℝ) (p a : ℝ) (ha : 0<a) (E : A → Prop)
    (hp : AronowAudit.P037.designMean (ab5_uniform A) X = p)
    (hE : ∀ w, E w → a ≤ |X w-p|) :
    uniformProb E ≤ AronowAudit.P037.designVariance (ab5_uniform A) X/a^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos ha), ← ab5_probability,
    AronowAudit.P037.designProbability,
    AronowAudit.P037.designVariance_centered, hp]
  unfold AronowAudit.P037.designMean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro w hw
  by_cases h : E w
  · simp only [if_pos h, mul_one]
    apply mul_le_mul_of_nonneg_left _ ((ab5_uniform A).nonneg w)
    nlinarith [hE w h, sq_abs (X w-p)]
  · simp only [if_neg h, mul_zero, zero_mul]
    exact mul_nonneg ((ab5_uniform A).nonneg w) (sq_nonneg _)

local instance ab5_assignment_nonempty : Nonempty (Assignment 30 15) :=
  ⟨⟨Finset.univ.filter (fun i : Fin 30 => i.val<15), by decide +kernel⟩⟩

def ab5_tail (v o : Counts) {n : ℕ} (z : Finset (Fin n)) : Prop :=
  (deviationNumerator v (canonicalObserved v z) (o.a+o.b)).natAbs ≥
    (deviationNumerator v o (o.a+o.b)).natAbs

instance ab5_tail_decidable (v o : Counts) {n : ℕ} (z : Finset (Fin n)) :
    Decidable (ab5_tail v o z) :=
  inferInstanceAs (Decidable ((deviationNumerator v (canonicalObserved v z) (o.a+o.b)).natAbs ≥
    (deviationNumerator v o (o.a+o.b)).natAbs))

lemma ab5_tail_count_one :
    (Finset.univ.filter (fun z : Assignment 30 15 =>
      ab5_tail ⟨1,9,0,20⟩ adaptiveData z.val)).card = 6387648 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h := ab5_sum_assignment_n (R := ℕ) 30 ⟨1,9,0,20⟩ rfl 15
    (fun o => if (deviationNumerator ⟨1,9,0,20⟩ o 15).natAbs ≥
      (deviationNumerator ⟨1,9,0,20⟩ adaptiveData 15).natAbs then 1 else 0)
  change (∑ z : Assignment 30 15, if ab5_tail ⟨1,9,0,20⟩ adaptiveData z.val then 1 else 0) = _
  simp only [ab5_tail, show adaptiveData.a+adaptiveData.b=15 from rfl]
  rw [h]
  simp only [← binomial_eq_choose]
  decide +kernel

lemma ab5_tail_count_two :
    (Finset.univ.filter (fun z : Assignment 30 15 =>
      ab5_tail ⟨1,12,0,17⟩ adaptiveData z.val)).card = 332112 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h := ab5_sum_assignment_n (R := ℕ) 30 ⟨1,12,0,17⟩ rfl 15
    (fun o => if (deviationNumerator ⟨1,12,0,17⟩ o 15).natAbs ≥
      (deviationNumerator ⟨1,12,0,17⟩ adaptiveData 15).natAbs then 1 else 0)
  change (∑ z : Assignment 30 15, if ab5_tail ⟨1,12,0,17⟩ adaptiveData z.val then 1 else 0) = _
  simp only [ab5_tail, show adaptiveData.a+adaptiveData.b=15 from rfl]
  rw [h]
  simp only [← binomial_eq_choose]
  decide +kernel

lemma ab5_probability_of_card {A : Type*} [Fintype A] (E : A → Prop)
    [DecidablePred E] (n : ℕ) (h : (Finset.univ.filter E).card=n) :
    uniformProb E = (n:ℝ)/Fintype.card A := by
  unfold uniformProb
  apply congrArg (fun k : ℕ => (k:ℝ)/Fintype.card A)
  calc
    _ = (Finset.univ.filter E).card := by
      apply congrArg Finset.card
      ext a
      simp
    _ = n := h

lemma ab5_tail_probability :
    uniformProb (fun z : Assignment 30 15 => ab5_tail ⟨1,9,0,20⟩ adaptiveData z.val) = 412/10005 ∧
    uniformProb (fun z : Assignment 30 15 => ab5_tail ⟨1,12,0,17⟩ adaptiveData z.val) = 407/190095 := by
  rw [ab5_probability_of_card _ _ ab5_tail_count_one,
    ab5_probability_of_card _ _ ab5_tail_count_two]
  have hd : Nat.choose 30 15 = 155117520 := by
    rw [← binomial_eq_choose]
    decide +kernel
  simp only [Assignment, Fintype.card_finset_len, Fintype.card_fin, hd]
  norm_num

lemma ab5_monteMean_cast {K : ℕ} (v : Counts) (w : Fin K → Assignment 30 15) :
    (monteMean v adaptiveData (fun i => (w i).val) : ℝ) =
      (∑ i, if ab5_tail v adaptiveData (w i).val then (1:ℝ) else 0)/K := by
  simp only [monteMean, ab5_tail, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> norm_num <;> omega

lemma ab5_sample_moments (v : Counts) (K : ℕ) (hK : 0<K) :
    let p := uniformProb (fun z : Assignment 30 15 => ab5_tail v adaptiveData z.val)
    let S := fun w : Fin K → Assignment 30 15 =>
      (monteMean v adaptiveData (fun i => (w i).val) : ℝ)
    AronowAudit.P037.designMean (ab5_uniform (Fin K → Assignment 30 15)) S = p ∧
    AronowAudit.P037.designVariance (ab5_uniform (Fin K → Assignment 30 15)) S = p*(1-p)/K := by
  have h := ab5_bernoulli_variance K hK
    (fun z : Assignment 30 15 => ab5_tail v adaptiveData z.val)
  dsimp only at h ⊢
  have hs : (fun w : Fin K → Assignment 30 15 =>
      (monteMean v adaptiveData (fun i => (w i).val) : ℝ)) =
      (fun w => (∑ i, @ite ℝ (ab5_tail v adaptiveData (w i).val)
        (Classical.propDecidable _) 1 0)/K) := by
    funext w
    rw [ab5_monteMean_cast]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ht : ab5_tail v adaptiveData (w i).val <;> simp [ht]
  rw [hs]
  exact h

abbrev ab5_Batch := Fin 5000 → Assignment 30 15

def ab5_good1 (w : ab5_Batch) : Prop :=
  3/100 ≤ (monteMean ⟨1,9,0,20⟩ adaptiveData (fun i => (w i).val) : ℝ)
def ab5_good2 (w : ab5_Batch) : Prop :=
  (monteMean ⟨1,12,0,17⟩ adaptiveData (fun i => (w i).val) : ℝ) < 3/100

lemma ab5_first_batch_bound :
    1-(7904632:ℝ)/125104225 ≤ uniformProb ab5_good1 := by
  let S := fun w : ab5_Batch =>
    (monteMean ⟨1,9,0,20⟩ adaptiveData (fun i => (w i).val) : ℝ)
  have hm := ab5_sample_moments ⟨1,9,0,20⟩ 5000 (by omega)
  dsimp only at hm
  rw [ab5_tail_probability.1] at hm
  have ht := ab5_chebyshev_event S (412/10005) (412/10005-3/100)
    (by norm_num) (fun w => S w<3/100) hm.1 (by
      intro w hw
      have := le_abs_self (412/10005-S w)
      rw [abs_sub_comm] at this
      linarith)
  rw [hm.2] at ht
  norm_num at ht
  have hc : uniformProb ab5_good1 = 1-uniformProb (fun w => S w<3/100) := by
    convert ab5_probability_compl (fun w => S w<3/100) using 1
    congr 1
    funext w
    simp only [ab5_good1, S, not_lt]
  rw [hc]
  linarith

lemma ab5_second_batch_bound :
    1-(154406032:ℝ)/280460272225 ≤ uniformProb ab5_good2 := by
  let S := fun w : ab5_Batch =>
    (monteMean ⟨1,12,0,17⟩ adaptiveData (fun i => (w i).val) : ℝ)
  have hm := ab5_sample_moments ⟨1,12,0,17⟩ 5000 (by omega)
  dsimp only at hm
  rw [ab5_tail_probability.2] at hm
  have ht := ab5_chebyshev_event S (407/190095) (3/100-407/190095)
    (by norm_num) (fun w => 3/100≤S w) hm.1 (by
      intro w hw
      have := le_abs_self (S w-407/190095)
      linarith)
  rw [hm.2] at ht
  norm_num at ht
  have hc : uniformProb ab5_good2 = 1-uniformProb (fun w => 3/100≤S w) := by
    convert ab5_probability_compl (fun w => 3/100≤S w) using 1
    congr 1
    funext w
    simp only [ab5_good2, S, not_le]
  rw [hc]
  linarith

lemma ab5_adaptive_trace_prefix (t : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) :
    ∃ ts, (adaptiveSearch (t+1) false o k₁ k₂ reject a b idx).trace =
      (runTests reject idx (candidates o ((a+b)/2))).trace++ts := by
  rw [adaptiveSearch]
  simp only [Bool.false_eq_true, false_and, if_false, not_false_eq_true, true_and]
  try dsimp only
  split_ifs
  all_goals first | exact ⟨_,rfl⟩ | exact ⟨[],by simp⟩

lemma ab5_first_two (reject : Counts → ℕ → Bool)
    (h0 : reject ⟨1,9,0,20⟩ 0 = false)
    (h1 : reject ⟨1,12,0,17⟩ 1 = true) :
    2 ≤ (upperRun false adaptiveData reject).trace.length ∧
      (upperRun false adaptiveData reject).trace[1]!.2 = true := by
  have hq : runTests reject 0 (candidates adaptiveData 9) =
      ⟨true,1,[(⟨1,9,0,20⟩,false)]⟩ := by
    rw [atr_candidates_9]
    simp only [runTests, h0, Bool.false_eq_true, if_false]
  have hfirst : (upperRun false adaptiveData reject).trace =
      (⟨1,9,0,20⟩,false)::
        (adaptiveSearch 32 false adaptiveData 2 16 reject 9 16 1).trace := by
    change (adaptiveSearch 33 false adaptiveData 2 16 reject 2 16 0).trace = _
    rw [adaptiveSearch]
    norm_num [hq]
  obtain ⟨ts,hp⟩ := ab5_adaptive_trace_prefix 31 adaptiveData 2 16 reject 9 16 1
  change (adaptiveSearch 32 false adaptiveData 2 16 reject 9 16 1).trace =
    (runTests reject 1 (candidates adaptiveData 12)).trace++ts at hp
  have hq2 : (runTests reject 1 (candidates adaptiveData 12)).trace =
      (⟨1,12,0,17⟩,true)::
        (runTests reject 2 [⟨2,12,0,16⟩,⟨3,12,0,15⟩,⟨3,13,1,13⟩,⟨3,14,2,11⟩]).trace := by
    rw [atr_candidates_12]
    simp only [runTests, h1, if_true]
  simp [hfirst, hp, hq2]

lemma ab5_good_subset (pool : Fin (2*testBudget 30+1) → ab5_Batch)
    (h : ab5_good1 (pool 0) ∧ ab5_good2 (pool 1)) :
    let b := upperRun false adaptiveData
      (approximateReject (1/20) (1/50) adaptiveData pool)
    2 ≤ b.trace.length ∧ b.trace[1]!.2=true := by
  apply ab5_first_two
  · simp only [approximateReject, decide_eq_false_iff_not]
    change ¬((monteMean ⟨1,9,0,20⟩ adaptiveData
      (fun i => (pool 0 i).val) : ℝ)+1/50<1/20)
    dsimp [ab5_good1] at h
    linarith [h.1]
  · simp only [approximateReject, decide_eq_true_eq]
    change (monteMean ⟨1,12,0,17⟩ adaptiveData
      (fun i => (pool 1 i).val) : ℝ)+1/50<1/20
    dsimp [ab5_good2] at h
    linarith [h.2]

lemma ab5_exp_bound : 16*Real.exp (-4) < 48/103 := by
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ)≤4 by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos (4:ℝ))]
  nlinarith


/-! Event trees for the chronological search. The
finite uniform law is proved by splitting the head coordinate from the tail.
Closed kernel certificates reduce the four events to their trees. -/

inductive api5_Tree (B : Type*) where
  | leaf : B → api5_Tree B
  | node : Counts → api5_Tree B → api5_Tree B → api5_Tree B
  deriving DecidableEq

def api5_eval {B : Type*} : api5_Tree B → (Counts → ℕ → Bool) → ℕ → B
  | .leaf b, _, _ => b
  | .node v r a, reject, idx =>
    if reject v idx then api5_eval r reject (idx+1) else api5_eval a reject (idx+1)

def api5_depth {B : Type*} : api5_Tree B → ℕ
  | .leaf _ => 0
  | .node _ r a => max (api5_depth r) (api5_depth a)+1

def api5_queries {B : Type*} (idx : ℕ) (vs : List Counts)
    (k : QueryResult → api5_Tree B) : api5_Tree B :=
  match vs with
  | [] => k ⟨false,idx,[]⟩
  | v::vs => .node v
      (api5_queries (idx+1) vs (fun q => k ⟨q.compatible,q.idx,(v,true)::q.trace⟩))
      (k ⟨true,idx+1,[(v,false)]⟩)

lemma api5_queries_eval {B : Type*} (reject : Counts → ℕ → Bool)
    (vs : List Counts) (idx : ℕ) (k : QueryResult → api5_Tree B) :
    api5_eval (api5_queries idx vs k) reject idx =
      api5_eval (k (runTests reject idx vs)) reject (runTests reject idx vs).idx := by
  induction vs generalizing idx k with
  | nil => rfl
  | cons v vs ih =>
    simp only [api5_queries, api5_eval, runTests]
    split_ifs with h
    · exact ih (idx+1) (fun q => k ⟨q.compatible,q.idx,(v,true)::q.trace⟩)
    · rfl

def api5_search {B : Type*} (fuel : ℕ) (C : ℤ → List Counts) (k₁ k₂ : ℤ)
    (a b : ℤ) (idx : ℕ) (f : EndpointResult → B) : api5_Tree B :=
  match fuel with
  | 0 => .leaf (f ⟨none,[]⟩)
  | t+1 =>
    let c := (a+b)/2
    api5_queries idx (C c) fun q =>
      let a' := if q.compatible then c else a
      let b' := if q.compatible then b else c
      if b'=a'+1 then
        if a'>k₁ ∧ b'<k₂ then .leaf (f ⟨some a',q.trace⟩)
        else if a'=k₁ then
          api5_queries q.idx (C k₁) fun e =>
            .leaf (f ⟨some (if e.compatible then k₁ else k₁-1),q.trace++e.trace⟩)
        else if b'=k₂ then
          api5_queries q.idx (C k₂) fun e =>
            .leaf (f ⟨some (if e.compatible then k₂ else k₂-1),q.trace++e.trace⟩)
        else .leaf (f ⟨none,q.trace⟩)
      else api5_search t C k₁ k₂ a' b' q.idx (fun r => f ⟨r.value,q.trace++r.trace⟩)

lemma api5_search_eval {B : Type*} (reject : Counts → ℕ → Bool)
    (fuel : ℕ) (o : Counts) (k₁ k₂ a b : ℤ) (idx : ℕ) (f : EndpointResult → B) :
    api5_eval (api5_search fuel (candidates o) k₁ k₂ a b idx f) reject idx =
      f (adaptiveSearch fuel false o k₁ k₂ reject a b idx) := by
  induction fuel generalizing a b idx f with
  | zero => simp [api5_search, api5_eval, adaptiveSearch]
  | succ t ih =>
    rw [api5_search, api5_queries_eval, adaptiveSearch]
    simp only [Bool.false_eq_true, false_and, if_false, not_false_eq_true, true_and]
    split_ifs
    all_goals try (solve | rfl | apply ih)
    all_goals
      rw [api5_queries_eval]
      simp only [api5_eval]
      congr 2 <;> split_ifs <;> first | rfl | contradiction

def api5_compatQueries {B : Type*} (vs : List Counts) (k : Bool → api5_Tree B) : api5_Tree B :=
  match vs with
  | [] => k false
  | v::vs => .node v (api5_compatQueries vs k) (k true)

lemma api5_compatQueries_eval {B : Type*} (reject : Counts → ℕ → Bool)
    (vs : List Counts) (idx : ℕ) (k : Bool → api5_Tree B) :
    api5_eval (api5_compatQueries vs k) reject idx =
      api5_eval (k (runTests reject idx vs).compatible) reject (runTests reject idx vs).idx := by
  induction vs generalizing idx with
  | nil => rfl
  | cons v vs ih =>
    simp only [api5_compatQueries, api5_eval, runTests]
    split_ifs
    · exact ih (idx+1)
    · rfl

def api5_endpointTree {B : Type*} (fuel : ℕ) (C : ℤ → List Counts) (k₁ k₂ a b : ℤ)
    (f : Option ℤ → B) : api5_Tree B :=
  match fuel with
  | 0 => .leaf (f none)
  | t+1 =>
    let c := (a+b)/2
    api5_compatQueries (C c) fun ok =>
      let a' := if ok then c else a
      let b' := if ok then b else c
      if b'=a'+1 then
        if a'>k₁ ∧ b'<k₂ then .leaf (f (some a'))
        else if a'=k₁ then
          api5_compatQueries (C k₁) fun good =>
            .leaf (f (some (if good then k₁ else k₁-1)))
        else if b'=k₂ then
          api5_compatQueries (C k₂) fun good =>
            .leaf (f (some (if good then k₂ else k₂-1)))
        else .leaf (f none)
      else api5_endpointTree t C k₁ k₂ a' b' f

lemma api5_endpointTree_eval {B : Type*} (reject : Counts → ℕ → Bool)
    (fuel : ℕ) (o : Counts) (k₁ k₂ a b : ℤ) (idx : ℕ) (f : Option ℤ → B) :
    api5_eval (api5_endpointTree fuel (candidates o) k₁ k₂ a b f) reject idx =
      f (adaptiveSearch fuel false o k₁ k₂ reject a b idx).value := by
  induction fuel generalizing a b idx with
  | zero => simp [api5_endpointTree, api5_eval, adaptiveSearch]
  | succ t ih =>
    rw [api5_endpointTree, api5_compatQueries_eval, adaptiveSearch]
    simp only [Bool.false_eq_true, false_and, if_false, not_false_eq_true, true_and]
    split_ifs
    all_goals try (solve | rfl | apply ih)
    all_goals
      rw [api5_compatQueries_eval]
      simp only [api5_eval]
      congr 2 <;> split_ifs <;> first | rfl | contradiction

def api5_smart (v : Counts) (r a : api5_Tree Bool) : api5_Tree Bool :=
  match r,a with
  | .leaf b, .leaf c => if b=c then .leaf b else .node v r a
  | _,_ => .node v r a

def api5_reduce : api5_Tree Bool → api5_Tree Bool
  | .leaf b => .leaf b
  | .node v r a => api5_smart v (api5_reduce r) (api5_reduce a)

lemma api5_smart_eval (v : Counts) (r a : api5_Tree Bool)
    (reject : Counts → ℕ → Bool) (idx : ℕ) :
    api5_eval (api5_smart v r a) reject idx =
      api5_eval (.node v r a) reject idx := by
  cases r with
  | leaf b =>
    cases a with
    | leaf c =>
      by_cases h : b=c
      · subst c; simp [api5_smart, api5_eval]
      · simp [api5_smart, h, api5_eval]
    | node v' r' a' => rfl
  | node v' r' a' => cases a <;> rfl

lemma api5_reduce_eval (T : api5_Tree Bool) (reject : Counts → ℕ → Bool) (idx : ℕ) :
    api5_eval (api5_reduce T) reject idx = api5_eval T reject idx := by
  induction T generalizing idx with
  | leaf b => rfl
  | node v r a hr ha =>
    rw [api5_reduce, api5_smart_eval]
    simp only [api5_eval]
    split_ifs <;> first | exact hr _ | exact ha _

def api5_vecEquiv (A : Type*) (n : ℕ) :
    A × (Fin n → A) ≃ (Fin (n+1) → A) where
  toFun w := Fin.cons w.1 w.2
  invFun w := (w 0,fun i => w i.succ)
  left_inv := by intro w; cases w; rfl
  right_inv := by intro w; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma api5_mean_equiv {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (e : A ≃ B) (f : B → ℝ) :
    AronowAudit.P037.designMean (ab5_uniform B) f =
      AronowAudit.P037.designMean (ab5_uniform A) (fun a => f (e a)) := by
  rw [ab5_mean, ab5_mean, Equiv.sum_comp, Fintype.card_congr e]

lemma api5_mean_prod {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (f : A × B → ℝ) :
    AronowAudit.P037.designMean (ab5_uniform (A × B)) f =
      AronowAudit.P037.designMean (ab5_uniform A)
        (fun a => AronowAudit.P037.designMean (ab5_uniform B) (fun b => f (a,b))) := by
  simp only [ab5_mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp_rw [Finset.sum_div]
  simp only [div_eq_mul_inv, mul_inv_rev, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

lemma api5_indicator_probability {A : Type*} [Fintype A] [Nonempty A]
    (E : A → Prop) [DecidablePred E] :
    AronowAudit.P037.designMean (ab5_uniform A) (fun x => if E x then (1:ℝ) else 0) =
      uniformProb E := by
  rw [← ab5_probability, AronowAudit.P037.designProbability]
  congr 1
  funext x
  by_cases h : E x <;> simp [h]

lemma api5_mean_ite {A : Type*} [Fintype A] [Nonempty A]
    (E : A → Prop) [DecidablePred E] (r a : ℝ) :
    AronowAudit.P037.designMean (ab5_uniform A) (fun x => if E x then r else a) =
      uniformProb E*r+(1-uniformProb E)*a := by
  have hf : (fun x => if E x then r else a) =
      (fun x => (if E x then (1:ℝ) else 0)*r+
        (1-(if E x then (1:ℝ) else 0))*a) := by
    funext x
    by_cases h : E x <;> simp [h]
  rw [hf, AronowAudit.P037.designMean_add]
  simp only [mul_comm _ r, mul_comm _ a]
  rw [AronowAudit.P037.designMean_mul, AronowAudit.P037.designMean_mul,
    AronowAudit.P037.designMean_sub, AronowAudit.P037.designMean_const]
  rw [api5_indicator_probability E]

def api5_vecOracle {A : Type*} {n : ℕ} (test : Counts → A → Bool)
    (w : Fin n → A) (v : Counts) (idx : ℕ) : Bool :=
  if h : idx<n then test v (w ⟨idx,h⟩) else false

lemma api5_eval_shift {B : Type*} (T : api5_Tree B) (reject : Counts → ℕ → Bool)
    (k idx : ℕ) :
    api5_eval T (fun v i => reject v (i+k)) idx = api5_eval T reject (idx+k) := by
  induction T generalizing idx with
  | leaf b => rfl
  | node v r a hr ha =>
    simp only [api5_eval]
    split_ifs <;> first
      | (rw [hr]; congr 1 <;> omega)
      | (rw [ha]; congr 1 <;> omega)

lemma api5_vecOracle_shift {A : Type*} {n : ℕ} (test : Counts → A → Bool)
    (w : Fin (n+1) → A) :
    (fun v i => api5_vecOracle test w (v) (i+1)) =
      api5_vecOracle test (fun j : Fin n => w j.succ) := by
  funext v i
  by_cases h : i<n
  · simp only [api5_vecOracle, dif_pos h, dif_pos (show i+1<n+1 by omega)]
    rfl
  · simp only [api5_vecOracle, dif_neg h, dif_neg (show ¬i+1<n+1 by omega)]

lemma api5_node_eval {A : Type*} {n : ℕ} (test : Counts → A → Bool)
    (w : Fin (n+1) → A) (v : Counts) (r a : api5_Tree Bool) :
    api5_eval (.node v r a) (api5_vecOracle test w) 0 =
      if test v (w 0) then
        api5_eval r (api5_vecOracle test (fun j : Fin n => w j.succ)) 0
      else api5_eval a (api5_vecOracle test (fun j : Fin n => w j.succ)) 0 := by
  have hz : api5_vecOracle test w v 0 = test v (w 0) := rfl
  simp only [api5_eval, hz]
  split_ifs
  all_goals
    rw [← api5_eval_shift _ (api5_vecOracle test w) 1 0, api5_vecOracle_shift]


lemma api5_branch_probability {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (test : A → Bool) (r a : B → Bool) :
    AronowAudit.P037.designProbability (ab5_uniform (A × B))
      (fun w => cond (test w.1) (r w.2) (a w.2)=true) =
      uniformProb (fun x => test x=true)*uniformProb (fun y => r y=true)+
        (1-uniformProb (fun x => test x=true))*uniformProb (fun y => a y=true) := by
  rw [AronowAudit.P037.designProbability, api5_mean_prod]
  trans AronowAudit.P037.designMean (ab5_uniform A)
    (fun x => if test x=true then uniformProb (fun y => r y=true)
      else uniformProb (fun y => a y=true))
  · congr 1
    funext x
    cases h : test x <;> simp only [h, Bool.cond_false, Bool.cond_true,
      Bool.false_eq_true, ite_false, ite_true]
    · exact api5_indicator_probability (fun y : B => a y=true)
    · exact api5_indicator_probability (fun y : B => r y=true)
  · exact api5_mean_ite (fun x => test x=true) _ _

def api5_support : api5_Tree Bool → Finset Counts
  | .leaf _ => ∅
  | .node v r a => insert v (api5_support r ∪ api5_support a)

def api5_weight {R : Type*} [CommRing R] (p : Counts → R) : api5_Tree Bool → R
  | .leaf b => if b then 1 else 0
  | .node v r a => (1-p v)*api5_weight p r+p v*api5_weight p a

lemma api5_probability_const {A : Type*} [Fintype A] [Nonempty A] (b : Bool) :
    uniformProb (fun _ : A => b=true) = if b then (1:ℝ) else 0 := by
  rw [← ab5_probability, AronowAudit.P037.designProbability]
  cases b <;> simp [AronowAudit.P037.designMean_const]

lemma api5_tree_probability {A : Type*} [Fintype A] [Nonempty A]
    (test : Counts → A → Bool) (p : Counts → ℝ) (T : api5_Tree Bool)
    (hp : ∀ v ∈ api5_support T, uniformProb (fun x => test v x=true)=1-p v)
    (n : ℕ) (hn : api5_depth T≤n) :
    uniformProb (fun w : Fin n → A => api5_eval T (api5_vecOracle test w) 0=true) =
      api5_weight p T := by
  classical
  induction T generalizing n with
  | leaf b =>
    simpa only [api5_eval, api5_weight] using api5_probability_const (A := Fin n → A) b
  | node v r a hr ha =>
    cases n with
    | zero => simp [api5_depth] at hn
    | succ n =>
      have hrd : api5_depth r≤n := by simp only [api5_depth] at hn; omega
      have had : api5_depth a≤n := by simp only [api5_depth] at hn; omega
      have hrp : ∀ v ∈ api5_support r,
          uniformProb (fun x => test v x=true)=1-p v := by
        intro z hz
        exact hp z (by simp [api5_support,hz])
      have hap : ∀ v ∈ api5_support a,
          uniformProb (fun x => test v x=true)=1-p v := by
        intro z hz
        exact hp z (by simp [api5_support,hz])
      have hv := hp v (by simp [api5_support])
      rw [← ab5_probability, AronowAudit.P037.designProbability,
        api5_mean_equiv (api5_vecEquiv A n)]
      trans AronowAudit.P037.designProbability (ab5_uniform (A × (Fin n → A)))
        (fun w => cond (test v w.1) (api5_eval r (api5_vecOracle test w.2) 0)
          (api5_eval a (api5_vecOracle test w.2) 0)=true)
      · rw [AronowAudit.P037.designProbability]
        congr 1
        funext w
        rw [api5_node_eval]
        cases ht : test v w.1 <;> simp [api5_vecEquiv, ht]
      · rw [api5_branch_probability (test v)
          (fun w : Fin n → A => api5_eval r (api5_vecOracle test w) 0)
          (fun w : Fin n → A => api5_eval a (api5_vecOracle test w) 0),
          hr hrp n hrd, ha hap n had, hv, api5_weight]
        ring


def api5_below (r : EndpointResult) : Bool := r.value.any (fun x => decide (x<10))
def api5_above (r : EndpointResult) : Bool := r.value.any (fun x => decide (10<x))
def api5_bad (ts : List (Counts × Bool)) (bad : Bool) (r : EndpointResult) : Bool :=
  let j := firstMismatch ts r.trace
  decide (j<ts.length) && (r.trace[j]!.2 == bad)

lemma api5_candidates_2 : candidates adaptiveData 2 = [⟨1,2,0,27⟩, ⟨2,2,0,26⟩, ⟨3,2,0,25⟩, ⟨3,3,1,23⟩, ⟨3,4,2,21⟩, ⟨3,5,3,19⟩, ⟨3,6,4,17⟩, ⟨3,7,5,15⟩, ⟨3,8,6,13⟩, ⟨3,9,7,11⟩, ⟨3,10,8,9⟩, ⟨3,11,9,7⟩, ⟨3,12,10,5⟩, ⟨3,13,11,3⟩, ⟨3,14,12,1⟩] := by
  decide +kernel

lemma api5_candidates_3 : candidates adaptiveData 3 = [⟨1,3,0,26⟩, ⟨2,3,0,25⟩, ⟨3,3,0,24⟩, ⟨3,4,1,22⟩, ⟨3,5,2,20⟩, ⟨3,6,3,18⟩, ⟨3,7,4,16⟩, ⟨3,8,5,14⟩, ⟨3,9,6,12⟩, ⟨3,10,7,10⟩, ⟨3,11,8,8⟩, ⟨3,12,9,6⟩, ⟨3,13,10,4⟩, ⟨3,14,11,2⟩] := by
  decide +kernel

lemma api5_candidates_4 : candidates adaptiveData 4 = [⟨1,4,0,25⟩, ⟨2,4,0,24⟩, ⟨3,4,0,23⟩, ⟨3,5,1,21⟩, ⟨3,6,2,19⟩, ⟨3,7,3,17⟩, ⟨3,8,4,15⟩, ⟨3,9,5,13⟩, ⟨3,10,6,11⟩, ⟨3,11,7,9⟩, ⟨3,12,8,7⟩, ⟨3,13,9,5⟩, ⟨3,14,10,3⟩] := by
  decide +kernel

lemma api5_candidates_5 : candidates adaptiveData 5 = [⟨1,5,0,24⟩, ⟨2,5,0,23⟩, ⟨3,5,0,22⟩, ⟨3,6,1,20⟩, ⟨3,7,2,18⟩, ⟨3,8,3,16⟩, ⟨3,9,4,14⟩, ⟨3,10,5,12⟩, ⟨3,11,6,10⟩, ⟨3,12,7,8⟩, ⟨3,13,8,6⟩, ⟨3,14,9,4⟩] := by
  decide +kernel

lemma api5_candidates_6 : candidates adaptiveData 6 = [⟨1,6,0,23⟩, ⟨2,6,0,22⟩, ⟨3,6,0,21⟩, ⟨3,7,1,19⟩, ⟨3,8,2,17⟩, ⟨3,9,3,15⟩, ⟨3,10,4,13⟩, ⟨3,11,5,11⟩, ⟨3,12,6,9⟩, ⟨3,13,7,7⟩, ⟨3,14,8,5⟩] := by
  decide +kernel

lemma api5_candidates_7 : candidates adaptiveData 7 = [⟨1,7,0,22⟩, ⟨2,7,0,21⟩, ⟨3,7,0,20⟩, ⟨3,8,1,18⟩, ⟨3,9,2,16⟩, ⟨3,10,3,14⟩, ⟨3,11,4,12⟩, ⟨3,12,5,10⟩, ⟨3,13,6,8⟩, ⟨3,14,7,6⟩] := by
  decide +kernel

lemma api5_candidates_8 : candidates adaptiveData 8 = [⟨1,8,0,21⟩, ⟨2,8,0,20⟩, ⟨3,8,0,19⟩, ⟨3,9,1,17⟩, ⟨3,10,2,15⟩, ⟨3,11,3,13⟩, ⟨3,12,4,11⟩, ⟨3,13,5,9⟩, ⟨3,14,6,7⟩] := by
  decide +kernel

lemma api5_candidates_9 : candidates adaptiveData 9 = [⟨1,9,0,20⟩, ⟨2,9,0,19⟩, ⟨3,9,0,18⟩, ⟨3,10,1,16⟩, ⟨3,11,2,14⟩, ⟨3,12,3,12⟩, ⟨3,13,4,10⟩, ⟨3,14,5,8⟩] := by
  exact atr_candidates_9

lemma api5_candidates_10 : candidates adaptiveData 10 = [⟨1,10,0,19⟩, ⟨2,10,0,18⟩, ⟨3,10,0,17⟩, ⟨3,11,1,15⟩, ⟨3,12,2,13⟩, ⟨3,13,3,11⟩, ⟨3,14,4,9⟩] := by
  exact atr_candidates_10

lemma api5_candidates_11 : candidates adaptiveData 11 = [⟨1,11,0,18⟩, ⟨2,11,0,17⟩, ⟨3,11,0,16⟩, ⟨3,12,1,14⟩, ⟨3,13,2,12⟩, ⟨3,14,3,10⟩] := by
  exact atr_candidates_11

lemma api5_candidates_12 : candidates adaptiveData 12 = [⟨1,12,0,17⟩, ⟨2,12,0,16⟩, ⟨3,12,0,15⟩, ⟨3,13,1,13⟩, ⟨3,14,2,11⟩] := by
  exact atr_candidates_12

lemma api5_candidates_13 : candidates adaptiveData 13 = [⟨1,13,0,16⟩, ⟨2,13,0,15⟩, ⟨3,13,0,14⟩, ⟨3,14,1,12⟩] := by
  decide +kernel

lemma api5_candidates_14 : candidates adaptiveData 14 = [⟨1,14,0,15⟩, ⟨2,14,0,14⟩, ⟨3,14,0,13⟩] := by
  exact atr_candidates_14

lemma api5_candidates_15 : candidates adaptiveData 15 = [⟨1,15,0,14⟩, ⟨2,15,0,13⟩] := by
  exact atr_candidates_15

lemma api5_candidates_16 : candidates adaptiveData 16 = [⟨1,16,0,13⟩] := by
  exact atr_candidates_16

def api5_cachedCandidates (x : ℤ) : List Counts :=
  if x=2 then [⟨1,2,0,27⟩, ⟨2,2,0,26⟩, ⟨3,2,0,25⟩, ⟨3,3,1,23⟩, ⟨3,4,2,21⟩, ⟨3,5,3,19⟩, ⟨3,6,4,17⟩, ⟨3,7,5,15⟩, ⟨3,8,6,13⟩, ⟨3,9,7,11⟩, ⟨3,10,8,9⟩, ⟨3,11,9,7⟩, ⟨3,12,10,5⟩, ⟨3,13,11,3⟩, ⟨3,14,12,1⟩] else
  if x=3 then [⟨1,3,0,26⟩, ⟨2,3,0,25⟩, ⟨3,3,0,24⟩, ⟨3,4,1,22⟩, ⟨3,5,2,20⟩, ⟨3,6,3,18⟩, ⟨3,7,4,16⟩, ⟨3,8,5,14⟩, ⟨3,9,6,12⟩, ⟨3,10,7,10⟩, ⟨3,11,8,8⟩, ⟨3,12,9,6⟩, ⟨3,13,10,4⟩, ⟨3,14,11,2⟩] else
  if x=4 then [⟨1,4,0,25⟩, ⟨2,4,0,24⟩, ⟨3,4,0,23⟩, ⟨3,5,1,21⟩, ⟨3,6,2,19⟩, ⟨3,7,3,17⟩, ⟨3,8,4,15⟩, ⟨3,9,5,13⟩, ⟨3,10,6,11⟩, ⟨3,11,7,9⟩, ⟨3,12,8,7⟩, ⟨3,13,9,5⟩, ⟨3,14,10,3⟩] else
  if x=5 then [⟨1,5,0,24⟩, ⟨2,5,0,23⟩, ⟨3,5,0,22⟩, ⟨3,6,1,20⟩, ⟨3,7,2,18⟩, ⟨3,8,3,16⟩, ⟨3,9,4,14⟩, ⟨3,10,5,12⟩, ⟨3,11,6,10⟩, ⟨3,12,7,8⟩, ⟨3,13,8,6⟩, ⟨3,14,9,4⟩] else
  if x=6 then [⟨1,6,0,23⟩, ⟨2,6,0,22⟩, ⟨3,6,0,21⟩, ⟨3,7,1,19⟩, ⟨3,8,2,17⟩, ⟨3,9,3,15⟩, ⟨3,10,4,13⟩, ⟨3,11,5,11⟩, ⟨3,12,6,9⟩, ⟨3,13,7,7⟩, ⟨3,14,8,5⟩] else
  if x=7 then [⟨1,7,0,22⟩, ⟨2,7,0,21⟩, ⟨3,7,0,20⟩, ⟨3,8,1,18⟩, ⟨3,9,2,16⟩, ⟨3,10,3,14⟩, ⟨3,11,4,12⟩, ⟨3,12,5,10⟩, ⟨3,13,6,8⟩, ⟨3,14,7,6⟩] else
  if x=8 then [⟨1,8,0,21⟩, ⟨2,8,0,20⟩, ⟨3,8,0,19⟩, ⟨3,9,1,17⟩, ⟨3,10,2,15⟩, ⟨3,11,3,13⟩, ⟨3,12,4,11⟩, ⟨3,13,5,9⟩, ⟨3,14,6,7⟩] else
  if x=9 then [⟨1,9,0,20⟩, ⟨2,9,0,19⟩, ⟨3,9,0,18⟩, ⟨3,10,1,16⟩, ⟨3,11,2,14⟩, ⟨3,12,3,12⟩, ⟨3,13,4,10⟩, ⟨3,14,5,8⟩] else
  if x=10 then [⟨1,10,0,19⟩, ⟨2,10,0,18⟩, ⟨3,10,0,17⟩, ⟨3,11,1,15⟩, ⟨3,12,2,13⟩, ⟨3,13,3,11⟩, ⟨3,14,4,9⟩] else
  if x=11 then [⟨1,11,0,18⟩, ⟨2,11,0,17⟩, ⟨3,11,0,16⟩, ⟨3,12,1,14⟩, ⟨3,13,2,12⟩, ⟨3,14,3,10⟩] else
  if x=12 then [⟨1,12,0,17⟩, ⟨2,12,0,16⟩, ⟨3,12,0,15⟩, ⟨3,13,1,13⟩, ⟨3,14,2,11⟩] else
  if x=13 then [⟨1,13,0,16⟩, ⟨2,13,0,15⟩, ⟨3,13,0,14⟩, ⟨3,14,1,12⟩] else
  if x=14 then [⟨1,14,0,15⟩, ⟨2,14,0,14⟩, ⟨3,14,0,13⟩] else
  if x=15 then [⟨1,15,0,14⟩, ⟨2,15,0,13⟩] else
  if x=16 then [⟨1,16,0,13⟩] else
  candidates adaptiveData x

lemma api5_cachedCandidates_eq : api5_cachedCandidates=candidates adaptiveData := by
  funext x
  unfold api5_cachedCandidates
  by_cases h2 : x=2
  · rw [if_pos h2, h2, api5_candidates_2]
  rw [if_neg h2]
  by_cases h3 : x=3
  · rw [if_pos h3, h3, api5_candidates_3]
  rw [if_neg h3]
  by_cases h4 : x=4
  · rw [if_pos h4, h4, api5_candidates_4]
  rw [if_neg h4]
  by_cases h5 : x=5
  · rw [if_pos h5, h5, api5_candidates_5]
  rw [if_neg h5]
  by_cases h6 : x=6
  · rw [if_pos h6, h6, api5_candidates_6]
  rw [if_neg h6]
  by_cases h7 : x=7
  · rw [if_pos h7, h7, api5_candidates_7]
  rw [if_neg h7]
  by_cases h8 : x=8
  · rw [if_pos h8, h8, api5_candidates_8]
  rw [if_neg h8]
  by_cases h9 : x=9
  · rw [if_pos h9, h9, api5_candidates_9]
  rw [if_neg h9]
  by_cases h10 : x=10
  · rw [if_pos h10, h10, api5_candidates_10]
  rw [if_neg h10]
  by_cases h11 : x=11
  · rw [if_pos h11, h11, api5_candidates_11]
  rw [if_neg h11]
  by_cases h12 : x=12
  · rw [if_pos h12, h12, api5_candidates_12]
  rw [if_neg h12]
  by_cases h13 : x=13
  · rw [if_pos h13, h13, api5_candidates_13]
  rw [if_neg h13]
  by_cases h14 : x=14
  · rw [if_pos h14, h14, api5_candidates_14]
  rw [if_neg h14]
  by_cases h15 : x=15
  · rw [if_pos h15, h15, api5_candidates_15]
  rw [if_neg h15]
  by_cases h16 : x=16
  · rw [if_pos h16, h16, api5_candidates_16]
  rw [if_neg h16]

def api5_code_0 : api5_Tree Bool := .node ⟨3,14,4,9⟩ (.leaf true) (.leaf false)
def api5_code_1 : api5_Tree Bool := .node ⟨3,13,3,11⟩ api5_code_0 (.leaf false)
def api5_code_2 : api5_Tree Bool := .node ⟨3,12,2,13⟩ api5_code_1 (.leaf false)
def api5_code_3 : api5_Tree Bool := .node ⟨3,11,1,15⟩ api5_code_2 (.leaf false)
def api5_code_4 : api5_Tree Bool := .node ⟨3,10,0,17⟩ api5_code_3 (.leaf false)
def api5_code_5 : api5_Tree Bool := .node ⟨2,10,0,18⟩ api5_code_4 (.leaf false)
def api5_code_6 : api5_Tree Bool := .node ⟨1,10,0,19⟩ api5_code_5 (.leaf false)
def api5_code_7 : api5_Tree Bool := .node ⟨3,14,2,11⟩ api5_code_6 (.leaf false)
def api5_code_8 : api5_Tree Bool := .node ⟨3,13,1,13⟩ api5_code_7 (.leaf false)
def api5_code_9 : api5_Tree Bool := .node ⟨3,12,0,15⟩ api5_code_8 (.leaf false)
def api5_code_10 : api5_Tree Bool := .node ⟨2,12,0,16⟩ api5_code_9 (.leaf false)
def api5_code_11 : api5_Tree Bool := .node ⟨1,12,0,17⟩ api5_code_10 (.leaf false)
def api5_code_12 : api5_Tree Bool := .node ⟨3,14,5,8⟩ (.leaf true) api5_code_11
def api5_code_13 : api5_Tree Bool := .node ⟨3,13,4,10⟩ api5_code_12 api5_code_11
def api5_code_14 : api5_Tree Bool := .node ⟨3,12,3,12⟩ api5_code_13 api5_code_11
def api5_code_15 : api5_Tree Bool := .node ⟨3,11,2,14⟩ api5_code_14 api5_code_11
def api5_code_16 : api5_Tree Bool := .node ⟨3,10,1,16⟩ api5_code_15 api5_code_11
def api5_code_17 : api5_Tree Bool := .node ⟨3,9,0,18⟩ api5_code_16 api5_code_11
def api5_code_18 : api5_Tree Bool := .node ⟨2,9,0,19⟩ api5_code_17 api5_code_11
def api5_code_19 : api5_Tree Bool := .node ⟨1,9,0,20⟩ api5_code_18 api5_code_11
def api5_code_20 : api5_Tree Bool := .node ⟨3,10,0,17⟩ (.leaf true) (.leaf false)
def api5_code_21 : api5_Tree Bool := .node ⟨2,10,0,18⟩ api5_code_20 (.leaf false)
def api5_code_22 : api5_Tree Bool := .node ⟨1,10,0,19⟩ api5_code_21 (.leaf false)
def api5_code_23 : api5_Tree Bool := .node ⟨3,14,2,11⟩ api5_code_22 (.leaf false)
def api5_code_24 : api5_Tree Bool := .node ⟨3,13,1,13⟩ api5_code_23 (.leaf false)
def api5_code_25 : api5_Tree Bool := .node ⟨3,12,0,15⟩ api5_code_24 (.leaf false)
def api5_code_26 : api5_Tree Bool := .node ⟨2,12,0,16⟩ api5_code_25 (.leaf false)
def api5_code_27 : api5_Tree Bool := .node ⟨1,12,0,17⟩ api5_code_26 (.leaf false)
def api5_code_28 : api5_Tree Bool := .node ⟨2,9,0,19⟩ (.leaf true) api5_code_27
def api5_code_29 : api5_Tree Bool := .node ⟨1,9,0,20⟩ api5_code_28 (.leaf false)
def api5_code_30 : api5_Tree Bool := .node ⟨3,14,3,10⟩ (.leaf false) (.leaf true)
def api5_code_31 : api5_Tree Bool := .node ⟨3,13,2,12⟩ api5_code_30 (.leaf true)
def api5_code_32 : api5_Tree Bool := .node ⟨3,12,1,14⟩ api5_code_31 (.leaf true)
def api5_code_33 : api5_Tree Bool := .node ⟨3,11,0,16⟩ api5_code_32 (.leaf true)
def api5_code_34 : api5_Tree Bool := .node ⟨2,11,0,17⟩ api5_code_33 (.leaf true)
def api5_code_35 : api5_Tree Bool := .node ⟨1,11,0,18⟩ api5_code_34 (.leaf true)
def api5_code_36 : api5_Tree Bool := .node ⟨3,14,4,9⟩ (.leaf false) api5_code_35
def api5_code_37 : api5_Tree Bool := .node ⟨3,13,3,11⟩ api5_code_36 api5_code_35
def api5_code_38 : api5_Tree Bool := .node ⟨3,12,2,13⟩ api5_code_37 api5_code_35
def api5_code_39 : api5_Tree Bool := .node ⟨3,11,1,15⟩ api5_code_38 api5_code_35
def api5_code_40 : api5_Tree Bool := .node ⟨3,10,0,17⟩ api5_code_39 api5_code_35
def api5_code_41 : api5_Tree Bool := .node ⟨2,10,0,18⟩ api5_code_40 api5_code_35
def api5_code_42 : api5_Tree Bool := .node ⟨1,10,0,19⟩ api5_code_41 api5_code_35
def api5_code_43 : api5_Tree Bool := .node ⟨3,14,2,11⟩ api5_code_42 (.leaf true)
def api5_code_44 : api5_Tree Bool := .node ⟨3,13,1,13⟩ api5_code_43 (.leaf true)
def api5_code_45 : api5_Tree Bool := .node ⟨3,12,0,15⟩ api5_code_44 (.leaf true)
def api5_code_46 : api5_Tree Bool := .node ⟨2,12,0,16⟩ api5_code_45 (.leaf true)
def api5_code_47 : api5_Tree Bool := .node ⟨1,12,0,17⟩ api5_code_46 (.leaf true)
def api5_code_48 : api5_Tree Bool := .node ⟨3,14,5,8⟩ (.leaf false) api5_code_47
def api5_code_49 : api5_Tree Bool := .node ⟨3,13,4,10⟩ api5_code_48 api5_code_47
def api5_code_50 : api5_Tree Bool := .node ⟨3,12,3,12⟩ api5_code_49 api5_code_47
def api5_code_51 : api5_Tree Bool := .node ⟨3,11,2,14⟩ api5_code_50 api5_code_47
def api5_code_52 : api5_Tree Bool := .node ⟨3,10,1,16⟩ api5_code_51 api5_code_47
def api5_code_53 : api5_Tree Bool := .node ⟨3,9,0,18⟩ api5_code_52 api5_code_47
def api5_code_54 : api5_Tree Bool := .node ⟨2,9,0,19⟩ api5_code_53 api5_code_47
def api5_code_55 : api5_Tree Bool := .node ⟨1,9,0,20⟩ api5_code_54 api5_code_47
def api5_code_56 : api5_Tree Bool := .node ⟨3,10,0,17⟩ (.leaf false) api5_code_35
def api5_code_57 : api5_Tree Bool := .node ⟨2,10,0,18⟩ api5_code_56 (.leaf true)
def api5_code_58 : api5_Tree Bool := .node ⟨1,10,0,19⟩ api5_code_57 (.leaf true)
def api5_code_59 : api5_Tree Bool := .node ⟨3,14,2,11⟩ api5_code_58 (.leaf true)
def api5_code_60 : api5_Tree Bool := .node ⟨3,13,1,13⟩ api5_code_59 (.leaf true)
def api5_code_61 : api5_Tree Bool := .node ⟨3,12,0,15⟩ api5_code_60 (.leaf true)
def api5_code_62 : api5_Tree Bool := .node ⟨2,12,0,16⟩ api5_code_61 (.leaf true)
def api5_code_63 : api5_Tree Bool := .node ⟨1,12,0,17⟩ api5_code_62 (.leaf true)
def api5_code_64 : api5_Tree Bool := .node ⟨1,9,0,20⟩ (.leaf false) api5_code_63
def api5_result_0 : api5_Tree Bool := api5_code_19
def api5_result_1 : api5_Tree Bool := api5_code_29
def api5_result_2 : api5_Tree Bool := api5_code_55
def api5_result_3 : api5_Tree Bool := api5_code_64

local instance api5_assignment_nonempty : Nonempty (Assignment 30 15) := ab5_assignment_nonempty

def api5_inputs : List (Counts × ℕ) :=
  [(⟨1,9,0,20⟩,6387648),
   (⟨2,9,0,19⟩,11659008),
   (⟨3,9,0,18⟩,16354272),
   (⟨3,10,1,16⟩,16033224),
   (⟨3,11,2,14⟩,15162536),
   (⟨3,12,3,12⟩,13728998),
   (⟨3,13,4,10⟩,11718848),
   (⟨3,14,5,8⟩,9134440),
   (⟨1,10,0,19⟩,2705448),
   (⟨2,10,0,18⟩,5644272),
   (⟨3,10,0,17⟩,8743032),
   (⟨3,11,1,15⟩,8345544),
   (⟨3,12,2,13⟩,7544198),
   (⟨3,13,3,11⟩,6358448),
   (⟨3,14,4,9⟩,4832760),
   (⟨1,11,0,18⟩,1017552),
   (⟨2,11,0,17⟩,2426512),
   (⟨3,11,0,16⟩,4189392),
   (⟨3,12,1,14⟩,3826848),
   (⟨3,13,2,12⟩,3213848),
   (⟨3,14,3,10⟩,2399856),
   (⟨1,12,0,17⟩,332112),
   (⟨2,12,0,16⟩,904992),
   (⟨3,12,0,15⟩,1754232),
   (⟨3,13,1,13⟩,1489578),
   (⟨3,14,2,11⟩,1104816)]

def api5_lookup (v : Counts) : List (Counts × ℕ) → ℕ
  | [] => 0
  | (w,n)::xs => if v=w then n else api5_lookup v xs

def api5_p (v : Counts) : ℚ := (api5_lookup v api5_inputs : ℚ)/155117520

def api5_tailNum (v : Counts) : ℕ :=
  ∑ a ∈ Finset.range (v.a+1), ∑ b ∈ Finset.range (v.b+1),
    ∑ c ∈ Finset.range (v.c+1), ∑ d ∈ Finset.range (v.d+1),
      binomial v.a a*binomial v.b b*binomial v.c c*binomial v.d d*
        if a+b+c+d=15 then
          if (deviationNumerator v (observed v ⟨a,b,c,d⟩) 15).natAbs ≥
            (deviationNumerator v adaptiveData 15).natAbs then 1 else 0
        else 0

lemma api5_count_law (v : Counts) (hn : v.total=30) :
    (Finset.univ.filter (fun z : Assignment 30 15 => ab5_tail v adaptiveData z.val)).card =
      api5_tailNum v := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [ab5_tail, show adaptiveData.a+adaptiveData.b=15 from rfl]
  rw [ab5_sum_assignment_n (R := ℕ) 30 v hn 15
    (fun o => if (deviationNumerator v o 15).natAbs ≥
      (deviationNumerator v adaptiveData 15).natAbs then 1 else 0)]
  simp only [api5_tailNum, binomial_eq_choose, Nat.cast_id]

set_option maxHeartbeats 6000000 in
lemma api5_input_certificate : api5_inputs.all (fun t =>
    decide (t.1.total=30 ∧ api5_tailNum t.1=t.2 ∧ api5_lookup t.1 api5_inputs=t.2)) = true := by
  decide +kernel

lemma api5_tail_prob (v : Counts) (hv : v ∈ api5_inputs.map Prod.fst) :
    uniformProb (fun z : Assignment 30 15 => ab5_tail v adaptiveData z.val) = (api5_p v : ℝ) := by
  obtain ⟨⟨v',num⟩,hmem,he⟩ := List.mem_map.mp hv
  dsimp only at he
  subst v'
  have hc := List.all_eq_true.mp api5_input_certificate (v,num) hmem
  simp only [decide_eq_true_eq] at hc
  rw [ab5_probability_of_card _ _ ((api5_count_law v hc.1).trans hc.2.1)]
  have hd : Nat.choose 30 15=155117520 := by rw [← binomial_eq_choose]; exact atr_denominator
  simp only [Assignment, Fintype.card_finset_len, Fintype.card_fin, hd,
    api5_p, hc.2.2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  norm_num

abbrev api5_Atom := Fin 1 → Assignment 30 15

def api5_test (v : Counts) (w : api5_Atom) : Bool :=
  decide (¬ab5_tail v adaptiveData (w 0).val)

lemma api5_probability_coordinate {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] (i : I) (E : A → Prop) :
    uniformProb (fun w : I → A => E (w i)) = uniformProb E := by
  rw [← ab5_probability, AronowAudit.P037.designProbability]
  trans AronowAudit.P037.designMean (ab5_uniform (I → A))
    (fun w => @ite ℝ (E (w i)) (Classical.propDecidable _) 1 0)
  · congr 1
  · rw [ab5_mean_coordinate i (fun a => @ite ℝ (E a) (Classical.propDecidable _) 1 0)]
    exact ab5_probability E

lemma api5_test_probability (v : Counts) (hv : v ∈ api5_inputs.map Prod.fst) :
    uniformProb (fun w : api5_Atom => api5_test v w=true) = 1-(api5_p v : ℝ) := by
  calc
    _ = uniformProb (fun w : api5_Atom => ¬ab5_tail v adaptiveData (w 0).val) := by
      congr 1
      funext w
      simp only [api5_test, decide_eq_true_eq]
    _ = 1-uniformProb (fun w : api5_Atom => ab5_tail v adaptiveData (w 0).val) :=
      ab5_probability_compl _
    _ = _ := by rw [api5_probability_coordinate (0 : Fin 1)
      (fun z : Assignment 30 15 => ab5_tail v adaptiveData z.val), api5_tail_prob v hv]

lemma api5_eval_congr {B : Type*} (T : api5_Tree B) (r s : Counts → ℕ → Bool) (idx : ℕ)
    (h : ∀ v j, idx≤j → j < idx+api5_depth T → r v j=s v j) :
    api5_eval T r idx = api5_eval T s idx := by
  induction T generalizing idx with
  | leaf b => rfl
  | node v tr ta hr ha =>
    have h0 : r v idx=s v idx := h v idx le_rfl (by simp [api5_depth])
    simp only [api5_eval, h0]
    split_ifs
    · apply hr
      intro z j hj hj'
      apply h z j (by omega)
      simp only [api5_depth]
      omega
    · apply ha
      intro z j hj hj'
      apply h z j (by omega)
      simp only [api5_depth]
      omega

lemma api5_actual_test (pool : Fin (2*testBudget 30+1) → api5_Atom) (v : Counts) (idx : ℕ)
    (hi : idx<2*testBudget 30+1) :
    approximateReject (1/20) (1/200) adaptiveData pool v idx =
      api5_vecOracle api5_test pool v idx := by
  have hb : batch pool idx (0 : Fin 1) = (pool ⟨idx,hi⟩ 0).val := by
    simp only [batch, Nat.mod_eq_of_lt hi]
  have hm : monteMean v adaptiveData (batch pool idx) =
      if ab5_tail v adaptiveData (pool ⟨idx,hi⟩ 0).val then 1 else 0 := by
    simp only [monteMean, Fin.sum_univ_one]
    simp only [ab5_tail, hb, Nat.cast_one, div_one]
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  simp only [approximateReject, api5_vecOracle, dif_pos hi, api5_test, hm]
  by_cases ht : ab5_tail v adaptiveData (pool ⟨idx,hi⟩ 0).val <;> simp [ht] <;> norm_num

lemma api5_weight_cast (T : api5_Tree Bool) :
    api5_weight (fun v => (api5_p v : ℝ)) T = (api5_weight (R := ℚ) api5_p T : ℝ) := by
  induction T with
  | leaf b => cases b <;> simp [api5_weight]
  | node v r a hr ha => simp only [api5_weight, Rat.cast_add, Rat.cast_mul,
      Rat.cast_sub, Rat.cast_one, hr, ha]


def api5_result (i : Fin 4) : api5_Tree Bool :=
  match i.val with
  | 0 => api5_result_0
  | 1 => api5_result_1
  | 2 => api5_result_2
  | _ => api5_result_3

lemma api5_result_properties (i : Fin 4) :
    api5_depth (api5_result i)≤2*testBudget 30+1 ∧
    api5_support (api5_result i) ⊆ api5_inputs.toFinset.image Prod.fst := by
  fin_cases i <;> decide +kernel

lemma api5_mass_bounds :
    api5_weight (R := ℚ) api5_p api5_result_0 < (864:ℚ)/1000 ∧
    (948:ℚ)/1000 < api5_weight (R := ℚ) api5_p api5_result_1 ∧
    (30:ℚ)/1000 < api5_weight (R := ℚ) api5_p api5_result_2 ∧
    api5_weight (R := ℚ) api5_p api5_result_3 < (4:ℚ)/1000 := by
  decide +kernel

lemma api5_result_probability (i : Fin 4) :
    uniformProb (fun pool : Fin (2*testBudget 30+1) → api5_Atom =>
      api5_eval (api5_result i) (api5_vecOracle api5_test pool) 0=true) =
      (api5_weight (R := ℚ) api5_p (api5_result i) : ℝ) := by
  rw [← api5_weight_cast]
  apply api5_tree_probability api5_test _ _ _ _ (api5_result_properties i).1
  intro v hv
  apply api5_test_probability
  obtain ⟨t,ht,he⟩ := Finset.mem_image.mp ((api5_result_properties i).2 hv)
  exact List.mem_map.mpr ⟨t,by simpa using ht,he⟩


set_option maxHeartbeats 6000000 in
lemma api5_below_certificate :
    api5_reduce (api5_endpointTree 33 api5_cachedCandidates 2 16 2 16 (fun v => v.any (fun x => decide (x<10)))) = api5_result_0 := by
  decide +kernel


set_option maxHeartbeats 6000000 in
lemma api5_bad_rejection_certificate :
    api5_reduce (api5_search 33 api5_cachedCandidates 2 16 2 16 0 (api5_bad atr_trace_exact true)) = api5_result_1 := by
  decide +kernel

set_option maxHeartbeats 6000000 in
lemma api5_above_certificate :
    api5_reduce (api5_endpointTree 33 api5_cachedCandidates 2 16 2 16 (fun v => v.any (fun x => decide (10<x)))) = api5_result_2 := by
  decide +kernel

set_option maxHeartbeats 6000000 in
lemma api5_bad_acceptance_certificate :
    api5_reduce (api5_search 33 api5_cachedCandidates 2 16 2 16 0 (api5_bad atr_trace_low false)) = api5_result_3 := by
  decide +kernel


lemma api5_actual_tree (f : EndpointResult → Bool) (T : api5_Tree Bool)
    (hT : api5_reduce (api5_search 33 api5_cachedCandidates 2 16 2 16 0 f)=T)
    (hd : api5_depth T≤2*testBudget 30+1)
    (pool : Fin (2*testBudget 30+1) → api5_Atom) :
    api5_eval T (api5_vecOracle api5_test pool) 0 =
      f (upperRun false adaptiveData (approximateReject (1/20) (1/200) adaptiveData pool)) := by
  calc
    _ = api5_eval T (approximateReject (1/20) (1/200) adaptiveData pool) 0 := by
      symm
      apply api5_eval_congr
      intro v j hj hj'
      apply api5_actual_test
      omega
    _ = _ := by
      rw [← hT, api5_reduce_eval, api5_cachedCandidates_eq, api5_search_eval]
      rfl

lemma api5_probability_actual (i : Fin 4) (f : EndpointResult → Bool)
    (hT : api5_reduce (api5_search 33 api5_cachedCandidates 2 16 2 16 0 f)=api5_result i) :
    uniformProb (fun pool : Fin (2*testBudget 30+1) → api5_Atom =>
      f (upperRun false adaptiveData (approximateReject (1/20) (1/200) adaptiveData pool))=true) =
      (api5_weight (R := ℚ) api5_p (api5_result i) : ℝ) := by
  rw [← api5_result_probability i]
  apply congrArg (@uniformProb (Fin (2*testBudget 30+1) → api5_Atom) _)
  funext pool
  rw [api5_actual_tree f (api5_result i) hT (api5_result_properties i).1 pool]

lemma api5_value_actual_tree (f : Option ℤ → Bool) (T : api5_Tree Bool)
    (hT : api5_reduce (api5_endpointTree 33 api5_cachedCandidates 2 16 2 16 f)=T)
    (hd : api5_depth T≤2*testBudget 30+1)
    (pool : Fin (2*testBudget 30+1) → api5_Atom) :
    api5_eval T (api5_vecOracle api5_test pool) 0 =
      f (upperRun false adaptiveData (approximateReject (1/20) (1/200) adaptiveData pool)).value := by
  calc
    _ = api5_eval T (approximateReject (1/20) (1/200) adaptiveData pool) 0 := by
      symm
      apply api5_eval_congr
      intro v j hj hj'
      apply api5_actual_test
      omega
    _ = _ := by
      rw [← hT, api5_reduce_eval, api5_cachedCandidates_eq, api5_endpointTree_eval]
      rfl

lemma api5_probability_value_actual (i : Fin 4) (f : Option ℤ → Bool)
    (hT : api5_reduce (api5_endpointTree 33 api5_cachedCandidates 2 16 2 16 f)=api5_result i) :
    uniformProb (fun pool : Fin (2*testBudget 30+1) → api5_Atom =>
      f (upperRun false adaptiveData (approximateReject (1/20) (1/200) adaptiveData pool)).value=true) =
      (api5_weight (R := ℚ) api5_p (api5_result i) : ℝ) := by
  rw [← api5_result_probability i]
  apply congrArg (@uniformProb (Fin (2*testBudget 30+1) → api5_Atom) _)
  funext pool
  rw [api5_value_actual_tree f (api5_result i) hT (api5_result_properties i).1 pool]

lemma api5_below_iff (r : EndpointResult) :
    api5_below r=true ↔ ∃ x, r.value=some x ∧ x<10 := by
  cases h : r.value <;> simp [api5_below,h]

lemma api5_above_iff (r : EndpointResult) :
    api5_above r=true ↔ ∃ x, r.value=some x ∧ 10<x := by
  cases h : r.value <;> simp [api5_above,h]

lemma api5_bad_iff (ts : List (Counts × Bool)) (bad : Bool) (r : EndpointResult) :
    api5_bad ts bad r=true ↔
      let j := firstMismatch ts r.trace
      j<ts.length ∧ r.trace[j]!.2=bad := by
  simp [api5_bad]

lemma api5_uniform_congr {A : Type*} [Fintype A] {E F : A → Prop}
    (h : ∀ w, E w ↔ F w) : uniformProb E=uniformProb F := by
  apply congrArg (@uniformProb A _)
  funext w
  exact propext (h w)


theorem adaptive_probability_inequalities_proof :
    let a := upperRun false adaptiveData (exactRejectQ (1/20) adaptiveData)
    let a' := upperRun false adaptiveData (exactRejectQ (1/25) adaptiveData)
    let b := fun pool : Fin (2*testBudget 30+1) → Fin 1 → Assignment 30 15 =>
      upperRun false adaptiveData (approximateReject (1/20) (1/200) adaptiveData pool)
    uniformProb (fun pool => ∃ x, (b pool).value = some x ∧ x < 10) ≠
      uniformProb (fun pool =>
        let J := firstMismatch a.trace (b pool).trace
        J < a.trace.length ∧ (b pool).trace[J]!.2 = true) ∧
    uniformProb (fun pool => ∃ x, (b pool).value = some x ∧ 10 < x) ≠
      uniformProb (fun pool =>
        let J := firstMismatch a'.trace (b pool).trace
        J < a'.trace.length ∧ (b pool).trace[J]!.2 = false) := by
  dsimp only
  simp only [atr_run_exact, atr_run_low]
  have h0 := api5_probability_value_actual (0:Fin 4) (fun v => v.any (fun x => decide (x<10))) api5_below_certificate
  have h1 := api5_probability_actual (1:Fin 4) (api5_bad atr_trace_exact true)
    api5_bad_rejection_certificate
  have h2 := api5_probability_value_actual (2:Fin 4) (fun v => v.any (fun x => decide (10<x))) api5_above_certificate
  have h3 := api5_probability_actual (3:Fin 4) (api5_bad atr_trace_low false)
    api5_bad_acceptance_certificate
  let run := fun pool : Fin (2*testBudget 30+1) → api5_Atom =>
    upperRun false adaptiveData (approximateReject (1/20) (1/200) adaptiveData pool)
  constructor
  · apply ne_of_lt
    calc
      _ = (api5_weight (R := ℚ) api5_p api5_result_0:ℝ) :=
        (api5_uniform_congr (fun pool : Fin (2*testBudget 30+1) → api5_Atom => (api5_below_iff (run pool)).symm)).trans h0
      _ < (864:ℝ)/1000 := by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_lt (K := ℝ)).mpr api5_mass_bounds.1)
      _ < (948:ℝ)/1000 := by norm_num
      _ < (api5_weight (R := ℚ) api5_p api5_result_1:ℝ) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_lt (K := ℝ)).mpr api5_mass_bounds.2.1)
      _ = _ := h1.symm.trans (api5_uniform_congr (fun pool : Fin (2*testBudget 30+1) → api5_Atom => api5_bad_iff atr_trace_exact true (run pool)))
  · apply ne_of_gt
    calc
      _ = (api5_weight (R := ℚ) api5_p api5_result_3:ℝ) :=
        (api5_uniform_congr (fun pool : Fin (2*testBudget 30+1) → api5_Atom => (api5_bad_iff atr_trace_low false (run pool)).symm)).trans h3
      _ < (4:ℝ)/1000 := by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_lt (K := ℝ)).mpr api5_mass_bounds.2.2.2)
      _ < (30:ℝ)/1000 := by norm_num
      _ < (api5_weight (R := ℚ) api5_p api5_result_2:ℝ) := by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_lt (K := ℝ)).mpr api5_mass_bounds.2.2.1)
      _ = _ := h2.symm.trans (api5_uniform_congr (fun pool : Fin (2*testBudget 30+1) → api5_Atom => api5_above_iff (run pool)))

/-! The second-test aggregate counterexample. -/

/-- The aggregate event uses the table actually selected after the first
acceptance. Only coordinates zero and one of the pool enter the lower bound. -/
theorem aggregate_bound_counterexample_proof :
    let E := fun pool : Fin (2*testBudget 30+1) → Fin 5000 → Assignment 30 15 =>
      let b := upperRun false adaptiveData (approximateReject (1/20) (1/50) adaptiveData pool)
      2 ≤ b.trace.length ∧ b.trace[1]!.2 = true
    uniformProb E ≥ (4693104776190294207 : ℝ)/5012394999999664375 ∧
    (4693104776190294207 : ℝ)/5012394999999664375 > 9/10 ∧
    16*Real.exp (-4) < 48/103 ∧ (48/103 : ℝ) < 9/10 := by
  dsimp only
  refine ⟨?_,by norm_num,ab5_exp_bound,by norm_num⟩
  have hn : 0 ≤ uniformProb ab5_good1 :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    (4693104776190294207:ℝ)/5012394999999664375 =
        (1-(7904632:ℝ)/125104225)*(1-(154406032:ℝ)/280460272225) := by norm_num
    _ ≤ uniformProb ab5_good1*uniformProb ab5_good2 :=
      mul_le_mul ab5_first_batch_bound ab5_second_batch_bound (by norm_num) hn
    _ = uniformProb (fun pool : Fin (2*testBudget 30+1) → ab5_Batch =>
        ab5_good1 (pool 0) ∧ ab5_good2 (pool 1)) :=
      (ab5_probability_pair (0 : Fin (2*testBudget 30+1)) 1 (by decide +kernel)
        ab5_good1 ab5_good2).symm
    _ ≤ _ := ab5_probability_mono ab5_good_subset

end AronowAudit.P003.Wave1
