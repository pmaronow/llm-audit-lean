import AronowAudit.P001.Wave1.Lib.TailA.MatchingLaw
import AronowAudit.P001.Wave1.Lib.TailA.ReuseProbability
import AronowAudit.P001.Wave1.Lib.TailA.ReuseDisintegration
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed

/-! Finite retained-neighbor bounds for aggregated original-label reuse. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace AronowAudit.P001.TailA

local instance instDecidableReuseMoments (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- The multiplicity of an original label, before aggregating its donor reuse. -/
def reuseOccupancy {n : ℕ} (a : Fin n → Fin n) (j : Fin n) : ℝ :=
  ((Finset.univ.filter (fun i => a i = j)).card : ℝ)

/-- A donor is available precisely when it responds and at least one copy is retained. -/
def reuseRetained {n : ℕ} (r : Fin n → Bool) (a : Fin n → Fin n) (j : Fin n) : Prop :=
  r j = true ∧ ∃ i, a i = j

/-- Original labels strictly between the central label and a query. -/
def reuseBetween {n : ℕ} (p : Fin n → ℝ) (j i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun l => min (p j) (p i) < p l ∧ p l < max (p j) (p i))

/-- The open interval contains no retained responding original label. -/
def reuseVoid {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j i : Fin n) : Prop :=
  ∀ l ∈ reuseBetween p j i, ¬reuseRetained r a l

theorem reuse_occupancy_nonneg {n : ℕ} (a : Fin n → Fin n) (j : Fin n) :
    0 ≤ reuseOccupancy a j := Nat.cast_nonneg _

theorem reuse_occupancy_sum {n : ℕ} (a : Fin n → Fin n) (f : Fin n → ℝ) :
    (∑ i, reuseOccupancy a i * f i) = ∑ t, f (a t) := by
  simp only [reuseOccupancy, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp [ite_mul]

theorem reuse_nearest_minimal {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (i j : Fin n) (h : nearestDonor p r i = some j) :
    r j = true ∧ ∀ l, r l = true → |p j-p i| ≤ |p l-p i| := by
  unfold nearestDonor at h
  split_ifs at h with hex
  have hj := Option.some.inj h
  simpa only [hj] using Classical.choose_spec hex

theorem reuse_between_distance {x y z : ℝ}
    (hz : min x y < z ∧ z < max x y) : |z-y| < |x-y| := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h] at hz
    rw [abs_of_nonpos (by linarith : z-y ≤ 0), abs_of_nonpos (by linarith : x-y ≤ 0)]
    linarith
  · rw [min_eq_right h, max_eq_left h] at hz
    rw [abs_of_nonneg (by linarith : 0 ≤ z-y), abs_of_nonneg (by linarith : 0 ≤ x-y)]
    linarith

/-- Any actual assignment excludes a retained donor strictly between its endpoints. -/
theorem reuse_assignment_void {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (t k j : Fin n)
    (hk : a k = j) (hd : nearestDonor (p ∘ a) (r ∘ a) t = some k) :
    reuseVoid p r a j (a t) := by
  intro l hl hret
  obtain ⟨hr,v,hv⟩ := hret
  have hmin := (reuse_nearest_minimal (p ∘ a) (r ∘ a) t k hd).2 v
  simp only [Function.comp_apply, hk, hv, hr, forall_const] at hmin
  have hb := (Finset.mem_filter.mp hl).2
  exact (not_lt_of_ge hmin) (reuse_between_distance hb)

theorem reuse_weight_rows {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (j : Fin n) :
    donorReuseWeight p r j = (if r j then 1 else 0) +
      ∑ i, if r i = false ∧ nearestDonor p r i = some j then 1 else 0 := by
  rw [Finset.sum_boole]
  cases hj : r j with
  | true => simp [donorReuseWeight, hj]
  | false =>
    have hempty : (Finset.univ.filter (fun i =>
        r i = false ∧ nearestDonor p r i = some j)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _ hi
      have h := (reuse_nearest_minimal p r i j hi.2).1
      simp [hj] at h
    simp [donorReuseWeight, hj, hempty]

/-- Domination by neighbor multiplicities up to the next retained donor on either side.
It includes absent central donors, omitted central labels, and donor-free samples. -/
theorem reuse_retained_neighbor_domination {n : ℕ} (p : Fin n → ℝ)
    (r : Fin n → Bool) (a : Fin n → Fin n) (j : Fin n) :
    bootstrapOriginalReuse p r a j ≤
      ∑ i, reuseOccupancy a i * (if reuseVoid p r a j i then 1 else 0) := by
  rw [reuse_occupancy_sum]
  unfold bootstrapOriginalReuse
  simp_rw [reuse_weight_rows]
  have hrow (k : Fin n) :
      (if a k = j then (if r (a k) then (1 : ℝ) else 0) +
        ∑ t, if r (a t) = false ∧ nearestDonor (p ∘ a) (r ∘ a) t = some k then 1 else 0
      else 0) =
      (if a k = j then (if r (a k) then 1 else 0) else 0) +
        ∑ t, if a k = j then
          (if r (a t) = false ∧ nearestDonor (p ∘ a) (r ∘ a) t = some k then 1 else 0)
          else 0 := by
    by_cases hk : a k = j <;> simp only [hk,ite_true,ite_false,Finset.sum_const_zero,add_zero]
  simp only [Function.comp_apply]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  cases hr : r (a t) with
  | true =>
    simp only [hr,Bool.true_eq_false,and_false,false_and,ite_false,ite_self,
      Finset.sum_const_zero,add_zero,ite_true]
    by_cases hat : a t = j
    · have hv : reuseVoid p r a j (a t) := by
        intro l hl
        have hb := (Finset.mem_filter.mp hl).2
        simp only [hat,min_self,max_self] at hb
        exact False.elim (lt_irrefl _ (hb.1.trans hb.2))
      rw [if_pos hat,if_pos hv]
    · simp only [if_neg hat]
      split_ifs <;> norm_num
  | false =>
    simp only [hr,Bool.false_eq_true,true_and,ite_false,ite_self,zero_add]
    cases hd : nearestDonor (p ∘ a) (r ∘ a) t with
    | none => simp; positivity
    | some k =>
      have heq : (fun l => if a l = j then
          if some k = some l then (1 : ℝ) else 0 else 0) =
          fun l => if l = k then (if a k = j then 1 else 0) else 0 := by
        funext l
        by_cases hl : l = k
        · subst l
          simp only [ite_true]
        · simp [hl,Ne.symm hl]
      rw [heq]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      by_cases hk : a k = j
      · rw [if_pos hk,if_pos (reuse_assignment_void p r a t k j hk hd)]
      · simp only [if_neg hk]
        split_ifs <;> norm_num

/-- The identity resample is the original-label reuse weight. -/
theorem reuse_identity {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (j : Fin n) :
    bootstrapOriginalReuse p r id j = donorReuseWeight p r j := by
  simp [bootstrapOriginalReuse, Function.comp_def]

theorem reuse_original_neighbor_domination {n : ℕ} (p : Fin n → ℝ)
    (r : Fin n → Bool) (j : Fin n) :
    donorReuseWeight p r j ≤
      ∑ i, if reuseVoid p r id j i then 1 else 0 := by
  have ho (i : Fin n) : reuseOccupancy (id : Fin n → Fin n) i = 1 := by
    have hf : Finset.univ.filter (fun t : Fin n => id t = i) = {i} := by ext t; simp
    simp only [reuseOccupancy, hf, Finset.card_singleton, Nat.cast_one]
  simpa only [reuse_identity,ho,one_mul] using reuse_retained_neighbor_domination p r id j

/-- Interval ranks increase strictly along either side of the central score. -/
theorem reuse_between_rank_strict {n : ℕ} (p : Fin n → ℝ) (j i l : Fin n)
    (h : (p j < p i ∧ p i < p l) ∨ (p l < p i ∧ p i < p j)) :
    (reuseBetween p j i).card < (reuseBetween p j l).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases h with h | h
    · simp only [min_eq_left h.1.le, max_eq_right h.1.le] at ht'
      simp only [min_eq_left (h.1.trans h.2).le, max_eq_right (h.1.trans h.2).le]
      exact ⟨ht'.1, ht'.2.trans h.2⟩
    · simp only [min_eq_right h.2.le, max_eq_left h.2.le] at ht'
      simp only [min_eq_right (h.1.trans h.2).le, max_eq_left (h.1.trans h.2).le]
      exact ⟨h.1.trans ht'.1, ht'.2⟩
  · intro heq
    have hi : i ∈ reuseBetween p j l := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases h with h | h
      · simpa only [min_eq_left (h.1.trans h.2).le, max_eq_right (h.1.trans h.2).le] using h
      · simpa only [min_eq_right (h.1.trans h.2).le, max_eq_left (h.1.trans h.2).le] using ⟨h.1,h.2⟩
    rw [← heq] at hi
    have hi' := (Finset.mem_filter.mp hi).2
    rcases h with h | h
    · simpa only [max_eq_right h.1.le, lt_self_iff_false, and_false] using hi'
    · simpa only [min_eq_right h.2.le, lt_self_iff_false, false_and] using hi'

/-- Distinct scores have distinct interval ranks on each fixed side. -/
theorem reuse_rank_injective {n : ℕ} (p : Fin n → ℝ) (hp : Function.Injective p)
    (j : Fin n) (side : Bool) :
    Set.InjOn (fun i => (reuseBetween p j i).card)
      {i | if side then p j < p i else p i < p j} := by
  intro i hi l hl heq
  change (reuseBetween p j i).card = (reuseBetween p j l).card at heq
  by_contra hne
  have hnep := fun h => hne (hp h)
  rcases lt_or_gt_of_ne hnep with h | h
  · have hr : (reuseBetween p j i).card < (reuseBetween p j l).card ∨
        (reuseBetween p j l).card < (reuseBetween p j i).card := by
      cases side with
      | true => exact Or.inl (reuse_between_rank_strict p j i l (Or.inl ⟨hi,h⟩))
      | false => exact Or.inr (reuse_between_rank_strict p j l i (Or.inr ⟨h,hl⟩))
    omega
  · have hr : (reuseBetween p j i).card < (reuseBetween p j l).card ∨
        (reuseBetween p j l).card < (reuseBetween p j i).card := by
      cases side with
      | true => exact Or.inr (reuse_between_rank_strict p j l i (Or.inl ⟨hl,h⟩))
      | false => exact Or.inl (reuse_between_rank_strict p j i l (Or.inr ⟨h,hi⟩))
    omega

/-- Each side contributes at most a geometric series; the central label contributes one. -/
theorem reuse_geometric_rank_sum {n : ℕ} (p : Fin n → ℝ) (hp : Function.Injective p)
    (j : Fin n) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑ i, q^(reuseBetween p j i).card) ≤ 1+2*(1-q)⁻¹ := by
  have hside (side : Bool) :
      (∑ i ∈ Finset.univ.filter (fun i => if side then p j < p i else p i < p j),
        q^(reuseBetween p j i).card) ≤ (1-q)⁻¹ := by
    let s := Finset.univ.filter (fun i => if side then p j < p i else p i < p j)
    have hinj : Set.InjOn (fun i => (reuseBetween p j i).card) s := by
      intro i hi l hl
      exact reuse_rank_injective p hp j side (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hl).2
    rw [← Finset.sum_image hinj]
    exact (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _
      (fun _ _ => pow_nonneg hq0 _) |>.trans_eq (tsum_geometric_of_lt_one hq0 hq1)
  have hsplit : (∑ i, q^(reuseBetween p j i).card) = 1+
      (∑ i ∈ Finset.univ.filter (fun i => p j < p i), q^(reuseBetween p j i).card)+
      (∑ i ∈ Finset.univ.filter (fun i => p i < p j), q^(reuseBetween p j i).card) := by
    have hpoint (i : Fin n) : q^(reuseBetween p j i).card =
        (if i = j then 1 else 0) +
        (if p j < p i then q^(reuseBetween p j i).card else 0)+
        (if p i < p j then q^(reuseBetween p j i).card else 0) := by
      by_cases hij : i = j
      · subst i
        have he : reuseBetween p j j = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro t _ ht
          simp only [min_self,max_self] at ht
          exact lt_irrefl _ (ht.1.trans ht.2)
        simp [he]
      · have hne : p i ≠ p j := fun h => hij (hp h)
        rcases lt_or_gt_of_ne hne with h | h
        · simp only [if_neg hij,if_pos h,if_neg (not_lt_of_ge h.le),zero_add,add_zero]
        · simp only [if_neg hij,if_pos h,if_neg (not_lt_of_ge h.le),zero_add,add_zero]
    calc
      _ = ∑ i : Fin n, ((if i = j then (1 : ℝ) else 0) +
        (if p j < p i then q^(reuseBetween p j i).card else 0)+
        (if p i < p j then q^(reuseBetween p j i).card else 0)) :=
          Finset.sum_congr rfl (fun i _ => hpoint i)
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_filter]

  rw [hsplit]
  have hr := hside true
  have hl := hside false
  simp only [ite_true, Bool.false_eq_true, ite_false] at hr hl
  linarith

theorem reuse_void_iff_no_retained {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j i : Fin n) :
    reuseVoid p r a j i ↔ reuseNoRetained (reuseBetween p j i) r a := by
  constructor
  · intro h l hl hr t ht
    exact h l hl ⟨hr,t,ht⟩
  · intro h l hl hr
    obtain ⟨hr,t,ht⟩ := hr
    exact h l hl hr t ht

theorem reuse_bootstrap_nonneg {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j : Fin n) : 0 ≤ bootstrapOriginalReuse p r a j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (matching_weight_bounds (p ∘ a) (r ∘ a) i).1
  · exact le_rfl

/-- Choose a geometric ratio at any fixed positive moment order. -/
theorem reuse_ratio_exists (k : ℕ) (hk : 0 < k) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ reuseRho ≤ q^(2*k) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hm : (1 : ℝ) ≤ 2*k := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  obtain ⟨hr0,hr1⟩ := reuse_rho_bounds
  let q : ℝ := 1-(1-reuseRho)/(2*k)
  have hdiv0 : 0 < (1-reuseRho)/(2*k) := div_pos (by linarith) (by positivity)
  have hdiv1 : (1-reuseRho)/(2*k) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  refine ⟨q,hq0,hq1,?_⟩
  have hb := one_add_mul_sub_le_pow (show -1 ≤ q by linarith) (2*k)
  have heq : 1+(2*k : ℕ)*(q-1) = reuseRho := by
    dsimp [q]
    push_cast
    field_simp
    <;> ring
  rwa [heq] at hb

/-- Conditional bootstrap moments, with no assumption on score spacing or support edges. -/
theorem reuse_conditional_bootstrap_moment {n : ℕ} (p : Fin n → ℝ)
    (hp : Function.Injective p) (θ : Fin n → unitInterval)
    (hθ : ∀ i, (1/4 : ℝ) ≤ θ i) (j : Fin n) (k : ℕ) (hk : 0 < k)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hrho : reuseRho ≤ q^(2*k)) :
    mean (ReuseResponseLaw θ) (fun r => mean (UniformResampling n)
      (fun a => (bootstrapOriginalReuse p r a j)^k)) ≤
      ((∑ r ∈ Finset.range (2*k+1), (Nat.stirlingSecond (2*k) r : ℝ))+1)*
        (1+2*(1-q)⁻¹)^k := by
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst n; exact Fin.elim0 j)
  let B : ℝ := ∑ r ∈ Finset.range (2*k+1), (Nat.stirlingSecond (2*k) r : ℝ)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  let μ := (ReuseResponseLaw θ).prod (UniformResampling n)
  let w (i : Fin n) : ℝ := q^(reuseBetween p j i).card
  let X (i : Fin n) (x : (Fin n → Bool) × (Fin n → Fin n)) : ℝ :=
    if reuseNoRetained (reuseBetween p j i) x.1 x.2 then reuseOccupancy x.2 i else 0
  have hw (i : Fin n) : 0 < w i := pow_pos hq0 _
  have hX (i : Fin n) (x) : 0 ≤ X i x := by
    dsimp [X]
    split_ifs
    · exact reuse_occupancy_nonneg _ _
    · exact le_rfl
  have hS : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) ⟨j,Finset.mem_univ _⟩
  have hm (i : Fin n) : (∫ x, X i x^k ∂μ) ≤ (B+1)*(w i)^k := by
    have hM : (∫ x, (reuseOccupancy x.2 i)^(2*k) ∂μ) ≤ B := by
      rw [show (∫ x, (reuseOccupancy x.2 i)^(2*k) ∂μ) =
        mean (UniformResampling n) (fun a => reuseOccupancy a i^(2*k)) from by
          dsimp [μ]
          rw [integral_prod _ Integrable.of_finite]
          simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,mean]]
      exact occupancy_moment_le_stirling hn i (2*k)
    have hvoid : (∫ x, (if reuseNoRetained (reuseBetween p j i) x.1 x.2 then (1 : ℝ) else 0) ∂μ) ≤
        ((w i)^k)^2 := by
      calc
        _ = mean (ReuseResponseLaw θ) (fun r => mean (UniformResampling n)
          (fun a => if reuseNoRetained (reuseBetween p j i) r a then 1 else 0)) :=
            integral_prod _ Integrable.of_finite
        _ ≤ reuseRho^(reuseBetween p j i).card := reuse_retained_void_bound hn θ hθ _
        _ ≤ ((w i)^k)^2 := by
          calc
            _ ≤ (q^(2*k))^(reuseBetween p j i).card :=
              pow_le_pow_left₀ reuse_rho_bounds.1.le hrho _
            _ = ((w i)^k)^2 := by dsimp [w]; simp only [← pow_mul]; congr 1; ring
    have hmask := reuse_masked_moment_le μ (fun x => reuseOccupancy x.2 i)
      (fun x => reuseNoRetained (reuseBetween p j i) x.1 x.2) k (pow_pos (hw i) k) hM hvoid
    have heq : (fun x => if reuseNoRetained (reuseBetween p j i) x.1 x.2
        then (reuseOccupancy x.2 i)^k else 0) = fun x => X i x^k := by
      funext x
      dsimp [X]
      split_ifs <;> simp only [zero_pow hk.ne']
    rw [heq] at hmask
    exact hmask.trans (by nlinarith [mul_nonneg (show 0 ≤ B+1 by linarith) (pow_nonneg (hw i).le k)])
  have hsum := reuse_weighted_sum_moment μ X w k hX hw hS hm
  have hdom (x : (Fin n → Bool) × (Fin n → Fin n)) :
      (bootstrapOriginalReuse p x.1 x.2 j)^k ≤ (∑ i, X i x)^k := by
    apply pow_le_pow_left₀ (reuse_bootstrap_nonneg _ _ _ _)
    convert reuse_retained_neighbor_domination p x.1 x.2 j using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [X]
    rw [reuse_void_iff_no_retained]
    split_ifs <;> simp
  calc
    _ = ∫ x, (bootstrapOriginalReuse p x.1 x.2 j)^k ∂μ :=
      (integral_prod _ Integrable.of_finite).symm
    _ ≤ ∫ x, (∑ i, X i x)^k ∂μ :=
      integral_mono Integrable.of_finite Integrable.of_finite hdom
    _ ≤ (B+1)*(∑ i, w i)^k := hsum
    _ ≤ (B+1)*(1+2*(1-q)⁻¹)^k := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact pow_le_pow_left₀ hS.le (reuse_geometric_rank_sum p hp j hq0.le hq1) k

/-- The same conditional bound for reuse in the original sample. -/
theorem reuse_conditional_original_moment {n : ℕ} (p : Fin n → ℝ)
    (hp : Function.Injective p) (θ : Fin n → unitInterval)
    (hθ : ∀ i, (1/4 : ℝ) ≤ θ i) (j : Fin n) (k : ℕ) (hk : 0 < k)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hrho : reuseRho ≤ q^(2*k)) :
    mean (ReuseResponseLaw θ) (fun r => (donorReuseWeight p r j)^k) ≤
      ((∑ r ∈ Finset.range (2*k+1), (Nat.stirlingSecond (2*k) r : ℝ))+1)*
        (1+2*(1-q)⁻¹)^k := by
  let B : ℝ := ∑ r ∈ Finset.range (2*k+1), (Nat.stirlingSecond (2*k) r : ℝ)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  let w (i : Fin n) : ℝ := q^(reuseBetween p j i).card
  let X (i : Fin n) (r : Fin n → Bool) : ℝ :=
    if reuseNoRetained (reuseBetween p j i) r id then 1 else 0
  have hw (i : Fin n) : 0 < w i := pow_pos hq0 _
  have hX (i : Fin n) (r) : 0 ≤ X i r := by dsimp [X]; split_ifs <;> norm_num
  have hS : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) ⟨j,Finset.mem_univ _⟩
  have hm (i : Fin n) : (∫ r, X i r^k ∂ReuseResponseLaw θ) ≤ (B+1)*(w i)^k := by
    have heq : (fun r => X i r^k) =
        fun r => if reuseNoRetained (reuseBetween p j i) r id then (1 : ℝ) else 0 := by
      funext r
      dsimp [X]
      split_ifs <;> simp [hk.ne']
    rw [heq]
    calc
      _ ≤ reuseRho^(reuseBetween p j i).card := reuse_original_void_bound θ hθ _
      _ ≤ ((w i)^k)^2 := by
        calc
          _ ≤ (q^(2*k))^(reuseBetween p j i).card :=
            pow_le_pow_left₀ reuse_rho_bounds.1.le hrho _
          _ = ((w i)^k)^2 := by dsimp [w]; simp only [← pow_mul]; congr 1; ring
      _ ≤ (w i)^k := by
        have htle : (w i)^k ≤ 1 := pow_le_one₀ (hw i).le
          (pow_le_one₀ hq0.le hq1.le)
        nlinarith [pow_nonneg (hw i).le k]
      _ ≤ (B+1)*(w i)^k := by nlinarith [mul_nonneg hB (pow_nonneg (hw i).le k)]
  have hdom (r : Fin n → Bool) : (donorReuseWeight p r j)^k ≤ (∑ i, X i r)^k := by
    apply pow_le_pow_left₀ (matching_weight_bounds p r j).1
    simpa only [X,reuse_void_iff_no_retained] using reuse_original_neighbor_domination p r j
  calc
    _ ≤ ∫ r, (∑ i, X i r)^k ∂ReuseResponseLaw θ :=
      integral_mono Integrable.of_finite Integrable.of_finite hdom
    _ ≤ (B+1)*(∑ i, w i)^k := reuse_weighted_sum_moment _ X w k hX hw hS hm
    _ ≤ (B+1)*(1+2*(1-q)⁻¹)^k := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact pow_le_pow_left₀ hS.le (reuse_geometric_rank_sum p hp j hq0.le hq1) k

/-- All fixed positive moments are bounded before integrating the scores.
The coefficient is uniform over finite distinct score vectors, including support edges. -/
theorem reuse_all_conditional_moments (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : Fin n → ℝ), Function.Injective p →
      ∀ (θ : Fin n → unitInterval), (∀ i, (1/4 : ℝ) ≤ θ i) → ∀ j : Fin n,
      mean (ReuseResponseLaw θ) (fun r => (donorReuseWeight p r j)^k) ≤ C ∧
      mean (ReuseResponseLaw θ) (fun r => mean (UniformResampling n)
        (fun a => (bootstrapOriginalReuse p r a j)^k)) ≤ C := by
  obtain ⟨q,hq0,hq1,hrho⟩ := reuse_ratio_exists k hk
  let B : ℝ := ∑ r ∈ Finset.range (2*k+1), (Nat.stirlingSecond (2*k) r : ℝ)
  refine ⟨(B+1)*(1+2*(1-q)⁻¹)^k,?_,?_⟩
  · have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hq : 0 < (1-q)⁻¹ := inv_pos.mpr (by linarith)
    positivity
  · intro n p hp θ hθ j
    exact ⟨reuse_conditional_original_moment p hp θ hθ j k hk hq0 hq1 hrho,
      reuse_conditional_bootstrap_moment p hp θ hθ j k hk hq0 hq1 hrho⟩

theorem reuse_W_norm {n : ℕ} (z : Fin n → MatchUnit) (j : Fin n) : ‖W z j‖ = W z j :=
  Real.norm_of_nonneg (matching_weight_bounds _ _ _).1

theorem reuse_U_norm {n : ℕ} (z : Fin n → MatchUnit) (a : Fin n → Fin n) (j : Fin n) :
    ‖U z a j‖ = U z a j := Real.norm_of_nonneg (reuse_bootstrap_nonneg _ _ _ _)

theorem reuse_W_moment_integrable {n : ℕ} (μ : Measure (Fin n → MatchUnit))
    [IsFiniteMeasure μ] (j : Fin n) (k : ℕ) : Integrable (fun z => (W z j)^k) μ := by
  simpa only [reuse_W_norm] using (matching_W_memLp μ j k).integrable_norm_pow'

theorem reuse_U_moment_integrable {n : ℕ} (μ : Measure (Fin n → MatchUnit))
    [IsFiniteMeasure μ] (a : Fin n → Fin n) (j : Fin n) (k : ℕ) :
    Integrable (fun z => (U z a j)^k) μ := by
  simpa only [reuse_U_norm] using (matching_U_memLp μ a j k).integrable_norm_pow'

/-- The response/design functional whose population expectation is the reuse moment. -/
def reuseBootstrapMoment {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (r : Fin n → Bool) (j : Fin n) : ℝ :=
  mean (UniformResampling n) (fun a => (bootstrapOriginalReuse p r a j)^k)

theorem reuse_bootstrap_moment_nonneg {n : ℕ} (k : ℕ) (p : Fin n → ℝ)
    (r : Fin n → Bool) (j : Fin n) : 0 ≤ reuseBootstrapMoment k p r j :=
  integral_nonneg (fun _ => pow_nonneg (reuse_bootstrap_nonneg _ _ _ _) k)

theorem reuse_bootstrap_moment_measurable {n : ℕ} (k : ℕ) (j : Fin n) :
    Measurable (fun z : Fin n → MatchUnit =>
      reuseBootstrapMoment k (fun i => (z i).1) (fun i => (z i).2.1) j) := by
  simp only [reuseBootstrapMoment,uniform_resampling_mean]
  exact (Finset.measurable_sum _ (fun a _ => (matching_U_measurable a j).pow_const k)).div_const _

theorem reuse_bootstrap_moment_integrable {n : ℕ} (μ : Measure (Fin n → MatchUnit))
    [IsFiniteMeasure μ] (k : ℕ) (j : Fin n) :
    Integrable (fun z : Fin n → MatchUnit =>
      reuseBootstrapMoment k (fun i => (z i).1) (fun i => (z i).2.1) j) μ := by
  simp only [reuseBootstrapMoment,uniform_resampling_mean]
  exact (integrable_finsetSum _ (fun a _ => reuse_U_moment_integrable μ a j k)).div_const _

/-- Uniform moments of original-label weights, under both actual iid and pinned experiments. -/
theorem uniform_reuse_moments (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (n : ℕ) (j : Fin n),
        mean (MatchProduct n) (fun z => (W z j)^k) ≤ C ∧
        mean (MatchProduct n) (fun z => mean (UniformResampling n)
          (fun a => (U z a j)^k)) ≤ C) ∧
      (∀ (n : ℕ) (p : ℝ), p ∈ Set.Icc (1/4 : ℝ) (3/4) →
        mean (MatchProduct n) (fun z => (W (pin n p z) 0)^k) ≤ C ∧
        mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
          (fun a => (U (pin n p z) a 0)^k)) ≤ C) := by
  obtain ⟨C,hC,hcond⟩ := reuse_all_conditional_moments k hk
  refine ⟨C,hC,?_,?_⟩
  · intro n j
    constructor
    · exact reuse_transfer_conditional_bound (fun p r => (donorReuseWeight p r j)^k)
        ((matching_W_measurable j).pow_const k) (reuse_W_moment_integrable _ j k)
        (fun p r => pow_nonneg (matching_weight_bounds p r j).1 k)
        (fun p hp θ hθ => (hcond n p hp θ hθ j).1)
    · exact reuse_transfer_conditional_bound (fun p r => reuseBootstrapMoment k p r j)
        (reuse_bootstrap_moment_measurable k j) (reuse_bootstrap_moment_integrable _ k j)
        (fun p r => reuse_bootstrap_moment_nonneg k p r j)
        (fun p hp θ hθ => (hcond n p hp θ hθ j).2)
  · intro n p _hp
    have hpin := reuse_pin_map_measurable n p
    constructor
    · have hmeas : Measurable (fun z => (W (pin n p z) 0)^k) :=
        ((matching_W_measurable 0).pow_const k).comp hpin
      have hint : Integrable (fun z => (W (pin n p z) 0)^k) (MatchProduct n) :=
        (integrable_map_measure ((matching_W_measurable 0).pow_const k).aestronglyMeasurable
          hpin.aemeasurable).mp (reuse_W_moment_integrable _ 0 k)
      have h := reuse_transfer_pinned_bound p (fun p r => (donorReuseWeight p r 0)^k)
        (by simpa only [W,reuse_pin_scores,reuse_pin_responses] using hmeas)
        (by simpa only [W,reuse_pin_scores,reuse_pin_responses] using hint)
        (fun p r => pow_nonneg (matching_weight_bounds p r 0).1 k)
        (fun p hp θ hθ => (hcond (n+1) p hp θ hθ 0).1)
      simpa only [W,reuse_pin_scores,reuse_pin_responses] using h
    · let F : (Fin (n+1) → MatchUnit) → ℝ := fun z =>
        reuseBootstrapMoment k (fun i => (z i).1) (fun i => (z i).2.1) 0
      have hFm : Measurable F := reuse_bootstrap_moment_measurable k 0
      have hmeas : Measurable (fun z => F (pin n p z)) := hFm.comp hpin
      have hint : Integrable (fun z => F (pin n p z)) (MatchProduct n) :=
        (integrable_map_measure hFm.aestronglyMeasurable hpin.aemeasurable).mp
          (reuse_bootstrap_moment_integrable _ k 0)
      have h := reuse_transfer_pinned_bound p (fun p r => reuseBootstrapMoment k p r 0)
        (by simpa only [F,reuse_pin_scores,reuse_pin_responses] using hmeas)
        (by simpa only [F,reuse_pin_scores,reuse_pin_responses] using hint)
        (fun p r => reuse_bootstrap_moment_nonneg k p r 0)
        (fun p hp θ hθ => (hcond (n+1) p hp θ hθ 0).2)
      simpa only [reuseBootstrapMoment,U,reuse_pin_scores,reuse_pin_responses] using h

/-- Convenient fourth-order specialization, including the pinned experiment. -/
theorem uniform_reuse_fourth_moments :
    ∃ C : ℝ, 0 < C ∧
      (∀ (n : ℕ) (j : Fin n),
        mean (MatchProduct n) (fun z => (W z j)^4) ≤ C ∧
        mean (MatchProduct n) (fun z => mean (UniformResampling n) (fun a => (U z a j)^4)) ≤ C) ∧
      (∀ (n : ℕ) (p : ℝ), p ∈ Set.Icc (1/4 : ℝ) (3/4) →
        mean (MatchProduct n) (fun z => (W (pin n p z) 0)^4) ≤ C ∧
        mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
          (fun a => (U (pin n p z) a 0)^4)) ≤ C) := uniform_reuse_moments 4 (by norm_num)


end AronowAudit.P001.TailA
