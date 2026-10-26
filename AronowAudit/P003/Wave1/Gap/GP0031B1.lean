import AronowAudit.P003.P003_Audit
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics



namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-! Parity convolution. A sum of two copies of ℤ makes the two
parity fibres explicit, including at negative integers. -/

def parity_convolution_sd_equiv (p : ℤ) : ℤ ⊕ ℤ ≃ ℤ where
  toFun := Sum.elim (fun k => p+2*k) (fun k => p+2*k+1)
  invFun := fun i => if (i-p)%2 = 0 then Sum.inl ((i-p)/2)
    else Sum.inr ((i-p)/2)
  left_inv := by
    intro t
    cases t with
    | inl k =>
      dsimp
      rw [if_pos (by omega)]
      congr 1 <;> omega
    | inr k =>
      dsimp
      rw [if_neg (by omega)]
      congr 1 <;> omega
  right_inv := by
    intro i
    dsimp
    split_ifs <;> dsimp <;> omega

lemma parity_convolution_sd_cells (f : ℤ → ℝ) (p k : ℤ) :
    paritySmooth f p (p+2*k) = f k/2 ∧
    paritySmooth f p (p+2*k+1) = f k/2 := by
  have h0 : (p+2*k-p)/2 = k := by omega
  have h1 : (p+2*k+1-p)/2 = k := by omega
  simp only [paritySmooth, h0, h1, and_self]

lemma parity_convolution_sd_mass_moment (f : ℤ → ℝ) (p : ℤ)
    (hf : IsMass f) :
    IsMass (paritySmooth f p) ∧
    (∑' i : ℤ, (i : ℝ)*paritySmooth f p i) =
      2*(∑' k : ℤ, (k : ℝ)*f k)+(p : ℝ)+1/2 := by
  rcases hf with ⟨hpos,hs,ht,hm⟩
  let e := parity_convolution_sd_equiv p
  let g := paritySmooth f p
  have hg0 : (fun k : ℤ => g (e (Sum.inl k))) = (fun k => f k/2) := by
    funext k
    exact (parity_convolution_sd_cells f p k).1
  have hg1 : (fun k : ℤ => g (e (Sum.inr k))) = (fun k => f k/2) := by
    funext k
    exact (parity_convolution_sd_cells f p k).2
  have hs0 : HasSum (fun k : ℤ => g (e (Sum.inl k))) (1/2) := by
    rw [hg0]
    simpa only [ht] using hs.hasSum.div_const 2
  have hs1 : HasSum (fun k : ℤ => g (e (Sum.inr k))) (1/2) := by
    rw [hg1]
    simpa only [ht] using hs.hasSum.div_const 2
  have hgs : HasSum g 1 := by
    apply e.hasSum_iff.mp
    convert (HasSum.sum (f := fun t : ℤ ⊕ ℤ => g (e t)) hs0 hs1) using 1 <;> first | rfl | norm_num
  let μ : ℝ := ∑' k : ℤ, (k : ℝ)*f k
  have hm0fun : (fun k : ℤ => (e (Sum.inl k) : ℝ)*g (e (Sum.inl k))) =
      (fun k : ℤ => (k : ℝ)*f k + (p : ℝ)/2*f k) := by
    funext k
    rw [show g (e (Sum.inl k)) = f k/2 from
      (parity_convolution_sd_cells f p k).1]
    change ((p+2*k : ℤ) : ℝ)*(f k/2) = _
    push_cast
    ring
  have hm1fun : (fun k : ℤ => (e (Sum.inr k) : ℝ)*g (e (Sum.inr k))) =
      (fun k : ℤ => (k : ℝ)*f k + ((p : ℝ)+1)/2*f k) := by
    funext k
    rw [show g (e (Sum.inr k)) = f k/2 from
      (parity_convolution_sd_cells f p k).2]
    change ((p+2*k+1 : ℤ) : ℝ)*(f k/2) = _
    push_cast
    ring
  have hm0 : HasSum (fun k : ℤ => (e (Sum.inl k) : ℝ)*g (e (Sum.inl k)))
      (μ+(p : ℝ)/2) := by
    rw [hm0fun]
    simpa only [ht,mul_one] using hm.hasSum.add (hs.hasSum.mul_left ((p : ℝ)/2))
  have hm1 : HasSum (fun k : ℤ => (e (Sum.inr k) : ℝ)*g (e (Sum.inr k)))
      (μ+((p : ℝ)+1)/2) := by
    rw [hm1fun]
    simpa only [ht,mul_one] using hm.hasSum.add (hs.hasSum.mul_left (((p : ℝ)+1)/2))
  have hgm : HasSum (fun i : ℤ => (i : ℝ)*g i) (2*μ+(p : ℝ)+1/2) := by
    apply e.hasSum_iff.mp
    convert (HasSum.sum (f := fun t : ℤ ⊕ ℤ => (e t : ℝ)*g (e t)) hm0 hm1) using 1 <;> first | rfl | ring
  exact ⟨⟨fun i => div_nonneg (hpos _) (by norm_num),
    hgs.summable,hgs.tsum_eq,hgm.summable⟩,hgm.tsum_eq⟩

lemma parity_convolution_sd_shape (f : ℤ → ℝ) (p c : ℤ)
    (hf : SDShape f c) : SDShape (paritySmooth f p) (2*p+2*c+1) := by
  constructor
  · intro i
    have hreflect : (2*p+2*c+1-i-p)/2 = c-(i-p)/2 := by omega
    simp only [paritySmooth,hreflect,hf.1]
  · intro i j hi hij
    have hc : c ≤ 2*((i-p)/2) := by omega
    have hq : (i-p)/2 ≤ (j-p)/2 := by omega
    exact div_le_div_of_nonneg_right (hf.2 _ _ hc hq) (by norm_num)

theorem parity_convolution_sd_proof (f : ℤ → ℝ) (hf : IsSD f) (p : ℤ)
    (hp : p = 0 ∨ p = 1) :
    IsSD (paritySmooth f p) ∧
    ∀ k, paritySmooth f p (p+2*k) = f k/2 ∧
      paritySmooth f p (p+2*k+1) = f k/2 := by
  rcases hf with ⟨hm,c,hmean,hshape⟩
  obtain ⟨hgm,hgmean⟩ := parity_convolution_sd_mass_moment f p hm
  refine ⟨⟨hgm,2*p+2*c+1,?_,parity_convolution_sd_shape f p c hshape⟩,
    parity_convolution_sd_cells f p⟩
  rw [hgmean,hmean]
  push_cast
  ring

/-! The finite weak-rank lemma. -/

lemma monte_rank_valid_uniform_reindex {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) :
    uniformProb (fun a => P (e a)) = uniformProb P := by
  classical
  have hc : (Finset.univ.filter (fun a => P (e a))).card =
      (Finset.univ.filter P).card := by
    let e' : {a // a ∈ Finset.univ.filter (fun a => P (e a))} ≃
        {b // b ∈ Finset.univ.filter P} :=
      { toFun := fun a => ⟨e a.val,by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp a.property).2⟩⟩
        invFun := fun b => ⟨e.symm b.val,by simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply] using (Finset.mem_filter.mp b.property).2⟩
        left_inv := by intro a; apply Subtype.ext; simp
        right_inv := by intro b; apply Subtype.ext; simp }
    simpa only [Fintype.card_coe] using Fintype.card_congr e'
  unfold uniformProb
  rw [hc,Fintype.card_congr e]

lemma monte_rank_valid_finite_rank {A : Type*} [Fintype A] [Nonempty A]
    (K : ℕ) (s : A → ℝ) (α : ℝ) (hα : 0 ≤ α) :
    uniformProb (fun x : Fin (K+1) → A =>
      (∑ j : Fin (K+1), if s (x 0) ≤ s (x j) then (1 : ℝ) else 0)/(K+1) ≤ α) ≤ α := by
  classical
  let L : ℝ := K+1
  let rank (x : Fin (K+1) → A) (i : Fin (K+1)) : ℝ :=
    ∑ j, if s (x i) ≤ s (x j) then 1 else 0
  let bad (x : Fin (K+1) → A) (i : Fin (K+1)) : Prop := rank x i ≤ α*L
  have hL : (0 : ℝ) < L := by dsimp [L]; positivity
  have hpoint (x : Fin (K+1) → A) :
      (∑ i, if bad x i then (1 : ℝ) else 0) ≤ α*L := by
    let B := Finset.univ.filter (bad x)
    by_cases hB : B.Nonempty
    · obtain ⟨i,hi,hmin⟩ := B.exists_min_image (fun i => s (x i)) hB
      have hle : (∑ j, if bad x j then (1 : ℝ) else 0) ≤ rank x i := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hb : bad x j
        · have hs : s (x i) ≤ s (x j) := hmin j (by simp [B,hb])
          simp only [if_pos hb,if_pos hs]
          exact le_rfl
        · simp only [if_neg hb]
          split_ifs <;> norm_num
      exact hle.trans ((Finset.mem_filter.mp hi).2)
    · have hn : ∀ i, ¬ bad x i := by
        intro i hi
        exact hB ⟨i,by simp [B,hi]⟩
      simp only [if_neg (hn _),Finset.sum_const_zero]
      exact mul_nonneg hα hL.le
  have hswap (i : Fin (K+1)) :
      (∑ x : Fin (K+1) → A, if bad x i then (1 : ℝ) else 0) =
        ∑ x : Fin (K+1) → A, if bad x 0 then (1 : ℝ) else 0 := by
    let σ := Equiv.swap i (0 : Fin (K+1))
    let e : (Fin (K+1) → A) ≃ (Fin (K+1) → A) :=
      { toFun := fun x j => x (σ j)
        invFun := fun x j => x (σ j)
        left_inv := by intro x; funext j; simp [σ]
        right_inv := by intro x; funext j; simp [σ] }
    have hr (x : Fin (K+1) → A) : rank (e x) 0 = rank x i := by
      dsimp [rank,e]
      simp only [show σ 0 = i by simp [σ]]
      exact Equiv.sum_comp σ (fun j => if s (x i) ≤ s (x j) then (1 : ℝ) else 0)
    calc
      _ = ∑ x, if bad (e x) 0 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [bad,hr]
      _ = _ := Equiv.sum_comp e (fun x => if bad x 0 then (1 : ℝ) else 0)
  have havg := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_comm] at havg
  simp_rw [hswap] at havg
  have hcard : (0 : ℝ) < Fintype.card (Fin (K+1) → A) := by
    exact_mod_cast Fintype.card_pos
  have hevent (x : Fin (K+1) → A) :
      ((∑ j, if s (x 0) ≤ s (x j) then (1 : ℝ) else 0)/(K+1) ≤ α) ↔ bad x 0 := by
    exact div_le_iff₀ hL
  simp only [hevent]
  unfold uniformProb
  rw [div_le_iff₀ hcard]
  have hcount : ((Finset.univ.filter (fun x => bad x 0)).card : ℝ) =
      ∑ x : Fin (K+1) → A, if bad x 0 then (1 : ℝ) else 0 := by simp
  rw [hcount]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at havg
  have hcancel := (mul_le_mul_iff_right₀ hL).mp (show
      (L : ℝ)*(∑ x : Fin (K+1) → A, if bad x 0 then (1 : ℝ) else 0) ≤
      (L : ℝ)*(α*(Fintype.card (Fin (K+1) → A) : ℝ)) by
        convert havg using 1 <;> dsimp [L] <;> push_cast <;> ring)
  exact hcancel

lemma monte_rank_valid_segment_card (n a b : ℕ) (h : a+b ≤ n) :
    (Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < a+b)).card = b := by
  classical
  let e : Fin b ≃ {i : Fin n // i ∈ Finset.univ.filter
      (fun i : Fin n => a ≤ i.val ∧ i.val < a+b)} :=
    { toFun := fun k => ⟨⟨a+k.val,by omega⟩,by
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        constructor <;> omega⟩
      invFun := fun i => ⟨i.val.val-a,by have := (Finset.mem_filter.mp i.property).2; omega⟩
      left_inv := by intro k; apply Fin.ext; dsimp; omega
      right_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        have := (Finset.mem_filter.mp i.property).2
        dsimp
        omega }
  simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr e).symm

lemma monte_rank_valid_canonical_type_cards (v : Counts) :
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (true,true))).card = v.a ∧
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (true,false))).card = v.b ∧
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (false,true))).card = v.c ∧
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (false,false))).card = v.d := by
  have hseg := monte_rank_valid_segment_card v.total
  have hp (i : Fin v.total) :
      (canonicalPair v i.val = (true,true) ↔ 0 ≤ i.val ∧ i.val < 0+v.a) ∧
      (canonicalPair v i.val = (true,false) ↔ v.a ≤ i.val ∧ i.val < v.a+v.b) ∧
      (canonicalPair v i.val = (false,true) ↔ v.a+v.b ≤ i.val ∧ i.val < (v.a+v.b)+v.c) ∧
      (canonicalPair v i.val = (false,false) ↔ v.a+v.b+v.c ≤ i.val ∧
        i.val < (v.a+v.b+v.c)+v.d) := by
    have hi := i.isLt
    dsimp [Counts.total] at hi
    unfold canonicalPair
    split_ifs <;> simp_all <;> omega
  simp_rw [(hp _).1,(hp _).2.1,(hp _).2.2.1,(hp _).2.2.2]
  exact ⟨hseg 0 v.a (by dsimp [Counts.total]; omega),
    hseg v.a v.b (by dsimp [Counts.total]; omega),
    hseg (v.a+v.b) v.c (by dsimp [Counts.total]; omega),
    hseg (v.a+v.b+v.c) v.d (by dsimp [Counts.total]; omega)⟩

lemma monte_rank_valid_pair_split {I : Type*} [DecidableEq I]
    (s : Finset I) (w : I → Bool × Bool) (b : Bool) :
    (s.filter (fun i => (w i).1 = b)).card =
      (s.filter (fun i => w i = (b,true))).card +
      (s.filter (fun i => w i = (b,false))).card ∧
    (s.filter (fun i => (w i).2 = b)).card =
      (s.filter (fun i => w i = (true,b))).card +
      (s.filter (fun i => w i = (false,b))).card := by
  classical
  constructor
  · have h := Finset.card_filter_add_card_filter_not
      (s := s.filter (fun i => (w i).1 = b)) (fun i => (w i).2 = true)
    have he (i : I) :
        ((w i).1 = b ∧ (w i).2 = true ↔ w i = (b,true)) ∧
        ((w i).1 = b ∧ ¬ (w i).2 = true ↔ w i = (b,false)) := by
      rcases w i with ⟨u,t⟩
      cases u <;> cases t <;> cases b <;> simp
    simpa only [Finset.filter_filter,(he _).1,(he _).2] using h.symm
  · have h := Finset.card_filter_add_card_filter_not
      (s := s.filter (fun i => (w i).2 = b)) (fun i => (w i).1 = true)
    have he (i : I) :
        ((w i).2 = b ∧ (w i).1 = true ↔ w i = (true,b)) ∧
        ((w i).2 = b ∧ ¬ (w i).1 = true ↔ w i = (false,b)) := by
      rcases w i with ⟨u,t⟩
      cases u <;> cases t <;> cases b <;> simp
    simpa only [Finset.filter_filter,(he _).1,(he _).2] using h.symm

lemma monte_rank_valid_observed_bridge (v : Counts) (z : Finset (Fin v.total)) :
    observed v (treatedCounts v z) = canonicalObserved v z := by
  classical
  let w := fun i : Fin v.total => canonicalPair v i.val
  have hcard := monte_rank_valid_canonical_type_cards v
  have hsub (b : Bool × Bool) :
      (z.filter (fun i => w i = b)).card ≤
        (Finset.univ.filter (fun i => w i = b)).card := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  have hqc : (z.filter (fun i => w i = (false,true))).card ≤ v.c := by
    simpa only [w, hcard.2.2.1] using hsub (false,true)
  have hqd : (z.filter (fun i => w i = (false,false))).card ≤ v.d := by
    simpa only [w, hcard.2.2.2] using hsub (false,false)
  have hcontrol (b : Bool × Bool) :
      ((Finset.univ \ z).filter (fun i => w i = b)).card =
        (Finset.univ.filter (fun i => w i = b)).card - (z.filter (fun i => w i = b)).card := by
    have he : (Finset.univ \ z).filter (fun i => w i = b) =
        (Finset.univ.filter (fun i => w i = b)) \ (z.filter (fun i => w i = b)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
      tauto
    rw [he,Finset.card_sdiff_of_subset (by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩)]
  have ht (b : Bool) :
      (Finset.univ.filter (fun i => i ∈ z ∧ (w i).1 = b)) =
        z.filter (fun i => (w i).1 = b) := by ext i; simp
  have hc (b : Bool) :
      (Finset.univ.filter (fun i => i ∉ z ∧ (w i).2 = b)) =
        (Finset.univ \ z).filter (fun i => (w i).2 = b) := by ext i; simp
  apply Counts.ext
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [ht true,(monte_rank_valid_pair_split z w true).1]
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [ht false,(monte_rank_valid_pair_split z w false).1]
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [hc true,(monte_rank_valid_pair_split (Finset.univ \ z) w true).2,
      hcontrol,hcontrol,hcard.1,hcard.2.2.1]
    dsimp [w] at *
    omega
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [hc false,(monte_rank_valid_pair_split (Finset.univ \ z) w false).2,
      hcontrol,hcontrol,hcard.2.1,hcard.2.2.2]
    dsimp [w] at *
    omega

theorem monte_rank_valid_proof (v : Counts) (m K : ℕ) (α : ℝ)
    (R : Counts → Counts → ℝ) (hm : 0 < m ∧ m < v.total) (hK : 0 < K)
    (hα : 0 ≤ α ∧ α ≤ 1) :
    uniformProb (fun ω : Assignment v.total m × (Fin K → Assignment v.total m) =>
      rankValue R (canonicalObserved v ω.1.val) v
        (fun i => treatedCounts v (ω.2 i).val) ≤ α) ≤ α := by
  classical
  let A := Assignment v.total m
  have hA : Nonempty A := by
    let z : Finset (Fin v.total) := Finset.univ.filter (fun i => i.val < m)
    have hz : z.card = m := by
      simpa [z] using monte_rank_valid_segment_card v.total 0 m (by omega)
    exact ⟨⟨z,hz⟩⟩
  letI : Nonempty A := hA
  let e : (Fin (K+1) → A) ≃ A × (Fin K → A) :=
    { toFun := fun x => (x 0,fun i => x i.succ)
      invFun := fun x => Fin.cons x.1 x.2
      left_inv := by intro x; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      right_inv := by intro x; cases x; rfl }
  let s : A → ℝ := fun z => |R (canonicalObserved v z.val) v|
  have he (x : Fin (K+1) → A) :
      rankValue R (canonicalObserved v (e x).1.val) v
        (fun i => treatedCounts v ((e x).2 i).val) =
      (∑ j : Fin (K+1), if s (x 0) ≤ s (x j) then (1 : ℝ) else 0)/(K+1) := by
    unfold rankValue
    simp_rw [monte_rank_valid_observed_bridge]
    rw [Fin.sum_univ_succ]
    simp [e,s]
  rw [← monte_rank_valid_uniform_reindex e]
  simp_rw [he]
  exact monte_rank_valid_finite_rank K s α hα.1

/-! A balanced family of first-query candidates. -/

lemma balanced_runtime_family_randomStates_iff (v q : Counts) (m : ℕ) :
    q ∈ randomStates v m ↔
      q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = m := by
  constructor
  · exact random_state_facts v m q
  · rintro ⟨ha,hb,hc,hd,ht⟩
    have htotal : q.a+q.b+q.c+q.d = m := ht
    simp only [randomStates,List.mem_flatMap,List.mem_filterMap,List.mem_range]
    refine ⟨q.a,?_,q.b,?_,q.c,?_,?_⟩
    · omega
    · omega
    · omega
    · have he : m-q.a-q.b-q.c = q.d := by omega
      simp only [he,if_pos hd]

lemma balanced_runtime_family_positive_multiplicity (v q : Counts) (m : ℕ)
    (hq : q ∈ randomStates v m) : 0 < multiplicity v q := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  unfold multiplicity
  simp only [binomial_eq_choose]
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
    (Nat.choose_pos ha) (Nat.choose_pos hb)) (Nat.choose_pos hc)) (Nat.choose_pos hd)

lemma balanced_runtime_family_arithmetic (r : ℕ) (hr : 4 ≤ r) :
    2^r = 4*(2^r/4) ∧ 2^r/2 = 2*(2^r/4) ∧
    2^r/4 = 2*((2^r/4)/2) ∧ 0 < 2^r/4 := by
  have he : r = 4+(r-4) := by omega
  have hn : 2^r = 16*2^(r-4) := by
    conv_lhs => rw [he,pow_add]
    norm_num
  have ht : 0 < 2^(r-4) := by positivity
  rw [hn]
  omega

lemma balanced_runtime_family_possible_zero (m : ℕ) (v : Counts) :
    Possible ⟨0,m,0,m⟩ v ↔
      v.a = 0 ∧ v.b ≤ m ∧ v.c ≤ m ∧ v.total = 2*m := by
  constructor
  · intro hv
    simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range] at hv
    rcases hv with ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩
    have hi0 : i = 0 := by omega
    have hk0 : k = 0 := by omega
    subst i
    subst k
    dsimp [Counts.total]
    omega
  · rintro ⟨ha,hb,hc,ht⟩
    simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range]
    refine ⟨0,by omega,v.c,by omega,0,by omega,v.b,by omega,?_⟩
    apply Counts.ext <;> dsimp <;> dsimp [Counts.total] at ht <;> omega

lemma balanced_runtime_family_firstOnLine (x : ℕ) (hx : 0 < x) (j : ℕ) :
    firstOnLine ⟨0,2*x,0,2*x⟩ (x : ℤ) j =
      if x ≤ j ∧ j ≤ 2*x then some ⟨0,j,j-x,4*x-2*j+x⟩ else none := by
  let o : Counts := ⟨0,2*x,0,2*x⟩
  let V : Counts := ⟨0,j,j-x,4*x-2*j+x⟩
  have hunique (u : Counts) (hu : Possible o u) (he : u.effect = (x : ℤ))
      (hj : u.a+u.b = j) : (x ≤ j ∧ j ≤ 2*x) ∧ u = V := by
    obtain ⟨ha,hb,hc,ht⟩ := (balanced_runtime_family_possible_zero (2*x) u).mp hu
    dsimp [Counts.effect] at he
    dsimp [Counts.total] at ht
    have hjx : x ≤ j ∧ j ≤ 2*x := by omega
    refine ⟨hjx,?_⟩
    apply Counts.ext <;> dsimp [V] <;> omega
  have hlegal (h : x ≤ j ∧ j ≤ 2*x) : V ∈ lineGroup o (x : ℤ) j := by
    have hp : Possible o V := by
      apply (balanced_runtime_family_possible_zero (2*x) V).mpr
      dsimp [V,Counts.total]
      omega
    simp only [lineGroup,List.mem_filter,decide_eq_true_eq]
    refine ⟨hp,?_,?_⟩
    · dsimp [V,Counts.effect]; omega
    · simp [V]
  change firstOnLine o (x : ℤ) j =
    if x ≤ j ∧ j ≤ 2*x then some V else none
  cases hs : firstOnLine o (x : ℤ) j with
  | none =>
    have hn : lineGroup o (x : ℤ) j = [] :=
      (minimum_b_spec _).1.mp hs
    have hnot : ¬ (x ≤ j ∧ j ≤ 2*x) := by
      intro h
      have hmem := hlegal h
      rw [hn] at hmem
      simp at hmem
    simp only [if_neg hnot]
  | some u =>
    have hu := first_on_line_spec o (x : ℤ) j u hs
    obtain ⟨hju,rfl⟩ := hunique u hu.1 hu.2.1 hu.2.2.1
    simp only [if_pos hju]

lemma balanced_runtime_family_flatMap_nil {A B : Type*} (l : List A)
    (F : A → List B) (h : ∀ a ∈ l, F a = []) : l.flatMap F = [] := by
  revert h
  induction l with
  | nil => intro h; rfl
  | cons a l ih =>
    intro h
    rw [List.flatMap_cons,h a (by simp),ih (fun b hb => h b (by simp [hb]))]
    rfl

lemma balanced_runtime_family_window {A : Type*} (V : ℕ → A) (a t : ℕ) :
    (List.range (a+t)).flatMap (fun j => if a ≤ j then [V j] else []) =
      (List.range t).map (fun j => V (a+j)) := by
  induction t with
  | zero =>
    simp only [Nat.add_zero,List.range_zero,List.map_nil]
    apply balanced_runtime_family_flatMap_nil
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [if_neg (by omega)]
  | succ t ih =>
    rw [show a+(t+1) = (a+t)+1 by omega,List.range_succ,List.flatMap_append,ih]
    simp [List.range_succ,show a ≤ a+t by omega]

/-- Ordered first-query candidates. -/
lemma balanced_runtime_family_zero_candidates (x : ℕ) (hx : 0 < x) :
    candidates ⟨0,2*x,0,2*x⟩ (x : ℤ) =
      (List.range (x+1)).map (fun t => (⟨0,x+t,t,4*x-2*(x+t)+x⟩ : Counts)) := by
  let V : ℕ → Counts := fun j => ⟨0,j,j-x,4*x-2*j+x⟩
  unfold candidates
  simp only [Counts.total, Nat.zero_add, Nat.add_zero, show 2*x+2*x = 4*x by omega]
  trans (List.range (4*x+1)).flatMap (fun j => if x ≤ j ∧ j ≤ 2*x then [V j] else [])
  · apply List.flatMap_congr
    intro j hj
    rw [balanced_runtime_family_firstOnLine x hx j]
    by_cases h : x ≤ j ∧ j ≤ 2*x
    · have hj0 : j ≠ 0 := by omega
      simp [h, hj0, V]
    · simp [h]
  change (List.range (4*x+1)).flatMap _ = _
  rw [show 4*x+1 = (2*x+1)+2*x by omega,List.range_add,List.flatMap_append]
  have htail : ((List.range (2*x)).map (fun t => (2*x+1)+t)).flatMap
      (fun j => if x ≤ j ∧ j ≤ 2*x then [V j] else []) = [] := by
    apply balanced_runtime_family_flatMap_nil
    intro j hj
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hj
    rw [if_neg (by omega)]
  rw [htail,List.append_nil]
  have hhead : (List.range (2*x+1)).flatMap
      (fun j => if x ≤ j ∧ j ≤ 2*x then [V j] else []) =
      (List.range (2*x+1)).flatMap (fun j => if x ≤ j then [V j] else []) := by
    apply List.flatMap_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    by_cases h : x ≤ j <;> simp [h,show j ≤ 2*x by omega]
  rw [hhead,show 2*x+1 = x+(x+1) by omega,balanced_runtime_family_window]
  apply List.map_congr_left
  intro t ht
  apply Counts.ext <;> dsimp [V] <;> omega

lemma balanced_runtime_family_assignment (n m x j : ℕ)
    (hn : n = 4*x) (hm : m = 2*x) (heven : x = 2*(x/2)) (hx : 0 < x)
    (hjlo : x ≤ j) (hjhi : j ≤ m) :
    let v : Counts := ⟨0,j,j-x,n-2*j+x⟩
    let q : Counts := ⟨0,j-x/2,0,m-j+x/2⟩
    q ∈ randomStates v m ∧ 0 < multiplicity v q ∧
      estimateQ (observed v q) = 1/4 ∧ tauQ v = 1/4 := by
  dsimp only
  let v : Counts := ⟨0,j,j-x,n-2*j+x⟩
  let q : Counts := ⟨0,j-x/2,0,m-j+x/2⟩
  have hmem : q ∈ randomStates v m := by
    apply (balanced_runtime_family_randomStates_iff v q m).mpr
    dsimp [v,q,Counts.total]
    omega
  have hobs : observed v q = ⟨j-x/2,m-j+x/2,j-x,m-j+x⟩ := by
    apply Counts.ext <;> dsimp [observed,v,q] <;> omega
  have htotal : v.total = n := by dsimp [v,Counts.total]; omega
  have heffect : v.effect = (x : ℤ) := by dsimp [v,Counts.effect]; omega
  have hmpos : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjhalf : ((j-x/2 : ℕ) : ℚ) = (j : ℚ)-(x/2 : ℕ) := by
    rw [Nat.cast_sub (by omega)]
  have hjx : ((j-x : ℕ) : ℚ) = (j : ℚ)-x := by rw [Nat.cast_sub hjlo]
  have hhalf : (x : ℚ) = 2*((x/2 : ℕ) : ℚ) := by exact_mod_cast heven
  have hmQ : (m : ℚ) = 2*(x : ℚ) := by exact_mod_cast hm
  have hnQ : (n : ℚ) = 4*(x : ℚ) := by exact_mod_cast hn
  refine ⟨hmem,balanced_runtime_family_positive_multiplicity v q m hmem,?_,?_⟩
  · rw [hobs]
    have ht : (j-x/2)+(m-j+x/2) = m := by omega
    have hc : (j-x)+(m-j+x) = m := by omega
    change ((j-x/2 : ℕ) : ℚ)/((j-x/2 : ℕ)+(m-j+x/2 : ℕ) : ℚ) -
      ((j-x : ℕ) : ℚ)/((j-x : ℕ)+(m-j+x : ℕ) : ℚ) = 1/4
    rw [← Nat.cast_add,← Nat.cast_add,ht,hc,hjhalf,hjx]
    field_simp [hmpos.ne']
    nlinarith
  · change (v.effect : ℚ)/(v.total : ℚ) = 1/4
    rw [htotal,heffect]
    push_cast
    apply (div_eq_iff hnpos.ne').mpr
    linarith

theorem balanced_runtime_family_proof (r : ℕ) (hr : 4 ≤ r) :
    let n : ℕ := 2^r
    let m : ℕ := n/2
    let x : ℕ := n/4
    let o : Counts := ⟨0,m,0,m⟩
    (candidates o (x : ℤ)).length = x+1 ∧
    ∀ j : ℕ, x ≤ j → j ≤ m →
      let v : Counts := ⟨0,j,j-x,n-2*j+x⟩
      let q : Counts := ⟨0,j-x/2,0,m-j+x/2⟩
      q ∈ randomStates v m ∧ 0 < multiplicity v q ∧
      estimateQ (observed v q) = 1/4 ∧ tauQ v = 1/4 := by
  dsimp only
  obtain ⟨hn,hm,heven,hx⟩ := balanced_runtime_family_arithmetic r hr
  constructor
  · rw [hm,balanced_runtime_family_zero_candidates _ hx,List.length_map,List.length_range]
  · intro j hjlo hjhi
    exact balanced_runtime_family_assignment (2^r) (2^r/2) (2^r/4) j
      hn hm heven hx hjlo hjhi



end AronowAudit.P003.Wave1
