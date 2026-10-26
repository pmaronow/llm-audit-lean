import AronowAudit.P009.P009_OutcomeCompletion

namespace AronowAudit.P009.MixingBasics
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem probability_le_one {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) :
    prob P A ≤ 1 := by
  calc
    _ ≤ ∑ ω, P.mass ω := by
      unfold prob mean
      apply Finset.sum_le_sum
      intro ω _
      by_cases h : A ω <;> simp [h, P.nonneg ω]
    _ = 1 := P.total

theorem event_abs_le_one {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (S : Set A) (T : Set B) :
    |prob P (fun ω => X ω ∈ S ∧ Y ω ∈ T) -
      prob P (fun ω => X ω ∈ S) * prob P (fun ω => Y ω ∈ T)| ≤ 1 := by
  have h0 := probability_nonnegative P (fun ω => X ω ∈ S ∧ Y ω ∈ T)
  have h1 := probability_le_one P (fun ω => X ω ∈ S ∧ Y ω ∈ T)
  have ha0 := probability_nonnegative P (fun ω => X ω ∈ S)
  have ha1 := probability_le_one P (fun ω => X ω ∈ S)
  have hb0 := probability_nonnegative P (fun ω => Y ω ∈ T)
  have hb1 := probability_le_one P (fun ω => Y ω ∈ T)
  have hp0 := mul_nonneg ha0 hb0
  have hp1 : prob P (fun ω => X ω ∈ S) * prob P (fun ω => Y ω ∈ T) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hb0]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem alpha_set_nonempty {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) :
    Set.Nonempty {r | ∃ (S : Set A) (T : Set B),
      r = |prob P (fun ω => X ω ∈ S ∧ Y ω ∈ T) -
        prob P (fun ω => X ω ∈ S) * prob P (fun ω => Y ω ∈ T)|} := by
  exact ⟨_, ∅, ∅, rfl⟩

theorem alpha_le_of_event_bound {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (C : ℝ)
    (h : ∀ (S : Set A) (T : Set B),
      |prob P (fun ω => X ω ∈ S ∧ Y ω ∈ T) -
        prob P (fun ω => X ω ∈ S) * prob P (fun ω => Y ω ∈ T)| ≤ C) :
    alpha P X Y ≤ C := by
  apply csSup_le (alpha_set_nonempty P X Y)
  rintro _ ⟨S,T,rfl⟩
  exact h S T

theorem alpha_le_one {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) : alpha P X Y ≤ 1 :=
  alpha_le_of_event_bound P X Y 1 (event_abs_le_one P X Y)

theorem event_abs_le_alpha {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (S : Set A) (T : Set B) :
    |prob P (fun ω => X ω ∈ S ∧ Y ω ∈ T) -
      prob P (fun ω => X ω ∈ S) * prob P (fun ω => Y ω ∈ T)| ≤ alpha P X Y := by
  apply le_csSup
  · exact ⟨1, by rintro _ ⟨U,V,rfl⟩; exact event_abs_le_one P X Y U V⟩
  · exact ⟨S,T,rfl⟩

theorem alpha_nonnegative {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) : 0 ≤ alpha P X Y :=
  (abs_nonneg _).trans (event_abs_le_alpha P X Y ∅ ∅)

theorem covariance_indicator_le_alpha {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (S : Set A) (T : Set B) :
    cov P (fun ω => if X ω ∈ S then 1 else 0)
      (fun ω => if Y ω ∈ T then 1 else 0) ≤ alpha P X Y := by
  rw [BernoulliCompletion.covariance_product_formula]
  have he : mean P (fun ω => (if X ω ∈ S then 1 else 0) *
      (if Y ω ∈ T then 1 else 0)) = prob P (fun ω => X ω ∈ S ∧ Y ω ∈ T) := by
    unfold prob
    congr 1
    funext ω
    by_cases h : X ω ∈ S <;> by_cases h' : Y ω ∈ T <;> simp [h,h']
  rw [he]
  exact (le_abs_self _).trans (event_abs_le_alpha P X Y S T)

theorem three_error_transfer (pab pa pb qa qb δ : ℝ)
    (hpa : 0 ≤ pa ∧ pa ≤ 1) (hqb : 0 ≤ qb ∧ qb ≤ 1)
    (hjoint : |pab-qa*qb| ≤ δ) (ha : |pa-qa| ≤ δ) (hb : |pb-qb| ≤ δ) :
    |pab-pa*pb| ≤ 3*δ := by
  have hp : |qa*qb-pa*pb| ≤ 2*δ := by
    calc
      _ = |(qa-pa)*qb+pa*(qb-pb)| := by congr 1; ring
      _ ≤ |(qa-pa)*qb|+|pa*(qb-pb)| := abs_add_le _ _
      _ = |pa-qa| *qb+pa*|pb-qb| := by
        rw [abs_mul,abs_mul,abs_of_nonneg hpa.1,abs_of_nonneg hqb.1,
          abs_sub_comm qa pa,abs_sub_comm qb pb]
      _ ≤ δ*qb+pa*δ := add_le_add (mul_le_mul_of_nonneg_right ha hqb.1)
        (mul_le_mul_of_nonneg_left hb hpa.1)
      _ ≤ 2*δ := by
        have hd : 0 ≤ δ := (abs_nonneg _).trans ha
        nlinarith [mul_nonneg hd (sub_nonneg.mpr hpa.2),
          mul_nonneg hd (sub_nonneg.mpr hqb.2)]
  calc
    _ = |(pab-qa*qb)+(qa*qb-pa*pb)| := by congr 1; ring
    _ ≤ |pab-qa*qb|+|qa*qb-pa*pb| := abs_add_le _ _
    _ ≤ δ+2*δ := add_le_add hjoint hp
    _ = _ := by ring

theorem corrected_full_pair_mixing_bound_completed {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (b : Bool) (k : ℝ) (hk : 0 < k) :
    k^2/(n:ℝ)^2 * (∑ i, ∑ j, cov E.design
      (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)) ≤
      k^2/(n:ℝ)^2 * (∑ i, ∑ j, alpha E.design (fun z => z i) (fun z => z j)) ∧
    k^2/(n:ℝ)^2 * (∑ i, ∑ j, alpha E.design (fun z => z i) (fun z => z j)) ≤
      k^2*dAvg E/(n:ℝ) + k^2/(n:ℝ)^2 *
        (∑ i, ∑ j, (1-d E i j)*alpha E.design (fun z => z i) (fun z => z j)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hc : 0≤k^2/(n:ℝ)^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · apply mul_le_mul_of_nonneg_left _ hc
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa only [Set.mem_singleton_iff] using
      covariance_indicator_le_alpha E.design (fun z=>z i) (fun z=>z j) {b} {b}
  · have hs : (∑i,∑j,d E i j)=(n:ℝ)*dAvg E := by
      unfold dAvg degree
      field_simp
    have hpoint (i j : Fin n) : alpha E.design (fun z=>z i) (fun z=>z j) ≤
        d E i j+(1-d E i j)*alpha E.design (fun z=>z i) (fun z=>z j) := by
      by_cases h : Dependent E i j
      · simpa [d,h] using alpha_le_one E.design (fun z=>z i) (fun z=>z j)
      · simp [d,h]
    calc
      _ ≤ k^2/(n:ℝ)^2 * (∑i,∑j,(d E i j+(1-d E i j)*alpha E.design (fun z=>z i) (fun z=>z j))) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hpoint i j))
      _ = _ := by
        simp_rw [Finset.sum_add_distrib]
        rw [mul_add,hs]
        congr 1
        field_simp
theorem sum_incoming {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    (∑ i, (incoming E i : ℝ)) = (n:ℝ)*C1 E := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have he (i : Fin n) : (incoming E i:ℝ) = ∑j,I E j i := by
    simp only [incoming,I,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp_rw [he]
  rw [Finset.sum_comm]
  unfold C1 outgoing
  field_simp

theorem exceptional_pair_finite_counts_completed {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (u : ℝ) (hu : 0 < u) :
    (∀ i, (incoming E i : ℝ) ≤ degree E i) ∧
    (∑ i, (incoming E i : ℝ)) = (n:ℝ)*C1 E ∧ C1 E ≤ dAvg E ∧
    (((Finset.univ.filter (fun ij : Fin n × Fin n =>
      u < incoming E ij.1 ∨ u < incoming E ij.2)).card : ℕ) : ℝ) ≤
        2*(n:ℝ)^2*dAvg E/u ∧
    ((Finset.univ.filter (fun ij : Fin n × Fin n => d E ij.1 ij.2 = 0)).card : ℝ) =
      (n:ℝ)^2-(n:ℝ)*dAvg E := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hs := sum_incoming hn E
  have hC : C1 E ≤ dAvg E := (le_max_left _ _).trans (interference_count_bounds hn E).1
  have hds : (∑i,∑j,d E i j)=(n:ℝ)*dAvg E := by
    unfold dAvg degree
    field_simp
  refine ⟨OutcomeCompletion.incoming_le_degree E,hs,hC,?_,?_⟩
  · have hp (i j : Fin n) :
        (if u < incoming E i ∨ u < incoming E j then u else 0) ≤
          (incoming E i:ℝ)+incoming E j := by
      split_ifs with h
      · rcases h with h|h <;> linarith [Nat.cast_nonneg (α:=ℝ) (incoming E i),Nat.cast_nonneg (α:=ℝ) (incoming E j)]
      · positivity
    have hc : u*((Finset.univ.filter (fun ij : Fin n × Fin n =>
        u < incoming E ij.1 ∨ u < incoming E ij.2)).card:ℝ) ≤
        2*(n:ℝ)*(∑i,(incoming E i:ℝ)) := by
      calc
        _ = ∑i,∑j,if u < incoming E i ∨ u < incoming E j then u else 0 := by
          simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
          rw [Finset.mul_sum,Fintype.sum_prod_type]
          simp only [mul_ite,mul_one,mul_zero]
        _ ≤ ∑i,∑j,((incoming E i:ℝ)+incoming E j) :=
          Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hp i j))
        _ = _ := by
          simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
          rw [←Finset.mul_sum]
          ring
    rw [hs] at hc
    apply (le_div_iff₀ hu).mpr
    have hb := mul_le_mul_of_nonneg_left hC (by positivity : 0≤2*(n:ℝ)^2)
    nlinarith
  · calc
      _ = ∑i,∑j,(1-d E i j) := by
        simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : Dependent E i j <;> simp [d,h]
      _ = _ := by
        simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [hds]
        ring

end
end AronowAudit.P009.MixingBasics

namespace AronowAudit.P009
open Filter
open scoped Topology BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
theorem exceptional_pair_finite_counts {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (u : ℝ) (hu : 0 < u) :
    (∀ i, (incoming E i : ℝ) ≤ degree E i) ∧
    (∑ i, (incoming E i : ℝ)) = (n:ℝ)*C1 E ∧ C1 E ≤ dAvg E ∧
    (((Finset.univ.filter (fun ij : Fin n × Fin n =>
      u < incoming E ij.1 ∨ u < incoming E ij.2)).card : ℕ) : ℝ) ≤
        2*(n:ℝ)^2*dAvg E/u ∧
    ((Finset.univ.filter (fun ij : Fin n × Fin n => d E ij.1 ij.2 = 0)).card : ℝ) =
      (n:ℝ)^2-(n:ℝ)*dAvg E := by
  exact MixingBasics.exceptional_pair_finite_counts_completed hn E u hu

theorem corrected_full_pair_mixing_bound {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (b : Bool) (k : ℝ) (hk : 0 < k) :
    k^2/(n:ℝ)^2 * (∑ i, ∑ j, cov E.design
      (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)) ≤
      k^2/(n:ℝ)^2 * (∑ i, ∑ j, alpha E.design (fun z => z i) (fun z => z j)) ∧
    k^2/(n:ℝ)^2 * (∑ i, ∑ j, alpha E.design (fun z => z i) (fun z => z j)) ≤
      k^2*dAvg E/(n:ℝ) + k^2/(n:ℝ)^2 *
        (∑ i, ∑ j, (1-d E i j)*alpha E.design (fun z => z i) (fun z => z j)) := by
  exact MixingBasics.corrected_full_pair_mixing_bound_completed hn E b k hk

end
end AronowAudit.P009
