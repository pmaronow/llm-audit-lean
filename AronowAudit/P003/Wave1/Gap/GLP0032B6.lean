import AronowAudit.P003.Wave1.Gap.GP0032B2
import AronowAudit.P003.Wave1.Gap.GP0031B1
import AronowAudit.P003.Wave1.Gap.GLP0032B1
import AronowAudit.P003.Wave1.Gap.GLP0031B1
import AronowAudit.P003.Wave1.Gap.GP0031B3b
import AronowAudit.P003.Wave1.Gap.GP0031B2
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Pi

/-!
P003-T7: corrected Monte Carlo interval inclusions.

Finite-product freshness uses an explicit nonnegative error bound.
The actual selected-test union combines iid Hoeffding bounds, chronological
causality and the two-endpoint budget. A discrete second-difference comparison
and the proved discordant shape theorem establish fixed-effect candidate
reduction, including the concordant-base exception. One-sided search invariants,
outcome reflection and averaging over the observed assignment establish the inclusions.
-/

namespace AronowAudit.P003.Wave1

open scoped BigOperators NNReal ENNReal
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-! Finite averaging and finite-product freshness with a nonnegative error bound. -/

noncomputable def GLP0032B6_avg {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

lemma GLP0032B6_prob_avg {A : Type*} [Fintype A] (P : A → Prop) :
    uniformProb P = GLP0032B6_avg (fun a => if P a then 1 else 0) := by
  simp [uniformProb, GLP0032B6_avg, Finset.sum_boole]

lemma GLP0032B6_avg_reindex {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    GLP0032B6_avg (fun a => f (e a)) = GLP0032B6_avg f := by
  unfold GLP0032B6_avg
  rw [e.sum_comp, Fintype.card_congr e]

lemma GLP0032B6_avg_mono {A : Type*} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a ≤ g a) : GLP0032B6_avg f ≤ GLP0032B6_avg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma GLP0032B6_avg_const {A : Type*} [Fintype A] [Nonempty A] (x : ℝ) :
    GLP0032B6_avg (fun _ : A => x) = x := by
  simp [GLP0032B6_avg, mul_div_cancel_left₀, Fintype.card_ne_zero]

lemma GLP0032B6_avg_sum {A I : Type*} [Fintype A] [Fintype I] (f : I → A → ℝ) :
    GLP0032B6_avg (fun a => ∑ i, f i a) = ∑ i, GLP0032B6_avg (f i) := by
  unfold GLP0032B6_avg
  rw [Finset.sum_comm, Finset.sum_div]

lemma GLP0032B6_avg_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A × B → ℝ) :
    GLP0032B6_avg f = GLP0032B6_avg (fun b => GLP0032B6_avg (fun a => f (a,b))) := by
  simp only [GLP0032B6_avg, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type, ← Finset.sum_div, div_div]
  rw [Finset.sum_comm]

lemma GLP0032B6_prob_mono {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : uniformProb P ≤ uniformProb Q := by
  rw [GLP0032B6_prob_avg, GLP0032B6_prob_avg]
  apply GLP0032B6_avg_mono
  intro a
  by_cases hp : P a
  · simp [hp, h a hp]
  · simp only [if_neg hp]
    split_ifs <;> norm_num

lemma GLP0032B6_prob_union {A I : Type*} [Fintype A] [Fintype I]
    (E : I → A → Prop) :
    uniformProb (fun a => ∃ i, E i a) ≤ ∑ i, uniformProb (E i) := by
  simp_rw [GLP0032B6_prob_avg]
  rw [← GLP0032B6_avg_sum]
  apply GLP0032B6_avg_mono
  intro a
  by_cases h : ∃ i, E i a
  · obtain ⟨i,hi⟩ := h
    rw [if_pos ⟨i,hi⟩]
    exact (show (1 : ℝ) = if E i a then 1 else 0 by simp [hi]).le.trans
      (Finset.single_le_sum (f := fun i => if E i a then (1 : ℝ) else 0)
        (by intro j _; split_ifs <;> norm_num) (Finset.mem_univ i))
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

/-- A slot's choice is fixed by its previously read coordinates. The bad
fraction is assumed only for active choices; an inactive choice contributes
zero, so the explicit nonnegativity premise is necessary. -/
lemma GLP0032B6_fresh_slot {B T : Type*} [Fintype B] [Nonempty B]
    (L : ℕ) (i : Fin L) (select : (Fin L → B) → Option T)
    (bad : T → B → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (hprefix : ∀ p q, (∀ j : Fin L, j.val < i.val → p j = q j) → select p = select q)
    (hbad : ∀ p t, select p = some t → uniformProb (bad t) ≤ δ) :
    uniformProb (fun p => ∃ t, select p = some t ∧ bad t (p i)) ≤ δ := by
  let e := Equiv.funSplitAt i B
  let b₀ : B := Classical.choice (inferInstance : Nonempty B)
  have hsel (b : B) (q : {j : Fin L // j ≠ i} → B) :
      select (e.symm (b,q)) = select (e.symm (b₀,q)) := by
    apply hprefix
    intro j hj
    have hji : j ≠ i := by intro h; subst j; omega
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hji]
  rw [GLP0032B6_prob_avg]
  have hreindex := GLP0032B6_avg_reindex e.symm
    (fun p => if ∃ t, select p = some t ∧ bad t (p i) then (1 : ℝ) else 0)
  calc
    _ = GLP0032B6_avg (fun bq => if ∃ t, select (e.symm bq) = some t ∧
        bad t (e.symm bq i) then (1 : ℝ) else 0) := by
      convert hreindex.symm using 1
      simp only [GLP0032B6_avg]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> rfl
    _ = GLP0032B6_avg (fun q => GLP0032B6_avg (fun b => if ∃ t,
        select (e.symm (b,q)) = some t ∧ bad t (e.symm (b,q) i) then (1 : ℝ) else 0)) :=
      GLP0032B6_avg_prod _
    _ ≤ GLP0032B6_avg (fun _ : {j : Fin L // j ≠ i} → B => δ) := by
      apply GLP0032B6_avg_mono
      intro q
      simp_rw [hsel]
      cases hs : select (e.symm (b₀,q)) with
      | none => simpa [hs, GLP0032B6_avg] using hδ
      | some t =>
        simpa [hs, e, Equiv.funSplitAt, Equiv.piSplitAt, ← GLP0032B6_prob_avg] using hbad (e.symm (b₀,q)) t hs
    _ = δ := GLP0032B6_avg_const δ

/-- Finite-product freshness with explicit `0 ≤ δ` and no upper bound on δ.
Inactive slots are permitted. -/
lemma GLP0032B6_finite_product_freshness {B T : Type*} [Fintype B] [Nonempty B]
    (L D : ℕ) (hDL : D ≤ L)
    (select : Fin D → (Fin L → B) → Option T) (bad : T → B → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hprefix : ∀ i p q, (∀ j : Fin L, j.val < i.val → p j = q j) →
      select i p = select i q)
    (hbad : ∀ i p t, select i p = some t → uniformProb (bad t) ≤ δ) :
    uniformProb (fun p => ∃ i : Fin D, ∃ t,
      select i p = some t ∧ bad t (p ⟨i.val, lt_of_lt_of_le i.isLt hDL⟩)) ≤ (D : ℝ)*δ := by
  calc
    _ ≤ ∑ i : Fin D, uniformProb (fun p => ∃ t,
        select i p = some t ∧ bad t (p ⟨i.val, lt_of_lt_of_le i.isLt hDL⟩)) :=
      GLP0032B6_prob_union _
    _ ≤ ∑ _ : Fin D, δ := by
      apply Finset.sum_le_sum
      intro i _
      exact GLP0032B6_fresh_slot L _ (select i) bad δ hδ (hprefix i) (hbad i)
    _ = (D : ℝ)*δ := by simp

/-! The finite iid concentration bridge. -/

open MeasureTheory ProbabilityTheory

lemma GLP0032B6_uniform_real {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (P : A → Prop) :
    (PMF.uniformOfFintype A).toMeasure.real {a | P a} = uniformProb P := by
  rw [measureReal_def, PMF.toMeasure_uniformOfFintype_apply _ (Set.to_countable _).measurableSet]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, uniformProb, Fintype.card_subtype, Set.mem_setOf_eq]

lemma GLP0032B6_uniform_integral {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) :
    ∫ a, f a ∂(PMF.uniformOfFintype A).toMeasure = GLP0032B6_avg f := by
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, GLP0032B6_avg, div_eq_mul_inv,
    ← Finset.sum_mul, mul_comm]

lemma GLP0032B6_uniform_pi {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (K : ℕ) :
    Measure.pi (fun _ : Fin K => (PMF.uniformOfFintype A).toMeasure) =
      (PMF.uniformOfFintype (Fin K → A)).toMeasure := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.inv_pow]

/-- Hoeffding for the mean of iid bounded finite observations, with the exact
constant `exp (-2*K*ε^2)`. -/
lemma GLP0032B6_finite_hoeffding_upper {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, f a ∈ Set.Icc (0 : ℝ) 1)
    (K : ℕ) (hK : 0 < K) (ε : ℝ) (hε : 0 ≤ ε) :
    uniformProb (fun x : Fin K → A =>
      ε ≤ (∑ i, f (x i))/(K : ℝ) - GLP0032B6_avg f) ≤ Real.exp (-2*(K : ℝ)*ε^2) := by
  let instGLP0032B6MeasurableSpace : MeasurableSpace A := ⊤
  let μ := (PMF.uniformOfFintype A).toMeasure
  let ν := Measure.pi (fun _ : Fin K => μ)
  let X : Fin K → (Fin K → A) → ℝ := fun i x => f (x i) - GLP0032B6_avg f
  have hμ : IsProbabilityMeasure μ := inferInstance
  have hν : IsProbabilityMeasure ν := inferInstance
  have hm : Measurable f := measurable_of_finite f
  have hi : iIndepFun (fun (i : Fin K) (x : Fin K → A) => f (x i)) ν :=
    iIndepFun_pi (fun _ => hm.aemeasurable)
  have hind : iIndepFun X ν := hi.comp (fun _ y => y - GLP0032B6_avg f)
    (fun _ => by fun_prop)
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin K)), HasSubgaussianMGF (X i) (1/4) ν := by
    intro i _
    have hm' : AEMeasurable (fun x : Fin K → A => f (x i)) ν :=
      (hm.comp (measurable_pi_apply i)).aemeasurable
    have hb : ∀ᵐ x ∂ν, f (x i) ∈ Set.Icc (0 : ℝ) 1 := Filter.Eventually.of_forall (fun x => hf (x i))
    have hmean : ∫ x : Fin K → A, f (x i) ∂ν = GLP0032B6_avg f := by
      rw [show ν = Measure.pi (fun _ : Fin K => μ) from rfl,
        integral_comp_eval hm.aestronglyMeasurable]
      exact GLP0032B6_uniform_integral f
    have hh := hasSubgaussianMGF_of_mem_Icc hm' hb
    rw [hmean] at hh
    convert hh using 1 <;> norm_num
  have hh := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hs
    (show 0 ≤ (K : ℝ)*ε by positivity)
  have hexp : -((K : ℝ)*ε)^2 / (2*((∑ _ : Fin K, (1/4 : ℝ≥0)) : ℝ)) =
      -2*(K : ℝ)*ε^2 := by
    have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    field_simp [hk]
    <;> ring
  simp only [NNReal.coe_sum] at hh
  rw [hexp] at hh
  have hset : {x : Fin K → A | (K : ℝ)*ε ≤ ∑ i, X i x} =
      {x | ε ≤ (∑ i, f (x i))/(K : ℝ) - GLP0032B6_avg f} := by
    have hk : (0 : ℝ) < K := by exact_mod_cast hK
    ext x
    simp only [Set.mem_setOf_eq, X, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [le_sub_iff_add_le, le_div_iff₀ hk]
    constructor <;> intro h <;> nlinarith
  rw [hset, show ν = (PMF.uniformOfFintype (Fin K → A)).toMeasure from GLP0032B6_uniform_pi K,
    GLP0032B6_uniform_real] at hh
  exact hh

lemma GLP0032B6_avg_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    GLP0032B6_avg (fun a => f a - g a) = GLP0032B6_avg f - GLP0032B6_avg g := by
  simp [GLP0032B6_avg, Finset.sum_sub_distrib, sub_div]

lemma GLP0032B6_finite_hoeffding_lower {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, f a ∈ Set.Icc (0 : ℝ) 1)
    (K : ℕ) (hK : 0 < K) (ε : ℝ) (hε : 0 ≤ ε) :
    uniformProb (fun x : Fin K → A =>
      ε ≤ GLP0032B6_avg f - (∑ i, f (x i))/(K : ℝ)) ≤ Real.exp (-2*(K : ℝ)*ε^2) := by
  have h := GLP0032B6_finite_hoeffding_upper (fun a => 1 - f a)
    (fun a => ⟨by linarith [(hf a).2], by linarith [(hf a).1]⟩) K hK ε hε
  have hmean : GLP0032B6_avg (fun a => 1 - f a) = 1 - GLP0032B6_avg f := by
    rw [GLP0032B6_avg_sub, GLP0032B6_avg_const]
  have heq (x : Fin K → A) :
      (∑ i, (1 - f (x i)))/(K : ℝ) - GLP0032B6_avg (fun a => 1 - f a) =
        GLP0032B6_avg f - (∑ i, f (x i))/(K : ℝ) := by
    rw [hmean, Finset.sum_sub_distrib, sub_div]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [div_self (by exact_mod_cast hK.ne')]
    ring
  simpa only [heq] using h

/-- The canonical assignment indicators have the p-value as their mean. -/
lemma GLP0032B6_tail_probability (v o : Counts) :
    uniformProb (fun z : Assignment v.total (o.a+o.b) =>
      (deviationNumerator v (canonicalObserved v z.val) (o.a+o.b)).natAbs ≥
        (deviationNumerator v o (o.a+o.b)).natAbs) = (pValue v o : ℝ) := by
  let w : PotentialTable v.total := fun i => canonicalPair v i.val
  have hw : tableCounts w = v := by
    have h := monte_rank_valid_canonical_type_cards v
    exact Counts.ext h.1 h.2.1 h.2.2.1 h.2.2.2
  let E : Counts → Prop := fun q =>
    (deviationNumerator v (observed v q) (o.a+o.b)).natAbs ≥
      (deviationNumerator v o (o.a+o.b)).natAbs
  have h := neyman_event_pushforward w v hw (o.a+o.b) E
  have hobs (z : Assignment v.total (o.a+o.b)) :
      observed v (neyman_treated w z.val) = canonicalObserved v z.val :=
    monte_rank_valid_observed_bridge v z.val
  have hevent : (fun z : Assignment v.total (o.a+o.b) => E (neyman_treated w z.val)) =
      (fun z => (deviationNumerator v (canonicalObserved v z.val) (o.a+o.b)).natAbs ≥
        (deviationNumerator v o (o.a+o.b)).natAbs) := by
    funext z
    simp only [E, hobs z]
  rw [← hevent, h]
  simp only [designProb, E, pValue, tailCount, Rat.cast_div, Rat.cast_natCast, binomial_eq_choose]
  congr 1
  rw [Nat.cast_list_sum]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  split_ifs <;> simp

/-! One-sided deterministic implications use only the decisions actually
present in the trace. -/

lemma GLP0032B6_runTests_no_bad_rejection (reject : Counts → ℕ → Bool)
    (idx : ℕ) (xs : List Counts) (P : Counts → Prop)
    (hgood : ∀ v, (v,true) ∈ (runTests reject idx xs).trace → ¬P v)
    (hw : ∃ v ∈ xs, P v) : (runTests reject idx xs).compatible = true := by
  induction xs generalizing idx with
  | nil => simp at hw
  | cons v vs ih =>
    by_cases hr : reject v idx = true
    · have hv : ¬P v := hgood v (by simp [runTests, hr])
      have ht : ∀ w, (w,true) ∈ (runTests reject (idx+1) vs).trace → ¬P w := by
        intro w hw
        exact hgood w (by simp only [runTests, hr, ite_true, List.mem_cons]; exact Or.inr hw)
      obtain ⟨w,hw,hP⟩ := hw
      have hvs : w ∈ vs := by
        rcases List.mem_cons.mp hw with he | hm
        · subst w; exact (hv hP).elim
        · exact hm
      simpa [runTests, hr] using ih (idx+1) ht ⟨w,hvs,hP⟩
    · simp [runTests, hr]

lemma GLP0032B6_runTests_no_bad_acceptance (reject : Counts → ℕ → Bool)
    (idx : ℕ) (xs : List Counts) (P : Counts → Prop)
    (hgood : ∀ v, (v,false) ∈ (runTests reject idx xs).trace → P v)
    (hc : (runTests reject idx xs).compatible = true) : ∃ v ∈ xs, P v := by
  induction xs generalizing idx with
  | nil => simp [runTests] at hc
  | cons v vs ih =>
    by_cases hr : reject v idx = true
    · have ht : ∀ w, (w,false) ∈ (runTests reject (idx+1) vs).trace → P w := by
        intro w hw
        exact hgood w (by simp only [runTests, hr, ite_true, List.mem_cons]; exact Or.inr hw)
      have hc' : (runTests reject (idx+1) vs).compatible = true := by
        simpa [runTests, hr] using hc
      obtain ⟨w,hw,hP⟩ := ih (idx+1) ht hc'
      exact ⟨w,List.mem_cons_of_mem _ hw,hP⟩
    · exact ⟨v,by simp,hgood v (by simp [runTests,hr])⟩

/-- Any accepted candidate is a possible table on the queried effect line. -/
lemma GLP0032B6_candidate_facts (o v : Counts) (x : ℤ) (hv : v ∈ candidates o x) :
    Possible o v ∧ v.effect = x := by
  simp only [candidates, List.mem_flatMap] at hv
  obtain ⟨j,hj,hv⟩ := hv
  cases he : firstOnLine o x j with
  | none => simp [he] at hv
  | some u =>
    have hu := first_on_line_spec o x j u he
    rw [he] at hv
    dsimp only at hv
    split_ifs at hv with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨hu.1,hu.2.1⟩
      · refine ⟨h.2.2.2.2,?_⟩
        have hx : x = 0 := by simpa [Counts.effect, h.1, h.2.1] using hu.2.1.symm
        simp [Counts.effect, hx]
    · simp only [List.mem_singleton] at hv
      subst v
      exact ⟨hu.1,hu.2.1⟩

lemma GLP0032B6_search_no_bad_rejection (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (P : Counts → Prop) (a b r : ℤ) (idx : ℕ)
    (hab : a < b) (hw : (b-a).toNat ≤ fuel+1) (hrb : r < b)
    (hcover : ∀ c, a < c → c < b → c ≤ r → ∃ v ∈ candidates o c, P v)
    (hgood : ∀ v, (v,true) ∈ (adaptiveSearch fuel true o k₁ k₂ reject a b idx).trace → ¬P v) :
    ∃ x, (adaptiveSearch fuel true o k₁ k₂ reject a b idx).value = some x ∧ r ≤ x := by
  induction fuel generalizing a b idx with
  | zero =>
    have hs : b ≤ a+1 := by omega
    exact ⟨a,by simp [adaptiveSearch,hs],by omega⟩
  | succ fuel ih =>
    rw [T7_search_succ] at hgood ⊢
    by_cases hs : b ≤ a+1
    · exact ⟨a,by simp [hs],by omega⟩
    · simp only [if_neg hs] at hgood ⊢
      let c := (a+b)/2
      let q := runTests reject idx (candidates o c)
      have hac : a < c := by dsimp [c]; omega
      have hcb : c < b := by dsimp [c]; omega
      by_cases hq : q.compatible = true
      · change ∃ x, (if q.compatible then
            adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
          else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).value = some x ∧ r ≤ x
        rw [if_pos hq]
        have hg : ∀ v, (v,true) ∈ (adaptiveSearch fuel true o k₁ k₂ reject c b q.idx).trace → ¬P v := by
          intro v hv
          apply hgood v
          change (v,true) ∈ q.trace ++ (if q.compatible then
            adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
            else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).trace
          rw [if_pos hq]
          exact List.mem_append_right _ hv
        exact ih c b q.idx hcb (by omega) hrb
          (fun d hcd hdb hdr => hcover d (by omega) hdb hdr) hg
      · change ∃ x, (if q.compatible then
            adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
          else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).value = some x ∧ r ≤ x
        rw [if_neg hq]
        have hqgood : ∀ v, (v,true) ∈ q.trace → ¬P v := by
          intro v hv
          apply hgood v
          exact List.mem_append_left _ hv
        have hrc : r < c := by
          by_contra h
          have hc := GLP0032B6_runTests_no_bad_rejection reject idx (candidates o c) P
            hqgood (hcover c hac hcb (by omega))
          exact hq hc
        have hg : ∀ v, (v,true) ∈ (adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).trace → ¬P v := by
          intro v hv
          apply hgood v
          change (v,true) ∈ q.trace ++ (if q.compatible then
            adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
            else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).trace
          rw [if_neg hq]
          exact List.mem_append_right _ hv
        exact ih a c q.idx hac (by omega) hrc
          (fun d had hdc hdr => hcover d had (by omega) hdr) hg

lemma GLP0032B6_search_no_bad_acceptance (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (P : Counts → Prop) (a b r : ℤ) (idx : ℕ)
    (hab : a < b) (hw : (b-a).toNat ≤ fuel+1) (har : a ≤ r)
    (hsound : ∀ c, a < c → c < b → ∀ v ∈ candidates o c, P v → c ≤ r)
    (hgood : ∀ v, (v,false) ∈ (adaptiveSearch fuel true o k₁ k₂ reject a b idx).trace → P v) :
    ∃ x, (adaptiveSearch fuel true o k₁ k₂ reject a b idx).value = some x ∧ x ≤ r := by
  induction fuel generalizing a b idx with
  | zero =>
    have hs : b ≤ a+1 := by omega
    exact ⟨a,by simp [adaptiveSearch,hs],har⟩
  | succ fuel ih =>
    rw [T7_search_succ] at hgood ⊢
    by_cases hs : b ≤ a+1
    · exact ⟨a,by simp [hs],har⟩
    · simp only [if_neg hs] at hgood ⊢
      let c := (a+b)/2
      let q := runTests reject idx (candidates o c)
      have hac : a < c := by dsimp [c]; omega
      have hcb : c < b := by dsimp [c]; omega
      by_cases hq : q.compatible = true
      · change ∃ x, (if q.compatible then
            adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
          else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).value = some x ∧ x ≤ r
        rw [if_pos hq]
        have hqgood : ∀ v, (v,false) ∈ q.trace → P v := by
          intro v hv
          exact hgood v (List.mem_append_left _ hv)
        obtain ⟨v,hv,hP⟩ := GLP0032B6_runTests_no_bad_acceptance reject idx
          (candidates o c) P hqgood hq
        have hcr : c ≤ r := hsound c hac hcb v hv hP
        have hg : ∀ v, (v,false) ∈ (adaptiveSearch fuel true o k₁ k₂ reject c b q.idx).trace → P v := by
          intro v hv
          apply hgood v
          change (v,false) ∈ q.trace ++ (if q.compatible then
            adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
            else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).trace
          rw [if_pos hq]
          exact List.mem_append_right _ hv
        exact ih c b q.idx hcb (by omega) hcr
          (fun d hcd hdb v hv hP => hsound d (by omega) hdb v hv hP) hg
      · change ∃ x, (if q.compatible then
            adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
          else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).value = some x ∧ x ≤ r
        rw [if_neg hq]
        have hg : ∀ v, (v,false) ∈ (adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).trace → P v := by
          intro v hv
          apply hgood v
          change (v,false) ∈ q.trace ++ (if q.compatible then
            adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
            else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).trace
          rw [if_neg hq]
          exact List.mem_append_right _ hv
        exact ih a c q.idx hac (by omega) har
          (fun d had hdc v hv hP => hsound d had (by omega) v hv hP) hg

/-! Actual fixed-table Monte Carlo errors. -/

lemma GLP0032B6_assignment_nonempty (n m : ℕ) (hmn : m ≤ n) :
    Nonempty (Assignment n m) := by
  apply Fintype.card_pos_iff.mp
  rw [neyman_assignment_card]
  exact Nat.choose_pos hmn

lemma GLP0032B6_monteMean_real {n K : ℕ} (v o : Counts)
    (draws : Fin K → Assignment n (o.a+o.b)) :
    (monteMean v o (fun i => (draws i).val) : ℝ) =
      (∑ i : Fin K, if
        (deviationNumerator v (canonicalObserved v (draws i).val) (o.a+o.b)).natAbs ≥
          (deviationNumerator v o (o.a+o.b)).natAbs then (1 : ℝ) else 0)/(K : ℝ) := by
  simp [monteMean]

lemma GLP0032B6_finite_bernoulli_hoeffding (v o : Counts) (K : ℕ)
    (hmn : o.a+o.b ≤ v.total) (hK : 0 < K) (ε : ℝ) (hε : 0 ≤ ε) :
    uniformProb (fun x : Fin K → Assignment v.total (o.a+o.b) =>
      ε ≤ (monteMean v o (fun i => (x i).val) : ℝ) - (pValue v o : ℝ)) ≤
        Real.exp (-2*(K : ℝ)*ε^2) ∧
    uniformProb (fun x : Fin K → Assignment v.total (o.a+o.b) =>
      ε ≤ (pValue v o : ℝ) - (monteMean v o (fun i => (x i).val) : ℝ)) ≤
        Real.exp (-2*(K : ℝ)*ε^2) := by
  let instGLP0032B6AssignmentNonempty := GLP0032B6_assignment_nonempty v.total (o.a+o.b) hmn
  let f : Assignment v.total (o.a+o.b) → ℝ := fun z => if
    (deviationNumerator v (canonicalObserved v z.val) (o.a+o.b)).natAbs ≥
      (deviationNumerator v o (o.a+o.b)).natAbs then 1 else 0
  have hf (z) : f z ∈ Set.Icc (0 : ℝ) 1 := by dsimp [f]; split_ifs <;> norm_num
  have hmean : GLP0032B6_avg f = (pValue v o : ℝ) := by
    rw [← GLP0032B6_tail_probability, GLP0032B6_prob_avg]
    unfold GLP0032B6_avg
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    dsimp only [f]
    split_ifs <;> rfl
  have hupper := GLP0032B6_finite_hoeffding_upper f hf K hK ε hε
  have hlower := GLP0032B6_finite_hoeffding_lower f hf K hK ε hε
  simp only [hmean] at hupper hlower
  simp_rw [GLP0032B6_monteMean_real]
  exact ⟨hupper,hlower⟩

/-! Causality at a chronological slot: its selected table is fixed before
reading that slot, while a run already finished before it is entirely fixed. -/

def GLP0032B6_peek (xs : List (Counts × Bool)) (n : ℕ) : Option Counts :=
  xs[n]?.map Prod.fst

lemma GLP0032B6_peek_append_left (xs ys : List (Counts × Bool)) (n : ℕ)
    (h : n < xs.length) : GLP0032B6_peek (xs++ys) n = GLP0032B6_peek xs n := by
  simp [GLP0032B6_peek, List.getElem?_append_left h]

lemma GLP0032B6_peek_append_right (xs ys : List (Counts × Bool)) (n : ℕ)
    (h : xs.length ≤ n) : GLP0032B6_peek (xs++ys) n = GLP0032B6_peek ys (n-xs.length) := by
  simp [GLP0032B6_peek, List.getElem?_append_right h]

lemma GLP0032B6_peek_isSome (xs : List (Counts × Bool)) (n : ℕ) :
    (GLP0032B6_peek xs n).isSome = true ↔ n < xs.length := by
  simp [GLP0032B6_peek]

lemma GLP0032B6_runTests_prefix (r s : Counts → ℕ → Bool) (xs : List Counts)
    (idx n : ℕ) (hagree : ∀ v j, j < idx+n → r v j = s v j) :
    GLP0032B6_peek (runTests r idx xs).trace n =
      GLP0032B6_peek (runTests s idx xs).trace n ∧
    ((runTests r idx xs).trace.length ≤ n → runTests r idx xs = runTests s idx xs) := by
  induction xs generalizing idx n with
  | nil => simp [runTests]
  | cons v vs ih =>
    cases n with
    | zero =>
      constructor
      · simp only [runTests]
        split_ifs <;> rfl
      · intro h
        simp only [runTests] at h
        split_ifs at h <;> simp at h
    | succ n =>
      have he : r v idx = s v idx := hagree v idx (by omega)
      by_cases hr : r v idx = true
      · have hs : s v idx = true := he ▸ hr
        have hi := ih (idx+1) n (fun v j hj => hagree v j (by omega))
        constructor
        · simpa only [runTests, if_pos hr, if_pos hs, GLP0032B6_peek,
            List.getElem?_cons_succ] using hi.1
        · intro h
          have hlen : (runTests r (idx+1) vs).trace.length ≤ n := by
            simpa only [runTests, if_pos hr, List.length_cons, Nat.add_le_add_iff_right] using h
          simp only [runTests, if_pos hr, if_pos hs, hi.2 hlen]
      · have hs : ¬s v idx = true := by simpa only [← he] using hr
        simp [runTests,hr,hs]

lemma GLP0032B6_search_prefix (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (r s : Counts → ℕ → Bool) (a b : ℤ) (idx n : ℕ)
    (hagree : ∀ v j, j < idx+n → r v j = s v j) :
    GLP0032B6_peek (adaptiveSearch fuel true o k₁ k₂ r a b idx).trace n =
      GLP0032B6_peek (adaptiveSearch fuel true o k₁ k₂ s a b idx).trace n ∧
    ((adaptiveSearch fuel true o k₁ k₂ r a b idx).trace.length ≤ n →
      adaptiveSearch fuel true o k₁ k₂ r a b idx = adaptiveSearch fuel true o k₁ k₂ s a b idx) := by
  induction fuel generalizing a b idx n with
  | zero =>
    by_cases h : b ≤ a+1 <;> simp [adaptiveSearch,h]
  | succ fuel ih =>
    rw [T7_search_succ, T7_search_succ]
    by_cases hs : b ≤ a+1
    · simp [hs]
    simp only [if_neg hs]
    let c := (a+b)/2
    let q := runTests r idx (candidates o c)
    let p := runTests s idx (candidates o c)
    let rr := if q.compatible then adaptiveSearch fuel true o k₁ k₂ r c b q.idx
      else adaptiveSearch fuel true o k₁ k₂ r a c q.idx
    let ss := if p.compatible then adaptiveSearch fuel true o k₁ k₂ s c b p.idx
      else adaptiveSearch fuel true o k₁ k₂ s a c p.idx
    change GLP0032B6_peek (q.trace++rr.trace) n = GLP0032B6_peek (p.trace++ss.trace) n ∧
      ((q.trace++rr.trace).length ≤ n →
        (⟨rr.value,q.trace++rr.trace⟩ : EndpointResult) = ⟨ss.value,p.trace++ss.trace⟩)
    have hq := GLP0032B6_runTests_prefix r s (candidates o c) idx n hagree
    by_cases hqn : q.trace.length ≤ n
    · have he : q = p := hq.2 hqn
      have hidx : q.idx + (n-q.trace.length) = idx+n := by
        have hcost := (T7_runTests_cost r (candidates o c) idx).1
        change q.idx = idx+q.trace.length at hcost
        omega
      have hr : GLP0032B6_peek rr.trace (n-q.trace.length) =
          GLP0032B6_peek ss.trace (n-q.trace.length) ∧
          (rr.trace.length ≤ n-q.trace.length → rr = ss) := by
        have hi1 := ih c b q.idx (n-q.trace.length) (fun v j hj => hagree v j (by omega))
        have hi2 := ih a c q.idx (n-q.trace.length) (fun v j hj => hagree v j (by omega))
        dsimp only [rr,ss]
        rw [← he]
        by_cases hc : q.compatible = true
        · simpa only [if_pos hc] using hi1
        · simpa only [if_neg hc] using hi2
      constructor
      · rw [GLP0032B6_peek_append_right _ _ n hqn,
          GLP0032B6_peek_append_right _ _ n (by simpa only [← he] using hqn)]
        simpa only [← he] using hr.1
      · intro h
        have hlen : rr.trace.length ≤ n-q.trace.length := by
          rw [List.length_append] at h
          omega
        rw [← he, hr.2 hlen]
    · have hqt : n < q.trace.length := by omega
      have hpt : n < p.trace.length := by
        apply (GLP0032B6_peek_isSome p.trace n).mp
        rw [← hq.1]
        exact (GLP0032B6_peek_isSome q.trace n).mpr hqt
      constructor
      · rw [GLP0032B6_peek_append_left _ _ n hqt, GLP0032B6_peek_append_left _ _ n hpt]
        exact hq.1
      · intro h
        rw [List.length_append] at h
        omega

lemma GLP0032B6_upperRun_prefix (o : Counts) (r s : Counts → ℕ → Bool) (idx n : ℕ)
    (hagree : ∀ v j, j < idx+n → r v j = s v j) :
    GLP0032B6_peek (upperRun true o r idx).trace n =
      GLP0032B6_peek (upperRun true o s idx).trace n ∧
    ((upperRun true o r idx).trace.length ≤ n → upperRun true o r idx = upperRun true o s idx) :=
  GLP0032B6_search_prefix _ _ _ _ _ _ _ _ _ _ hagree

/-- Chronological table selection across both endpoint runs, tagged by the
observation against which it is tested. The second run starts after the first. -/
def GLP0032B6_selected (o : Counts) (r s : Counts → ℕ → Bool) (i : ℕ) :
    Option (Counts × Counts) :=
  let hi := upperRun true o r
  let lo := upperRun true (complementObserved o) s hi.trace.length
  if i < hi.trace.length then (GLP0032B6_peek hi.trace i).map (fun v => (o,v))
  else (GLP0032B6_peek lo.trace (i-hi.trace.length)).map (fun v => (complementObserved o,v))

lemma GLP0032B6_selected_prefix (o : Counts) (r s r' s' : Counts → ℕ → Bool) (i : ℕ)
    (hr : ∀ v j, j < i → r v j = r' v j)
    (hs : ∀ v j, j < i → s v j = s' v j) :
    GLP0032B6_selected o r s i = GLP0032B6_selected o r' s' i := by
  let hi := upperRun true o r
  let hi' := upperRun true o r'
  have h := GLP0032B6_upperRun_prefix o r r' 0 i (by simpa using hr)
  by_cases hiend : hi.trace.length ≤ i
  · have he : hi = hi' := h.2 hiend
    have he' : (upperRun true o r).trace.length = (upperRun true o r').trace.length :=
      congrArg (fun z : EndpointResult => z.trace.length) he
    have hlow := GLP0032B6_upperRun_prefix (complementObserved o) s s'
      hi.trace.length (i-hi.trace.length) (fun v j hj => hs v j (by omega))
    simp only [GLP0032B6_selected]
    rw [if_neg (by change ¬i < hi.trace.length; omega),
      if_neg (by change ¬i < hi'.trace.length; rw [← he]; omega), ← he']
    exact congrArg (Option.map (fun v => (complementObserved o,v))) hlow.1
  · have hit : i < hi.trace.length := by omega
    have hit' : i < hi'.trace.length := by
      apply (GLP0032B6_peek_isSome hi'.trace i).mp
      rw [← h.1]
      exact (GLP0032B6_peek_isSome hi.trace i).mpr hit
    dsimp only [hi,hi'] at hit hit'
    simp only [GLP0032B6_selected, if_pos hit, if_pos hit']
    exact congrArg (Option.map (fun v => (o,v))) h.1

lemma GLP0032B6_approximateReject_prefix {n m K : ℕ} (α ε : ℝ) (o : Counts)
    (p q : Fin (2*testBudget n+1) → Fin K → Assignment n m) (i : Fin (2*testBudget n))
    (hpq : ∀ j : Fin (2*testBudget n+1), j.val < i.val → p j = q j) :
    ∀ v j, j < i.val → approximateReject α ε o p v j = approximateReject α ε o q v j := by
  intro v j hj
  have hval : j < 2*testBudget n+1 := by omega
  have hbatch : batch p j = batch q j := by
    funext k
    dsimp only [batch]
    rw [hpq _ (by simpa only [Nat.mod_eq_of_lt hval] using hj)]
  unfold approximateReject
  rw [hbatch]

lemma GLP0032B6_monte_selected_prefix {n m K : ℕ} (α ε : ℝ) (o : Counts)
    (p q : Fin (2*testBudget n+1) → Fin K → Assignment n m) (i : Fin (2*testBudget n))
    (hpq : ∀ j : Fin (2*testBudget n+1), j.val < i.val → p j = q j) :
    GLP0032B6_selected o (approximateReject α ε o p)
        (approximateReject α ε (complementObserved o) p) i.val =
      GLP0032B6_selected o (approximateReject α ε o q)
        (approximateReject α ε (complementObserved o) q) i.val :=
  GLP0032B6_selected_prefix o _ _ _ _ i.val
    (GLP0032B6_approximateReject_prefix α ε o p q i hpq)
    (GLP0032B6_approximateReject_prefix α ε (complementObserved o) p q i hpq)

lemma GLP0032B6_fixed_errors {n m K : ℕ} (o v : Counts) (α ε : ℝ)
    (ht : v.total = n) (ho : o.a+o.b = m) (hmn : m ≤ n) (hK : 0 < K) (hε : 0 ≤ ε) :
    uniformProb (fun x : Fin K → Assignment n m =>
      α ≤ (pValue v o : ℝ) ∧ (monteMean v o (fun i => (x i).val) : ℝ)+ε < α) ≤
        Real.exp (-2*(K : ℝ)*ε^2) ∧
    uniformProb (fun x : Fin K → Assignment n m =>
      (pValue v o : ℝ) < α-2*ε ∧ α ≤ (monteMean v o (fun i => (x i).val) : ℝ)+ε) ≤
        Real.exp (-2*(K : ℝ)*ε^2) := by
  subst n
  subst m
  have h := GLP0032B6_finite_bernoulli_hoeffding v o K hmn hK ε hε
  constructor
  · refine (GLP0032B6_prob_mono ?_).trans h.2
    intro x hx
    linarith [hx.1,hx.2]
  · refine (GLP0032B6_prob_mono ?_).trans h.1
    intro x hx
    linarith [hx.1,hx.2]

lemma GLP0032B6_runTests_trace_mem (r : Counts → ℕ → Bool) (xs : List Counts)
    (idx : ℕ) (v : Counts) (b : Bool) (hv : (v,b) ∈ (runTests r idx xs).trace) : v ∈ xs := by
  induction xs generalizing idx with
  | nil => simp [runTests] at hv
  | cons w ws ih =>
    by_cases hw : r w idx = true
    · simp only [runTests,if_pos hw,List.mem_cons,Prod.mk.injEq] at hv
      rcases hv with ⟨rfl,hb⟩ | hv
      · simp
      · exact List.mem_cons_of_mem _ (ih (idx+1) hv)
    · simp only [runTests,if_neg hw,List.mem_singleton,Prod.mk.injEq] at hv
      obtain ⟨rfl,hb⟩ := hv
      simp

lemma GLP0032B6_search_trace_possible (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (r : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) (v : Counts) (b₀ : Bool)
    (hv : (v,b₀) ∈ (adaptiveSearch fuel true o k₁ k₂ r a b idx).trace) : Possible o v := by
  induction fuel generalizing a b idx with
  | zero => by_cases h : b ≤ a+1 <;> simp [adaptiveSearch,h] at hv
  | succ fuel ih =>
    rw [T7_search_succ] at hv
    by_cases h : b ≤ a+1
    · simp [h] at hv
    · simp only [if_neg h, List.mem_append] at hv
      rcases hv with hv | hv
      · exact (GLP0032B6_candidate_facts o v _ (GLP0032B6_runTests_trace_mem r
          (candidates o ((a+b)/2)) idx v b₀ hv)).1
      · split_ifs at hv <;> exact ih _ _ _ hv

lemma GLP0032B6_upperRun_trace_possible (o : Counts) (r : Counts → ℕ → Bool)
    (idx : ℕ) (v : Counts) (b : Bool) (hv : (v,b) ∈ (upperRun true o r idx).trace) :
    Possible o v := GLP0032B6_search_trace_possible _ _ _ _ _ _ _ _ _ _ hv

lemma GLP0032B6_peek_possible (o : Counts) (r : Counts → ℕ → Bool)
    (idx i : ℕ) (v : Counts) (hv : GLP0032B6_peek (upperRun true o r idx).trace i = some v) :
    Possible o v := by
  obtain ⟨⟨w,b⟩,hw,hv⟩ := Option.map_eq_some_iff.mp hv
  dsimp at hv
  subst w
  exact GLP0032B6_upperRun_trace_possible o r idx v b (List.mem_of_getElem? hw)

lemma GLP0032B6_selected_possible (o : Counts) (r s : Counts → ℕ → Bool)
    (i : ℕ) (o' v : Counts) (h : GLP0032B6_selected o r s i = some (o',v)) :
    (o' = o ∨ o' = complementObserved o) ∧ Possible o' v := by
  dsimp only [GLP0032B6_selected] at h
  split_ifs at h with hi
  · obtain ⟨w,hw,he⟩ := Option.map_eq_some_iff.mp h
    have he' := Prod.mk.inj he
    obtain ⟨rfl,rfl⟩ := he'
    exact ⟨Or.inl rfl,GLP0032B6_peek_possible o r _ _ w hw⟩
  · obtain ⟨w,hw,he⟩ := Option.map_eq_some_iff.mp h
    have he' := Prod.mk.inj he
    obtain ⟨rfl,rfl⟩ := he'
    exact ⟨Or.inr rfl,GLP0032B6_peek_possible (complementObserved o) s _ _ w hw⟩

/-- Either dangerous-error union is bounded over the actual selected tests.
The exponential supplies the nonnegative bound required by
`GLP0032B6_finite_product_freshness`. -/
lemma GLP0032B6_actual_test_error_union {n m K : ℕ} (o : Counts) (α ε : ℝ)
    (ho : o.total = n) (hm : o.a+o.b = m)
    (hmn : m ≤ n) (hK : 0 < K) (hε : 0 ≤ ε) :
    uniformProb (fun pool : Fin (2*testBudget n+1) → Fin K → Assignment n m =>
      ∃ i : Fin (2*testBudget n), ∃ o' v,
        GLP0032B6_selected o (approximateReject α ε o pool)
          (approximateReject α ε (complementObserved o) pool) i.val = some (o',v) ∧
        α ≤ (pValue v o' : ℝ) ∧
        (monteMean v o' (fun j => (pool ⟨i.val,by omega⟩ j).val) : ℝ)+ε < α) ≤
      2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) ∧
    uniformProb (fun pool : Fin (2*testBudget n+1) → Fin K → Assignment n m =>
      ∃ i : Fin (2*testBudget n), ∃ o' v,
        GLP0032B6_selected o (approximateReject α ε o pool)
          (approximateReject α ε (complementObserved o) pool) i.val = some (o',v) ∧
        (pValue v o' : ℝ) < α-2*ε ∧
        α ≤ (monteMean v o' (fun j => (pool ⟨i.val,by omega⟩ j).val) : ℝ)+ε) ≤
      2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) := by
  let instGLP0032B6AssignmentNonempty := GLP0032B6_assignment_nonempty n m hmn
  let sel := fun (i : Fin (2*testBudget n))
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) => GLP0032B6_selected o
    (approximateReject α ε o pool) (approximateReject α ε (complementObserved o) pool) i.val
  let bad₁ := fun (t : Counts × Counts) (x : Fin K → Assignment n m) =>
    α ≤ (pValue t.2 t.1 : ℝ) ∧ (monteMean t.2 t.1 (fun j => (x j).val) : ℝ)+ε < α
  let bad₂ := fun (t : Counts × Counts) (x : Fin K → Assignment n m) =>
    (pValue t.2 t.1 : ℝ) < α-2*ε ∧ α ≤ (monteMean t.2 t.1 (fun j => (x j).val) : ℝ)+ε
  let δ := Real.exp (-2*(K : ℝ)*ε^2)
  have hδ : 0 ≤ δ := (Real.exp_pos _).le
  have hpre : ∀ i p q, (∀ j : Fin (2*testBudget n+1), j.val < i.val → p j = q j) →
      sel i p = sel i q := by
    intro i p q hpq
    exact GLP0032B6_monte_selected_prefix α ε o p q i hpq
  have hbad : ∀ i pool t, sel i pool = some t →
      uniformProb (bad₁ t) ≤ δ ∧ uniformProb (bad₂ t) ≤ δ := by
    intro i pool t ht
    obtain ⟨hor,hposs⟩ := GLP0032B6_selected_possible o _ _ _ t.1 t.2 ht
    have ht₁ : t.1.total = n := by
      rcases hor with he | he
      · simpa only [he] using ho
      · rw [he]
        dsimp only [complementObserved,Counts.total] at *
        omega
    have ht₂ : t.1.a+t.1.b = m := by
      rcases hor with he | he
      · simpa only [he] using hm
      · simpa only [he,complementObserved,Nat.add_comm] using hm
    have hv : t.2.total = n := (possible_table_facts t.1 t.2 hposs).1.trans ht₁
    exact GLP0032B6_fixed_errors t.1 t.2 α ε hv ht₂ hmn hK hε
  have h₁ := GLP0032B6_finite_product_freshness (2*testBudget n+1) (2*testBudget n)
    (by omega) sel bad₁ δ hδ hpre (fun i pool t ht => (hbad i pool t ht).1)
  have h₂ := GLP0032B6_finite_product_freshness (2*testBudget n+1) (2*testBudget n)
    (by omega) sel bad₂ δ hδ hpre (fun i pool t ht => (hbad i pool t ht).2)
  simpa only [sel,bad₁,bad₂,δ,Prod.exists,Nat.cast_mul,Nat.cast_ofNat] using And.intro h₁ h₂

/-- The chronological pool has enough distinct coordinates for both runs,
including the lower run's variable starting index. -/
lemma GLP0032B6_joint_budget (o : Counts) (r s : Counts → ℕ → Bool)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) :
    let hi := upperRun true o r
    let lo := upperRun true (complementObserved o) s hi.trace.length
    hi.value.isSome ∧ lo.value.isSome ∧
      hi.trace.length + lo.trace.length ≤ 2*testBudget o.total := by
  dsimp only
  have hc : 0 < (complementObserved o).a+(complementObserved o).b ∧
      (complementObserved o).a+(complementObserved o).b =
        (complementObserved o).c+(complementObserved o).d := by
    dsimp [complementObserved]
    omega
  have hct : (complementObserved o).total = o.total := by
    dsimp [complementObserved,Counts.total]
    omega
  have hi := T7_upperRun_budget o r 0 ho
  have hl := T7_upperRun_budget (complementObserved o) s (upperRun true o r).trace.length hc
  rw [hct] at hl
  have hcost : (o.total+1)*(Nat.log2 (o.total+1)+2) ≤ testBudget o.total := by
    unfold testBudget
    exact Nat.mul_le_mul_left _ (by omega)
  exact ⟨hi.1,hl.1,by omega⟩

/-- Averaging a uniform conditional bound over independent observed data. -/
lemma GLP0032B6_observed_average {A B : Type*} [Fintype A] [Nonempty A] [Fintype B]
    (P : A → B → Prop) (δ : ℝ) (h : ∀ a, uniformProb (P a) ≤ δ) :
    uniformProb (fun ω : A × B => P ω.1 ω.2) ≤ δ := by
  rw [GLP0032B6_prob_avg]
  have he := GLP0032B6_avg_reindex (Equiv.prodComm B A)
    (fun ω : A × B => if P ω.1 ω.2 then (1 : ℝ) else 0)
  rw [← he, GLP0032B6_avg_prod]
  calc
    _ ≤ GLP0032B6_avg (fun _ : A => δ) := by
      apply GLP0032B6_avg_mono
      intro a
      convert h a using 1
      rw [GLP0032B6_prob_avg]
      unfold GLP0032B6_avg
      congr 1
    _ = δ := GLP0032B6_avg_const δ

/-! The fixed-effect candidate reduction. -/

local notation "B₆" => discordant_estimator_sd_binom
local notation "C₆" => discordant_estimator_sd_count

lemma GLP0032B6_count_add_a (a d z : ℕ) (t s : ℤ) :
    C₆ (a+1) d z t s = C₆ a d z t (s+1) + C₆ a d z (t-1) (s-1) := by
  unfold discordant_estimator_sd_count
  simp_rw [discordant_estimator_sd_binom_pascal, add_mul]
  rw [(discordant_estimator_sd_binom_summable a _).tsum_add
    (discordant_estimator_sd_binom_shift_summable a 1 _)]
  congr 1
  · apply tsum_congr
    intro x
    congr 2 <;> push_cast <;> ring
  · let e : ℤ ≃ ℤ := Equiv.addRight 1
    rw [← e.tsum_eq]
    apply tsum_congr
    intro x
    dsimp [e]
    congr 2 <;> push_cast <;> ring

lemma GLP0032B6_count_add_d (a d z : ℕ) (t s : ℤ) :
    C₆ a (d+1) z t s = C₆ a d z t s + C₆ a d z (t-1) (s-1) := by
  unfold discordant_estimator_sd_count
  simp_rw [discordant_estimator_sd_binom_pascal, add_mul, mul_add]
  rw [(discordant_estimator_sd_binom_summable a _).tsum_add
    (discordant_estimator_sd_binom_summable a _)]
  congr 1
  apply tsum_congr
  intro x
  congr 2 <;> ring

lemma GLP0032B6_count_add_z (a d z : ℕ) (t s : ℤ) :
    C₆ a d (z+1) t s = C₆ a d z t s + C₆ a d z (t-1) s := by
  unfold discordant_estimator_sd_count
  simp_rw [discordant_estimator_sd_binom_pascal, mul_add]
  rw [(discordant_estimator_sd_binom_summable a _).tsum_add
    (discordant_estimator_sd_binom_summable a _)]
  congr 1
  apply tsum_congr
  intro x
  congr 2 <;> ring

lemma GLP0032B6_pair_difference (a d z : ℕ) (t s : ℤ) :
    C₆ (a+1) d (z+1) t s - C₆ a (d+2) z t (s+1) =
      C₆ a d z (t-1) (s+1) + C₆ a d z (t-1) (s-1) - 2*C₆ a d z (t-1) s := by
  rw [GLP0032B6_count_add_a, GLP0032B6_count_add_z, GLP0032B6_count_add_z,
    show d+2 = (d+1)+1 by omega, GLP0032B6_count_add_d,
    GLP0032B6_count_add_d, GLP0032B6_count_add_d]
  simp only [show s+1-1 = s by ring, show t-1-1 = t-2 by ring]
  ring

/-- The adjacent-mass comparison includes the reflected central pair. -/
lemma GLP0032B6_shape_adjacent (f : ℤ → ℝ) (d H : ℤ)
    (hf : SDShape f d) (hH : d < 2*H) : f H ≤ f (H-1) := by
  by_cases h : d ≤ 2*(H-1)
  · exact hf.2 (H-1) H h (by omega)
  · have hd : d = 2*H-1 := by omega
    simpa only [hd, show 2*H-1-H = H-1 by ring] using (hf.1 H).ge

/-- Smoothing by a fair ±1 pair increases every symmetric integer tail. -/
lemma GLP0032B6_shape_tail (f : ℤ → ℝ) (d e : ℤ)
    (hf : SDShape f d) (hs : Summable f) :
    0 ≤ ∑' s : ℤ, (if |2*e-d| ≤ |2*s-d| then
      f (s+1)+f (s-1)-2*f s else 0) := by
  let E : ℤ → ℝ := fun s => if |2*e-d| ≤ |2*s-d| then 1 else 0
  have hsum (g : ℤ → ℝ) (hg : Summable g) :
      Summable (fun s => E s * g s) := by
    convert hg.indicator {s | |2*e-d| ≤ |2*s-d|} using 1
    funext s
    simp [E, Set.indicator]
  have hsPlus : Summable (fun s => f (s+1)) := (Equiv.addRight (1 : ℤ)).summable_iff.mpr hs
  have hsMinus : Summable (fun s => f (s-1)) := (Equiv.subRight (1 : ℤ)).summable_iff.mpr hs
  have hshiftPlus : (∑' s : ℤ, E s*f (s+1)) = ∑' s : ℤ, E (s-1)*f s := by
    rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
    simp
  have hshiftMinus : (∑' s : ℤ, E s*f (s-1)) = ∑' s : ℤ, E (s+1)*f s := by
    rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
    simp
  have heq : (∑' s : ℤ, (if |2*e-d| ≤ |2*s-d| then
      f (s+1)+f (s-1)-2*f s else 0)) =
      ∑' s : ℤ, (E (s-1)+E (s+1)-2*E s)*f s := by
    calc
      _ = ∑' s : ℤ, (E s*f (s+1)+E s*f (s-1)-2*(E s*f s)) := by
        apply tsum_congr
        intro s
        dsimp [E]
        split_ifs <;> ring
      _ = (∑' s : ℤ, E s*f (s+1)) + (∑' s : ℤ, E s*f (s-1)) -
          2*(∑' s : ℤ, E s*f s) := by
        rw [((hsum _ hsPlus).add (hsum _ hsMinus)).tsum_sub ((hsum _ hs).mul_left 2),
          (hsum _ hsPlus).tsum_add (hsum _ hsMinus), tsum_mul_left]
      _ = _ := by
        rw [hshiftPlus, hshiftMinus, ← tsum_mul_left]
        have hA : Summable (fun s => E (s-1)*f s) := by
          convert (hsum _ hsPlus).comp_injective (Equiv.subRight (1 : ℤ)).injective using 1
          funext s
          simp [Function.comp_def, Equiv.subRight]
        have hB : Summable (fun s => E (s+1)*f s) := by
          convert (hsum _ hsMinus).comp_injective (Equiv.addRight (1 : ℤ)).injective using 1
          funext s
          simp [Function.comp_def, Equiv.addRight]
        rw [← hA.tsum_add hB, ← (hA.add hB).tsum_sub ((hsum _ hs).mul_left 2)]
        apply tsum_congr; intro s; ring
  rw [heq]
  let H := max e (d-e)
  let L := min e (d-e)
  have hHL : H+L = d := by dsimp [H,L]; omega
  have hLH : L ≤ H := min_le_max
  have hE (s : ℤ) : E s = if s ≤ L ∨ H ≤ s then 1 else 0 := by
    have hiff : |2*e-d| ≤ |2*s-d| ↔ s ≤ min e (d-e) ∨ max e (d-e) ≤ s := by
      rcases le_total 0 (2*e-d) with he | he <;>
        rcases le_total 0 (2*s-d) with hs | hs
      · rw [abs_of_nonneg he, abs_of_nonneg hs]; omega
      · rw [abs_of_nonneg he, abs_of_nonpos hs]; omega
      · rw [abs_of_nonpos he, abs_of_nonneg hs]; omega
      · rw [abs_of_nonpos he, abs_of_nonpos hs]; omega
    exact if_congr hiff rfl rfl
  by_cases hgap : H ≤ L+1
  · have he (s : ℤ) : E s = 1 := by rw [hE, if_pos]; omega
    simp only [he]
    norm_num
  · have hkernel (s : ℤ) : (E (s-1)+E (s+1)-2*E s)*f s =
        (if s = H-1 then f (H-1) else 0) +
        (if s = L+1 then f (L+1) else 0) -
        (if s = H then f H else 0) - (if s = L then f L else 0) := by
      simp only [hE]
      split_ifs <;> first | omega | (subst_vars; simp_all only [add_sub_cancel_right]; nlinarith) | ring
    simp_rw [hkernel]
    rw [((((hasSum_ite_eq (H-1) (f (H-1))).summable).add
      ((hasSum_ite_eq (L+1) (f (L+1))).summable)).sub ((hasSum_ite_eq H (f H)).summable)).tsum_sub
      ((hasSum_ite_eq L (f L)).summable),
      (((hasSum_ite_eq (H-1) (f (H-1))).summable).add
      ((hasSum_ite_eq (L+1) (f (L+1))).summable)).tsum_sub ((hasSum_ite_eq H (f H)).summable),
      ((hasSum_ite_eq (H-1) (f (H-1))).summable).tsum_add
      ((hasSum_ite_eq (L+1) (f (L+1))).summable)]
    simp only [tsum_ite_eq]
    have h₁ : f (L+1) = f (H-1) := by
      convert hf.1 (H-1) using 1 <;> congr 1 <;> omega
    have h₂ : f L = f H := by convert hf.1 H using 1 <;> congr 1 <;> omega
    have hle := GLP0032B6_shape_adjacent f d H hf (by omega)
    rw [h₁,h₂]
    linarith

lemma GLP0032B6_weighted_hasSum {A : Type*} (xs : List A)
    (g : A → ℤ) (w : A → ℝ) (F : ℤ → ℝ) :
    HasSum (fun s : ℤ => F s *
      (xs.map fun q => if g q = s then w q else 0).sum)
      (xs.map fun q => F (g q)*w q).sum := by
  induction xs with
  | nil => simpa using (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0)
  | cons q xs ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    convert (hasSum_ite_eq (g q) (F (g q)*w q)).add ih using 1
    funext s
    by_cases h : s = g q
    · subst s; simp
    · simp [h,Ne.symm h]

lemma GLP0032B6_tail_integer (o v : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (ht : v.total = o.total)
    (q : Counts) (hq : q ∈ randomStates v (o.a+o.b)) :
    (deviationNumerator v o (o.a+o.b)).natAbs ≤
      (deviationNumerator v (observed v q) (o.a+o.b)).natAbs ↔
    |2*((o.a : ℤ)-o.c)-v.effect| ≤
      |2*(2*(q.a : ℤ)+q.b+q.c-v.a-v.c)-v.effect| := by
  let m := o.a+o.b
  have hn : v.total = 2*m := by rw [ht]; dsimp [m,Counts.total]; omega
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,hqt⟩
  have hobs : deviationNumerator v o m = (m : ℤ)^2 *
      (2*((o.a : ℤ)-o.c)-v.effect) := by
    simp only [deviationNumerator, hn, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hqobs : deviationNumerator v (observed v q) m = (m : ℤ)^2 *
      (2*(2*(q.a : ℤ)+q.b+q.c-v.a-v.c)-v.effect) := by
    simp only [deviationNumerator, hn, Nat.cast_mul, Nat.cast_ofNat, observed,
      Nat.cast_add, Nat.cast_sub (show q.c ≤ v.a-q.a+v.c by omega), Nat.cast_sub ha,
      Counts.effect]
    ring
  have hp : 0 < ((m : ℤ)^2).natAbs := by
    apply Int.natAbs_pos.mpr
    exact pow_ne_zero _ (by exact_mod_cast ho.1.ne')
  rw [hobs,hqobs,Int.natAbs_mul,Int.natAbs_mul,mul_le_mul_iff_right₀ hp]
  simp only [Int.abs_eq_natAbs]
  exact Int.ofNat_le.symm

lemma GLP0032B6_pvalue_count (o v : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (ht : v.total = o.total) :
    (pValue v o : ℝ) =
      (∑' s : ℤ, if |2*((o.a : ℤ)-o.c)-v.effect| ≤ |2*s-v.effect| then
        C₆ v.a (v.b+v.c) v.d ((o.a+o.b : ℕ) : ℤ) (s+v.c) else 0) /
        v.total.choose (o.a+o.b) := by
  let m := o.a+o.b
  let g := fun q : Counts => 2*(q.a : ℤ)+q.b+q.c-v.a-v.c
  let F := fun s : ℤ => if |2*((o.a : ℤ)-o.c)-v.effect| ≤ |2*s-v.effect| then (1 : ℝ) else 0
  have hn : v.total = 2*m := by rw [ht]; dsimp [m,Counts.total]; omega
  have hD : (0 : ℝ) < v.total.choose m := by exact_mod_cast Nat.choose_pos (by omega : m ≤ v.total)
  have hcount (s : ℤ) :
      ((randomStates v m).map fun q => if g q = s then (multiplicity v q : ℝ) else 0).sum =
        C₆ v.a (v.b+v.c) v.d m (s+v.c) := by
    have h := congrFun (discordant_estimator_sd_mass_expansion v m ho.1 hn) s
    rw [discordant_estimator_sd_mass_formula v m ho.1 hn s] at h
    exact (div_left_inj' hD.ne').mp h.symm
  have hs := GLP0032B6_weighted_hasSum (randomStates v m) g
    (fun q => (multiplicity v q : ℝ)) F
  have htail : ((randomStates v m).map fun q => F (g q)*(multiplicity v q : ℝ)).sum =
      (tailCount v o : ℝ) := by
    unfold tailCount
    rw [Nat.cast_list_sum]
    simp only [List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    simp only [F,g, ← GLP0032B6_tail_integer o v ho ht q hq]
    split_ifs <;> simp
  rw [htail] at hs
  simp_rw [hcount] at hs
  have he : (∑' s : ℤ, if |2*((o.a : ℤ)-o.c)-v.effect| ≤ |2*s-v.effect| then
        C₆ v.a (v.b+v.c) v.d m (s+v.c) else 0) = (tailCount v o : ℝ) := by
    simpa only [F,ite_mul,one_mul,zero_mul] using hs.tsum_eq
  change (pValue v o : ℝ) = _ / (v.total.choose m : ℝ)
  rw [he]
  simp only [pValue, Rat.cast_div, Rat.cast_natCast, binomial_eq_choose, m]

lemma GLP0032B6_count_summable (a d z m : ℕ) (hm : 0 < m)
    (hn : a+d+z = 2*m) : Summable (fun s : ℤ => C₆ a d z m s) := by
  let v : Counts := ⟨a,d,0,z⟩
  have hv : v.total = 2*m := by simpa [v,Counts.total] using hn
  have hD : (v.total.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega : m ≤ v.total)).ne'
  have h := (discordant_estimator_sd_isMass v m hm hv).2.1.mul_left (v.total.choose m : ℝ)
  convert h using 1
  funext s
  rw [discordant_estimator_sd_mass_formula v m hm hv]
  dsimp only [v]
  simp only [Nat.add_zero, Nat.cast_zero, Int.add_zero]
  dsimp only [v] at hD
  field_simp [hD]

lemma GLP0032B6_pair_pvalue (o : Counts) (a b c z : ℕ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hn : a+(b+1)+(c+1)+z = o.total) (hd : 1 ≤ b+c) :
    pValue (⟨a,b+1,c+1,z⟩ : Counts) o ≤ pValue ⟨a+1,b,c,z+1⟩ o := by
  let m := o.a+o.b-1
  have hm : 0 < m := by dsimp [m,Counts.total] at *; omega
  have hfull : o.a+o.b = m+1 := by dsimp [m]; omega
  have hbase : a+(b+c)+z = 2*m := by dsimp [m,Counts.total] at *; omega
  let f : ℤ → ℝ := fun s => C₆ a (b+c) z m (s+c)
  have hf : SDShape f ((b : ℤ)-c) := by
    have h := discordant_estimator_sd_canonical_shape a (b+c) z m hm hbase hd
    constructor
    · intro s
      convert h.1 (s+c) using 1 <;> dsimp [f] <;> congr 1 <;> push_cast <;> ring
    · intro i j hi hij
      exact h.2 (i+c) (j+c) (by push_cast; omega) (by omega)
  have hs : Summable f :=
    (Equiv.addRight (c : ℤ)).summable_iff.mpr (GLP0032B6_count_summable a (b+c) z m hm hbase)
  have hdif (s : ℤ) :
      C₆ (a+1) (b+c) (z+1) (m+1) (s+c) -
        C₆ a ((b+1)+(c+1)) z (m+1) (s+(c+1 : ℕ)) =
      f (s+1)+f (s-1)-2*f s := by
    simpa only [f, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      show (b+1)+(c+1) = b+c+2 by omega,
      show (m+1 : ℕ) - (1 : ℤ) = (m : ℤ) by push_cast; ring,
      show s+(c : ℤ)+1 = s+(c+1 : ℕ) by push_cast; ring,
      show s+1+(c : ℤ) = s+(c : ℤ)+1 by ring,
      show s-1+(c : ℤ) = s+(c : ℤ)-1 by ring]
      using GLP0032B6_pair_difference a (b+c) z (m+1) (s+c)
  have hshape := GLP0032B6_shape_tail f ((b : ℤ)-c) ((o.a : ℤ)-o.c) hf hs
  have hnew : Summable (fun s : ℤ => C₆ (a+1) (b+c) (z+1) (m+1) (s+c)) :=
    (Equiv.addRight (c : ℤ)).summable_iff.mpr
      (GLP0032B6_count_summable (a+1) (b+c) (z+1) (m+1) (by omega) (by omega))
  have hold : Summable (fun s : ℤ => C₆ a ((b+1)+(c+1)) z (m+1) (s+(c+1 : ℕ))) :=
    (Equiv.addRight ((c+1 : ℕ) : ℤ)).summable_iff.mpr
      (GLP0032B6_count_summable a ((b+1)+(c+1)) z (m+1) (by omega) (by omega))
  let E := {s : ℤ | |2*((o.a : ℤ)-o.c)-((b : ℤ)-c)| ≤ |2*s-((b : ℤ)-c)|}
  have hdiff : 0 ≤ (∑' s : ℤ, E.indicator
        (fun s => C₆ (a+1) (b+c) (z+1) (m+1) (s+c)) s) -
      ∑' s : ℤ, E.indicator
        (fun s => C₆ a ((b+1)+(c+1)) z (m+1) (s+(c+1 : ℕ))) s := by
    rw [← (hnew.indicator E).tsum_sub (hold.indicator E)]
    convert hshape using 1
    apply tsum_congr
    intro s
    simp only [Set.indicator, E, Set.mem_setOf_eq]
    split_ifs <;> simp_all only [sub_zero, sub_self, hdif]
  have hD : 0 ≤ (o.total.choose (o.a+o.b) : ℝ) := Nat.cast_nonneg _
  have htnew : (⟨a+1,b,c,z+1⟩ : Counts).total = o.total := by dsimp [Counts.total]; omega
  have htold : (⟨a,b+1,c+1,z⟩ : Counts).total = o.total := hn
  have hreal : (pValue (⟨a,b+1,c+1,z⟩ : Counts) o : ℝ) ≤
      (pValue (⟨a+1,b,c,z+1⟩ : Counts) o : ℝ) := by
    rw [GLP0032B6_pvalue_count o _ ho htold, GLP0032B6_pvalue_count o _ ho htnew,
      htold, htnew]
    apply div_le_div_of_nonneg_right _ hD
    have heffect : (⟨a,b+1,c+1,z⟩ : Counts).effect = (b : ℤ)-c := by
      simp only [Counts.effect, Nat.cast_add, Nat.cast_one]; ring
    simpa only [Set.indicator, E, Set.mem_setOf_eq, heffect, Counts.effect,
      hfull, Counts.a, Counts.b, Counts.c, Counts.d, Nat.cast_add,Nat.cast_one,add_sub_add_right_eq_sub] using (sub_nonneg.mp hdiff)
  exact_mod_cast hreal

lemma GLP0032B6_reuse_pvalue (o v : Counts) (k : ℕ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (ht : v.total = o.total)
    (ha : k ≤ v.a) (hz : k ≤ v.d) (hd : 1 ≤ v.b+v.c) :
    pValue (reuseVector v k) o ≤ pValue v o := by
  induction k with
  | zero => simp [reuseVector]
  | succ k ih =>
    have h := GLP0032B6_pair_pvalue o (v.a-(k+1)) (v.b+k) (v.c+k) (v.d-(k+1))
      ho (by dsimp [Counts.total] at ht ⊢; omega) (by omega)
    have hold : (⟨v.a-(k+1),v.b+k+1,v.c+k+1,v.d-(k+1)⟩ : Counts) = reuseVector v (k+1) := by
      ext <;> simp [reuseVector, Nat.add_assoc]
    have hnew : (⟨v.a-(k+1)+1,v.b+k,v.c+k,v.d-(k+1)+1⟩ : Counts) = reuseVector v k := by
      ext <;> dsimp [reuseVector] <;> omega
    rw [hold,hnew] at h
    exact h.trans (ih (by omega) (by omega))

/-- When the minimum line table is concordant, a positive feasible reuse
step forces mixed outcomes in at least one observed arm. -/
lemma GLP0032B6_zero_companion (o v : Counts) (k : ℕ)
    (hv : Possible o v) (hu : Possible o (reuseVector v k))
    (hb : v.b = 0) (hc : v.c = 0) (hk : 0 < k)
    (ha : k ≤ v.a) (hz : k ≤ v.d) :
    Possible o ⟨v.a-1,1,1,v.d-1⟩ := by
  have hbase : v.a = o.a+o.c ∧ v.d = o.b+o.d := by
    simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range] at hv
    obtain ⟨i,hi,j,hj,t,ht,l,hl,he⟩ := hv
    have heA := congrArg Counts.a he
    have heB := congrArg Counts.b he
    have heC := congrArg Counts.c he
    have heD := congrArg Counts.d he
    dsimp only at heA heB heC heD
    omega
  have hmixed : (0 < o.a ∧ 0 < o.b) ∨ (0 < o.c ∧ 0 < o.d) := by
    simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range] at hu
    obtain ⟨i,hi,j,hj,t,ht,l,hl,he⟩ := hu
    have heA := congrArg Counts.a he
    have heB := congrArg Counts.b he
    have heC := congrArg Counts.c he
    have heD := congrArg Counts.d he
    dsimp only [reuseVector] at heA heB heC heD
    omega
  simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range]
  rcases hmixed with ⟨hA,hB⟩ | ⟨hC,hD⟩
  · refine ⟨o.a-1,by omega,1,by omega,o.c,by omega,0,by omega,?_⟩
    ext <;> dsimp <;> omega
  · refine ⟨o.a,by omega,0,by omega,o.c-1,by omega,1,by omega,?_⟩
    ext <;> dsimp <;> omega

lemma GLP0032B6_candidate_dominates (o u : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hu : Possible o u) :
    ∃ v ∈ candidates o u.effect, pValue u o ≤ pValue v o := by
  obtain ⟨hx,hj,v,hv,k,hk,ha,hz,rfl⟩ := corrected_general_loop o u hu
  have hspec := first_on_line_spec o _ _ v hv
  have ht := (possible_table_facts o v hspec.1).1
  have hmem : v ∈ candidates o (reuseVector v k).effect := by
    simp only [candidates,List.mem_flatMap]
    refine ⟨(reuseVector v k).a+(reuseVector v k).b,List.mem_range.mpr (by omega),?_⟩
    rw [hv]
    dsimp only
    split_ifs <;> simp
  by_cases hd : 1 ≤ v.b+v.c
  · exact ⟨v,hmem,GLP0032B6_reuse_pvalue o v k ho ht ha hz hd⟩
  · have hb : v.b = 0 := by omega
    have hc : v.c = 0 := by omega
    by_cases hzero : k = 0
    · refine ⟨v,hmem,?_⟩
      simp [hzero,reuseVector]
    · have hkp : 0 < k := by omega
      have hcomp := GLP0032B6_zero_companion o v k hspec.1 hu hb hc hkp ha hz
      let w : Counts := ⟨v.a-1,1,1,v.d-1⟩
      have hw : w ∈ candidates o (reuseVector v k).effect := by
        simp only [candidates,List.mem_flatMap]
        refine ⟨(reuseVector v k).a+(reuseVector v k).b,List.mem_range.mpr (by omega),?_⟩
        rw [hv]
        simp [hb,hc,show 1 ≤ v.a by omega,show 1 ≤ v.d by omega,hcomp,w]
      have hu' : reuseVector w (k-1) = reuseVector v k := by
        ext <;> dsimp [reuseVector,w] <;> omega
      refine ⟨w,hw,?_⟩
      rw [← hu']
      apply GLP0032B6_reuse_pvalue o w (k-1) ho
      · exact (possible_table_facts o w hcomp).1
      · dsimp [w]; omega
      · dsimp [w]; omega
      · norm_num [w]

lemma GLP0032B6_fill_down (o u : Counts) (c : ℤ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hu : Possible o u)
    (hc : 2*((o.a : ℤ)-o.c) ≤ c) (hcu : c ≤ u.effect) :
    ∃ w, Possible o w ∧ w.effect = c ∧ pValue u o ≤ pValue w o := by
  generalize hN : (u.effect-c).toNat = N
  induction N using Nat.strong_induction_on generalizing u with
  | h N ih =>
    by_cases he : u.effect = c
    · exact ⟨u,hu,he,le_rfl⟩
    · obtain ⟨w,hw,hwe,hp⟩ := GP0031B3b_t25_possible_effect_down o u ho hu (by omega)
      obtain ⟨z,hz,hze,hpz⟩ := ih (w.effect-c).toNat (by omega) w hw (by omega) rfl
      exact ⟨z,hz,hze,hp.trans hpz⟩

lemma GLP0032B6_tau_real (v : Counts) : tau v = (v.effect : ℝ)/v.total := by
  simp [tau,tauQ]

lemma GLP0032B6_estimate_real (o : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) :
    estimate o = ((2*((o.a : ℤ)-o.c) : ℤ) : ℝ)/o.total := by
  have hm : ((o.a+o.b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have hn : o.total = 2*(o.a+o.b) := by dsimp [Counts.total]; omega
  simp only [estimate,estimateQ,Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,
    Rat.cast_add, ← Nat.cast_add, ← ho.2, hn, Nat.cast_mul,Nat.cast_ofNat,
    Int.cast_mul,Int.cast_sub,Int.cast_ofNat,Int.cast_natCast]
  field_simp <;> ring

lemma GLP0032B6_upper_certificate (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1) :
    ∃ r : ℤ, 2*((o.a : ℤ)-o.c) ≤ r ∧ r ≤ (o.a : ℤ)-o.c+(o.a+o.b) ∧
      upper α o = (r : ℝ)/o.total ∧
      (∀ c : ℤ, 2*((o.a : ℤ)-o.c) ≤ c → c ≤ r →
        ∃ w ∈ candidates o c, α ≤ (pValue w o : ℝ)) ∧
      (∀ c : ℤ, ∀ w ∈ candidates o c, α ≤ (pValue w o : ℝ) → c ≤ r) := by
  have hest := balanced_estimate_in_interval o α ho hα
  have hne : (accepted α o).Nonempty := ⟨estimate o,hest.1⟩
  have hu : upper α o ∈ accepted α o := hne.csSup_mem
  obtain ⟨u,hu,hpu,heu⟩ := (balanced_completion_inclusion_accepted_spec α o _).mp hu
  have ht := (possible_table_facts o u hu).1
  have hN : (0 : ℝ) < o.total := by
    have : 0 < o.total := by dsimp [Counts.total]; omega
    exact_mod_cast this
  have heq : upper α o = (u.effect : ℝ)/o.total := by
    rw [← heu,GLP0032B6_tau_real,ht]
  have hleft : 2*((o.a : ℤ)-o.c) ≤ u.effect := by
    have h := hest.2.2.2
    rw [GLP0032B6_estimate_real o ho,heq,div_le_div_iff_of_pos_right hN] at h
    exact_mod_cast h
  have hright : u.effect ≤ (o.a : ℤ)-o.c+(o.a+o.b) := by
    have h := (possible_table_facts o u hu).2
    simp only [candidateNumerators,List.mem_map,List.mem_range] at h
    obtain ⟨k,hk,he⟩ := h
    dsimp [Counts.total] at *
    omega
  refine ⟨u.effect,hleft,hright,heq,?_,?_⟩
  · intro c hc hcr
    obtain ⟨v,hv,hvc,hpv⟩ := GLP0032B6_fill_down o u c ho hu hc hcr
    obtain ⟨w,hw,hpw⟩ := GLP0032B6_candidate_dominates o v ho hv
    rw [hvc] at hw
    refine ⟨w,hw,hpu.trans ?_⟩
    exact_mod_cast hpv.trans hpw
  · intro c w hw hp
    have hf := GLP0032B6_candidate_facts o w c hw
    have hacc := accepted_of_possible α o w hf.1 hp
    have hbound := le_csSup (accepted α o).finite_toSet.bddAbove hacc
    change tau w ≤ upper α o at hbound
    rw [GLP0032B6_tau_real, (possible_table_facts o w hf.1).1, hf.2, heq,
      div_le_div_iff_of_pos_right hN] at hbound
    exact_mod_cast hbound

lemma GLP0032B6_upper_no_rejection (o : Counts) (α : ℝ)
    (reject : Counts → ℕ → Bool) (idx : ℕ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1)
    (hgood : ∀ v, (v,true) ∈ (upperRun true o reject idx).trace → (pValue v o : ℝ) < α) :
    ∃ x, (upperRun true o reject idx).value = some x ∧ upper α o ≤ (x : ℝ)/o.total := by
  obtain ⟨r,hr₁,hr₂,heq,hcover,hsound⟩ := GLP0032B6_upper_certificate o α ho hα
  obtain ⟨x,hx,hrx⟩ := GLP0032B6_search_no_bad_rejection (o.total+3) o
    (2*((o.a : ℤ)-o.c)) ((o.a : ℤ)-o.c+(o.a+o.b)) reject
    (fun v => α ≤ (pValue v o : ℝ))
    (2*((o.a : ℤ)-o.c)-1) ((o.a : ℤ)-o.c+(o.a+o.b)+1) r idx
    (by omega) (by dsimp [Counts.total]; omega) (by omega)
    (fun c hac hcb hcr => hcover c (by omega) hcr)
    (fun v hv => not_le.mpr (hgood v hv))
  refine ⟨x,hx,?_⟩
  rw [heq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hrx

lemma GLP0032B6_upper_no_acceptance (o : Counts) (β : ℝ)
    (reject : Counts → ℕ → Bool) (idx : ℕ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hβ : 0 < β ∧ β < 1)
    (hgood : ∀ v, (v,false) ∈ (upperRun true o reject idx).trace → β ≤ (pValue v o : ℝ)) :
    ∃ x, (upperRun true o reject idx).value = some x ∧ (x : ℝ)/o.total ≤ upper β o := by
  obtain ⟨r,hr₁,hr₂,heq,hcover,hsound⟩ := GLP0032B6_upper_certificate o β ho hβ
  obtain ⟨x,hx,hxr⟩ := GLP0032B6_search_no_bad_acceptance (o.total+3) o
    (2*((o.a : ℤ)-o.c)) ((o.a : ℤ)-o.c+(o.a+o.b)) reject
    (fun v => β ≤ (pValue v o : ℝ))
    (2*((o.a : ℤ)-o.c)-1) ((o.a : ℤ)-o.c+(o.a+o.b)+1) r idx
    (by omega) (by dsimp [Counts.total]; omega) (by omega)
    (fun c hac hcb v hv hp => hsound c v hv hp) hgood
  refine ⟨x,hx,?_⟩
  rw [heq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hxr

lemma GLP0032B6_runTests_reply (r : Counts → ℕ → Bool) (xs : List Counts)
    (idx i : ℕ) (v : Counts) (b : Bool)
    (h : (runTests r idx xs).trace[i]? = some (v,b)) : r v (idx+i) = b := by
  induction xs generalizing idx i with
  | nil => simp [runTests] at h
  | cons w ws ih =>
    by_cases hw : r w idx = true
    · cases i with
      | zero =>
        simp only [runTests,if_pos hw,List.getElem?_cons_zero,Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        simpa using hw
      | succ i =>
        simp only [runTests,if_pos hw,List.getElem?_cons_succ] at h
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (idx+1) i h
    · cases i with
      | zero =>
        simp only [runTests,if_neg hw,List.getElem?_cons_zero,Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        simpa using Bool.eq_false_iff.mpr hw
      | succ i => simp [runTests,hw] at h

lemma GLP0032B6_search_reply (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (r : Counts → ℕ → Bool) (a b : ℤ) (idx i : ℕ) (v : Counts) (B : Bool)
    (h : (adaptiveSearch fuel true o k₁ k₂ r a b idx).trace[i]? = some (v,B)) :
    r v (idx+i) = B := by
  induction fuel generalizing a b idx i with
  | zero => by_cases hs : b ≤ a+1 <;> simp [adaptiveSearch,hs] at h
  | succ fuel ih =>
    rw [T7_search_succ] at h
    by_cases hs : b ≤ a+1
    · simp [hs] at h
    · simp only [if_neg hs] at h
      let c := (a+b)/2
      let q := runTests r idx (candidates o c)
      change (q.trace ++ (if q.compatible then
        adaptiveSearch fuel true o k₁ k₂ r c b q.idx
        else adaptiveSearch fuel true o k₁ k₂ r a c q.idx).trace)[i]? = some (v,B) at h
      by_cases hi : i < q.trace.length
      · rw [List.getElem?_append_left hi] at h
        exact GLP0032B6_runTests_reply r (candidates o c) idx i v B h
      · rw [List.getElem?_append_right (by omega)] at h
        have hidx : q.idx = idx+q.trace.length := (T7_runTests_cost r (candidates o c) idx).1
        split_ifs at h with hq
        · have hr := ih c b q.idx (i-q.trace.length) h
          convert hr using 1
          congr 1
          omega
        · have hr := ih a c q.idx (i-q.trace.length) h
          convert hr using 1
          congr 1
          omega

lemma GLP0032B6_upperRun_reply (o : Counts) (r : Counts → ℕ → Bool)
    (idx i : ℕ) (v : Counts) (b : Bool)
    (h : (upperRun true o r idx).trace[i]? = some (v,b)) : r v (idx+i) = b :=
  GLP0032B6_search_reply _ _ _ _ _ _ _ _ _ _ _ h

/-- Every trace reply occurs at its actual chronological selected slot. -/
lemma GLP0032B6_trace_good (o : Counts) (dec : Counts → Counts → ℕ → Bool)
    (D : ℕ) (b : Bool) (P : Counts → Counts → Prop)
    (hbudget : (upperRun true o (dec o)).trace.length +
      (upperRun true (complementObserved o) (dec (complementObserved o))
        (upperRun true o (dec o)).trace.length).trace.length ≤ D)
    (hgood : ∀ i : Fin D, ∀ o' v,
      GLP0032B6_selected o (dec o) (dec (complementObserved o)) i.val = some (o',v) →
      dec o' v i.val = b → P o' v) :
    (∀ v, (v,b) ∈ (upperRun true o (dec o)).trace → P o v) ∧
    (∀ v, (v,b) ∈ (upperRun true (complementObserved o) (dec (complementObserved o))
      (upperRun true o (dec o)).trace.length).trace → P (complementObserved o) v) := by
  let hi := upperRun true o (dec o)
  let lo := upperRun true (complementObserved o) (dec (complementObserved o)) hi.trace.length
  constructor
  · intro v hv
    obtain ⟨i,hi'⟩ := List.mem_iff_getElem?.mp hv
    have hit : i < hi.trace.length := (List.getElem?_eq_some_iff.mp hi').1
    refine hgood ⟨i,by dsimp [hi,lo] at *; omega⟩ o v ?_ ?_
    · dsimp only [hi] at hit
      simp only [GLP0032B6_selected,if_pos hit,GLP0032B6_peek,hi',Option.map_some]
    · simpa only [Nat.zero_add] using GLP0032B6_upperRun_reply o (dec o) 0 i v b hi'
  · intro v hv
    obtain ⟨i,hi'⟩ := List.mem_iff_getElem?.mp hv
    have hit : i < lo.trace.length := (List.getElem?_eq_some_iff.mp hi').1
    refine hgood ⟨hi.trace.length+i,by dsimp [hi,lo] at *; omega⟩ (complementObserved o) v ?_ ?_
    · simp [hi,GLP0032B6_selected,GLP0032B6_peek,hi']
    · exact GLP0032B6_upperRun_reply (complementObserved o) (dec (complementObserved o))
        hi.trace.length i v b hi'

lemma GLP0032B6_inner_inclusion {n m K : ℕ} (o : Counts) (α ε : ℝ)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1)
    (hgood : (∀ v, (v,true) ∈
      (upperRun true o (approximateReject α ε o pool)).trace → (pValue v o : ℝ) < α) ∧
      (∀ v, (v,true) ∈ (upperRun true (complementObserved o)
        (approximateReject α ε (complementObserved o) pool)
        (upperRun true o (approximateReject α ε o pool)).trace.length).trace →
          (pValue v (complementObserved o) : ℝ) < α)) :
    exactInterval α o ⊆ monteInterval true α ε o pool := by
  have hc : 0 < (complementObserved o).a+(complementObserved o).b ∧
      (complementObserved o).a+(complementObserved o).b =
        (complementObserved o).c+(complementObserved o).d := by dsimp [complementObserved]; omega
  have hct : (complementObserved o).total = o.total := by dsimp [complementObserved,Counts.total]; omega
  have hne : (accepted α o).Nonempty := ⟨estimate o,(balanced_estimate_in_interval o α ho hα).1⟩
  obtain ⟨x,hx,hxbound⟩ := GLP0032B6_upper_no_rejection o α _ 0 ho hα hgood.1
  obtain ⟨y,hy,hybound⟩ := GLP0032B6_upper_no_rejection (complementObserved o) α _
    (upperRun true o (approximateReject α ε o pool)).trace.length hc hα hgood.2
  rw [hct,balanced_completion_inclusion_complement_upper α o ⟨ho.1,by omega⟩ hne] at hybound
  simp only [monteInterval,monteEndpoints,hx,hy]
  rintro t ⟨l,hl,u,hu,hlt,htu⟩
  have hlow : lower α o ≤ l := csInf_le (accepted α o).finite_toSet.bddBelow hl
  have hupp : u ≤ upper α o := le_csSup (accepted α o).finite_toSet.bddAbove hu
  constructor
  · rw [neg_div]
    linarith
  · exact htu.trans (hupp.trans hxbound)

lemma GLP0032B6_outer_inclusion {n m K : ℕ} (o : Counts) (α ε : ℝ)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hβ : 0 < α-2*ε ∧ α-2*ε < 1)
    (hgood : (∀ v, (v,false) ∈
      (upperRun true o (approximateReject α ε o pool)).trace → α-2*ε ≤ (pValue v o : ℝ)) ∧
      (∀ v, (v,false) ∈ (upperRun true (complementObserved o)
        (approximateReject α ε (complementObserved o) pool)
        (upperRun true o (approximateReject α ε o pool)).trace.length).trace →
          α-2*ε ≤ (pValue v (complementObserved o) : ℝ))) :
    monteInterval true α ε o pool ⊆ exactInterval (α-2*ε) o := by
  have hc : 0 < (complementObserved o).a+(complementObserved o).b ∧
      (complementObserved o).a+(complementObserved o).b =
        (complementObserved o).c+(complementObserved o).d := by dsimp [complementObserved]; omega
  have hct : (complementObserved o).total = o.total := by dsimp [complementObserved,Counts.total]; omega
  have hne : (accepted (α-2*ε) o).Nonempty :=
    ⟨estimate o,(balanced_estimate_in_interval o (α-2*ε) ho hβ).1⟩
  obtain ⟨x,hx,hxbound⟩ := GLP0032B6_upper_no_acceptance o (α-2*ε) _ 0 ho hβ hgood.1
  obtain ⟨y,hy,hybound⟩ := GLP0032B6_upper_no_acceptance (complementObserved o) (α-2*ε) _
    (upperRun true o (approximateReject α ε o pool)).trace.length hc hβ hgood.2
  rw [hct,balanced_completion_inclusion_complement_upper (α-2*ε) o ⟨ho.1,by omega⟩ hne] at hybound
  simp only [monteInterval,monteEndpoints,hx,hy]
  intro t ht
  refine ⟨lower (α-2*ε) o,hne.csInf_mem,upper (α-2*ε) o,hne.csSup_mem,?_,?_⟩
  · have h := ht.1
    rw [neg_div] at h
    linarith
  · exact ht.2.trans hxbound

noncomputable def GLP0032B6_bad_rejection {n m K : ℕ} (o : Counts) (α ε : ℝ)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) : Prop :=
  ∃ i : Fin (2*testBudget n), ∃ o' v,
    GLP0032B6_selected o (approximateReject α ε o pool)
      (approximateReject α ε (complementObserved o) pool) i.val = some (o',v) ∧
    α ≤ (pValue v o' : ℝ) ∧
    (monteMean v o' (fun j => (pool ⟨i.val,by omega⟩ j).val) : ℝ)+ε < α

noncomputable def GLP0032B6_bad_acceptance {n m K : ℕ} (o : Counts) (α ε : ℝ)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) : Prop :=
  ∃ i : Fin (2*testBudget n), ∃ o' v,
    GLP0032B6_selected o (approximateReject α ε o pool)
      (approximateReject α ε (complementObserved o) pool) i.val = some (o',v) ∧
    (pValue v o' : ℝ) < α-2*ε ∧
    α ≤ (monteMean v o' (fun j => (pool ⟨i.val,by omega⟩ j).val) : ℝ)+ε

lemma GLP0032B6_no_error_inner {n m K : ℕ} (o : Counts) (α ε : ℝ)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (ht : o.total = n) (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hα : 0 < α ∧ α < 1) (hno : ¬GLP0032B6_bad_rejection o α ε pool) :
    exactInterval α o ⊆ monteInterval true α ε o pool := by
  apply GLP0032B6_inner_inclusion o α ε pool ho hα
  have hb := (GLP0032B6_joint_budget o (approximateReject α ε o pool)
    (approximateReject α ε (complementObserved o) pool) ho).2.2
  rw [ht] at hb
  apply GLP0032B6_trace_good o (fun o' => approximateReject α ε o' pool)
    (2*testBudget n) true (fun o' v => (pValue v o' : ℝ) < α) hb
  intro i o' v hsel hdec
  by_contra h
  apply hno
  refine ⟨i,o',v,hsel,le_of_not_gt h,?_⟩
  have hi : i.val < 2*testBudget n+1 := by omega
  have hbatch : batch pool i.val = fun j => (pool ⟨i.val,hi⟩ j).val := by
    funext j
    simp only [batch,Nat.mod_eq_of_lt hi]
  simpa only [approximateReject,decide_eq_true_eq,hbatch] using hdec

lemma GLP0032B6_no_error_outer {n m K : ℕ} (o : Counts) (α ε : ℝ)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (ht : o.total = n) (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hβ : 0 < α-2*ε ∧ α-2*ε < 1) (hno : ¬GLP0032B6_bad_acceptance o α ε pool) :
    monteInterval true α ε o pool ⊆ exactInterval (α-2*ε) o := by
  apply GLP0032B6_outer_inclusion o α ε pool ho hβ
  have hb := (GLP0032B6_joint_budget o (approximateReject α ε o pool)
    (approximateReject α ε (complementObserved o) pool) ho).2.2
  rw [ht] at hb
  apply GLP0032B6_trace_good o (fun o' => approximateReject α ε o' pool)
    (2*testBudget n) false (fun o' v => α-2*ε ≤ (pValue v o' : ℝ)) hb
  intro i o' v hsel hdec
  by_contra h
  apply hno
  refine ⟨i,o',v,hsel,lt_of_not_ge h,?_⟩
  have hi : i.val < 2*testBudget n+1 := by omega
  have hbatch : batch pool i.val = fun j => (pool ⟨i.val,hi⟩ j).val := by
    funext j
    simp only [batch,Nat.mod_eq_of_lt hi]
  have hdec' : ¬(monteMean v o' (fun j => (pool ⟨i.val,by omega⟩ j).val) : ℝ)+ε < α := by
    simpa only [approximateReject,decide_eq_false_iff_not,hbatch] using hdec
  exact le_of_not_gt hdec'

lemma GLP0032B6_prob_compl {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    uniformProb (fun a => ¬P a) = 1-uniformProb P := by
  rw [GLP0032B6_prob_avg,GLP0032B6_prob_avg,eq_sub_iff_add_eq]
  calc
    _ = GLP0032B6_avg (fun a => (if ¬P a then (1 : ℝ) else 0) +
        (if P a then (1 : ℝ) else 0)) := by
      unfold GLP0032B6_avg
      rw [Finset.sum_add_distrib,add_div]
      congr 1 <;> congr 1 <;> apply Finset.sum_congr rfl <;>
        intro a ha <;> dsimp only <;> split_ifs <;> rfl
    _ = GLP0032B6_avg (fun _ : A => (1 : ℝ)) := by
      congr 1
      funext a
      by_cases h : P a <;> simp [h]
    _ = 1 := GLP0032B6_avg_const 1

lemma GLP0032B6_conditional_failure {n m K : ℕ} (o : Counts) (α ε : ℝ)
    (ht : o.total = n) (hm : o.a+o.b = m)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hmn : m ≤ n) (hK : 0 < K) (hα : 0 < α ∧ α < 1) (hε : 0 < ε) :
    uniformProb (fun pool : Fin (2*testBudget n+1) → Fin K → Assignment n m =>
      ¬exactInterval α o ⊆ monteInterval true α ε o pool) ≤
        2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) ∧
    (0 < α-2*ε → uniformProb (fun pool : Fin (2*testBudget n+1) → Fin K → Assignment n m =>
      ¬monteInterval true α ε o pool ⊆ exactInterval (α-2*ε) o) ≤
        2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2)) := by
  have herr := GLP0032B6_actual_test_error_union o α ε ht hm hmn hK hε.le
  change uniformProb (GLP0032B6_bad_rejection o α ε) ≤ _ ∧
    uniformProb (GLP0032B6_bad_acceptance o α ε) ≤ _ at herr
  constructor
  · refine (GLP0032B6_prob_mono ?_).trans herr.1
    intro pool hfail
    by_contra hno
    exact hfail (GLP0032B6_no_error_inner o α ε pool ht ho hα hno)
  · intro hβ
    refine (GLP0032B6_prob_mono ?_).trans herr.2
    intro pool hfail
    by_contra hno
    exact hfail (GLP0032B6_no_error_outer o α ε pool ht ho ⟨hβ,by linarith [hα.2]⟩ hno)

lemma GLP0032B6_canonical_design (v : Counts) (m : ℕ) (hn : v.total = 2*m)
    (z : Assignment v.total m) :
    (canonicalObserved v z.val).total = v.total ∧
      (canonicalObserved v z.val).a+(canonicalObserved v z.val).b = m ∧
      (canonicalObserved v z.val).c+(canonicalObserved v z.val).d = m := by
  let w : PotentialTable v.total := fun i => canonicalPair v i.val
  have hw : tableCounts w = v := by
    have h := monte_rank_valid_canonical_type_cards v
    exact Counts.ext h.1 h.2.1 h.2.2.1 h.2.2.2
  have hq := neyman_treated_mem w v hw m z
  have hobs : observed v (neyman_treated w z.val) = canonicalObserved v z.val :=
    monte_rank_valid_observed_bridge v z.val
  have h := neyman_observed_arms v _ m hq
  have h' := balanced_missing_coverage_observed_arms v m hn _ hq
  simpa only [hobs] using And.intro h.1 (And.intro h.2 h'.2)

theorem corrected_monte_inclusions_proof (v : Counts) (m K : ℕ) (α ε : ℝ)
    (hm : 0 < m) (hn : v.total = 2*m) (hK : 0 < K)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε < α) :
    uniformProb (fun ω : MonteSpace v.total m K =>
      exactInterval α (canonicalObserved v ω.1.val) ⊆
        monteInterval true α ε (canonicalObserved v ω.1.val) ω.2) ≥
          1-2*(testBudget v.total : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) ∧
    (0 < α-2*ε → uniformProb (fun ω : MonteSpace v.total m K =>
      monteInterval true α ε (canonicalObserved v ω.1.val) ω.2 ⊆
        exactInterval (α-2*ε) (canonicalObserved v ω.1.val)) ≥
          1-2*(testBudget v.total : ℝ)*Real.exp (-2*(K : ℝ)*ε^2)) := by
  let instGLP0032B6FinalAssignmentNonempty := GLP0032B6_assignment_nonempty v.total m (by omega)
  let δ := 2*(testBudget v.total : ℝ)*Real.exp (-2*(K : ℝ)*ε^2)
  have hcond (z : Assignment v.total m) := GLP0032B6_canonical_design v m hn z
  have hfail (z : Assignment v.total m) := GLP0032B6_conditional_failure
    (canonicalObserved v z.val) α ε (hcond z).1 (hcond z).2.1
    (show 0 < (canonicalObserved v z.val).a+(canonicalObserved v z.val).b ∧
      (canonicalObserved v z.val).a+(canonicalObserved v z.val).b =
        (canonicalObserved v z.val).c+(canonicalObserved v z.val).d from
      ⟨by rw [(hcond z).2.1]; exact hm,by rw [(hcond z).2.1,(hcond z).2.2]⟩)
    (by omega) hK hα hε.1
  constructor
  · have h := GLP0032B6_observed_average
      (fun (z : Assignment v.total m) pool =>
        ¬exactInterval α (canonicalObserved v z.val) ⊆
          monteInterval true α ε (canonicalObserved v z.val) pool) δ
      (fun z => (hfail z).1)
    have hc := GLP0032B6_prob_compl (fun ω : MonteSpace v.total m K =>
      ¬exactInterval α (canonicalObserved v ω.1.val) ⊆
        monteInterval true α ε (canonicalObserved v ω.1.val) ω.2)
    simp only [not_not] at hc
    rw [hc]
    linarith
  · intro hβ
    have h := GLP0032B6_observed_average
      (fun (z : Assignment v.total m) pool =>
        ¬monteInterval true α ε (canonicalObserved v z.val) pool ⊆
          exactInterval (α-2*ε) (canonicalObserved v z.val)) δ
      (fun z => (hfail z).2 hβ)
    have hc := GLP0032B6_prob_compl (fun ω : MonteSpace v.total m K =>
      ¬monteInterval true α ε (canonicalObserved v ω.1.val) ω.2 ⊆
        exactInterval (α-2*ε) (canonicalObserved v ω.1.val))
    simp only [not_not] at hc
    rw [hc]
    linarith

end AronowAudit.P003.Wave1
