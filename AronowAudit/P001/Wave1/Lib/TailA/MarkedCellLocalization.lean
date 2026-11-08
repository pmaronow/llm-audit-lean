import AronowAudit.P001.Wave1.Lib.TailA.ReuseMoments
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDensity

/-! Actual multinomial void bounds and the deterministic geometry of a pinned cell. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellLocalization (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- No original label in the specified category is retained by a size-`n+1` resample.
The central pinned label is separate from these `n` independent original labels. -/
def markedNoRetained {n : ℕ} (E : Set MatchUnit) (z : Fin n → MatchUnit)
    (a : Fin (n+1) → Fin (n+1)) : Prop :=
  ∀ i, z i ∈ E → ∀ t, a t ≠ i.succ

theorem marked_no_retained_measurable (n : ℕ) (E : Set MatchUnit)
    (hE : MeasurableSet E) (a : Fin (n+1) → Fin (n+1)) :
    MeasurableSet {z : Fin n → MatchUnit | markedNoRetained E z a} := by
  simp only [markedNoRetained, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases h : ∀ t, a t ≠ i.succ
  · convert MeasurableSet.univ using 1
    ext z
    simp [h]
  · have hm : Measurable (fun z : Fin n → MatchUnit => z i) := measurable_pi_apply i
    convert (hE.preimage hm).compl using 1
    ext z
    simp [h]

theorem marked_exp_count_product {n : ℕ} (E : Set MatchUnit)
    (z : Fin n → MatchUnit) (c : ℝ) :
    c^(Finset.univ.filter (fun i => z i ∈ E)).card =
      ∏ i, if z i ∈ E then c else 1 := by
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]

/-- A conditional bound for the actual multinomial resample, including the pinned label. -/
theorem marked_no_retained_conditional (n : ℕ) (E : Set MatchUnit)
    (z : Fin n → MatchUnit) :
    mean (UniformResampling (n+1))
      (fun a => if markedNoRetained E z a then 1 else 0) ≤
        ∏ i, if z i ∈ E then Real.exp (-1) else 1 := by
  let e : Fin n ↪ Fin (n+1) := ⟨Fin.succ, Fin.succ_injective n⟩
  let D := (Finset.univ.filter (fun i => z i ∈ E)).map e
  have heq (a : Fin (n+1) → Fin (n+1)) :
      markedNoRetained E z a ↔ ∀ t, a t ∉ D := by
    constructor
    · intro h t ht
      obtain ⟨i,hi,hit⟩ := Finset.mem_map.mp ht
      exact h i (Finset.mem_filter.mp hi).2 t hit.symm
    · intro h i hi t ht
      exact h t (Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hi⟩,ht.symm⟩)
  simp only [heq]
  have hb := reuse_uniform_avoid_le_exp (Nat.succ_pos n) D
  simpa only [D,Finset.card_map,marked_exp_count_product] using hb

/-- The one-point response-mark generating function, under any probability law. -/
theorem marked_category_generating_integral (E : Set MatchUnit) (hE : MeasurableSet E) :
    (∫ u, (if u ∈ E then Real.exp (-1) else 1) ∂matchingUnitLaw) =
      1-matchS*(matchingUnitLaw.real E) := by
  have heq : (fun u : MatchUnit => if u ∈ E then Real.exp (-1) else 1) =
      fun u => 1-matchS*E.indicator (fun _ => (1 : ℝ)) u := by
    funext u
    by_cases hu : u ∈ E <;> simp [hu,matchS] <;> ring
  rw [heq,integral_sub (integrable_const _)
    (((integrable_const (1 : ℝ)).indicator hE).const_mul _),
    integral_const_mul, integral_indicator_const _ hE]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one]

/-- Actual finite-sample exponential localization bound.  No Poisson replacement is used. -/
theorem marked_no_retained_bound (n : ℕ) (E : Set MatchUnit) (hE : MeasurableSet E) :
    mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
      (fun a => if markedNoRetained E z a then 1 else 0)) ≤
        Real.exp (-(matchS*matchingUnitLaw.real E)*(n : ℝ)) := by
  let f : MatchUnit → ℝ := fun u => if u ∈ E then Real.exp (-1) else 1
  have hf : Measurable f := Measurable.ite hE measurable_const measurable_const
  have hfi : Integrable f matchingUnitLaw := by
    apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    apply ae_of_all
    intro u
    dsimp [f]
    split_ifs
    · rw [abs_of_pos (Real.exp_pos _)]
      exact (Real.exp_lt_one_iff.mpr (by norm_num)).le
    · norm_num
  have hprod : Integrable (fun z : Fin n → MatchUnit => ∏ i, f (z i))
      (MatchProduct n) := by
    exact Integrable.fintype_prod (fun _ => hfi)
  calc
    _ ≤ ∫ z : Fin n → MatchUnit, ∏ i, f (z i) ∂MatchProduct n := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun z => integral_nonneg (fun a => by split_ifs <;> norm_num))
      · exact hprod
      · exact ae_of_all _ (fun z => marked_no_retained_conditional n E z)
    _ = (1-matchS*matchingUnitLaw.real E)^n := by
      change (∫ z : Fin n → MatchUnit, ∏ i, f (z i) ∂Measure.pi
        (fun _ => matchingUnitLaw)) = _
      rw [integral_fintype_prod_eq_pow]
      simp only [Fintype.card_fin]
      rw [marked_category_generating_integral E hE]
    _ ≤ _ := by
      have hbase : 0 ≤ 1-matchS*matchingUnitLaw.real E := by
        rw [← marked_category_generating_integral E hE]
        exact integral_nonneg (fun u => by split_ifs <;> positivity)
      have hexp : 1-matchS*matchingUnitLaw.real E ≤
          Real.exp (-(matchS*matchingUnitLaw.real E)) := by
        have h := Real.add_one_le_exp (-(matchS*matchingUnitLaw.real E))
        linarith
      calc
        _ ≤ (Real.exp (-(matchS*matchingUnitLaw.real E)))^n :=
          pow_le_pow_left₀ hbase hexp n
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem marked_retained_interval_void_bound (n : ℕ) (a b : ℝ)
    (hab : a ≤ b) (ha : (1/4 : ℝ) ≤ a) (hb : b ≤ (3/4 : ℝ)) :
    mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
      (fun c => if markedNoRetained (markedTypeInterval true a b) z c then 1 else 0)) ≤
        Real.exp (-matchS*(b-a)*(n : ℝ)/2) := by
  apply le_trans (marked_no_retained_bound n _ (marked_type_interval_measurable _ _ _))
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ matchS := by
    unfold matchS
    have := (Real.exp_lt_one_iff.mpr (show (-1 : ℝ) < 0 by norm_num)).le
    linarith
  have hmass := marked_donor_interval_lower a b hab ha hb
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass hs) (show (0 : ℝ) ≤ n by positivity)
  nlinarith

/-- A physical radius `R/n` has an exponentially small retained-donor void bound. -/
theorem marked_retained_window_void_bound {n : ℕ} (hn : 0 < n) (p R : ℝ)
    (hR : 0 ≤ R) (ha : (1/4 : ℝ) ≤ p) (hb : p+R/(n : ℝ) ≤ (3/4 : ℝ)) :
    mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
      (fun c => if markedNoRetained (markedTypeInterval true p (p+R/(n : ℝ))) z c
        then 1 else 0)) ≤ Real.exp (-matchS*R/2) := by
  have h := marked_retained_interval_void_bound n p (p+R/(n : ℝ))
    (le_add_of_nonneg_right (div_nonneg hR (Nat.cast_nonneg _))) ha hb
  convert h using 1
  congr 1
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  <;> ring

/-- Hölder control for removing a rare localization event under a fourth-moment bound. -/
theorem marked_masked_square_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (E : Set Ω) (hE : MeasurableSet E)
    (hi2 : Integrable (fun x => (X x)^2) μ)
    (hi4 : Integrable (fun x => (X x)^4) μ)
    {C t : ℝ} (ht : 0 < t)
    (hfourth : (∫ x, (X x)^4 ∂μ) ≤ C) (hvoid : μ.real E ≤ t^2) :
    (∫ x, (if x ∈ E then (X x)^2 else 0) ∂μ) ≤ (C+1)*t/2 := by
  have hpoint (x : Ω) :
      2*t*(if x ∈ E then (X x)^2 else 0) ≤
        t^2*(X x)^4+E.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ E
    · simp only [if_pos hx,Set.indicator_of_mem hx]
      nlinarith [sq_nonneg (t*(X x)^2-1)]
    · simp only [if_neg hx,Set.indicator_of_notMem hx,mul_zero,add_zero]
      positivity
  have hleft : Integrable (fun x => 2*t*(if x ∈ E then (X x)^2 else 0)) μ :=
    (hi2.indicator hE).const_mul _
  have hright : Integrable (fun x => t^2*(X x)^4+E.indicator (fun _ => (1 : ℝ)) x) μ :=
    (hi4.const_mul _).add ((integrable_const _).indicator hE)
  have h := integral_mono hleft hright hpoint
  rw [integral_const_mul,integral_add (hi4.const_mul _)
    ((integrable_const _).indicator hE),integral_const_mul,integral_indicator_const _ hE] at h
  simp only [smul_eq_mul,mul_one] at h
  have hmul := mul_le_mul_of_nonneg_left hfourth (sq_nonneg t)
  nlinarith

/-- A nearer donor to the right excludes queries beyond its midpoint. -/
theorem marked_right_midpoint_exclusion {p x q : ℝ} (hpq : p < q)
    (hmin : |p-x| ≤ |q-x|) : x ≤ (p+q)/2 := by
  by_contra h
  have hx : (p+q)/2 < x := lt_of_not_ge h
  have hpx : p < x := by linarith
  rw [abs_of_neg (by linarith : p-x < 0)] at hmin
  rcases le_total q x with hqx | hxq
  · rw [abs_of_nonpos (sub_nonpos.mpr hqx)] at hmin
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hxq)] at hmin
    linarith

theorem marked_left_midpoint_exclusion {p x q : ℝ} (hqp : q < p)
    (hmin : |p-x| ≤ |q-x|) : (p+q)/2 ≤ x := by
  have h := marked_right_midpoint_exclusion
    (p := -p) (x := -x) (q := -q) (by linarith)
  have hmin' : |-p- -x| ≤ |-q- -x| := by
    simpa only [neg_sub_neg,abs_sub_comm] using hmin
  have h' := h hmin'
  linarith

/-- Two retained neighboring donors localize every actual assignment to the pinned donor.
Bootstrap copies of any original label may tie; the result uses only minimality. -/
theorem marked_assignment_localized {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (t k j l u : Fin n) (R : ℝ)
    (hk : a k = j) (hd : nearestDonor (p ∘ a) (r ∘ a) t = some k)
    (hl : reuseRetained r a l) (hu : reuseRetained r a u)
    (hlp : p j-R < p l ∧ p l < p j) (hup : p j < p u ∧ p u < p j+R) :
    p j-R/2 < p (a t) ∧ p (a t) < p j+R/2 := by
  obtain ⟨hrl,v,hv⟩ := hl
  obtain ⟨hru,w,hw⟩ := hu
  have hnear := (reuse_nearest_minimal (p ∘ a) (r ∘ a) t k hd).2
  have hleft := hnear v (by simpa only [Function.comp_apply,hv] using hrl)
  have hright := hnear w (by simpa only [Function.comp_apply,hw] using hru)
  simp only [Function.comp_apply,hk,hv] at hleft
  simp only [Function.comp_apply,hk,hw] at hright
  have hL := marked_left_midpoint_exclusion hlp.2 hleft
  have hR := marked_right_midpoint_exclusion hup.1 hright
  constructor <;> linarith

theorem marked_far_competitor_excluded {p x q R : ℝ}
    (hx : |x-p| < R/2) (hq : R ≤ |q-p|) : |p-x| < |q-x| := by
  have htri := abs_sub_le q x p
  rw [abs_sub_comm p x]
  linarith

/-- A central assignment comparison is determined inside the radius-`R` window
for every query inside the half-radius window. -/
theorem marked_comparison_localized {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j i : Fin n) (R : ℝ) (hi : |p i-p j| < R/2) :
    (∀ l, reuseRetained r a l → |p j-p i| ≤ |p l-p i|) ↔
      (∀ l, reuseRetained r a l → |p l-p j| < R → |p j-p i| ≤ |p l-p i|) := by
  constructor
  · exact fun h l hl _ => h l hl
  · intro h l hl
    by_cases hlocal : |p l-p j| < R
    · exact h l hl hlocal
    · exact (marked_far_competitor_excluded hi (le_of_not_gt hlocal)).le

/-- A cell is specified by the actual retained original-label sites. -/
def markedCellContains {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j i : Fin n) : Prop :=
  reuseRetained r a j ∧ ∀ l, reuseRetained r a l → |p j-p i| ≤ |p l-p i|

/-- Distinct original-site comparison distances suffice even though bootstrap copies tie. -/
theorem marked_selected_original_iff {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j : Fin n)
    (hp : ∀ i l v, l ≠ v → |p l-p i| ≠ |p v-p i|) (t : Fin n) :
    Option.map a (nearestDonor (p ∘ a) (r ∘ a) t) = some j ↔
      markedCellContains p r a j (a t) := by
  unfold nearestDonor
  split_ifs with hex
  · let k := Classical.choose hex
    have hk := Classical.choose_spec hex
    change r (a k) = true ∧ ∀ v, r (a v) = true →
      |p (a k)-p (a t)| ≤ |p (a v)-p (a t)| at hk
    simp only [Option.map_some,Option.some.injEq]
    change a k = j ↔ _
    constructor
    · intro hkj
      refine ⟨⟨by simpa only [Function.comp_apply,hkj] using hk.1,k,hkj⟩,?_⟩
      intro l hl
      obtain ⟨hr,v,hv⟩ := hl
      have h := hk.2 v (by simpa only [Function.comp_apply,hv] using hr)
      simpa only [Function.comp_apply,hkj,hv] using h
    · intro hcell
      have hkret : reuseRetained r a (a k) := ⟨hk.1,k,rfl⟩
      have hle := hcell.2 (a k) hkret
      obtain ⟨hr,v,hv⟩ := hcell.1
      have hge := hk.2 v (by simpa only [Function.comp_apply,hv] using hr)
      simp only [Function.comp_apply,hv] at hge
      by_contra hne
      exact hp (a t) (a k) j hne (le_antisymm hge hle)
  · simp only [Option.map_none,reduceCtorEq,false_iff]
    intro hcell
    obtain ⟨hr,v,hv⟩ := hcell.1
    apply hex
    refine ⟨v,by simpa only [Function.comp_apply,hv] using hr,?_⟩
    intro k hk
    have h := hcell.2 (a k) ⟨hk,k,rfl⟩
    simpa only [Function.comp_apply,hv] using h

/-- Exact aggregation by original multiplicity and retained-site cell membership. -/
theorem marked_aggregated_weight {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j : Fin n)
    (hp : ∀ i l v, l ≠ v → |p l-p i| ≠ |p v-p i|) :
    bootstrapOriginalReuse p r a j =
      ∑ i, reuseOccupancy a i *
        (if r i then (if i = j then 1 else 0)
          else if markedCellContains p r a j i then 1 else 0) := by
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
  rw [Finset.sum_add_distrib,Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  cases hr : r (a t) with
  | true => simp [hr]
  | false =>
    simp only [hr,Bool.false_eq_true,ite_false,zero_add,true_and,ite_self]
    have hcell := marked_selected_original_iff p r a j hp t
    cases hd : nearestDonor (p ∘ a) (r ∘ a) t with
    | none =>
      simp only [hd,Option.map_none,reduceCtorEq,false_iff] at hcell
      simp [hcell]
    | some k =>
      simp only [hd,Option.map_some,Option.some.injEq] at hcell
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
      rw [← hcell]
      simp

end AronowAudit.P001.TailA
