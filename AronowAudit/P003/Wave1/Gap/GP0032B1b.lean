import AronowAudit.P003.Wave1.Gap.GLP0032B6

/-! P003-T34: balanced Monte Carlo coverage and approximation. -/

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

/-! ## Coverage arithmetic and probability helpers -/

/-- Inversion of the recommended Monte Carlo sample-size inequality. -/
theorem GP0032B1b_recommended_K_tail_inversion (C ε : ℝ) (K : ℕ)
    (hC : 0 < C) (hε : 0 < ε)
    (hK : Real.log (C/ε)/(2*ε^2) ≤ (K : ℝ)) :
    C*Real.exp (-2*(K : ℝ)*ε^2) ≤ ε := by
  have hden : 0 < 2*ε^2 := by positivity
  have hlog : Real.log (C/ε) ≤ (K : ℝ)*(2*ε^2) :=
    (div_le_iff₀ hden).mp hK
  have he : Real.exp (-2*(K : ℝ)*ε^2) ≤ Real.exp (-Real.log (C/ε)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    C*Real.exp (-2*(K : ℝ)*ε^2) ≤ C*Real.exp (-Real.log (C/ε)) :=
      mul_le_mul_of_nonneg_left he hC.le
    _ = ε := by
      rw [Real.exp_neg, Real.exp_log (div_pos hC hε)]
      field_simp [ne_of_gt hC, ne_of_gt hε] <;> ring

/-- The deterministic numerical budget comparison, independent of all searches. -/
theorem GP0032B1b_two_budget_le (n : ℕ) (hn : 15 ≤ n) :
    2*(testBudget n : ℝ) ≤ 4*(n : ℝ)*logTwo n := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases h16 : 16 ≤ n
  · have hnR : (16 : ℝ) ≤ n := by exact_mod_cast h16
    have hnpos : (0 : ℝ) < n := by linarith
    have hlog16 : Real.log (16 : ℝ) = 4*Real.log 2 := by
      simpa only [show (2 : ℝ)^4 = 16 by norm_num, Nat.cast_ofNat] using
        (Real.log_pow (2 : ℝ) 4)
    have hlower : 4*Real.log 2 ≤ Real.log (n : ℝ) := by
      rw [← hlog16]
      exact Real.log_le_log (by norm_num) hnR
    have hL : 4 ≤ logTwo n := by
      unfold logTwo
      apply (le_div_iff₀ h2).mpr
      simpa only [mul_comm] using hlower
    have hpoly : ((n : ℝ)+1)^2 ≤ 2*(n : ℝ)^2 := by nlinarith
    have hlogs := Real.log_le_log
      (sq_pos_of_pos (by linarith : 0 < (n : ℝ)+1)) hpoly
    rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (sq_pos_of_pos hnpos)), Real.log_pow] at hlogs
    have hhalf : logTwo ((n : ℝ)+1) ≤ logTwo n+1/2 := by
      unfold logTwo
      apply (div_le_iff₀ h2).mpr
      have hcancel : (Real.log (n : ℝ)/Real.log 2)*Real.log 2 =
          Real.log (n : ℝ) := div_mul_cancel₀ _ (ne_of_gt h2)
      norm_num only [Nat.cast_ofNat] at hlogs
      nlinarith
    have hh : (Nat.log2 (n+1) : ℝ) ≤ logTwo ((n : ℝ)+1) := by
      simpa only [Real.logb, logTwo, Nat.cast_add, Nat.cast_one] using
        (Real.log2_le_logb (n+1))
    have hD : (testBudget n : ℝ) =
        ((n : ℝ)+1)*((Nat.log2 (n+1) : ℝ)+3) := by
      simp only [testBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    have hmul : ((n : ℝ)+1)*((Nat.log2 (n+1) : ℝ)+3) ≤
        ((n : ℝ)+1)*(logTwo n+7/2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have hproduct : 0 ≤ ((n : ℝ)-1)*(logTwo n-4) :=
      mul_nonneg (by linarith) (by linarith)
    have hlast : ((n : ℝ)+1)*(logTwo n+7/2) ≤ 2*(n : ℝ)*logTwo n := by
      nlinarith
    nlinarith [hmul.trans hlast]
  · have hn15 : n = 15 := by omega
    subst n
    have hlog := Real.log_lt_log
      (by norm_num : (0 : ℝ) < 2^15) (by norm_num : (2 : ℝ)^15 < 15^4)
    rw [Real.log_pow, Real.log_pow] at hlog
    have hL : (15 : ℝ)/4 < logTwo 15 := by
      unfold logTwo
      apply (lt_div_iff₀ h2).mpr
      norm_num only [Nat.cast_ofNat] at hlog
      nlinarith
    have hD : testBudget 15 = 112 := by decide +kernel
    rw [hD]
    norm_num only [Nat.cast_ofNat]
    nlinarith

theorem GP0032B1b_constant_pos (n : ℕ) (hn : 15 ≤ n) :
    0 < 4*(n : ℝ)*logTwo n := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hl : 0 < logTwo n :=
    div_pos (Real.log_pos hnR) (Real.log_pos (by norm_num))
  have hnpos : (0 : ℝ) < n := by linarith
  positivity

/-- The average of the actual tail indicators is nonnegative, including K=0. -/
theorem GP0032B1b_monteMean_nonneg {n K : ℕ} (v o : Counts)
    (draws : Fin K → Finset (Fin n)) : 0 ≤ (monteMean v o draws : ℝ) := by
  have hq : (0 : ℚ) ≤ monteMean v o draws := by
    unfold monteMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> norm_num
    · exact Nat.cast_nonneg K
  exact_mod_cast hq

/-- Decision-rule half of the large-tolerance coverage branch. -/
theorem GP0032B1b_all_tests_accept {n m K : ℕ} (β ε : ℝ) (o v : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (idx : ℕ) (hβε : β ≤ ε) : approximateReject β ε o pool v idx = false := by
  have hs := GP0032B1b_monteMean_nonneg v o (batch pool idx)
  have hnot : ¬ (monteMean v o (batch pool idx) : ℝ)+ε < β := by linarith
  simp only [approximateReject, hnot, decide_false]

/-- Every integer in the feasible balanced effect range has an imputation witness.
U and V are the sums of missing potential outcomes in controls and treated units. -/
theorem GP0032B1b_possible_of_effect (o : Counts) (x : ℤ)
    (hbal : o.a+o.b = o.c+o.d)
    (hlo : (o.a : ℤ)-o.c-(o.a+o.b) ≤ x)
    (hhi : x ≤ (o.a : ℤ)-o.c+(o.a+o.b)) :
    ∃ v, Possible o v ∧ v.effect = x := by
  let U := (x-((o.a : ℤ)-o.c)).toNat
  let V := (((o.a : ℤ)-o.c)-x).toNat
  have hU : U ≤ o.c+o.d := by dsimp [U]; omega
  have hV : V ≤ o.a+o.b := by dsimp [V]; omega
  have hdiff : x = (o.a : ℤ)-o.c+(U : ℤ)-(V : ℤ) := by
    dsimp [U, V]
    omega
  let i := min o.a V
  let j := V-i
  let k := min o.c U
  let l := U-k
  have hi : i ≤ o.a := Nat.min_le_left _ _
  have hj : j ≤ o.b := by dsimp [j, i]; omega
  have hk : k ≤ o.c := Nat.min_le_left _ _
  have hl : l ≤ o.d := by dsimp [l, k]; omega
  have hVs : i+j = V := by dsimp [i, j]; omega
  have hUs : k+l = U := by dsimp [k, l]; omega
  let v : Counts := ⟨i+k, o.a-i+l, o.c-k+j, o.b+o.d-j-l⟩
  refine ⟨v, ?_, ?_⟩
  · simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨i, by omega, j, by omega, k, by omega, l, by omega, rfl⟩
  · dsimp [v, Counts.effect]
    omega

/-- An actual candidate is present at every query in the balanced upper domain.
The corrected general loop supplies a candidate; no p-value theorem is used. -/
theorem GP0032B1b_candidates_nonempty (o : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (x : ℤ)
    (hlo : 2*((o.a : ℤ)-o.c) ≤ x)
    (hhi : x ≤ (o.a : ℤ)-o.c+(o.a+o.b)) : candidates o x ≠ [] := by
  have hfull : (o.a : ℤ)-o.c-(o.a+o.b) ≤ x := by omega
  obtain ⟨u, hu, hux⟩ := GP0032B1b_possible_of_effect o x ho.2 hfull hhi
  obtain ⟨hj, w, hw, _⟩ := (corrected_general_loop o u hu).2
  rw [hux] at hw
  have hmem : w ∈ candidates o x := by
    unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨u.a+u.b, List.mem_range.mpr (by omega), ?_⟩
    rw [hw]
    dsimp only
    split_ifs <;> simp
  intro he
  rw [he] at hmem
  exact List.not_mem_nil hmem

theorem GP0032B1b_runTests_accept (reject : Counts → ℕ → Bool)
    (hrej : ∀ v idx, reject v idx = false) (idx : ℕ) (vs : List Counts)
    (hvs : vs ≠ []) : (runTests reject idx vs).compatible = true := by
  cases vs with
  | nil => exact False.elim (hvs rfl)
  | cons v vs => simp only [runTests, hrej, Bool.false_eq_true, if_false]

/-- When every nonempty query accepts, the corrected sentinel search reaches k₂.
Fuel is charged by the strictly increasing lower sentinel, not a logarithmic bound. -/
theorem GP0032B1b_all_accept_search (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool)
    (hcan : ∀ x, k₁ ≤ x → x ≤ k₂ → candidates o x ≠ [])
    (hrej : ∀ v idx, reject v idx = false)
    (a : ℤ) (idx : ℕ) (ha : k₁-1 ≤ a) (ha' : a ≤ k₂)
    (hf : k₂-a ≤ (fuel : ℤ)) :
    (adaptiveSearch fuel true o k₁ k₂ reject a (k₂+1) idx).value = some k₂ := by
  induction fuel generalizing a idx with
  | zero =>
    have he : a = k₂ := by omega
    subst a
    rw [adaptiveSearch]
    simp only [true_and, le_refl, if_true]
  | succ fuel ih =>
    by_cases he : a = k₂
    · subst a
      rw [adaptiveSearch]
      simp only [true_and, le_refl, if_true]
    · have hadj : ¬ k₂+1 ≤ a+1 := by omega
      let c : ℤ := (a+(k₂+1))/2
      have hc₁ : k₁ ≤ c := by dsimp [c]; omega
      have hc₂ : c ≤ k₂ := by dsimp [c]; omega
      have hac : a < c := by dsimp [c]; omega
      have hq : (runTests reject idx (candidates o c)).compatible = true :=
        GP0032B1b_runTests_accept reject hrej idx _ (hcan c hc₁ hc₂)
      dsimp only [c] at hq
      rw [adaptiveSearch]
      simp only [true_and, if_neg hadj, hq, if_true,
        not_true_eq_false, false_and, if_false]
      change (adaptiveSearch fuel true o k₁ k₂ reject c (k₂+1)
        (runTests reject idx (candidates o c)).idx).value = some k₂
      exact ih c _ (by omega) hc₂ (by omega)

theorem GP0032B1b_all_accept_upper (o : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (reject : Counts → ℕ → Bool) (hrej : ∀ v idx, reject v idx = false) (idx : ℕ) :
    (upperRun true o reject idx).value = some ((o.a : ℤ)-o.c+(o.a+o.b)) := by
  change (adaptiveSearch (o.total+3) true o (2*((o.a : ℤ)-o.c))
    ((o.a : ℤ)-o.c+(o.a+o.b)) reject (2*((o.a : ℤ)-o.c)-1)
    ((o.a : ℤ)-o.c+(o.a+o.b)+1) idx).value = _
  apply GP0032B1b_all_accept_search
  · intro x hx hy
    exact GP0032B1b_candidates_nonempty o ho x hx hy
  · exact hrej
  · omega
  · omega
  · dsimp [Counts.total]
    omega

/-- The entire possible-effect hull is covered in the large-tolerance branch. -/
theorem GP0032B1b_all_accept_returns_candidate_hull {n m K : ℕ} (β ε : ℝ)
    (o u : Counts) (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (hβε : β ≤ ε) (hu : Possible o u) :
    tau u ∈ monteInterval true β ε o pool := by
  have hrej : ∀ v idx, approximateReject β ε o pool v idx = false := by
    intro v idx
    exact GP0032B1b_all_tests_accept β ε o v pool idx hβε
  have hoc : 0 < (complementObserved o).a+(complementObserved o).b ∧
      (complementObserved o).a+(complementObserved o).b =
        (complementObserved o).c+(complementObserved o).d := by
    dsimp [complementObserved]
    omega
  have hrejc : ∀ v idx, approximateReject β ε (complementObserved o) pool v idx = false := by
    intro v idx
    exact GP0032B1b_all_tests_accept β ε (complementObserved o) v pool idx hβε
  have hhi := GP0032B1b_all_accept_upper o ho _ hrej 0
  have hlo := GP0032B1b_all_accept_upper (complementObserved o) hoc _ hrejc
    (upperRun true o (approximateReject β ε o pool)).trace.length
  dsimp only [monteInterval, monteEndpoints]
  rw [hlo, hhi]
  have htotal := (possible_table_facts o u hu).1
  have heff := (possible_table_facts o u hu).2
  simp only [candidateNumerators, List.mem_map, List.mem_range] at heff
  obtain ⟨k, hk, he⟩ := heff
  have hnum : -(((complementObserved o).a : ℤ)-(complementObserved o).c+
        ((complementObserved o).a+(complementObserved o).b : ℕ)) ≤ u.effect ∧
      u.effect ≤ (o.a : ℤ)-o.c+(o.a+o.b) := by
    dsimp [complementObserved, Counts.total] at *
    omega
  have hnpos : (0 : ℝ) < o.total := by
    have hp : 0 < o.total := by dsimp [Counts.total]; omega
    exact_mod_cast hp
  simp only [Set.mem_Icc, tau, tauQ, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_natCast, htotal]
  constructor
  · apply div_le_div_of_nonneg_right _ hnpos.le
    exact_mod_cast hnum.1
  · apply div_le_div_of_nonneg_right _ hnpos.le
    exact_mod_cast hnum.2

/-- Monotonicity of the exact finite uniform probability definition. -/
theorem GP0032B1b_uniformProb_mono {Ω : Type*} [Fintype Ω] (E F : Ω → Prop)
    (hEF : ∀ ω, E ω → F ω) : uniformProb E ≤ uniformProb F := by
  have hs : Finset.univ.filter E ⊆ Finset.univ.filter F := by
    intro ω hω
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ ω, hEF ω (Finset.mem_filter.mp hω).2⟩
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card hs

/-- Intersection form of the finite union bound used by coverage composition. -/
theorem GP0032B1b_uniformProb_inter_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E F : Ω → Prop) :
    uniformProb E + uniformProb F - 1 ≤ uniformProb (fun ω => E ω ∧ F ω) := by
  let s := Finset.univ.filter E
  let t := Finset.univ.filter F
  have hu : (s ∪ t).card ≤ Fintype.card Ω := by
    simpa only [Finset.card_univ] using
      (Finset.card_le_card (Finset.subset_univ (s ∪ t)))
  have hi : s ∩ t = Finset.univ.filter (fun ω => E ω ∧ F ω) := by
    ext ω
    simp only [s, t, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and]
  have hc := Finset.card_union_add_card_inter s t
  rw [hi] at hc
  have hnat : s.card+t.card ≤ Fintype.card Ω +
      (Finset.univ.filter (fun ω => E ω ∧ F ω)).card := by omega
  have hr : (s.card : ℝ)+(t.card : ℝ)-(Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => E ω ∧ F ω)).card : ℝ) := by
    have hcast : (s.card : ℝ)+(t.card : ℝ) ≤ (Fintype.card Ω : ℝ) +
        ((Finset.univ.filter (fun ω => E ω ∧ F ω)).card : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hpos : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hd := div_le_div_of_nonneg_right hr hpos.le
  convert (show _ from hd) using 1 <;>
    simp only [sub_div, add_div, div_self (ne_of_gt hpos), s, t, uniformProb] <;>
    congr 3 <;> ext ω <;> simp


/-! Deterministic canonical observation helpers. -/

lemma GP0032B1b_segment_card (n a b : ℕ) (h : a+b ≤ n) :
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

lemma GP0032B1b_canonical_type_cards (v : Counts) :
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (true,true))).card = v.a ∧
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (true,false))).card = v.b ∧
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (false,true))).card = v.c ∧
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (false,false))).card = v.d := by
  have hseg := GP0032B1b_segment_card v.total
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

lemma GP0032B1b_pair_split {I : Type*} [DecidableEq I]
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

lemma GP0032B1b_observed_bridge (v : Counts) (z : Finset (Fin v.total)) :
    observed v (treatedCounts v z) = canonicalObserved v z := by
  classical
  let w := fun i : Fin v.total => canonicalPair v i.val
  have hcard := GP0032B1b_canonical_type_cards v
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
    rw [ht true,(GP0032B1b_pair_split z w true).1]
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [ht false,(GP0032B1b_pair_split z w false).1]
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [hc true,(GP0032B1b_pair_split (Finset.univ \ z) w true).2,
      hcontrol,hcontrol,hcard.1,hcard.2.2.1]
    dsimp [w] at *
    omega
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [hc false,(GP0032B1b_pair_split (Finset.univ \ z) w false).2,
      hcontrol,hcontrol,hcard.2.1,hcard.2.2.2]
    dsimp [w] at *
    omega


lemma GP0032B1b_bool_card {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → Bool) :
    (s.filter (fun i => f i = true)).card +
      (s.filter (fun i => f i = false)).card = s.card := by
  have he (i : I) : ¬ f i = true ↔ f i = false := by cases f i <;> simp
  simpa only [he] using
    (Finset.card_filter_add_card_filter_not (s := s) (fun i => f i = true))

lemma GP0032B1b_observed_arms {n : ℕ} (v : Counts) (z : Finset (Fin n)) :
    (canonicalObserved v z).a + (canonicalObserved v z).b = z.card ∧
    (canonicalObserved v z).c + (canonicalObserved v z).d = n-z.card := by
  have ht (b : Bool) :
      (Finset.univ.filter (fun i => i ∈ z ∧ (canonicalPair v i.val).1 = b)) =
        z.filter (fun i => (canonicalPair v i.val).1 = b) := by ext i; simp
  have hc (b : Bool) :
      (Finset.univ.filter (fun i => i ∉ z ∧ (canonicalPair v i.val).2 = b)) =
        (Finset.univ \ z).filter (fun i => (canonicalPair v i.val).2 = b) := by
    ext i; simp
  dsimp only [canonicalObserved]
  rw [ht true, ht false, hc true, hc false,
    GP0032B1b_bool_card, GP0032B1b_bool_card,
    Finset.card_sdiff_of_subset (Finset.subset_univ z), Finset.card_univ,
    Fintype.card_fin]
  exact ⟨rfl, rfl⟩

lemma GP0032B1b_treated_legal (v : Counts) (z : Finset (Fin v.total)) :
    let q := treatedCounts v z
    q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = z.card := by
  dsimp only
  have hc := GP0032B1b_canonical_type_cards v
  have hsub (b : Bool × Bool) :
      (z.filter (fun i => canonicalPair v i.val = b)).card ≤
        (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = b)).card := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [treatedCounts, hc.1] using hsub (true,true)
  · simpa only [treatedCounts, hc.2.1] using hsub (true,false)
  · simpa only [treatedCounts, hc.2.2.1] using hsub (false,true)
  · simpa only [treatedCounts, hc.2.2.2] using hsub (false,false)
  · have ha := (GP0032B1b_pair_split z (fun i => canonicalPair v i.val) true).1
    have hb := (GP0032B1b_pair_split z (fun i => canonicalPair v i.val) false).1
    have ht := GP0032B1b_bool_card z (fun i => (canonicalPair v i.val).1)
    change (treatedCounts v z).a + (treatedCounts v z).b +
      (treatedCounts v z).c + (treatedCounts v z).d = z.card
    dsimp only [treatedCounts]
    omega

lemma GP0032B1b_canonical_possible (v : Counts) (z : Finset (Fin v.total)) :
    Possible (canonicalObserved v z) v := by
  rw [← GP0032B1b_observed_bridge]
  obtain ⟨ha,hb,hc,hd,ht⟩ := GP0032B1b_treated_legal v z
  let q := treatedCounts v z
  change q.a ≤ v.a at ha
  change q.b ≤ v.b at hb
  change q.c ≤ v.c at hc
  change q.d ≤ v.d at hd
  change Possible (observed v q) v
  simp only [Possible,possibleTables,observed,List.mem_flatMap,List.mem_map,List.mem_range]
  refine ⟨q.a,?_,q.c,?_,v.a-q.a,?_,v.b-q.b,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · ext <;> dsimp <;> omega

lemma GP0032B1b_large_tolerance_pointwise (v : Counts) (m K : ℕ) (α ε : ℝ)
    (hm : 0 < m) (hn : v.total = 2*m) (hlarge : α/2 ≤ ε)
    (ω : MonteSpace v.total m K) :
    tau v ∈ monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2 := by
  apply GP0032B1b_all_accept_returns_candidate_hull
  · have ho := GP0032B1b_observed_arms v ω.1.val
    simp only [ω.1.property] at ho
    omega
  · linarith
  · exact GP0032B1b_canonical_possible v ω.1.val

lemma GP0032B1b_large_tolerance_probability (v : Counts) (m K : ℕ) (α ε : ℝ)
    (hm : 0 < m) (hn : v.total = 2*m) (hlarge : α/2 ≤ ε) :
    uniformProb (fun ω : MonteSpace v.total m K => tau v ∈
      monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2) = 1 := by
  have hA : Nonempty (Assignment v.total m) := by
    let z : Finset (Fin v.total) := Finset.univ.filter (fun i => i.val < m)
    have hz : z.card = m := by
      simpa [z] using GP0032B1b_segment_card v.total 0 m (by omega)
    exact ⟨⟨z,hz⟩⟩
  letI GP0032B1b_instNonemptyAssignment : Nonempty (Assignment v.total m) := hA
  have he : (fun ω : MonteSpace v.total m K => tau v ∈
      monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2) = (fun _ => True) := by
    funext ω
    exact propext ⟨fun _ => trivial,
      fun _ => GP0032B1b_large_tolerance_pointwise v m K α ε hm hn hlarge ω⟩
  rw [he]
  simp only [uniformProb, Finset.filter_true, Finset.card_univ]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

/-- An event on the first coordinate has its original uniform probability. -/
lemma GP0032B1b_uniformProb_first {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty B] (E : A → Prop) :
    uniformProb (fun ω : A × B => E ω.1) = uniformProb E := by
  rw [GLP0032B6_prob_avg, GLP0032B6_avg_prod]
  change GLP0032B6_avg (fun _ : B =>
    GLP0032B6_avg (fun a : A => if E a then 1 else 0)) = uniformProb E
  rw [GLP0032B6_avg_const, ← GLP0032B6_prob_avg]

/-- Exact coverage under the observed-assignment and simulation-pool joint law. -/
lemma GP0032B1b_exact_coverage_joint (v : Counts) (m K : ℕ) (β : ℝ)
    (hm : 0 < m) (hn : v.total = 2*m) (hβ : 0 < β ∧ β < 1) :
    uniformProb (fun ω : MonteSpace v.total m K =>
      tau v ∈ exactInterval β (canonicalObserved v ω.1.val)) ≥ 1-β := by
  letI GP0032B1b_jointAssignmentNonempty : Nonempty (Assignment v.total m) :=
    GLP0032B6_assignment_nonempty v.total m (by omega)
  rw [GP0032B1b_uniformProb_first
    (fun z : Assignment v.total m => tau v ∈ exactInterval β (canonicalObserved v z.val))]
  let w : PotentialTable v.total := fun i => canonicalPair v i.val
  have hw : tableCounts w = v := by
    have h := monte_rank_valid_canonical_type_cards v
    exact Counts.ext h.1 h.2.1 h.2.2.1 h.2.2.2
  let E : Counts → Prop := fun q => tau v ∈ exactInterval β (observed v q)
  have h := neyman_event_pushforward w v hw m E
  have he : (fun z : Assignment v.total m => E (neyman_treated w z.val)) =
      (fun z => tau v ∈ exactInterval β (canonicalObserved v z.val)) := by
    funext z
    have hobs : observed v (neyman_treated w z.val) = canonicalObserved v z.val :=
      monte_rank_valid_observed_bridge v z.val
    simp only [E, hobs]
  rw [← he, h]
  exact exact_coverage v m β ⟨hm, by omega⟩ hβ

/-- Proposition 4.6 with the prescribed joint law and actual corrected search. -/
theorem balanced_monte_coverage_proof (v : Counts) (m K : ℕ) (α ε : ℝ)
    (hm : 0 < m) (hn : v.total = 2*m) (hsize : 15 ≤ v.total) (hK : 0 < K)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε < α) :
    ((K : ℝ) ≥ Real.log (4*(v.total : ℝ)*logTwo v.total/ε)/(2*ε^2) →
      uniformProb (fun ω : MonteSpace v.total m K => tau v ∈
        monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2) ≥ 1-α) ∧
    (ε < α/3 → uniformProb (fun ω : MonteSpace v.total m K =>
      monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2 ⊆
        exactInterval (α-3*ε) (canonicalObserved v ω.1.val)) ≥
          1-4*(v.total : ℝ)*logTwo v.total*Real.exp (-2*(K : ℝ)*ε^2)) := by
  letI GP0032B1b_finalAssignmentNonempty : Nonempty (Assignment v.total m) :=
    GLP0032B6_assignment_nonempty v.total m (by omega)
  have hβ : 0 < α-ε ∧ α-ε < 1 := by constructor <;> linarith
  have hbudget := mul_le_mul_of_nonneg_right (GP0032B1b_two_budget_le v.total hsize)
    (Real.exp_pos (-2*(K : ℝ)*ε^2)).le
  constructor
  · intro hsample
    by_cases hlarge : α/2 ≤ ε
    · rw [GP0032B1b_large_tolerance_probability v m K α ε hm hn hlarge]
      linarith [hα.1]
    · have hshift : 0 < ε ∧ ε < α-ε := ⟨hε.1, by linarith⟩
      have hin := (corrected_monte_inclusions_proof v m K (α-ε) ε hm hn hK hβ hshift).1
      have hex := GP0032B1b_exact_coverage_joint v m K (α-ε) hm hn hβ
      have hinter := GP0032B1b_uniformProb_inter_lower
        (fun ω : MonteSpace v.total m K =>
          tau v ∈ exactInterval (α-ε) (canonicalObserved v ω.1.val))
        (fun ω : MonteSpace v.total m K =>
          exactInterval (α-ε) (canonicalObserved v ω.1.val) ⊆
            monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2)
      have hmono := GP0032B1b_uniformProb_mono
        (fun ω : MonteSpace v.total m K =>
          tau v ∈ exactInterval (α-ε) (canonicalObserved v ω.1.val) ∧
          exactInterval (α-ε) (canonicalObserved v ω.1.val) ⊆
            monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2)
        (fun ω : MonteSpace v.total m K => tau v ∈
          monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2)
        (fun ω h => h.2 h.1)
      have htail := GP0032B1b_recommended_K_tail_inversion
        (4*(v.total : ℝ)*logTwo v.total) ε K
        (GP0032B1b_constant_pos v.total hsize) hε.1 hsample
      linarith
  · intro hthird
    have hshift : 0 < ε ∧ ε < α-ε := ⟨hε.1, by linarith⟩
    have hout := (corrected_monte_inclusions_proof v m K (α-ε) ε hm hn hK hβ hshift).2
      (by linarith)
    have hlevel : α-ε-2*ε = α-3*ε := by ring
    rw [hlevel] at hout
    linarith

end AronowAudit.P003.Wave1
