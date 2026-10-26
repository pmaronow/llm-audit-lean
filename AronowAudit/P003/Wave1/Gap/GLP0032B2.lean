import AronowAudit.P003.P003_Audit

/-!
P003-T32: corrected exact search.
The proof uses a finite binomial shape induction, a two-unit Pascal decomposition,
one-unobserved-bit tail transport, candidate-line reduction, and stateful sentinel
search. Outcome reflection supplies the lower endpoint. The stronger pathwise
cost bound supplies the prescribed logarithmic total cost.
-/

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-- The chronological counter advances by the number of actual tests. -/
lemma glp0032b2_runTests_cost (reject : Counts → ℕ → Bool) (xs : List Counts) (idx : ℕ) :
    (runTests reject idx xs).idx = idx + (runTests reject idx xs).trace.length ∧
    (runTests reject idx xs).trace.length ≤ xs.length := by
  induction xs generalizing idx with
  | nil => simp [runTests]
  | cons v vs ih =>
    by_cases hv : reject v idx = true
    · have hi := ih (idx+1)
      simpa [runTests, hv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        And.intro hi.1 (Nat.succ_le_succ hi.2)
    · simp [runTests, hv]

/-- A uniform flat-map length bound. -/
lemma glp0032b2_flatMap_length {α β : Type*} (xs : List α) (f : α → List β) (B : ℕ)
    (hf : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

/-- Only a zero effect can contribute two candidates at one value of j. -/
lemma glp0032b2_candidates_length (o : Counts) (x : ℤ) :
    (candidates o x).length ≤ (o.total+1) * (if x = 0 then 2 else 1) := by
  unfold candidates
  generalize hjs : List.range (o.total+1) = js
  have hjlen : js.length = o.total+1 := by rw [← hjs, List.length_range]
  rw [← hjlen]
  apply glp0032b2_flatMap_length
  intro j hj
  cases hv : firstOnLine o x j with
  | none => simp
  | some v =>
    have he : v.effect = x := (first_on_line_spec o x j v hv).2.1
    by_cases hx : x = 0
    · simp only [if_pos hx]
      split <;> simp
    · have hn : ¬ (v.b = 0 ∧ v.c = 0 ∧ 1 ≤ v.a ∧ 1 ≤ v.d ∧
          Possible o ⟨v.a-1,1,1,v.d-1⟩) := by
        intro h
        apply hx
        simpa only [Counts.effect, h.1, h.2.1, Nat.cast_zero, sub_self] using he.symm
      simp [hx, hn]

/-- One extra block is reserved precisely while zero is strictly between sentinels. -/
def glp0032b2_zeroCredit (a b : ℤ) : ℕ := if a < 0 ∧ 0 < b then 1 else 0

lemma glp0032b2_zeroCredit_le (a b : ℤ) : glp0032b2_zeroCredit a b ≤ 1 := by
  unfold glp0032b2_zeroCredit
  split <;> omega

lemma glp0032b2_zeroCredit_left (a c b : ℤ) (hac : a < c) (hcb : c < b) :
    (if c = 0 then 1 else 0) + glp0032b2_zeroCredit a c ≤ glp0032b2_zeroCredit a b := by
  unfold glp0032b2_zeroCredit
  split_ifs <;> omega

lemma glp0032b2_zeroCredit_right (a c b : ℤ) (hac : a < c) (hcb : c < b) :
    (if c = 0 then 1 else 0) + glp0032b2_zeroCredit c b ≤ glp0032b2_zeroCredit a b := by
  unfold glp0032b2_zeroCredit
  split_ifs <;> omega

/-- Expose the corrected branch of the recursion. -/
lemma glp0032b2_search_succ (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) :
    adaptiveSearch (fuel+1) true o k₁ k₂ reject a b idx =
      if b ≤ a+1 then ⟨some a, []⟩ else
        let c := (a+b)/2
        let q := runTests reject idx (candidates o c)
        let r := if q.compatible then
          adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
        else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx
        ⟨r.value, q.trace ++ r.trace⟩ := by
  conv_lhs => unfold adaptiveSearch
  simp only [eq_self, true_and, not_true_eq_false, false_and, ite_false]
  by_cases hs : b ≤ a+1
  · simp only [if_pos hs]
  · simp only [if_neg hs]
    cases hq : (runTests reject idx (candidates o ((a+b)/2))).compatible <;>
      simp [hq]

/-- Strict narrowing makes the supplied linear fuel sufficient, for every start index. -/
lemma glp0032b2_search_terminates (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ)
    (hab : a < b) (hw : (b-a).toNat ≤ fuel+1) :
    (adaptiveSearch fuel true o k₁ k₂ reject a b idx).value.isSome := by
  induction fuel generalizing a b idx with
  | zero =>
    have hs : b ≤ a+1 := by omega
    simp [adaptiveSearch, hs]
  | succ fuel ih =>
    rw [glp0032b2_search_succ]
    by_cases hs : b ≤ a+1
    · simp [hs]
    · simp only [if_neg hs]
      let c : ℤ := (a+b)/2
      let q := runTests reject idx (candidates o c)
      have hac : a < c := by dsimp [c]; omega
      have hcb : c < b := by dsimp [c]; omega
      change (if q.compatible then
        adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
        else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).value.isSome
      by_cases hq : q.compatible = true
      · simp only [if_pos hq]
        exact ih c b q.idx hcb (by omega)
      · simp only [if_neg hq]
        exact ih a c q.idx hac (by omega)

/-- A stateful search cost bound, measured in table tests.
The reserve pays for the exceptional candidate block at zero at most once.
No property of `reject`, or of the chronological start index, is assumed. -/
lemma glp0032b2_search_cost (q fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ)
    (hw : b-a ≤ (2 : ℤ)^q) :
    (adaptiveSearch fuel true o k₁ k₂ reject a b idx).trace.length ≤
      (o.total+1) * (q + glp0032b2_zeroCredit a b) := by
  induction q generalizing fuel a b idx with
  | zero =>
    have hs : b ≤ a+1 := by simp only [pow_zero] at hw; omega
    cases fuel <;> simp [adaptiveSearch, hs]
  | succ q ih =>
    cases fuel with
    | zero =>
      by_cases hs : b ≤ a+1 <;> simp [adaptiveSearch, hs]
    | succ fuel =>
      rw [glp0032b2_search_succ]
      by_cases hs : b ≤ a+1
      · simp [hs]
      · simp only [if_neg hs]
        let c : ℤ := (a+b)/2
        let r := runTests reject idx (candidates o c)
        have hac : a < c := by dsimp [c]; omega
        have hcb : c < b := by dsimp [c]; omega
        have hp : (2 : ℤ)^(q+1) = 2*(2 : ℤ)^q := by ring
        rw [hp] at hw
        have hl : c-a ≤ (2 : ℤ)^q := by dsimp [c]; omega
        have hr : b-c ≤ (2 : ℤ)^q := by dsimp [c]; omega
        have hquery : r.trace.length ≤
            (o.total+1) * (1 + if c = 0 then 1 else 0) := by
          have h₁ := (glp0032b2_runTests_cost reject (candidates o c) idx).2
          have h₂ := glp0032b2_candidates_length o c
          have hh := le_trans h₁ h₂
          show (runTests reject idx (candidates o c)).trace.length ≤ _
          split_ifs at hh ⊢ <;> omega
        change (r.trace ++ (if r.compatible then
          adaptiveSearch fuel true o k₁ k₂ reject c b r.idx
          else adaptiveSearch fuel true o k₁ k₂ reject a c r.idx).trace).length ≤ _
        by_cases hrc : r.compatible = true
        · simp only [if_pos hrc, List.length_append]
          have hi := ih fuel c b r.idx hr
          have hc := glp0032b2_zeroCredit_right a c b hac hcb
          have hm := Nat.mul_le_mul_left (o.total+1) hc
          nlinarith
        · simp only [if_neg hrc, List.length_append]
          have hi := ih fuel a c r.idx hl
          have hc := glp0032b2_zeroCredit_left a c b hac hcb
          have hm := Nat.mul_le_mul_left (o.total+1) hc
          nlinarith

/-- A bound on the number of table tests, valid for every starting index. -/
lemma glp0032b2_upperRun_budget (o : Counts) (reject : Counts → ℕ → Bool) (idx : ℕ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) :
    (upperRun true o reject idx).value.isSome ∧
    (upperRun true o reject idx).trace.length ≤
      (o.total+1)*(Nat.log2 (o.total+1)+2) := by
  let k₁ : ℤ := 2*((o.a : ℤ)-o.c)
  let k₂ : ℤ := (o.a : ℤ)-o.c+(o.a+o.b)
  have hk : k₁ ≤ k₂ := by dsimp [k₁, k₂]; omega
  have hw : k₂+1-(k₁-1) ≤ (o.total : ℤ)+2 := by
    dsimp [k₁, k₂, Counts.total]
    omega
  have hterm := glp0032b2_search_terminates (o.total+3) o k₁ k₂ reject
    (k₁-1) (k₂+1) idx (by omega) (by omega)
  have hpN := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (o.total+1)
  have hp : (o.total : ℤ)+1 < (2 : ℤ)^(Nat.log2 (o.total+1)+1) := by
    rw [Nat.log2_eq_log_two]
    exact_mod_cast hpN
  have hcost := glp0032b2_search_cost (Nat.log2 (o.total+1)+1) (o.total+3)
    o k₁ k₂ reject (k₁-1) (k₂+1) idx (by omega)
  have hcredit := glp0032b2_zeroCredit_le (k₁-1) (k₂+1)
  have hm := Nat.mul_le_mul_left (o.total+1)
    (show Nat.log2 (o.total+1)+1+glp0032b2_zeroCredit (k₁-1) (k₂+1) ≤
      Nat.log2 (o.total+1)+2 by omega)
  have hu : upperRun true o reject idx =
      adaptiveSearch (o.total+3) true o k₁ k₂ reject (k₁-1) (k₂+1) idx := rfl
  rw [hu]
  exact ⟨hterm, le_trans hcost hm⟩


/-- Exact decisions ignore the chronological counter and accept precisely
when one of the actually enumerated candidates passes the level. -/
lemma glp0032b2_runTests_exact (α : ℝ) (o : Counts) (xs : List Counts) (idx : ℕ) :
    (runTests (fun v _ => decide ((pValue v o : ℝ) < α)) idx xs).compatible = true ↔
      ∃ v ∈ xs, α ≤ (pValue v o : ℝ) := by
  induction xs generalizing idx with
  | nil => simp [runTests]
  | cons v vs ih =>
    by_cases hv : (pValue v o : ℝ) < α
    · simp [runTests, hv, ih, not_le.mpr hv]
    · have hle : α ≤ (pValue v o : ℝ) := le_of_not_gt hv
      simp [runTests, hv, hle]

/-- The stateful search locates a threshold once its actual compatibility
predicate has been identified. The fuel premise is a linear width bound. -/
lemma glp0032b2_search_threshold (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b r : ℤ) (idx : ℕ)
    (har : a ≤ r) (hrb : r < b) (hw : (b-a).toNat ≤ fuel+1)
    (hquery : ∀ c, a < c → c < b → ∀ i,
      (runTests reject i (candidates o c)).compatible = true ↔ c ≤ r) :
    (adaptiveSearch fuel true o k₁ k₂ reject a b idx).value = some r := by
  induction fuel generalizing a b idx with
  | zero =>
    have hs : b ≤ a+1 := by omega
    have he : a = r := by omega
    rw [← he]
    simp [adaptiveSearch, hs]
  | succ fuel ih =>
    rw [glp0032b2_search_succ]
    by_cases hs : b ≤ a+1
    · have he : a = r := by omega
      rw [← he]
      simp [hs]
    · simp only [if_neg hs]
      let c : ℤ := (a+b)/2
      let q := runTests reject idx (candidates o c)
      have hac : a < c := by dsimp [c]; omega
      have hcb : c < b := by dsimp [c]; omega
      change (if q.compatible then
        adaptiveSearch fuel true o k₁ k₂ reject c b q.idx
        else adaptiveSearch fuel true o k₁ k₂ reject a c q.idx).value = some r
      by_cases hq : q.compatible = true
      · simp only [if_pos hq]
        have hcr : c ≤ r := (hquery c hac hcb idx).mp hq
        apply ih c b q.idx hcr hrb (by omega)
        intro d hcd hdb i
        exact hquery d (lt_trans hac hcd) hdb i
      · simp only [if_neg hq]
        have hrc : r < c := by
          have hnc : ¬ c ≤ r := fun h => hq ((hquery c hac hcb idx).mpr h)
          omega
        apply ih a c q.idx har hrc (by omega)
        intro d had hdc i
        exact hquery d had (lt_trans hdc hcb) i

/-- This numerical estimate uses the stronger pathwise bound, so balance
and n≥15 allow the uniform assumption n≥16. -/
lemma glp0032b2_log_cost (n : ℕ) (hn : 16 ≤ n) :
    2 * (((n+1)*(Nat.log2 (n+1)+2) : ℕ) : ℝ) ≤ 4*(n : ℝ)*logTwo n := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfour : (4 : ℝ) ≤ logTwo n := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hnR
    have h16 : Real.log (16 : ℝ) = 4*Real.log 2 := by
      rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
      norm_num
    rw [h16] at hh
    exact (le_div_iff₀ hlog2).mpr hh
  have hlogn : (Nat.log2 (n+1) : ℝ) ≤ logTwo n + 1 := by
    have hfloor := Real.log2_le_logb (n+1)
    have hmono := Real.log_le_log (by positivity : (0 : ℝ) < (n+1 : ℕ))
      (show ((n+1 : ℕ) : ℝ) ≤ 2*n by push_cast; linarith)
    have hmul : Real.log (2*(n : ℝ)) = Real.log 2 + Real.log n :=
      Real.log_mul (by norm_num) hn0.ne'
    rw [hmul] at hmono
    have hbound : Real.logb 2 ((n+1 : ℕ) : ℝ) ≤ logTwo n + 1 := by
      unfold Real.logb logTwo
      apply (div_le_iff₀ hlog2).mpr
      calc
        Real.log ((n+1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log n := hmono
        _ = (Real.log n / Real.log 2 + 1)*Real.log 2 := by
          field_simp
          ring
    exact hfloor.trans hbound
  have hmul := mul_le_mul_of_nonneg_left hlogn
    (show (0 : ℝ) ≤ n+1 by positivity)
  have hlarge := mul_le_mul_of_nonneg_left hfour
    (show (0 : ℝ) ≤ n-1 by linarith)
  push_cast
  nlinarith

/-- Possible tables admit a one-dimensional integer imputation witness. -/
lemma glp0032b2_possible_iff (o v : Counts) :
    Possible o v ↔ v.total = o.total ∧ ∃ i : ℤ,
      0 ≤ i ∧ i ≤ o.a ∧
      0 ≤ (v.a : ℤ)-i ∧ (v.a : ℤ)-i ≤ o.c ∧
      0 ≤ (v.b : ℤ)+i-o.a ∧ (v.b : ℤ)+i-o.a ≤ o.d ∧
      0 ≤ (v.a : ℤ)+(v.c : ℤ)-i-o.c ∧
        (v.a : ℤ)+(v.c : ℤ)-i-o.c ≤ o.b := by
  constructor
  · intro hv
    have ht := (possible_table_facts o v hv).1
    simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map,
      List.mem_range] at hv
    obtain ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩ := hv
    refine ⟨ht, i, ?_⟩
    dsimp
    omega
  · rintro ⟨ht,i,hi0,hia,hk0,hkc,hl0,hld,hj0,hjb⟩
    simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map,
      List.mem_range]
    refine ⟨i.toNat, by omega,
      ((v.a : ℤ)+(v.c : ℤ)-i-o.c).toNat, by omega,
      ((v.a : ℤ)-i).toNat, by omega,
      ((v.b : ℤ)+i-o.a).toNat, by omega, ?_⟩
    unfold Counts.total at ht
    ext <;> dsimp <;> omega

/-- Feasibility along a fixed effect and treated-success line is an integer
interval, including its endpoints. -/
lemma glp0032b2_line_feasibility (o v : Counts) (k t : ℕ)
    (hv : Possible o v) (hk : k ≤ v.a ∧ k ≤ v.d)
    (hu : Possible o (reuseVector v k)) (ht : t ≤ k) :
    Possible o (reuseVector v t) := by
  obtain ⟨hvt,i,hi⟩ := (glp0032b2_possible_iff o v).mp hv
  obtain ⟨hut,j,hj⟩ := (glp0032b2_possible_iff o (reuseVector v k)).mp hu
  apply (glp0032b2_possible_iff o (reuseVector v t)).mpr
  constructor
  · dsimp [reuseVector, Counts.total] at *
    omega
  · refine ⟨max j (i-t), ?_⟩
    dsimp [reuseVector] at *
    rcases le_total j (i-t) with hij | hij
    · rw [max_eq_right hij]
      omega
    · rw [max_eq_left hij]
      omega

/-- Base candidates really are enumerated, at every feasible value of j. -/
lemma glp0032b2_base_mem (o v : Counts) (x : ℤ) (j : ℕ)
    (hj : j ≤ o.total) (hv : firstOnLine o x j = some v) :
    v ∈ candidates o x := by
  apply List.mem_flatMap.mpr
  refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
  simp only [hv]
  split <;> simp

/-- The exceptional positive-discordance candidate is present whenever its
guard is justified by a possible point further along the line. -/
lemma glp0032b2_extra_mem (o v : Counts) (x : ℤ) (j : ℕ)
    (hj : j ≤ o.total) (hv : firstOnLine o x j = some v)
    (hb : v.b = 0) (hc : v.c = 0) (ha : 1 ≤ v.a) (hd : 1 ≤ v.d)
    (hp : Possible o (reuseVector v 1)) :
    reuseVector v 1 ∈ candidates o x := by
  apply List.mem_flatMap.mpr
  refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
  simp only [hv]
  have hvec : reuseVector v 1 = ⟨v.a-1,1,1,v.d-1⟩ := by
    ext <;> simp [reuseVector, hb, hc]
  rw [hvec] at hp ⊢
  simp [hb, hc, ha, hd, hp]

/-- This comparison isolates the exact finite shape input needed from T33.
It never attempts the invalid last merge from discordance two to zero. -/
lemma glp0032b2_reuse_comparison (o v : Counts) (k : ℕ)
    (htot : v.total = o.total) (hk : k ≤ v.a ∧ k ≤ v.d)
    (hdisc : 1 ≤ v.b+v.c)
    (hmerge : ∀ w : Counts, w.total = o.total →
      1 ≤ min w.b w.c → 2 ≤ max w.b w.c →
      pValue w o ≤ pValue ⟨w.a+1,w.b-1,w.c-1,w.d+1⟩ o) :
    pValue (reuseVector v k) o ≤ pValue v o := by
  induction k with
  | zero => simp [reuseVector]
  | succ k ih =>
    have hka : k ≤ v.a ∧ k ≤ v.d := by omega
    have hi := ih hka
    let w := reuseVector v (k+1)
    have hw : w.total = o.total := by
      dsimp [w, reuseVector, Counts.total]
      dsimp [Counts.total] at htot
      omega
    have hmin : 1 ≤ min w.b w.c := by dsimp [w, reuseVector]; omega
    have hmax : 2 ≤ max w.b w.c := by dsimp [w, reuseVector]; omega
    have hm := hmerge w hw hmin hmax
    have he : (⟨w.a+1,w.b-1,w.c-1,w.d+1⟩ : Counts) = reuseVector v k := by
      ext <;> dsimp [w, reuseVector] <;> omega
    rw [he] at hm
    exact hm.trans hi

/-- Every actual candidate is possible and has the queried effect. -/
lemma glp0032b2_candidate_sound (o v : Counts) (x : ℤ)
    (hv : v ∈ candidates o x) : Possible o v ∧ v.effect = x := by
  obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp hv
  cases hbase : firstOnLine o x j with
  | none => simp [hbase] at hv
  | some w =>
    have hw := first_on_line_spec o x j w hbase
    simp only [hbase] at hv
    split at hv
    · rename_i hguard
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨hw.1, hw.2.1⟩
      · refine ⟨hguard.2.2.2.2, ?_⟩
        dsimp [Counts.effect] at *
        omega
    · simp only [List.mem_singleton] at hv
      subst v
      exact ⟨hw.1, hw.2.1⟩

/-- Candidate reduction conditional only on the precise pair-merge inequality.
This is a transfer lemma, not a substitute hypothesis for the target theorem. -/
lemma glp0032b2_candidate_reduction (o : Counts) (x : ℤ) (α : ℝ)
    (hmerge : ∀ w : Counts, w.total = o.total →
      1 ≤ min w.b w.c → 2 ≤ max w.b w.c →
      pValue w o ≤ pValue ⟨w.a+1,w.b-1,w.c-1,w.d+1⟩ o) :
    (∃ v ∈ candidates o x, α ≤ (pValue v o : ℝ)) ↔
      ∃ u, Possible o u ∧ u.effect = x ∧ α ≤ (pValue u o : ℝ) := by
  constructor
  · rintro ⟨v,hv,hp⟩
    have hs := glp0032b2_candidate_sound o v x hv
    exact ⟨v,hs.1,hs.2,hp⟩
  · rintro ⟨u,hu,hx,hp⟩
    obtain ⟨he,hj,v,hv,k,hkn,hka,hkd,huv⟩ := corrected_general_loop o u hu
    rw [hx] at hv
    have hs := first_on_line_spec o x (u.a+u.b) v hv
    have htot := (possible_table_facts o v hs.1).1
    have hbase := glp0032b2_base_mem o v x (u.a+u.b) hj hv
    by_cases hd : 1 ≤ v.b+v.c
    · refine ⟨v,hbase,?_⟩
      have hh := glp0032b2_reuse_comparison o v k htot ⟨hka,hkd⟩ hd hmerge
      rw [← huv] at hh
      exact hp.trans (by exact_mod_cast hh)
    · have hb : v.b = 0 := by omega
      have hc : v.c = 0 := by omega
      by_cases hk : k = 0
      · subst k
        have he : u = v := by simpa [reuseVector] using huv
        exact ⟨v,hbase,by simpa only [he] using hp⟩
      · let w := reuseVector v 1
        have hwp : Possible o w := glp0032b2_line_feasibility o v k 1
          hs.1 ⟨hka,hkd⟩ (by simpa only [← huv] using hu) (by omega)
        have hmem : w ∈ candidates o x := glp0032b2_extra_mem o v x (u.a+u.b)
          hj hv hb hc (by omega) (by omega) hwp
        have hwtot := (possible_table_facts o w hwp).1
        have hwk : k-1 ≤ w.a ∧ k-1 ≤ w.d := by
          dsimp [w, reuseVector]
          omega
        have hwdisc : 1 ≤ w.b+w.c := by simp [w, reuseVector, hb, hc]
        have hwu : reuseVector w (k-1) = u := by
          rw [huv]
          ext <;> dsimp [w, reuseVector] <;> omega
        have hh := glp0032b2_reuse_comparison o w (k-1) hwtot hwk hwdisc hmerge
        rw [hwu] at hh
        exact ⟨w,hmem,hp.trans (by exact_mod_cast hh)⟩


/- Enumeration of random states (T24). -/
lemma glp0032b2_mem_randomStates_iff (v q : Counts) (m : ℕ) :
    q ∈ randomStates v m ↔
      q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = m := by
  constructor
  · exact random_state_facts v m q
  · rintro ⟨ha,hb,hc,hd,ht⟩
    have hsum : q.a+q.b+q.c+q.d = m := ht
    have he : m-q.a-q.b-q.c = q.d := by omega
    simp only [randomStates,List.mem_flatMap,List.mem_filterMap,List.mem_range]
    refine ⟨q.a,?_,q.b,?_,q.c,?_,?_⟩
    · omega
    · omega
    · omega
    · simp only [he,if_pos hd,Option.some.injEq]

/-- Disjoint blocks can be recognized by a tag on each of their elements. -/
lemma glp0032b2_tagged_flatMap_nodup {A B : Type*} (xs : List A)
    (f : A → List B) (tag : B → A) (hx : xs.Nodup)
    (hf : ∀ a ∈ xs, (f a).Nodup)
    (htag : ∀ a, ∀ b ∈ f a, tag b = a) :
    (xs.flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨hf,?_⟩
  apply hx.imp
  intro a b hab q hqa hqb
  exact hab ((htag a q hqa).symm.trans (htag b q hqb))

lemma glp0032b2_randomStates_nodup (v : Counts) (m : ℕ) :
    (randomStates v m).Nodup := by
  let block (a b : ℕ) : List Counts :=
    (List.range (min v.c (m-a-b)+1)).filterMap fun c =>
      if m-a-b-c ≤ v.d then some ⟨a,b,c,m-a-b-c⟩ else none
  have hblock (a b : ℕ) : (block a b).Nodup := by
    apply List.Nodup.filterMap (l := List.range (min v.c (m-a-b)+1))
      (f := fun c => if m-a-b-c ≤ v.d then
        some (⟨a,b,c,m-a-b-c⟩ : Counts) else none)
    · intro c c' q hc hc'
      change (if m-a-b-c ≤ v.d then
        some (⟨a,b,c,m-a-b-c⟩ : Counts) else none) = some q at hc
      change (if m-a-b-c' ≤ v.d then
        some (⟨a,b,c',m-a-b-c'⟩ : Counts) else none) = some q at hc'
      by_cases hd : m-a-b-c ≤ v.d
      · by_cases hd' : m-a-b-c' ≤ v.d
        · simp only [if_pos hd,Option.some.injEq] at hc
          simp only [if_pos hd',Option.some.injEq] at hc'
          have he := congrArg Counts.c (hc.trans hc'.symm)
          exact he
        · simp [hd'] at hc'
      · simp [hd] at hc
    · exact List.nodup_range
  have htag (a b : ℕ) (q : Counts) (hq : q ∈ block a b) :
      q.a = a ∧ q.b = b := by
    simp only [block,List.mem_filterMap] at hq
    obtain ⟨c,hc,hret⟩ := hq
    by_cases hd : m-a-b-c ≤ v.d
    · simp only [if_pos hd,Option.some.injEq] at hret
      subst q
      exact ⟨rfl,rfl⟩
    · simp [hd] at hret
  have hinner (a : ℕ) :
      ((List.range (min v.b (m-a)+1)).flatMap (block a)).Nodup := by
    apply glp0032b2_tagged_flatMap_nodup _ _ Counts.b (List.nodup_range)
    · intro b hb
      exact hblock a b
    · intro b q hq
      exact (htag a b q hq).2
  change ((List.range (min v.a m+1)).flatMap fun a =>
    (List.range (min v.b (m-a)+1)).flatMap (block a)).Nodup
  apply glp0032b2_tagged_flatMap_nodup _ _ Counts.a (List.nodup_range)
  · intro a ha
    exact hinner a
  · intro a q hq
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    exact (htag a b q hq).1


def glp0032b2_score (v q : Counts) : ℤ :=
  2*(q.a : ℤ)+q.b+q.c-v.a-v.c


lemma glp0032b2_allCounts_mem (m : ℕ) (q : Counts) :
    q ∈ allCounts m ↔ q.total = m := by
  rw [allCounts, List.mem_toFinset, glp0032b2_mem_randomStates_iff]
  change (q.a ≤ m ∧ q.b ≤ m ∧ q.c ≤ m ∧ q.d ≤ m ∧ q.total = m) ↔ _
  constructor
  · exact fun h => h.2.2.2.2
  · intro ht
    dsimp [Counts.total] at ht
    exact ⟨by omega, by omega, by omega, by omega, ht⟩

noncomputable def glp0032b2_sumAll (v : Counts) (m : ℕ) (F : Counts → ℝ) : ℝ :=
  ∑ q ∈ allCounts m, (multiplicity v q : ℝ)*F q


/- Zero-extended binomial coefficients and canonical counts. -/
/-- Binomial coefficients with zero extension to negative integer indices. -/
noncomputable def glp0032b2_sd_binom (n : ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k then (n.choose k.toNat : ℝ) else 0

local notation "B" => glp0032b2_sd_binom

lemma glp0032b2_sd_binom_nat (n k : ℕ) : B n k = n.choose k := by
  simp [glp0032b2_sd_binom]

lemma glp0032b2_sd_binom_nonneg (n : ℕ) (k : ℤ) : 0 ≤ B n k := by
  unfold glp0032b2_sd_binom
  split_ifs <;> positivity

lemma glp0032b2_sd_binom_zero (n : ℕ) (k : ℤ)
    (h : k < 0 ∨ (n : ℤ) < k) : B n k = 0 := by
  rcases h with h | h
  · simp [glp0032b2_sd_binom, not_le.mpr h]
  · by_cases hk : 0 ≤ k
    · have hnk : n < k.toNat := by omega
      simp [glp0032b2_sd_binom, hk, Nat.choose_eq_zero_of_lt hnk]
    · simp [glp0032b2_sd_binom, hk]

lemma glp0032b2_sd_binom_symm (n : ℕ) (k : ℤ) :
    B n ((n : ℤ)-k) = B n k := by
  by_cases hk : 0 ≤ k ∧ k ≤ n
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hk.1
    rw [← Nat.cast_sub (by exact_mod_cast hk.2)]
    simp only [glp0032b2_sd_binom_nat]
    exact_mod_cast Nat.choose_symm (by exact_mod_cast hk.2 : r ≤ n)
  · rw [glp0032b2_sd_binom_zero n k (by omega),
      glp0032b2_sd_binom_zero n ((n : ℤ)-k) (by omega)]

lemma glp0032b2_sd_binom_summable (n : ℕ) (f : ℤ → ℝ) :
    Summable (fun k => B n k * f k) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (0 : ℤ) n)
  intro k hk
  have hz := glp0032b2_sd_binom_zero n k (by
    simp only [Finset.mem_Icc] at hk
    omega)
  simp [hz]

lemma glp0032b2_sd_binom_pascal (n : ℕ) (k : ℤ) :
    B (n+1) k = B n k + B n (k-1) := by
  by_cases hk : k < 0
  · rw [glp0032b2_sd_binom_zero _ _ (Or.inl hk),
      glp0032b2_sd_binom_zero _ _ (Or.inl hk),
      glp0032b2_sd_binom_zero _ _ (Or.inl (by omega))]
    ring
  have hk' : 0 ≤ k := by omega
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hk'
  cases r with
  | zero => simp [glp0032b2_sd_binom]
  | succ r =>
    rw [show ((r+1 : ℕ) : ℤ)-1 = (r : ℤ) by push_cast; ring]
    simp only [glp0032b2_sd_binom_nat]
    exact_mod_cast (Nat.choose_succ_succ n r).trans (Nat.add_comm _ _)

lemma glp0032b2_sd_binom_select (n : ℕ) (k : ℤ) :
    (k : ℝ) * B (n+1) k = (n+1 : ℕ) * B n (k-1) := by
  by_cases hk : k < 0
  · rw [glp0032b2_sd_binom_zero _ _ (Or.inl hk),
      glp0032b2_sd_binom_zero _ _ (Or.inl (by omega))]
    ring
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k)
  cases r with
  | zero => simp [glp0032b2_sd_binom]
  | succ r =>
    rw [show ((r+1 : ℕ) : ℤ)-1 = (r : ℤ) by push_cast; ring]
    simp only [glp0032b2_sd_binom_nat, Int.cast_natCast]
    have h := Nat.add_one_mul_choose_eq n r
    exact_mod_cast (Nat.mul_comm (r+1) ((n+1).choose (r+1))).trans h.symm

lemma glp0032b2_sd_binom_omit (n : ℕ) (k : ℤ) :
    ((n+1 : ℕ) - (k : ℝ)) * B (n+1) k = (n+1 : ℕ) * B n k := by
  have h := glp0032b2_sd_binom_select n ((n+1 : ℕ)-k)
  rw [glp0032b2_sd_binom_symm] at h
  rw [show ((n+1 : ℕ) : ℤ)-k-1 = (n : ℤ)-k by push_cast; ring,
    glp0032b2_sd_binom_symm] at h
  push_cast at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

lemma glp0032b2_sd_binom_right (n : ℕ) (k : ℤ) (hk : (n : ℤ) ≤ 2*k) :
    B n (k+1) ≤ B n k := by
  by_cases hkn : (n : ℤ) < k+1
  · rw [glp0032b2_sd_binom_zero _ _ (Or.inr hkn)]
    exact glp0032b2_sd_binom_nonneg _ _
  have hk0 : 0 ≤ k := by omega
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  have hr : r+1 ≤ n := by omega
  have heq := Nat.choose_succ_right_eq n r
  have hnr : n-r ≤ r+1 := by omega
  have hle : n.choose (r+1) ≤ n.choose r := by nlinarith [Nat.choose_pos hr]
  rw [show (r : ℤ)+1 = ((r+1 : ℕ) : ℤ) by push_cast; ring]
  simpa only [glp0032b2_sd_binom_nat] using (show (n.choose (r+1) : ℝ) ≤ n.choose r by exact_mod_cast hle)

lemma glp0032b2_sd_binom_left (n : ℕ) (k : ℤ) (hk : 2*k ≤ (n : ℤ)) :
    B n (k-1) ≤ B n k := by
  have h := glp0032b2_sd_binom_right n ((n : ℤ)-k) (by omega)
  rw [show (n : ℤ)-k+1 = (n : ℤ)-(k-1) by ring,
    glp0032b2_sd_binom_symm, glp0032b2_sd_binom_symm] at h
  exact h

lemma glp0032b2_sd_binom_right_weak (n : ℕ) (k : ℤ)
    (hk : (n : ℤ)+1 ≤ 2*k) : B n k ≤ B n (k-1) := by
  by_cases h : (n : ℤ) ≤ 2*(k-1)
  · simpa using glp0032b2_sd_binom_right n (k-1) h
  · have hn : (n : ℤ) = 2*k-1 := by omega
    have hsym := glp0032b2_sd_binom_symm n k
    rw [show (n : ℤ)-k = k-1 by omega] at hsym
    exact le_of_eq hsym.symm

lemma glp0032b2_sd_binom_left_weak (n : ℕ) (k : ℤ)
    (hk : 2*k ≤ (n : ℤ)-1) : B n k ≤ B n (k+1) := by
  have h := glp0032b2_sd_binom_right_weak n ((n : ℤ)-k) (by omega)
  rw [show (n : ℤ)-k-1 = (n : ℤ)-(k+1) by ring,
    glp0032b2_sd_binom_symm, glp0032b2_sd_binom_symm] at h
  exact h

/-- Number of assignments with `t` treated labels and canonical scaled sum `s`. -/
noncomputable def glp0032b2_sd_count (a d z : ℕ) (t s : ℤ) : ℝ :=
  ∑' x : ℤ, B a x * (B d (s+a-2*x) * B z (t+x-s-a))

local notation "C" => glp0032b2_sd_count


lemma glp0032b2_sd_count_symm (a d z m : ℕ) (hn : a+d+z = 2*m) (s : ℤ) :
    C a d z m ((d : ℤ)-s) = C a d z m s := by
  let e : ℤ ≃ ℤ := Equiv.subLeft a
  rw [glp0032b2_sd_count, ← e.tsum_eq]
  apply tsum_congr
  intro x
  dsimp [e]
  change B a ((a : ℤ)-x) *
    (B d ((d : ℤ)-s+a-2*((a : ℤ)-x)) * B z ((m : ℤ)+((a : ℤ)-x)-((d : ℤ)-s)-a)) = _
  rw [glp0032b2_sd_binom_symm]
  have hn' : (a : ℤ)+d+z = 2*m := by exact_mod_cast hn
  rw [show (d : ℤ)-s+a-2*((a : ℤ)-x) = (d : ℤ)-(s+a-2*x) by ring,
    glp0032b2_sd_binom_symm]
  rw [show (m : ℤ)+((a : ℤ)-x)-((d : ℤ)-s)-a = (z : ℤ)-((m : ℤ)+x-s-a) by omega,
    glp0032b2_sd_binom_symm]

lemma glp0032b2_sd_binom_one (k : ℤ) :
    B 1 k = if k = 0 ∨ k = 1 then 1 else 0 := by
  by_cases h0 : k = 0
  · subst k; norm_num [glp0032b2_sd_binom]
  by_cases h1 : k = 1
  · subst k; norm_num [glp0032b2_sd_binom]
  rw [if_neg (by tauto), glp0032b2_sd_binom_zero _ _ (by omega)]

lemma glp0032b2_sd_binom_two (k : ℤ) :
    B 2 k = if k = 0 ∨ k = 2 then 1 else if k = 1 then 2 else 0 := by
  by_cases h0 : k = 0
  · subst k; norm_num [glp0032b2_sd_binom]
  by_cases h1 : k = 1
  · subst k; norm_num [glp0032b2_sd_binom]
  by_cases h2 : k = 2
  · subst k; norm_num [glp0032b2_sd_binom]
  rw [if_neg (by tauto), if_neg h1, glp0032b2_sd_binom_zero _ _ (by omega)]

lemma glp0032b2_sd_one_even (a z : ℕ) (t s x : ℤ) (hx : s+a = 2*x) :
    C a 1 z t s = B a x * B z (t-x) := by
  unfold glp0032b2_sd_count
  rw [tsum_eq_single x]
  · rw [show s+a-2*x = 0 by omega, glp0032b2_sd_binom_one,
      show t+x-s-a = t-x by omega]
    norm_num
  · intro y hy
    rw [glp0032b2_sd_binom_one, if_neg (by omega)]
    ring

lemma glp0032b2_sd_one_odd (a z : ℕ) (t s x : ℤ) (hx : s+a = 2*x+1) :
    C a 1 z t s = B a x * B z (t-x-1) := by
  unfold glp0032b2_sd_count
  rw [tsum_eq_single x]
  · rw [show s+a-2*x = 1 by omega, glp0032b2_sd_binom_one,
      show t+x-s-a = t-x-1 by omega]
    norm_num
  · intro y hy
    rw [glp0032b2_sd_binom_one, if_neg (by omega)]
    ring

lemma glp0032b2_sd_two_even (a z : ℕ) (t s x : ℤ) (hx : s+a = 2*x) :
    C a 2 z t s = B a x * B z (t-x) + B a (x-1) * B z (t-x-1) := by
  unfold glp0032b2_sd_count
  rw [tsum_eq_sum (s := {x, x-1}) (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [glp0032b2_sd_binom_two, if_neg (by omega), if_neg (by omega)]
    ring)]
  rw [Finset.sum_pair (by omega : x ≠ x-1)]
  rw [show s+a-2*x = 0 by omega, show s+a-2*(x-1) = 2 by omega,
    glp0032b2_sd_binom_two, glp0032b2_sd_binom_two,
    show t+x-s-a = t-x by omega, show t+(x-1)-s-a = t-x-1 by omega]
  norm_num

lemma glp0032b2_sd_two_odd (a z : ℕ) (t s x : ℤ) (hx : s+a = 2*x+1) :
    C a 2 z t s = 2 * B a x * B z (t-x-1) := by
  unfold glp0032b2_sd_count
  rw [tsum_eq_single x]
  · rw [show s+a-2*x = 1 by omega, glp0032b2_sd_binom_two,
      show t+x-s-a = t-x-1 by omega]
    norm_num
    ring
  · intro y hy
    rw [glp0032b2_sd_binom_two, if_neg (by omega), if_neg (by omega)]
    ring

lemma glp0032b2_sd_one_step (a z m : ℕ) (hn : a+1+z = 2*m)
    (s : ℤ) (hs : 1 ≤ s) : C a 1 z m (s+1) ≤ C a 1 z m s := by
  have hn' : (a : ℤ)+1+z = 2*m := by exact_mod_cast hn
  let x := (s+a)/2
  have hx : s+a = 2*x ∨ s+a = 2*x+1 := by dsimp [x]; omega
  rcases hx with hx | hx
  · rw [glp0032b2_sd_one_even a z m s x hx,
      glp0032b2_sd_one_odd a z m (s+1) x (by omega)]
    exact mul_le_mul_of_nonneg_left
      (glp0032b2_sd_binom_left z ((m : ℤ)-x) (by omega))
      (glp0032b2_sd_binom_nonneg _ _)
  · rw [glp0032b2_sd_one_odd a z m s x hx,
      glp0032b2_sd_one_even a z m (s+1) (x+1) (by omega),
      show (m : ℤ)-(x+1) = (m : ℤ)-x-1 by ring]
    exact mul_le_mul_of_nonneg_right
      (glp0032b2_sd_binom_right a x (by omega))
      (glp0032b2_sd_binom_nonneg _ _)

lemma glp0032b2_sd_two_step (a z m : ℕ) (hn : a+2+z = 2*m)
    (s : ℤ) (hs : 1 ≤ s) : C a 2 z m (s+1) ≤ C a 2 z m s := by
  have hn' : (a : ℤ)+2+z = 2*m := by exact_mod_cast hn
  let x := (s+a)/2
  have hx : s+a = 2*x ∨ s+a = 2*x+1 := by dsimp [x]; omega
  rcases hx with hx | hx
  · rw [glp0032b2_sd_two_even a z m s x hx,
      glp0032b2_sd_two_odd a z m (s+1) x (by omega)]
    have h1 := mul_le_mul_of_nonneg_left
      (glp0032b2_sd_binom_left_weak z ((m : ℤ)-x-1) (by omega))
      (glp0032b2_sd_binom_nonneg a x)
    have h2 := mul_le_mul_of_nonneg_right
      (glp0032b2_sd_binom_right_weak a x (by omega))
      (glp0032b2_sd_binom_nonneg z ((m : ℤ)-x-1))
    rw [show (m : ℤ)-x-1+1 = (m : ℤ)-x by ring] at h1
    linarith
  · rw [glp0032b2_sd_two_odd a z m s x hx,
      glp0032b2_sd_two_even a z m (s+1) (x+1) (by omega),
      show x+1-1 = x by ring, show (m : ℤ)-(x+1) = (m : ℤ)-x-1 by ring]
    have h1 := mul_le_mul_of_nonneg_right
      (glp0032b2_sd_binom_right a x (by omega))
      (glp0032b2_sd_binom_nonneg z ((m : ℤ)-x-1))
    have h2 := mul_le_mul_of_nonneg_left
      (glp0032b2_sd_binom_left z ((m : ℤ)-x-1) (by omega))
      (glp0032b2_sd_binom_nonneg a x)
    linarith

lemma glp0032b2_sd_shape_of_step (f : ℤ → ℝ) (c : ℤ)
    (hsym : ∀ s, f (c-s) = f s)
    (hstep : ∀ s, c ≤ 2*s → f (s+1) ≤ f s) : SDShape f c := by
  refine ⟨hsym, ?_⟩
  intro i j hi hij
  exact Int.leInduction (motive := fun j _ => f j ≤ f i) le_rfl
    (fun j hji hj => (hstep j (by omega)).trans hj) j hij

lemma glp0032b2_sd_one_shape (a z m : ℕ) (hn : a+1+z = 2*m) :
    SDShape (C a 1 z m) 1 := by
  apply glp0032b2_sd_shape_of_step
  · exact glp0032b2_sd_count_symm a 1 z m hn
  · intro s hs
    exact glp0032b2_sd_one_step a z m hn s (by omega)

lemma glp0032b2_sd_two_shape (a z m : ℕ) (hn : a+2+z = 2*m) :
    SDShape (C a 2 z m) 2 := by
  apply glp0032b2_sd_shape_of_step
  · exact glp0032b2_sd_count_symm a 2 z m hn
  · intro s hs
    exact glp0032b2_sd_two_step a z m hn s (by omega)

lemma glp0032b2_sd_binom_zero_top (k : ℤ) :
    B 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k; norm_num [glp0032b2_sd_binom]
  · rw [if_neg hk, glp0032b2_sd_binom_zero _ _ (by omega)]

lemma glp0032b2_sd_binom_select_pred (n : ℕ) (k : ℤ) :
    (k : ℝ) * B n k = (n : ℝ) * B (n-1) (k-1) := by
  cases n with
  | zero => by_cases hk : k = 0 <;> simp [glp0032b2_sd_binom_zero_top, hk]
  | succ n => simpa using glp0032b2_sd_binom_select n k

lemma glp0032b2_sd_binom_omit_pred (n : ℕ) (k : ℤ) :
    ((n : ℝ) - (k : ℝ)) * B n k = (n : ℝ) * B (n-1) k := by
  cases n with
  | zero => by_cases hk : k = 0 <;> simp [glp0032b2_sd_binom_zero_top, hk]
  | succ n => simpa using glp0032b2_sd_binom_omit n k

lemma glp0032b2_sd_binom_shift_summable (n : ℕ) (r : ℤ) (f : ℤ → ℝ) :
    Summable (fun k => B n (k-r) * f k) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc r ((n : ℤ)+r))
  intro k hk
  rw [glp0032b2_sd_binom_zero n (k-r) (by
    simp only [Finset.mem_Icc] at hk
    omega), zero_mul]

lemma glp0032b2_sd_partner_term (a e z m : ℕ)
    (hn : a+(e+2)+z = 2*m) (x s : ℤ) :
    (m : ℝ) * (B a x * (B (e+2) (s+a-2*x) * B z ((m : ℤ)+x-s-a))) =
      (a : ℝ) *
        (B (a-1) x * (B (e+1) (s+a-2*x-1) * B z ((m : ℤ)+x-s-a)) +
          B (a-1) (x-1) * (B (e+1) (s+a-2*x) * B z ((m : ℤ)+x-s-a))) +
      (2*(e+1) : ℝ) * (B a x * (B e (s+a-2*x-1) * B z ((m : ℤ)+x-s-a))) +
      (z : ℝ) * (B a x *
        (B (e+1) (s+a-2*x) * B (z-1) ((m : ℤ)+x-s-a-1) +
          B (e+1) (s+a-2*x-1) * B (z-1) ((m : ℤ)+x-s-a))) := by
  let u := s+(a : ℤ)-2*x
  let y := (m : ℤ)+x-s-a
  have hA0 := glp0032b2_sd_binom_omit_pred a x
  have hA1 := glp0032b2_sd_binom_select_pred a x
  have hZ0 := glp0032b2_sd_binom_omit_pred z y
  have hZ1 := glp0032b2_sd_binom_select_pred z y
  have hD0 := glp0032b2_sd_binom_select e u
  have hD1 := glp0032b2_sd_binom_omit e (u-1)
  have ht : (x : ℝ)+(u : ℝ)+(y : ℝ) = m := by dsimp [u,y]; push_cast; ring
  have hn' : (a : ℝ)+(e+2)+z = 2*m := by exact_mod_cast hn
  change (m : ℝ) * (B a x * (B (e+2) u * B z y)) =
    (a : ℝ) * (B (a-1) x * (B (e+1) (u-1) * B z y) +
      B (a-1) (x-1) * (B (e+1) u * B z y)) +
    (2*(e+1) : ℝ) * (B a x * (B e (u-1) * B z y)) +
    (z : ℝ) * (B a x * (B (e+1) u * B (z-1) (y-1) + B (e+1) (u-1) * B (z-1) y))
  rw [show e+2 = (e+1)+1 by omega, glp0032b2_sd_binom_pascal]
  push_cast at hD0 hD1
  linear_combination
    B (e+1) (u-1) * B z y * hA0 +
    B (e+1) u * B z y * hA1 +
    B a x * B (e+1) (u-1) * hZ0 +
    B a x * B (e+1) u * hZ1 +
    B a x * B z y * hD0 + B a x * B z y * hD1 +
    B a x * B z y * (B (e+1) (u-1) - B (e+1) u) * ht -
    B a x * B z y * B (e+1) (u-1) * hn'

lemma glp0032b2_sd_partner11 (a e z m : ℕ) (s : ℤ) :
    (∑' x : ℤ, (a : ℝ) *
      (B (a-1) x * (B (e+1) (s+a-2*x-1) * B z ((m : ℤ)+x-s-a)) +
        B (a-1) (x-1) * (B (e+1) (s+a-2*x) * B z ((m : ℤ)+x-s-a)))) =
      (a : ℝ) * (C (a-1) (e+1) z ((m : ℤ)-1) s +
        C (a-1) (e+1) z ((m : ℤ)-1) (s-1)) := by
  by_cases ha : a = 0
  · simp [ha]
  have ha' : ((a-1 : ℕ) : ℤ) = (a : ℤ)-1 := by omega
  rw [tsum_mul_left,
    (glp0032b2_sd_binom_summable (a-1) _).tsum_add
      (glp0032b2_sd_binom_shift_summable (a-1) 1 _)]
  congr 1
  congr 1
  · apply tsum_congr
    intro x
    simp only [glp0032b2_sd_count, ha']
    congr 2 <;> congr 1 <;> ring
  · let e' : ℤ ≃ ℤ := Equiv.subRight 1
    symm
    rw [glp0032b2_sd_count, ← e'.tsum_eq]
    apply tsum_congr
    intro x
    change B (a-1) (x-1) * (B (e+1) (s-1+(a-1 : ℕ)-2*(x-1)) *
      B z ((m : ℤ)-1+(x-1)-(s-1)-(a-1 : ℕ))) =
      B (a-1) (x-1) * (B (e+1) (s+a-2*x) * B z ((m : ℤ)+x-s-a))
    simp only [ha']
    congr 2 <;> congr 1 <;> ring

lemma glp0032b2_sd_partner00 (a e z m : ℕ) (s : ℤ) :
    (∑' x : ℤ, (z : ℝ) * (B a x *
      (B (e+1) (s+a-2*x) * B (z-1) ((m : ℤ)+x-s-a-1) +
        B (e+1) (s+a-2*x-1) * B (z-1) ((m : ℤ)+x-s-a)))) =
      (z : ℝ) * (C a (e+1) (z-1) ((m : ℤ)-1) s +
        C a (e+1) (z-1) ((m : ℤ)-1) (s-1)) := by
  rw [tsum_mul_left]
  simp_rw [mul_add]
  rw [(glp0032b2_sd_binom_summable a _).tsum_add
    (glp0032b2_sd_binom_summable a _)]
  rw [← mul_add]
  congr 1
  congr 1
  · apply tsum_congr
    intro x
    congr 2 <;> congr 1 <;> ring
  · apply tsum_congr
    intro x
    congr 2 <;> congr 1 <;> ring

lemma glp0032b2_sd_partner_sum (a e z m : ℕ)
    (hn : a+(e+2)+z = 2*m) (s : ℤ) :
    (m : ℝ) * C a (e+2) z m s =
      (a : ℝ) * (C (a-1) (e+1) z ((m : ℤ)-1) s +
        C (a-1) (e+1) z ((m : ℤ)-1) (s-1)) +
      (2*(e+1) : ℝ) * C a e z ((m : ℤ)-1) (s-1) +
      (z : ℝ) * (C a (e+1) (z-1) ((m : ℤ)-1) s +
        C a (e+1) (z-1) ((m : ℤ)-1) (s-1)) := by
  let p := fun x : ℤ => (a : ℝ) *
    (B (a-1) x * (B (e+1) (s+a-2*x-1) * B z ((m : ℤ)+x-s-a)) +
      B (a-1) (x-1) * (B (e+1) (s+a-2*x) * B z ((m : ℤ)+x-s-a)))
  let q := fun x : ℤ => (2*(e+1) : ℝ) *
    (B a x * (B e (s+a-2*x-1) * B z ((m : ℤ)+x-s-a)))
  let r := fun x : ℤ => (z : ℝ) * (B a x *
    (B (e+1) (s+a-2*x) * B (z-1) ((m : ℤ)+x-s-a-1) +
      B (e+1) (s+a-2*x-1) * B (z-1) ((m : ℤ)+x-s-a)))
  have hp : Summable p :=
    ((glp0032b2_sd_binom_summable (a-1) _).add
      (glp0032b2_sd_binom_shift_summable (a-1) 1 _)).mul_left _
  have hq : Summable q := (glp0032b2_sd_binom_summable a _).mul_left _
  have hr : Summable r := (glp0032b2_sd_binom_summable a _).mul_left _
  calc
    (m : ℝ) * C a (e+2) z m s = ∑' x : ℤ,
        (m : ℝ) * (B a x * (B (e+2) (s+a-2*x) * B z ((m : ℤ)+x-s-a))) := by
      rw [tsum_mul_left]; rfl
    _ = ∑' x : ℤ, ((p x + q x) + r x) := by
      apply tsum_congr
      intro x
      exact glp0032b2_sd_partner_term a e z m hn x s
    _ = (∑' x, p x) + (∑' x, q x) + ∑' x, r x := by
      rw [(hp.add hq).tsum_add hr, hp.tsum_add hq]
    _ = _ := by
      dsimp only [p,q,r]
      rw [glp0032b2_sd_partner11, glp0032b2_sd_partner00,
        tsum_mul_left]
      congr 2
      congr 1
      apply tsum_congr
      intro x
      congr 2 <;> congr 1 <;> ring

lemma glp0032b2_sd_smooth_step (f : ℤ → ℝ) (c s : ℤ)
    (hf : SDShape f c) (hs : c+1 ≤ 2*s) :
    f (s+1) + f s ≤ f s + f (s-1) := by
  have h := (independent_convolution_shape f c hf).2 s (s+1) hs (by omega)
  simp only [smoothMass, show s+1-1 = s by ring] at h
  linarith

lemma glp0032b2_sd_canonical_shape (a d z m : ℕ) (hm : 0 < m)
    (hn : a+d+z = 2*m) (hd : 1 ≤ d) : SDShape (C a d z m) d := by
  induction m using Nat.strong_induction_on generalizing a d z with
  | h m ih =>
    by_cases hd1 : d = 1
    · subst d
      exact glp0032b2_sd_one_shape a z m hn
    by_cases hd2 : d = 2
    · subst d
      exact glp0032b2_sd_two_shape a z m hn
    obtain ⟨e, rfl⟩ : ∃ e, d = e+2 := ⟨d-2, by omega⟩
    have he : 1 ≤ e := by omega
    have hm2 : 2 ≤ m := by omega
    have hcast : ((m-1 : ℕ) : ℤ) = (m : ℤ)-1 := by omega
    have hmid : SDShape (C a e z ((m : ℤ)-1)) e := by
      rw [← hcast]
      exact ih (m-1) (by omega) a e z (by omega) (by omega) he
    apply glp0032b2_sd_shape_of_step
    · exact glp0032b2_sd_count_symm a (e+2) z m hn
    · intro s hs
      have hA : (a : ℝ) *
          (C (a-1) (e+1) z ((m : ℤ)-1) (s+1) + C (a-1) (e+1) z ((m : ℤ)-1) s) ≤
          (a : ℝ) * (C (a-1) (e+1) z ((m : ℤ)-1) s + C (a-1) (e+1) z ((m : ℤ)-1) (s-1)) := by
        by_cases ha : a = 0
        · simp [ha]
        have hres : SDShape (C (a-1) (e+1) z ((m : ℤ)-1)) (e+1) := by
          rw [← hcast]
          exact ih (m-1) (by omega) (a-1) (e+1) z (by omega) (by omega) (by omega)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg a)
        exact glp0032b2_sd_smooth_step _ (e+1) s hres (by push_cast at hs ⊢; omega)
      have hZ : (z : ℝ) *
          (C a (e+1) (z-1) ((m : ℤ)-1) (s+1) + C a (e+1) (z-1) ((m : ℤ)-1) s) ≤
          (z : ℝ) * (C a (e+1) (z-1) ((m : ℤ)-1) s + C a (e+1) (z-1) ((m : ℤ)-1) (s-1)) := by
        by_cases hz : z = 0
        · simp [hz]
        have hres : SDShape (C a (e+1) (z-1) ((m : ℤ)-1)) (e+1) := by
          rw [← hcast]
          exact ih (m-1) (by omega) a (e+1) (z-1) (by omega) (by omega) (by omega)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg z)
        exact glp0032b2_sd_smooth_step _ (e+1) s hres (by push_cast at hs ⊢; omega)
      have hD : (2*(e+1) : ℝ) * C a e z ((m : ℤ)-1) s ≤
          (2*(e+1) : ℝ) * C a e z ((m : ℤ)-1) (s-1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hmid.2 (s-1) s (by push_cast at hs; omega) (by omega)
      have h := add_le_add (add_le_add hA hD) hZ
      have hnext := glp0032b2_sd_partner_sum a e z m hn (s+1)
      simp only [show s+1-1 = s by ring] at hnext
      rw [← hnext,
        ← glp0032b2_sd_partner_sum a e z m hn s] at h
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      nlinarith

lemma glp0032b2_sd_real_range (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [List.sum_range_succ, Finset.sum_range_succ, ih]

lemma glp0032b2_sd_binom_tsum_range (n : ℕ) (f : ℤ → ℝ) :
    (∑' k : ℤ, B n k * f k) = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * f k := by
  rw [tsum_eq_sum (s := (Finset.range (n+1)).image (fun k : ℕ => (k : ℤ))) (by
    intro k hk
    by_cases h : 0 ≤ k ∧ k ≤ n
    · exfalso
      apply hk
      exact Finset.mem_image.mpr ⟨k.toNat, Finset.mem_range.mpr (by omega), by omega⟩
    · rw [glp0032b2_sd_binom_zero _ _ (by omega), zero_mul])]
  rw [Finset.sum_image (by
    intro i hi j hj hij
    exact Int.ofNat_injective hij)]
  simp only [glp0032b2_sd_binom_nat]

lemma glp0032b2_sd_binom_truncate (n r : ℕ) (f : ℤ → ℝ)
    (hf : ∀ k : ℤ, (r : ℤ) < k → f k = 0) :
    (∑' k : ℤ, B n k * f k) =
      ((List.range (min n r+1)).map fun k => (n.choose k : ℝ) * f k).sum := by
  rw [glp0032b2_sd_binom_tsum_range, glp0032b2_sd_real_range]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkr
  have h : (r : ℤ) < k := by
    simp only [Finset.mem_range] at hk hkr
    omega
  rw [hf k h, mul_zero]

/-- A joint count sum. The last coordinate is forced by the treatment total. -/
noncomputable def glp0032b2_sd_joint : List ℕ → ℤ → (List ℤ → ℝ) → ℝ
  | [], t, f => if t = 0 then f [] else 0
  | [n], t, f => B n t * f [t]
  | n :: n' :: ns, t, f =>
      ∑' x : ℤ, B n x * glp0032b2_sd_joint (n' :: ns) (t-x) (fun xs => f (x::xs))

local notation "J" => glp0032b2_sd_joint

lemma glp0032b2_sd_joint_cons (n : ℕ) (ns : List ℕ) (t : ℤ) (f : List ℤ → ℝ) :
    J (n::ns) t f = ∑' x : ℤ, B n x * J ns (t-x) (fun xs => f (x::xs)) := by
  cases ns with
  | nil =>
    symm
    rw [tsum_eq_single t]
    · simp [glp0032b2_sd_joint]
    · intro x hx
      simp [glp0032b2_sd_joint, show t-x ≠ 0 by omega]
  | cons n' ns => rfl

lemma glp0032b2_sd_joint_negative (ns : List ℕ) (t : ℤ) (f : List ℤ → ℝ)
    (ht : t < 0) : J ns t f = 0 := by
  induction ns generalizing t f with
  | nil => simp [glp0032b2_sd_joint, show t ≠ 0 by omega]
  | cons n ns ih =>
    rw [glp0032b2_sd_joint_cons]
    refine (tsum_congr (g := fun _ : ℤ => (0 : ℝ)) ?_).trans tsum_zero
    intro x
    by_cases hx : x < 0
    · rw [glp0032b2_sd_binom_zero _ _ (Or.inl hx), zero_mul]
    · rw [ih (t-x) _ (by omega), mul_zero]

lemma glp0032b2_sd_joint_cons_nat (n r : ℕ) (ns : List ℕ) (f : List ℤ → ℝ) :
    J (n::ns) r f = ((List.range (min n r+1)).map fun k =>
      (n.choose k : ℝ) * J ns (r-k : ℕ) (fun xs => f ((k : ℤ)::xs))).sum := by
  rw [glp0032b2_sd_joint_cons,
    glp0032b2_sd_binom_truncate n r _ (by
      intro k hk
      exact glp0032b2_sd_joint_negative _ _ _ (by omega))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  have hk' : k ≤ r := by
    have h := List.mem_range.mp hk
    omega
  rw [Nat.cast_sub hk']

lemma glp0032b2_sd_binom_vandermonde (a b : ℕ) (t : ℤ) :
    (∑' x : ℤ, B a x * B b (t-x)) = B (a+b) t := by
  by_cases ht : t < 0
  · rw [glp0032b2_sd_binom_zero _ _ (Or.inl ht)]
    refine (tsum_congr (g := fun _ : ℤ => (0 : ℝ)) ?_).trans tsum_zero
    intro x
    by_cases hx : x < 0
    · rw [glp0032b2_sd_binom_zero _ _ (Or.inl hx), zero_mul]
    · rw [glp0032b2_sd_binom_zero b (t-x) (Or.inl (by omega)), mul_zero]
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t)
  rw [glp0032b2_sd_binom_truncate a r _ (by
    intro k hk
    exact glp0032b2_sd_binom_zero _ _ (Or.inl (by omega))),
    glp0032b2_sd_binom_nat]
  have hfun : ((List.range (min a r+1)).map fun k =>
      (a.choose k : ℝ) * B b ((r : ℤ)-k)).sum =
      (((List.range (min a r+1)).map fun k => binomial a k * binomial b (r-k)).sum : ℕ) := by
    rw [Nat.cast_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    have hk' : k ≤ r := by have h := List.mem_range.mp hk; omega
    simp only [Function.comp_apply, Nat.cast_mul, binomial_eq_choose,
      ← Nat.cast_sub hk', glp0032b2_sd_binom_nat]
  rw [hfun, bounded_vandermonde, binomial_eq_choose]

lemma glp0032b2_sd_joint_canonical (a b c z m : ℕ) (s : ℤ) :
    J [a,b,c,z] m (fun xs => if 2*xs[0]!+xs[1]!+xs[2]!-(a : ℤ)-c = s then 1 else 0) =
      C a (b+c) z m (s+c) := by
  simp only [glp0032b2_sd_joint, List.getElem!_cons_zero,
    List.getElem!_cons_succ, glp0032b2_sd_count]
  apply tsum_congr
  intro x
  congr 1
  calc
    (∑' y : ℤ, B b y * ∑' w : ℤ,
        B c w * (B z ((m : ℤ)-x-y-w) *
          if 2*x+y+w-a-c = s then 1 else 0)) =
      ∑' y : ℤ, B b y * (B c (s+a+c-2*x-y) * B z ((m : ℤ)+x-s-a-c)) := by
        apply tsum_congr
        intro y
        congr 1
        rw [tsum_eq_single (s+a+c-2*x-y)]
        · rw [if_pos (by omega)]
          simp only [mul_one]
          rw [show (m : ℤ)-x-y-(s+a+c-2*x-y) = (m : ℤ)+x-s-a-c by ring]
        · intro w hw
          rw [if_neg (by omega)]
          ring
    _ = (∑' y : ℤ, B b y * B c ((s+c+a-2*x)-y)) * B z ((m : ℤ)+x-s-a-c) := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro y
      rw [show s+a+c-2*x-y = s+c+a-2*x-y by ring]
      ring
    _ = _ := by
      rw [glp0032b2_sd_binom_vandermonde]
      rw [show (m : ℤ)+x-s-a-c = (m : ℤ)+x-(s+c)-a by ring]

lemma glp0032b2_sd_flatMap_sum {A D : Type*} (xs : List A)
    (f : A → List D) (g : D → ℝ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma glp0032b2_sd_filterMap_sum {A D : Type*} (xs : List A)
    (f : A → Option D) (g : D → ℝ) :
    ((xs.filterMap f).map g).sum =
      (xs.map fun x => match f x with | none => 0 | some y => g y).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [List.filterMap_cons, h, ih]

lemma glp0032b2_sd_joint_design (v : Counts) (m : ℕ) (f : List ℤ → ℝ) :
    ((randomStates v m).map fun q => (multiplicity v q : ℝ) *
      f [q.a,q.b,q.c,q.d]).sum = J [v.a,v.b,v.c,v.d] m f := by
  have inner (a b : ℕ) :
      (((List.range (min v.c (m-a-b)+1)).filterMap fun c =>
        if m-a-b-c ≤ v.d then some (⟨a,b,c,m-a-b-c⟩ : Counts) else none).map
        fun q => (multiplicity v q : ℝ) * f [q.a,q.b,q.c,q.d]).sum =
      (binomial v.a a : ℝ) * (binomial v.b b : ℝ) *
        J [v.c,v.d] (m-a-b : ℕ) (fun xs => f ((a : ℤ)::(b : ℤ)::xs)) := by
    rw [glp0032b2_sd_filterMap_sum,
      glp0032b2_sd_joint_cons_nat, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    by_cases hd : m-a-b-c ≤ v.d
    · simp only [if_pos hd, multiplicity, Nat.cast_mul, glp0032b2_sd_joint,
        glp0032b2_sd_binom_nat, Function.comp_apply, binomial_eq_choose]
      ring
    · simp only [if_neg hd, glp0032b2_sd_joint, glp0032b2_sd_binom_nat,
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hd), zero_mul, mul_zero, Function.comp_apply]
      norm_num
  unfold randomStates
  simp only [glp0032b2_sd_flatMap_sum, inner]
  rw [glp0032b2_sd_joint_cons_nat]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [glp0032b2_sd_joint_cons_nat, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp_apply, binomial_eq_choose]
  ring


/- Weighted Pascal decomposition and one-bit tail transport. -/
def glp0032b2_bit_coord (v : Counts) (i : Fin 4) : ℕ := ![v.a,v.b,v.c,v.d] i

def glp0032b2_bit_add (v : Counts) (i : Fin 4) : Counts :=
  ⟨v.a + if i = 0 then 1 else 0, v.b + if i = 1 then 1 else 0,
   v.c + if i = 2 then 1 else 0, v.d + if i = 3 then 1 else 0⟩

def glp0032b2_bit_sub (v : Counts) (i : Fin 4) : Counts :=
  ⟨v.a - if i = 0 then 1 else 0, v.b - if i = 1 then 1 else 0,
   v.c - if i = 2 then 1 else 0, v.d - if i = 3 then 1 else 0⟩

lemma glp0032b2_bit_add_total (v : Counts) (i : Fin 4) :
    (glp0032b2_bit_add v i).total = v.total + 1 := by
  fin_cases i <;> simp [glp0032b2_bit_add, Counts.total] <;> omega

lemma glp0032b2_bit_sub_total (v : Counts) (i : Fin 4)
    (h : 0 < glp0032b2_bit_coord v i) :
    (glp0032b2_bit_sub v i).total + 1 = v.total := by
  fin_cases i <;> simp [glp0032b2_bit_coord] at h <;>
    simp [glp0032b2_bit_sub, Counts.total] <;> omega

lemma glp0032b2_bit_sub_add (v : Counts) (i : Fin 4) :
    glp0032b2_bit_sub (glp0032b2_bit_add v i) i = v := by
  fin_cases i <;> ext <;> simp [glp0032b2_bit_sub, glp0032b2_bit_add]

lemma glp0032b2_bit_add_sub (v : Counts) (i : Fin 4)
    (h : 0 < glp0032b2_bit_coord v i) :
    glp0032b2_bit_add (glp0032b2_bit_sub v i) i = v := by
  fin_cases i <;> simp [glp0032b2_bit_coord] at h <;>
    ext <;> simp [glp0032b2_bit_sub, glp0032b2_bit_add] <;> omega

lemma glp0032b2_bit_coord_add (v : Counts) (i : Fin 4) :
    0 < glp0032b2_bit_coord (glp0032b2_bit_add v i) i := by
  fin_cases i <;> simp [glp0032b2_bit_coord, glp0032b2_bit_add]

lemma glp0032b2_bit_mult_add (v q : Counts) (i : Fin 4) :
    multiplicity (glp0032b2_bit_add v i) q = multiplicity v q +
      if 0 < glp0032b2_bit_coord q i then multiplicity v (glp0032b2_bit_sub q i) else 0 := by
  rcases q with ⟨a,b,c,d⟩
  fin_cases i
  · cases a <;> simp [glp0032b2_bit_add, glp0032b2_bit_coord, glp0032b2_bit_sub,
      multiplicity, binomial_eq_choose, Nat.choose_succ_succ] <;> ring
  · cases b <;> simp [glp0032b2_bit_add, glp0032b2_bit_coord, glp0032b2_bit_sub,
      multiplicity, binomial_eq_choose, Nat.choose_succ_succ] <;> ring
  · cases c <;> simp [glp0032b2_bit_add, glp0032b2_bit_coord, glp0032b2_bit_sub,
      multiplicity, binomial_eq_choose, Nat.choose_succ_succ] <;> ring
  · cases d <;> simp [glp0032b2_bit_add, glp0032b2_bit_coord, glp0032b2_bit_sub,
      multiplicity, binomial_eq_choose, Nat.choose_succ_succ] <;> ring

noncomputable def glp0032b2_bit_weighted (v : Counts) (m : ℕ) (f : Counts → ℕ) : ℕ :=
  ∑ q ∈ allCounts m, multiplicity v q * f q

lemma glp0032b2_bit_weighted_add (v : Counts) (m : ℕ) (i : Fin 4) (f : Counts → ℕ) :
    glp0032b2_bit_weighted (glp0032b2_bit_add v i) (m+1) f =
      glp0032b2_bit_weighted v (m+1) f +
      glp0032b2_bit_weighted v m (fun q => f (glp0032b2_bit_add q i)) := by
  unfold glp0032b2_bit_weighted
  simp_rw [glp0032b2_bit_mult_add, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  have he : (∑ q ∈ allCounts (m+1),
      (if 0 < glp0032b2_bit_coord q i then multiplicity v (glp0032b2_bit_sub q i) else 0) * f q) =
      ∑ q ∈ (allCounts (m+1)).filter (fun q => 0 < glp0032b2_bit_coord q i),
        multiplicity v (glp0032b2_bit_sub q i) * f q := by
    simp only [Finset.sum_filter, ite_mul, zero_mul]
  rw [he]
  symm
  apply Finset.sum_nbij' (fun q => glp0032b2_bit_add q i) (fun q => glp0032b2_bit_sub q i)
  · intro q hq
    apply Finset.mem_filter.mpr
    refine ⟨?_, glp0032b2_bit_coord_add q i⟩
    rw [glp0032b2_allCounts_mem, glp0032b2_bit_add_total,
      (glp0032b2_allCounts_mem _ _).mp hq]
  · intro q hq
    obtain ⟨hq,hpos⟩ := Finset.mem_filter.mp hq
    rw [glp0032b2_allCounts_mem] at hq ⊢
    have ht := glp0032b2_bit_sub_total q i hpos
    omega
  · intro q _
    exact glp0032b2_bit_sub_add q i
  · intro q hq
    exact glp0032b2_bit_add_sub q i (Finset.mem_filter.mp hq).2
  · intro q _
    rw [glp0032b2_bit_sub_add]


lemma glp0032b2_bit_mult_zero (v q : Counts) (m : ℕ) (ht : q.total = m)
    (hq : q ∉ randomStates v m) : multiplicity v q = 0 := by
  by_cases ha : q.a ≤ v.a
  · by_cases hb : q.b ≤ v.b
    · by_cases hc : q.c ≤ v.c
      · by_cases hd : q.d ≤ v.d
        · exact False.elim (hq ((glp0032b2_mem_randomStates_iff _ _ _).mpr
            ⟨ha,hb,hc,hd,ht⟩))
        · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hd)]
      · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc)]
    · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hb)]
  · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]

lemma glp0032b2_bit_weighted_list (v : Counts) (m : ℕ) (f : Counts → ℕ) :
    glp0032b2_bit_weighted v m f =
      ((randomStates v m).map fun q => multiplicity v q * f q).sum := by
  rw [← List.sum_toFinset _ (glp0032b2_randomStates_nodup _ _)]
  unfold glp0032b2_bit_weighted
  symm
  apply Finset.sum_subset
  · intro q hq
    rw [glp0032b2_allCounts_mem]
    exact (random_state_facts v m q (List.mem_toFinset.mp hq)).2.2.2.2
  · intro q hq hnot
    have hz := glp0032b2_bit_mult_zero v q m
      ((glp0032b2_allCounts_mem _ _).mp hq)
      (fun h => hnot (List.mem_toFinset.mpr h))
    rw [hz, zero_mul]

def glp0032b2_bit_score (v q : Counts) : ℤ :=
  4*(q.a : ℤ)+2*q.b+2*q.c-2*v.a-v.b-v.c

def glp0032b2_bit_threshold (v o : Counts) : ℤ := 2*((o.a : ℤ)-o.c)-v.effect

def glp0032b2_bit_tailIndicator (v o q : Counts) : ℕ :=
  if (glp0032b2_bit_threshold v o).natAbs ≤ (glp0032b2_bit_score v q).natAbs then 1 else 0

lemma glp0032b2_bit_dev_obs (v o : Counts) (m : ℕ)
    (hn : v.total = 2*m) :
    deviationNumerator v o m = (m : ℤ)^2 * glp0032b2_bit_threshold v o := by
  unfold deviationNumerator glp0032b2_bit_threshold
  rw [hn]
  push_cast
  ring

lemma glp0032b2_bit_dev_state (v q : Counts) (m : ℕ)
    (hn : v.total = 2*m) (hq : q ∈ randomStates v m) :
    deviationNumerator v (observed v q) m = (m : ℤ)^2 * glp0032b2_bit_score v q := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  rw [glp0032b2_bit_dev_obs v (observed v q) m hn]
  congr 1
  dsimp [glp0032b2_bit_threshold, glp0032b2_bit_score, observed, Counts.effect]
  rw [Nat.cast_sub (by omega : q.c ≤ v.a-q.a+v.c), Nat.cast_add, Nat.cast_sub ha]
  push_cast
  ring

lemma glp0032b2_bit_tail_weighted (v o : Counts) (m : ℕ)
    (hm : 0 < m) (hn : v.total = 2*m) (ho : o.a+o.b = m) :
    tailCount v o = glp0032b2_bit_weighted v m (glp0032b2_bit_tailIndicator v o) := by
  rw [glp0032b2_bit_weighted_list]
  unfold tailCount
  rw [ho]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  rw [glp0032b2_bit_dev_state v q m hn hq, glp0032b2_bit_dev_obs v o m hn]
  simp only [Int.natAbs_mul]
  have hpos : 0 < ((m : ℤ)^2).natAbs := by positivity
  have he : ((m : ℤ)^2).natAbs * (glp0032b2_bit_threshold v o).natAbs ≤
      ((m : ℤ)^2).natAbs * (glp0032b2_bit_score v q).natAbs ↔
      (glp0032b2_bit_threshold v o).natAbs ≤ (glp0032b2_bit_score v q).natAbs :=
    mul_le_mul_iff_right₀ hpos
  simp only [he, glp0032b2_bit_tailIndicator]
  split_ifs <;> simp

lemma glp0032b2_bit_tail_indicator_mono (v v' o o' q q' : Counts)
    (ht : glp0032b2_bit_threshold v' o' = glp0032b2_bit_threshold v o + 1)
    (hneg : glp0032b2_bit_threshold v' o' ≤ 0)
    (hs : glp0032b2_bit_score v' q' = glp0032b2_bit_score v q + 1 ∨
      glp0032b2_bit_score v' q' = glp0032b2_bit_score v q - 1) :
    glp0032b2_bit_tailIndicator v o q ≤ glp0032b2_bit_tailIndicator v' o' q' := by
  unfold glp0032b2_bit_tailIndicator
  split_ifs with h h'
  · rfl
  · exfalso
    have ha := Int.natAbs_eq (glp0032b2_bit_threshold v o)
    have hb := Int.natAbs_eq (glp0032b2_bit_threshold v' o')
    have hc := Int.natAbs_eq (glp0032b2_bit_score v q)
    have hd := Int.natAbs_eq (glp0032b2_bit_score v' q')
    omega
  all_goals omega


lemma glp0032b2_bit_pvalue_step (u o o' : Counts) (i j : Fin 4) (m : ℕ)
    (hm : 0 < m) (hn : u.total+1 = 2*m)
    (ho : o.a+o.b = m) (ho' : o'.a+o'.b = m)
    (ht : glp0032b2_bit_threshold (glp0032b2_bit_add u i) o' =
      glp0032b2_bit_threshold (glp0032b2_bit_add u j) o + 1)
    (hneg : glp0032b2_bit_threshold (glp0032b2_bit_add u i) o' ≤ 0)
    (hs : ∀ q, glp0032b2_bit_score (glp0032b2_bit_add u i) q =
      glp0032b2_bit_score (glp0032b2_bit_add u j) q + 1 ∨
      glp0032b2_bit_score (glp0032b2_bit_add u i) q =
      glp0032b2_bit_score (glp0032b2_bit_add u j) q - 1)
    (hs' : ∀ q, glp0032b2_bit_score (glp0032b2_bit_add u i) (glp0032b2_bit_add q i) =
      glp0032b2_bit_score (glp0032b2_bit_add u j) (glp0032b2_bit_add q j) + 1 ∨
      glp0032b2_bit_score (glp0032b2_bit_add u i) (glp0032b2_bit_add q i) =
      glp0032b2_bit_score (glp0032b2_bit_add u j) (glp0032b2_bit_add q j) - 1) :
    pValue (glp0032b2_bit_add u j) o ≤ pValue (glp0032b2_bit_add u i) o' := by
  have hn' (k : Fin 4) : (glp0032b2_bit_add u k).total = 2*m := by
    rw [glp0032b2_bit_add_total, hn]
  unfold pValue
  rw [hn' i, hn' j, ho, ho']
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  rw [glp0032b2_bit_tail_weighted _ _ m hm (hn' j) ho,
    glp0032b2_bit_tail_weighted _ _ m hm (hn' i) ho']
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [glp0032b2_bit_weighted_add, glp0032b2_bit_weighted_add]
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro q _
    exact Nat.mul_le_mul_left _ (glp0032b2_bit_tail_indicator_mono _ _ _ _ _ _ ht hneg (hs q))
  · apply Finset.sum_le_sum
    intro q _
    exact Nat.mul_le_mul_left _ (glp0032b2_bit_tail_indicator_mono _ _ _ _ _ _ ht hneg (hs' q))


lemma glp0032b2_sumAll_add (v : Counts) (m : ℕ) (i : Fin 4) (F : Counts → ℝ) :
    glp0032b2_sumAll (glp0032b2_bit_add v i) (m+1) F =
      glp0032b2_sumAll v (m+1) F +
      glp0032b2_sumAll v m (fun q => F (glp0032b2_bit_add q i)) := by
  unfold glp0032b2_sumAll
  simp_rw [glp0032b2_bit_mult_add, Nat.cast_add, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  have he : (∑ q ∈ allCounts (m+1),
      ((if 0 < glp0032b2_bit_coord q i then multiplicity v (glp0032b2_bit_sub q i) else 0 : ℕ) : ℝ) * F q) =
      ∑ q ∈ (allCounts (m+1)).filter (fun q => 0 < glp0032b2_bit_coord q i),
        (multiplicity v (glp0032b2_bit_sub q i) : ℝ) * F q := by
    simp only [Finset.sum_filter, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
  rw [he]
  symm
  apply Finset.sum_nbij' (fun q => glp0032b2_bit_add q i) (fun q => glp0032b2_bit_sub q i)
  · intro q hq
    apply Finset.mem_filter.mpr
    refine ⟨?_, glp0032b2_bit_coord_add q i⟩
    rw [glp0032b2_allCounts_mem, glp0032b2_bit_add_total,
      (glp0032b2_allCounts_mem _ _).mp hq]
  · intro q hq
    obtain ⟨hq,hpos⟩ := Finset.mem_filter.mp hq
    rw [glp0032b2_allCounts_mem] at hq ⊢
    have ht := glp0032b2_bit_sub_total q i hpos
    omega
  · intro q _
    exact glp0032b2_bit_sub_add q i
  · intro q hq
    exact glp0032b2_bit_add_sub q i (Finset.mem_filter.mp hq).2
  · intro q _
    rw [glp0032b2_bit_sub_add]

lemma glp0032b2_sumAll_list (v : Counts) (m : ℕ) (F : Counts → ℝ) :
    glp0032b2_sumAll v m F =
      ((randomStates v m).map fun q => (multiplicity v q : ℝ) * F q).sum := by
  rw [← List.sum_toFinset _ (glp0032b2_randomStates_nodup _ _)]
  unfold glp0032b2_sumAll
  symm
  apply Finset.sum_subset
  · intro q hq
    rw [glp0032b2_allCounts_mem]
    exact (random_state_facts v m q (List.mem_toFinset.mp hq)).2.2.2.2
  · intro q hq hnot
    have hz := glp0032b2_bit_mult_zero v q m
      ((glp0032b2_allCounts_mem _ _).mp hq)
      (fun h => hnot (List.mem_toFinset.mpr h))
    rw [hz, Nat.cast_zero, zero_mul]

noncomputable def glp0032b2_mass (v : Counts) (m : ℕ) (s : ℤ) : ℝ :=
  glp0032b2_sumAll v m (fun q => if glp0032b2_score v q = s then 1 else 0)

lemma glp0032b2_mass_formula (v : Counts) (m : ℕ) (s : ℤ) :
    glp0032b2_mass v m s = glp0032b2_sd_count v.a (v.b+v.c) v.d m (s+v.c) := by
  unfold glp0032b2_mass
  rw [glp0032b2_sumAll_list]
  convert
    (glp0032b2_sd_joint_design v m
      (fun xs => if 2*xs[0]!+xs[1]!+xs[2]!-(v.a : ℤ)-v.c = s then 1 else 0)).trans
      (glp0032b2_sd_joint_canonical v.a v.b v.c v.d m s) using 1
  congr 1

lemma glp0032b2_mass_shape (v : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (hd : 1 ≤ v.b+v.c) :
    SDShape (glp0032b2_mass v m) v.effect := by
  have hcan := glp0032b2_sd_canonical_shape v.a (v.b+v.c) v.d m hm
    (by simpa only [Counts.total, Nat.add_assoc] using hn) hd
  constructor
  · intro s
    rw [glp0032b2_mass_formula, glp0032b2_mass_formula]
    rw [show v.effect-s+v.c = ((v.b+v.c : ℕ) : ℤ)-(s+v.c) by
      dsimp [Counts.effect]; push_cast; ring]
    exact hcan.1 (s+v.c)
  · intro i j hi hij
    rw [glp0032b2_mass_formula, glp0032b2_mass_formula]
    exact hcan.2 (i+v.c) (j+v.c) (by dsimp [Counts.effect] at hi; push_cast; omega) (by omega)

lemma glp0032b2_sumAll_pair (v : Counts) (m : ℕ) (i j : Fin 4) (F : Counts → ℝ) :
    glp0032b2_sumAll (glp0032b2_bit_add (glp0032b2_bit_add v i) j) (m+2) F =
      glp0032b2_sumAll v (m+2) F +
      glp0032b2_sumAll v (m+1) (fun q => F (glp0032b2_bit_add q i)) +
      glp0032b2_sumAll v (m+1) (fun q => F (glp0032b2_bit_add q j)) +
      glp0032b2_sumAll v m (fun q => F (glp0032b2_bit_add (glp0032b2_bit_add q i) j)) := by
  rw [show m+2 = (m+1)+1 by omega, glp0032b2_sumAll_add,
    glp0032b2_sumAll_add, glp0032b2_sumAll_add]
  ring

noncomputable def glp0032b2_tail (d e s : ℤ) : ℝ :=
  if (2*e-d).natAbs ≤ (2*s-d).natAbs then 1 else 0

lemma glp0032b2_tail_real (v o : Counts) (m : ℕ)
    (hm : 0 < m) (hn : v.total = 2*m) (ho : o.a+o.b = m) :
    (tailCount v o : ℝ) = glp0032b2_sumAll v m
      (fun q => glp0032b2_tail v.effect ((o.a : ℤ)-o.c) (glp0032b2_score v q)) := by
  rw [glp0032b2_bit_tail_weighted v o m hm hn ho]
  unfold glp0032b2_bit_weighted glp0032b2_sumAll
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  have hs : glp0032b2_bit_score v q = 2*glp0032b2_score v q-v.effect := by
    dsimp [glp0032b2_bit_score, glp0032b2_score, Counts.effect]
    ring
  simp only [glp0032b2_bit_tailIndicator, glp0032b2_bit_threshold, hs,
    glp0032b2_tail, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma glp0032b2_tail_boundary (d e s : ℤ) (he : 2*e ≠ d) :
    glp0032b2_tail d e (s+1) + glp0032b2_tail d e (s-1) -
      2*glp0032b2_tail d e s =
      (if s = max e (d-e)-1 then 1 else 0) +
      (if s = min e (d-e)+1 then 1 else 0) -
      (if s = max e (d-e) then 1 else 0) -
      (if s = min e (d-e) then 1 else 0) := by
  have hE (x : ℤ) : (2*e-d).natAbs ≤ (2*x-d).natAbs ↔
      x ≤ min e (d-e) ∨ max e (d-e) ≤ x := by
    have h1 := Int.natAbs_eq (2*e-d)
    have h2 := Int.natAbs_eq (2*x-d)
    constructor <;> intro h <;> omega
  unfold glp0032b2_tail
  simp only [hE]
  have hlh : min e (d-e) < max e (d-e) := by omega
  split_ifs <;> norm_num <;> omega

lemma glp0032b2_tail_smoothing (v : Counts) (m : ℕ) (e : ℤ)
    (hf : SDShape (glp0032b2_mass v m) v.effect) :
    glp0032b2_sumAll v m (fun q => glp0032b2_tail v.effect e (glp0032b2_score v q)) * 2 ≤
      glp0032b2_sumAll v m (fun q => glp0032b2_tail v.effect e (glp0032b2_score v q+1)) +
      glp0032b2_sumAll v m (fun q => glp0032b2_tail v.effect e (glp0032b2_score v q-1)) := by
  by_cases he : 2*e = v.effect
  · have ht (s : ℤ) : glp0032b2_tail v.effect e s = 1 := by
      simp [glp0032b2_tail, ← he]
    simp only [ht]
    linarith
  let H := max e (v.effect-e)
  let L := min e (v.effect-e)
  have hLH : L+H = v.effect := by dsimp [L,H]; omega
  have hlt : L < H := by dsimp [L,H]; omega
  have hsym1 : glp0032b2_mass v m L = glp0032b2_mass v m H := by
    simpa only [show v.effect-H = L by omega] using hf.1 H
  have hsym2 : glp0032b2_mass v m (L+1) = glp0032b2_mass v m (H-1) := by
    simpa only [show v.effect-(H-1) = L+1 by omega] using hf.1 (H-1)
  have hdec : glp0032b2_mass v m H ≤ glp0032b2_mass v m (H-1) := by
    by_cases hr : v.effect ≤ 2*(H-1)
    · exact hf.2 (H-1) H hr (by omega)
    · have hmid : v.effect-H = H-1 := by omega
      exact le_of_eq (by simpa only [hmid] using (hf.1 H).symm)
  have hid : glp0032b2_sumAll v m (fun q =>
      glp0032b2_tail v.effect e (glp0032b2_score v q+1) +
      glp0032b2_tail v.effect e (glp0032b2_score v q-1) -
      2*glp0032b2_tail v.effect e (glp0032b2_score v q)) =
      glp0032b2_mass v m (H-1) + glp0032b2_mass v m (L+1) -
      glp0032b2_mass v m H - glp0032b2_mass v m L := by
    simp only [glp0032b2_mass, glp0032b2_sumAll]
    simp_rw [glp0032b2_tail_boundary _ _ _ he]
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rfl
  rw [hsym1,hsym2] at hid
  unfold glp0032b2_sumAll at hid ⊢
  have hc : (∑ q ∈ allCounts m, (multiplicity v q : ℝ) *
      (2*glp0032b2_tail v.effect e (glp0032b2_score v q))) =
      2 * ∑ q ∈ allCounts m, (multiplicity v q : ℝ) *
        glp0032b2_tail v.effect e (glp0032b2_score v q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hid
  rw [hc] at hid
  linarith


lemma glp0032b2_score_add (v q : Counts) (i : Fin 4) :
    glp0032b2_score v (glp0032b2_bit_add q i) = glp0032b2_score v q +
      (if i = 0 then 2 else if i = 1 ∨ i = 2 then 1 else 0) := by
  fin_cases i <;> simp [glp0032b2_bit_add, glp0032b2_score] <;> ring

lemma glp0032b2_pair_old_effect (v : Counts) :
    (glp0032b2_bit_add (glp0032b2_bit_add v 1) 2).effect = v.effect := by
  simp [glp0032b2_bit_add, Counts.effect]

lemma glp0032b2_pair_new_effect (v : Counts) :
    (glp0032b2_bit_add (glp0032b2_bit_add v 0) 3).effect = v.effect := by
  simp [glp0032b2_bit_add, Counts.effect]

lemma glp0032b2_pair_old_score (v q : Counts) :
    glp0032b2_score (glp0032b2_bit_add (glp0032b2_bit_add v 1) 2) q =
      glp0032b2_score v q - 1 := by
  simp [glp0032b2_bit_add, glp0032b2_score]
  ring

lemma glp0032b2_pair_new_score (v q : Counts) :
    glp0032b2_score (glp0032b2_bit_add (glp0032b2_bit_add v 0) 3) q =
      glp0032b2_score v q - 1 := by
  simp [glp0032b2_bit_add, glp0032b2_score]
  ring

lemma glp0032b2_pair_tail_comparison (u o : Counts) (m : ℕ)
    (hn : u.total = 2*(m+1)) (hd : 1 ≤ u.b+u.c) (ho : o.a+o.b = m+2) :
    pValue (glp0032b2_bit_add (glp0032b2_bit_add u 1) 2) o ≤
      pValue (glp0032b2_bit_add (glp0032b2_bit_add u 0) 3) o := by
  let v := glp0032b2_bit_add (glp0032b2_bit_add u 1) 2
  let w := glp0032b2_bit_add (glp0032b2_bit_add u 0) 3
  have hvn : v.total = 2*(m+2) := by
    dsimp [v]
    rw [glp0032b2_bit_add_total, glp0032b2_bit_add_total, hn]
    omega
  have hwn : w.total = 2*(m+2) := by
    dsimp [w]
    rw [glp0032b2_bit_add_total, glp0032b2_bit_add_total, hn]
    omega
  have hs := glp0032b2_tail_smoothing u (m+1) ((o.a : ℤ)-o.c)
    (glp0032b2_mass_shape u (m+1) (by omega) hn hd)
  have hv : (tailCount v o : ℝ) =
      glp0032b2_sumAll u (m+2) (fun q => glp0032b2_tail u.effect ((o.a : ℤ)-o.c) (glp0032b2_score u q-1)) +
      2*glp0032b2_sumAll u (m+1) (fun q => glp0032b2_tail u.effect ((o.a : ℤ)-o.c) (glp0032b2_score u q)) +
      glp0032b2_sumAll u m (fun q => glp0032b2_tail u.effect ((o.a : ℤ)-o.c) (glp0032b2_score u q+1)) := by
    rw [glp0032b2_tail_real v o (m+2) (by omega) hvn ho]
    dsimp only [v]
    rw [glp0032b2_sumAll_pair]
    simp only [glp0032b2_pair_old_effect, glp0032b2_pair_old_score,
      glp0032b2_score_add, Fin.reduceEq, or_true, true_or, if_true, if_false, sub_add_cancel, add_zero,
      show ∀ s : ℤ, s+1-1 = s by intro s; ring,
      show ∀ s : ℤ, s+1+1-1 = s+1 by intro s; ring]
    ring
  have hw : (tailCount w o : ℝ) =
      glp0032b2_sumAll u (m+2) (fun q => glp0032b2_tail u.effect ((o.a : ℤ)-o.c) (glp0032b2_score u q-1)) +
      glp0032b2_sumAll u (m+1) (fun q => glp0032b2_tail u.effect ((o.a : ℤ)-o.c) (glp0032b2_score u q+1)) +
      glp0032b2_sumAll u (m+1) (fun q => glp0032b2_tail u.effect ((o.a : ℤ)-o.c) (glp0032b2_score u q-1)) +
      glp0032b2_sumAll u m (fun q => glp0032b2_tail u.effect ((o.a : ℤ)-o.c) (glp0032b2_score u q+1)) := by
    rw [glp0032b2_tail_real w o (m+2) (by omega) hwn ho]
    dsimp only [w]
    rw [glp0032b2_sumAll_pair]
    simp only [glp0032b2_pair_new_effect, glp0032b2_pair_new_score,
      glp0032b2_score_add, Fin.reduceEq, false_or, or_false, if_true, if_false, add_zero,
      show ∀ s : ℤ, s-1+2 = s+1 by intro s; ring,
      show ∀ s : ℤ, s+2-1 = s+1 by intro s; ring,
      show ∀ s : ℤ, s+0-1 = s-1 by intro s; ring,
      show ∀ s : ℤ, s+2+0-1 = s+1 by intro s; ring]
  have htailR : (tailCount v o : ℝ) ≤ tailCount w o := by linarith
  have htail : tailCount v o ≤ tailCount w o := by exact_mod_cast htailR
  unfold pValue
  rw [hvn, hwn]
  exact div_le_div_of_nonneg_right (by exact_mod_cast htail) (by positivity)

lemma glp0032b2_merge (o v : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hn : v.total = o.total)
    (hmin : 1 ≤ min v.b v.c) (hmax : 2 ≤ max v.b v.c) :
    pValue v o ≤ pValue ⟨v.a+1,v.b-1,v.c-1,v.d+1⟩ o := by
  let u : Counts := ⟨v.a,v.b-1,v.c-1,v.d⟩
  have hm : 2 ≤ o.a+o.b := by dsimp [Counts.total] at hn; omega
  have hut : u.total = 2*((o.a+o.b-2)+1) := by
    dsimp [u, Counts.total] at *
    omega
  have hud : 1 ≤ u.b+u.c := by dsimp [u]; omega
  have h := glp0032b2_pair_tail_comparison u o (o.a+o.b-2) hut hud (by omega)
  have hv : glp0032b2_bit_add (glp0032b2_bit_add u 1) 2 = v := by
    ext <;> simp [glp0032b2_bit_add, u] <;> omega
  have hw : glp0032b2_bit_add (glp0032b2_bit_add u 0) 3 =
      (⟨v.a+1,v.b-1,v.c-1,v.d+1⟩ : Counts) := by
    ext <;> simp [glp0032b2_bit_add, u]
  simpa only [hv,hw] using h

/- Outcome reflection. -/
def glp0032b2_reflect_reverse (v : Counts) : Counts :=
  ⟨v.d, v.c, v.b, v.a⟩

lemma glp0032b2_reflect_reverse_reverse (v : Counts) :
    glp0032b2_reflect_reverse (glp0032b2_reflect_reverse v) = v := by
  cases v
  rfl

lemma glp0032b2_reflect_complement_complement (o : Counts) :
    complementObserved (complementObserved o) = o := by
  cases o
  rfl

lemma glp0032b2_reflect_reverse_total (v : Counts) :
    (glp0032b2_reflect_reverse v).total = v.total := by
  dsimp [glp0032b2_reflect_reverse, Counts.total]
  omega

lemma glp0032b2_reflect_complement_total (o : Counts) :
    (complementObserved o).total = o.total := by
  dsimp [complementObserved, Counts.total]
  omega

lemma glp0032b2_reflect_reverse_effect (v : Counts) :
    (glp0032b2_reflect_reverse v).effect = -v.effect := by
  dsimp [glp0032b2_reflect_reverse, Counts.effect]
  ring

lemma glp0032b2_reflect_reverse_tau (v : Counts) :
    tau (glp0032b2_reflect_reverse v) = -tau v := by
  have hQ : tauQ (glp0032b2_reflect_reverse v) = -tauQ v := by
    unfold tauQ
    rw [glp0032b2_reflect_reverse_total,
      glp0032b2_reflect_reverse_effect]
    push_cast
    ring
  simpa only [tau, Rat.cast_neg] using congrArg (fun x : ℚ => (x : ℝ)) hQ


lemma glp0032b2_reflect_possible_forward (o v : Counts)
    (hv : Possible o v) :
    Possible (complementObserved o) (glp0032b2_reflect_reverse v) := by
  simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map,
    List.mem_range] at hv ⊢
  rcases hv with ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩
  dsimp [complementObserved]
  refine ⟨o.b-j, by omega, o.a-i, by omega,
    o.d-l, by omega, o.c-k, by omega, ?_⟩
  ext <;> dsimp [glp0032b2_reflect_reverse] <;> omega


lemma glp0032b2_reflect_reverse_state (v q : Counts) (m : ℕ)
    (hq : q ∈ randomStates v m) :
    glp0032b2_reflect_reverse q ∈
      randomStates (glp0032b2_reflect_reverse v) m := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  apply (glp0032b2_mem_randomStates_iff _ _ _).mpr
  exact ⟨hd,hc,hb,ha, by rw [glp0032b2_reflect_reverse_total, ht]⟩

lemma glp0032b2_reflect_reverse_observed (v q : Counts)
    (ha : q.a ≤ v.a) (hb : q.b ≤ v.b) (hc : q.c ≤ v.c) (hd : q.d ≤ v.d) :
    observed (glp0032b2_reflect_reverse v)
      (glp0032b2_reflect_reverse q) = complementObserved (observed v q) := by
  ext <;> dsimp [observed, glp0032b2_reflect_reverse, complementObserved] <;> omega

lemma glp0032b2_reflect_reverse_multiplicity (v q : Counts) :
    multiplicity (glp0032b2_reflect_reverse v)
      (glp0032b2_reflect_reverse q) = multiplicity v q := by
  dsimp [multiplicity, glp0032b2_reflect_reverse]
  ring

lemma glp0032b2_reflect_complement_deviation (v o : Counts)
    (hn : v.total = o.total) :
    deviationNumerator (glp0032b2_reflect_reverse v)
      (complementObserved o) (o.a+o.b) = -deviationNumerator v o (o.a+o.b) := by
  have hZ : (v.total : ℤ) = (o.a : ℤ)+o.b+o.c+o.d := by
    exact_mod_cast hn
  unfold deviationNumerator
  rw [glp0032b2_reflect_reverse_total,
    glp0032b2_reflect_reverse_effect]
  dsimp [complementObserved]
  push_cast
  rw [hZ]
  ring

/-- The outcome-complementation p-value identity requires equal table totals,
even when both observed arms are positive. -/
lemma glp0032b2_reflect_complement_pValue (v o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hn : v.total = o.total) :
    pValue (⟨v.d,v.c,v.b,v.a⟩ : Counts) (complementObserved o) = pValue v o := by
  change pValue (glp0032b2_reflect_reverse v) (complementObserved o) = _
  have hm : (complementObserved o).a+(complementObserved o).b = o.a+o.b := by
    dsimp [complementObserved]
    omega
  have htail : tailCount (glp0032b2_reflect_reverse v) (complementObserved o) =
      tailCount v o := by
    unfold tailCount
    rw [hm]
    rw [← List.sum_toFinset _ (glp0032b2_randomStates_nodup _ _),
      ← List.sum_toFinset _ (glp0032b2_randomStates_nodup _ _)]
    symm
    apply Finset.sum_nbij' glp0032b2_reflect_reverse
      glp0032b2_reflect_reverse
    · intro q hq
      exact List.mem_toFinset.mpr (glp0032b2_reflect_reverse_state _ _ _
        (List.mem_toFinset.mp hq))
    · intro q hq
      have h := glp0032b2_reflect_reverse_state _ _ _ (List.mem_toFinset.mp hq)
      simpa only [glp0032b2_reflect_reverse_reverse, List.mem_toFinset] using h
    · intro q hq
      exact glp0032b2_reflect_reverse_reverse q
    · intro q hq
      exact glp0032b2_reflect_reverse_reverse q
    · intro q hq
      have hq' := List.mem_toFinset.mp hq
      obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v (o.a+o.b) q hq'
      have hobs : v.total = (observed v q).total := by
        dsimp [observed, Counts.total]
        omega
      have hmq : (observed v q).a+(observed v q).b = o.a+o.b := by
        dsimp [observed]
        change q.a+q.b+(q.c+q.d) = o.a+o.b
        dsimp [Counts.total] at ht
        omega
      rw [glp0032b2_reflect_reverse_observed v q ha hb hc hd,
        glp0032b2_reflect_reverse_multiplicity]
      have hdev := glp0032b2_reflect_complement_deviation v (observed v q) hobs
      rw [hmq] at hdev
      rw [hdev, glp0032b2_reflect_complement_deviation v o hn,
        Int.natAbs_neg, Int.natAbs_neg]
  unfold pValue
  rw [htail, glp0032b2_reflect_reverse_total, hm]

lemma glp0032b2_reflect_accepted_spec (α : ℝ) (o : Counts) (t : ℝ) :
    t ∈ accepted α o ↔ ∃ v, Possible o v ∧ α ≤ (pValue v o : ℝ) ∧ tau v = t := by
  simp only [accepted, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq, Possible, exists_prop, and_assoc]

/-- Acceptance is transported through the possibility bijection. Every
p-value call gets its total equality from the actual possible-table witness. -/
lemma glp0032b2_reflect_complement_accepted (α : ℝ) (o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) :
    accepted α (complementObserved o) = (accepted α o).image (fun t => -t) := by
  have hoC : 0 < (complementObserved o).a+(complementObserved o).b ∧
      0 < (complementObserved o).c+(complementObserved o).d := by
    dsimp [complementObserved]
    constructor <;> omega
  ext t
  constructor
  · intro ht
    obtain ⟨v,hv,hp,rfl⟩ := (glp0032b2_reflect_accepted_spec _ _ _).mp ht
    have hn : v.total = (complementObserved o).total := (possible_table_facts _ _ hv).1
    have hvC := glp0032b2_reflect_possible_forward _ _ hv
    rw [glp0032b2_reflect_complement_complement] at hvC
    have hpC := glp0032b2_reflect_complement_pValue v (complementObserved o) hoC hn
    rw [glp0032b2_reflect_complement_complement] at hpC
    have hacc : tau (glp0032b2_reflect_reverse v) ∈ accepted α o := by
      apply accepted_of_possible _ _ _ hvC
      change α ≤ ((pValue (⟨v.d,v.c,v.b,v.a⟩ : Counts) o : ℚ) : ℝ)
      rw [hpC]
      exact hp
    apply Finset.mem_image.mpr
    exact ⟨_,hacc,by rw [glp0032b2_reflect_reverse_tau, neg_neg]⟩
  · intro ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v,hv,hp,rfl⟩ := (glp0032b2_reflect_accepted_spec _ _ _).mp hs
    have hn : v.total = o.total := (possible_table_facts _ _ hv).1
    rw [← glp0032b2_reflect_reverse_tau]
    apply accepted_of_possible _ _ _ (glp0032b2_reflect_possible_forward _ _ hv)
    change α ≤ ((pValue (⟨v.d,v.c,v.b,v.a⟩ : Counts) (complementObserved o) : ℚ) : ℝ)
    rw [glp0032b2_reflect_complement_pValue v o ho hn]
    exact hp

lemma glp0032b2_reflect_complement_upper (α : ℝ) (o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hne : (accepted α o).Nonempty) :
    upper α (complementObserved o) = -lower α o := by
  change sSup (↑(accepted α (complementObserved o)) : Set ℝ) = _
  apply IsGreatest.csSup_eq
  constructor
  · rw [glp0032b2_reflect_complement_accepted α o ho]
    exact Finset.mem_image.mpr ⟨lower α o, hne.csInf_mem, rfl⟩
  · intro t ht
    rw [glp0032b2_reflect_complement_accepted α o ho] at ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    apply neg_le_neg
    exact csInf_le (accepted α o).finite_toSet.bddBelow hs


lemma glp0032b2_bit_lower (v o : Counts) (i j : Fin 4)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hn : v.total = o.total)
    (hp : 0 < glp0032b2_bit_coord v j)
    (hpair : (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) ∨
      (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3))
    (he : 2*((o.a : ℤ)-o.c) < v.effect) :
    (glp0032b2_bit_add (glp0032b2_bit_sub v j) i).effect = v.effect-1 ∧
    pValue v o ≤ pValue (glp0032b2_bit_add (glp0032b2_bit_sub v j) i) o := by
  let u := glp0032b2_bit_sub v j
  have hv : glp0032b2_bit_add u j = v := glp0032b2_bit_add_sub v j hp
  have hut : u.total+1 = 2*(o.a+o.b) := by
    have h := glp0032b2_bit_sub_total v j hp
    dsimp [u, Counts.total] at *
    omega
  have hd : (glp0032b2_bit_add u i).effect = (glp0032b2_bit_add u j).effect-1 := by
    rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [glp0032b2_bit_add, Counts.effect] <;> ring
  rw [hv] at hd
  refine ⟨hd, ?_⟩
  have ht : glp0032b2_bit_threshold (glp0032b2_bit_add u i) o =
      glp0032b2_bit_threshold (glp0032b2_bit_add u j) o+1 := by
    rw [hv]
    dsimp [glp0032b2_bit_threshold]
    rw [hd]
    ring
  have hneg : glp0032b2_bit_threshold (glp0032b2_bit_add u i) o ≤ 0 := by
    dsimp [glp0032b2_bit_threshold]
    rw [hd]
    omega
  have hs : ∀ q, glp0032b2_bit_score (glp0032b2_bit_add u i) q =
      glp0032b2_bit_score (glp0032b2_bit_add u j) q+1 ∨
      glp0032b2_bit_score (glp0032b2_bit_add u i) q =
      glp0032b2_bit_score (glp0032b2_bit_add u j) q-1 := by
    rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      intro q <;> simp [glp0032b2_bit_add, glp0032b2_bit_score] <;> omega
  have hs' : ∀ q, glp0032b2_bit_score (glp0032b2_bit_add u i) (glp0032b2_bit_add q i) =
      glp0032b2_bit_score (glp0032b2_bit_add u j) (glp0032b2_bit_add q j)+1 ∨
      glp0032b2_bit_score (glp0032b2_bit_add u i) (glp0032b2_bit_add q i) =
      glp0032b2_bit_score (glp0032b2_bit_add u j) (glp0032b2_bit_add q j)-1 := by
    rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      intro q <;> simp [glp0032b2_bit_add, glp0032b2_bit_score] <;> omega
  simpa only [hv] using glp0032b2_bit_pvalue_step u o o i j (o.a+o.b)
    ho.1 hut rfl rfl ht hneg hs hs'

lemma glp0032b2_possible_down (o v : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hv : Possible o v)
    (he : 2*((o.a : ℤ)-o.c) < v.effect) :
    ∃ w, Possible o w ∧ w.effect = v.effect-1 ∧ pValue v o ≤ pValue w o := by
  have hn := (possible_table_facts o v hv).1
  simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range] at hv
  obtain ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩ := hv
  let v : Counts := ⟨i+k,o.a-i+l,o.c-k+j,o.b+o.d-j-l⟩
  have hstep (i' j' k' l' : ℕ) (a b : Fin 4)
      (hi' : i' ≤ o.a) (hj' : j' ≤ o.b) (hk' : k' ≤ o.c) (hl' : l' ≤ o.d)
      (hp : 0 < glp0032b2_bit_coord v b)
      (hpairs : (a = 2 ∧ b = 0) ∨ (a = 3 ∧ b = 1) ∨
        (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3))
      (hw : (⟨i'+k',o.a-i'+l',o.c-k'+j',o.b+o.d-j'-l'⟩ : Counts) =
        glp0032b2_bit_add (glp0032b2_bit_sub v b) a) :
      ∃ w, Possible o w ∧ w.effect = v.effect-1 ∧ pValue v o ≤ pValue w o := by
    refine ⟨(⟨i'+k',o.a-i'+l',o.c-k'+j',o.b+o.d-j'-l'⟩ : Counts), ?_, ?_⟩
    · simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨i',by omega,j',by omega,k',by omega,l',by omega,rfl⟩
    · rw [hw]
      exact glp0032b2_bit_lower v o a b ho hn hp hpairs he
  change ∃ w, Possible o w ∧ w.effect = v.effect-1 ∧ pValue v o ≤ pValue w o
  by_cases hk0 : 0 < k
  · apply hstep i j (k-1) l 2 0 (by omega) (by omega) (by omega) (by omega)
      (by simp [glp0032b2_bit_coord,v]; omega) (Or.inl ⟨rfl,rfl⟩)
    ext <;> simp [v, glp0032b2_bit_add, glp0032b2_bit_sub] <;> omega
  by_cases hl0 : 0 < l
  · apply hstep i j k (l-1) 3 1 (by omega) (by omega) (by omega) (by omega)
      (by simp [glp0032b2_bit_coord,v]; omega) (Or.inr (Or.inl ⟨rfl,rfl⟩))
    ext <;> simp [v, glp0032b2_bit_add, glp0032b2_bit_sub] <;> omega
  by_cases hi0 : i < o.a
  · apply hstep (i+1) j k l 0 1 (by omega) (by omega) (by omega) (by omega)
      (by simp [glp0032b2_bit_coord,v]; omega) (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩)))
    ext <;> simp [v, glp0032b2_bit_add, glp0032b2_bit_sub] <;> omega
  have hj0 : j < o.b := by
    dsimp [Counts.effect] at he
    omega
  apply hstep i (j+1) k l 2 3 (by omega) (by omega) (by omega) (by omega)
    (by simp [glp0032b2_bit_coord,v]; omega) (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩)))
  ext <;> simp [v, glp0032b2_bit_add, glp0032b2_bit_sub] <;> omega

noncomputable def glp0032b2_effects (α : ℝ) (o : Counts) : Finset ℤ :=
  ((possibleTables o).filter fun v => α ≤ (pValue v o : ℝ)).toFinset.image Counts.effect

lemma glp0032b2_effects_spec (α : ℝ) (o : Counts) (x : ℤ) :
    x ∈ glp0032b2_effects α o ↔
      ∃ v, Possible o v ∧ v.effect = x ∧ α ≤ (pValue v o : ℝ) := by
  simp only [glp0032b2_effects, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq, Possible]
  aesop

lemma glp0032b2_effects_down (α : ℝ) (o : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (x y : ℤ)
    (hx : x ∈ glp0032b2_effects α o) (hy : 2*((o.a : ℤ)-o.c) ≤ y) (hyx : y ≤ x) :
    y ∈ glp0032b2_effects α o := by
  have hsteps : ∀ k : ℕ, 2*((o.a : ℤ)-o.c) ≤ x-k →
      x-(k : ℤ) ∈ glp0032b2_effects α o := by
    intro k
    induction k with
    | zero => simpa using (fun _ => hx)
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      obtain ⟨v,hv,he,hp⟩ := (glp0032b2_effects_spec _ _ _).mp hi
      obtain ⟨w,hw,hwx,hle⟩ := glp0032b2_possible_down o v ho hv (by omega)
      apply (glp0032b2_effects_spec _ _ _).mpr
      refine ⟨w,hw,by omega,hp.trans ?_⟩
      exact_mod_cast hle
  have h := hsteps (x-y).toNat (by omega)
  simpa only [show x-((x-y).toNat : ℤ) = y by omega] using h


lemma glp0032b2_center (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : α ≤ 1) :
    2*((o.a : ℤ)-o.c) ∈ glp0032b2_effects α o := by
  let v : Counts := ⟨0,o.a+o.d,o.c+o.b,0⟩
  have hv : Possible o v := by
    simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range]
    refine ⟨0,by omega,o.b,by omega,0,by omega,o.d,by omega,?_⟩
    ext <;> dsimp [v] <;> omega
  have hn : v.total = 2*(o.a+o.b) := by dsimp [v, Counts.total]; omega
  have he : v.effect = 2*((o.a : ℤ)-o.c) := by dsimp [v, Counts.effect]; omega
  have hd : deviationNumerator v o (o.a+o.b) = 0 := by
    rw [glp0032b2_bit_dev_obs v o (o.a+o.b) hn]
    simp [glp0032b2_bit_threshold, he]
  have htail : tailCount v o = v.total.choose (o.a+o.b) := by
    simp only [tailCount,hd,Int.natAbs_zero,Nat.zero_le,ite_true]
    exact design_weight_total v (o.a+o.b) (by omega)
  have hp : pValue v o = 1 := by
    rw [pValue,htail,binomial_eq_choose]
    apply div_self
    exact_mod_cast (Nat.choose_pos (show o.a+o.b ≤ v.total by omega)).ne'
  apply (glp0032b2_effects_spec _ _ _).mpr
  refine ⟨v,hv,he,?_⟩
  simpa only [hp, Rat.cast_one] using hα

lemma glp0032b2_tau (v : Counts) : tau v = (v.effect : ℝ)/v.total := by
  simp [tau, tauQ]

lemma glp0032b2_prefix (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : α ≤ 1) :
    ∃ r : ℤ, 2*((o.a : ℤ)-o.c) ≤ r ∧
      r ≤ (o.a : ℤ)-o.c+(o.a+o.b) ∧ upper α o = (r : ℝ)/o.total ∧
      ∀ x : ℤ, 2*((o.a : ℤ)-o.c) ≤ x →
        (x ∈ glp0032b2_effects α o ↔ x ≤ r) := by
  have hc := glp0032b2_center o α ho hα
  let es := glp0032b2_effects α o
  have hne : es.Nonempty := ⟨_,hc⟩
  let r := es.max' hne
  have hr : r ∈ es := Finset.max'_mem es hne
  have hmax (x : ℤ) (hx : x ∈ es) : x ≤ r := Finset.le_max' es x hx
  obtain ⟨v,hv,hve,hvp⟩ := (glp0032b2_effects_spec _ _ _).mp hr
  have hbounds := (possible_table_facts o v hv).2
  simp only [candidateNumerators, List.mem_map, List.mem_range] at hbounds
  obtain ⟨k,hk,he⟩ := hbounds
  have hrhi : r ≤ (o.a : ℤ)-o.c+(o.a+o.b) := by
    dsimp [Counts.total] at hk
    omega
  refine ⟨r,hmax _ hc,hrhi,?_,?_⟩
  · apply IsGreatest.csSup_eq
    constructor
    · have ht : tau v = (r : ℝ)/o.total := by
        rw [glp0032b2_tau, (possible_table_facts o v hv).1, hve]
      rw [← ht]
      exact accepted_of_possible α o v hv hvp
    · intro t ht
      obtain ⟨u,hu,hup,hut⟩ := (glp0032b2_reflect_accepted_spec _ _ _).mp ht
      have hue : u.effect ∈ es := (glp0032b2_effects_spec _ _ _).mpr ⟨u,hu,rfl,hup⟩
      rw [← hut, glp0032b2_tau, (possible_table_facts o u hu).1]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmax _ hue) (Nat.cast_nonneg _)
  · intro x hx
    constructor
    · exact hmax x
    · intro hxr
      exact glp0032b2_effects_down α o ho r x hr hx hxr

lemma glp0032b2_exact_value (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : α ≤ 1) :
    ∃ r : ℤ, (exactUpperRun α o).value = some r ∧ upper α o = (r : ℝ)/o.total := by
  obtain ⟨r,hrlo,hrhi,hupper,hprefix⟩ := glp0032b2_prefix o α ho hα
  refine ⟨r,?_,hupper⟩
  let k₁ : ℤ := 2*((o.a : ℤ)-o.c)
  let k₂ : ℤ := (o.a : ℤ)-o.c+(o.a+o.b)
  change (adaptiveSearch (o.total+3) true o k₁ k₂
    (fun v _ => decide ((pValue v o : ℝ) < α)) (k₁-1) (k₂+1) 0).value = some r
  apply glp0032b2_search_threshold
  · dsimp [k₁]; omega
  · dsimp [k₂]; omega
  · dsimp [k₁,k₂,Counts.total]
    omega
  · intro c hac hcb i
    rw [glp0032b2_runTests_exact,
      glp0032b2_candidate_reduction o c α (fun w hw hmin hmax => glp0032b2_merge o w ho hw hmin hmax)]
    rw [← glp0032b2_effects_spec]
    exact hprefix c (by dsimp [k₁] at hac; omega)

theorem fast_exact_interval_proof (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hn : 15 ≤ o.total)
    (hα : 0 < α ∧ α < 1) :
    (exactUpperRun α o).value.map (fun x => (x : ℝ)/o.total) = some (upper α o) ∧
    (exactUpperRun α (complementObserved o)).value.map
      (fun x => -(x : ℝ)/o.total) = some (lower α o) ∧
    (((exactUpperRun α o).trace.length +
      (exactUpperRun α (complementObserved o)).trace.length : ℕ) : ℝ) ≤
        4*(o.total : ℝ)*logTwo o.total := by
  have hoC : 0 < (complementObserved o).a+(complementObserved o).b ∧
      (complementObserved o).a+(complementObserved o).b =
        (complementObserved o).c+(complementObserved o).d := by
    dsimp [complementObserved]
    omega
  have htC := glp0032b2_reflect_complement_total o
  obtain ⟨r,hr,hupper⟩ := glp0032b2_exact_value o α ho hα.2.le
  obtain ⟨s,hs,hupperC⟩ := glp0032b2_exact_value (complementObserved o) α hoC hα.2.le
  refine ⟨?_,?_,?_⟩
  · rw [hr]
    change some ((r : ℝ)/o.total) = some (upper α o)
    rw [hupper]
  · rw [hs]
    change some (-(s : ℝ)/o.total) = some (lower α o)
    apply congrArg some
    have href := glp0032b2_reflect_complement_upper α o ⟨ho.1,by omega⟩
      ⟨estimate o,(balanced_estimate_in_interval o α ho hα).1⟩
    rw [htC] at hupperC
    rw [hupperC] at href
    rw [neg_div]
    linarith
  · have hb := (glp0032b2_upperRun_budget o
      (fun v _ => decide ((pValue v o : ℝ) < α)) 0 ho).2
    have hbC := (glp0032b2_upperRun_budget (complementObserved o)
      (fun v _ => decide ((pValue v (complementObserved o) : ℝ) < α)) 0 hoC).2
    rw [htC] at hbC
    change (exactUpperRun α o).trace.length ≤ _ at hb
    change (exactUpperRun α (complementObserved o)).trace.length ≤ _ at hbC
    have hbR : (((exactUpperRun α o).trace.length +
        (exactUpperRun α (complementObserved o)).trace.length : ℕ) : ℝ) ≤
        2*(((o.total+1)*(Nat.log2 (o.total+1)+2) : ℕ) : ℝ) := by
      exact_mod_cast (show (exactUpperRun α o).trace.length +
        (exactUpperRun α (complementObserved o)).trace.length ≤
        2*((o.total+1)*(Nat.log2 (o.total+1)+2)) by omega)
    exact hbR.trans (glp0032b2_log_cost o.total (by dsimp [Counts.total] at *; omega))

end AronowAudit.P003.Wave1
