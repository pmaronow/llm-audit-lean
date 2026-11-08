import SAP.P003b.WH.W1.Existing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1
open SAP.P003b SAP.P003b.Bridge
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

lemma queryCosts : W1QueryCosts := by
  intro o x reject idx
  have h := (AronowAudit.P003.Wave1.glp0032b2_runTests_cost
    (fun v i => reject (fromCounts v) i)
    (AronowAudit.P003.candidates (toCounts o) x) idx).2
  have hc := AronowAudit.P003.Wave1.glp0032b2_candidates_length (toCounts o) x
  simp only [candidates_eq,runTests_eq,from_to,toQuery,List.length_map,total_eq] at h hc
  exact h.trans hc

lemma budgetFloor : W1BudgetFloor := by
  intro n
  have hp : 0 ≤ Real.logb (2 : ℝ) ((n+1 : ℕ) : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n+1 by omega))
  have hf := Real.natFloor_logb_natCast 2 (n+1)
  have he : ⌊logTwo ((n : ℝ)+1)⌋ = (Nat.log2 (n+1) : ℤ) := by
    rw [← Nat.log2_eq_log_two] at hf
    have hh := congrArg (fun k : ℕ => (k : ℤ)) hf
    norm_num only [Nat.cast_ofNat] at hh
    rw [Int.natCast_floor_eq_floor hp] at hh
    simpa only [Real.logb,logTwo,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hh
  rw [show logTwo ((n : ℝ)+1)+3 = logTwo ((n : ℝ)+1)+(3 : ℤ) by norm_num,
    Int.floor_add_intCast, he]
  simp only [testBudget,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]

lemma oracle_exists (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (x : ℤ) (idx : ℕ) :
    (runTests (fun v _ => decide ((pValue v o : ℝ) < α)) idx (candidates o x)).compatible = true ↔
      ∃ v, Possible o v ∧ v.effect = x ∧ α ≤ (pValue v o : ℝ) := by
  have h := AronowAudit.P003.Wave1.glp0032b2_runTests_exact α (toCounts o)
    (AronowAudit.P003.candidates (toCounts o) x) idx
  rw [AronowAudit.P003.Wave1.glp0032b2_candidate_reduction (toCounts o) x α
    (fun w hw hmin hmax => AronowAudit.P003.Wave1.glp0032b2_merge
      (toCounts o) w ho hw hmin hmax)] at h
  simp only [candidates_eq,runTests_eq,pValue_eq,toQuery] at h
  rw [h]
  constructor
  · rintro ⟨v,hv,he,hp⟩
    exact ⟨fromCounts v, (possible_any _ _).mp hv, he, by simpa only [pValue_any,from_to] using hp⟩
  · rintro ⟨v,hv,he,hp⟩
    exact ⟨toCounts v,(possible_eq _ _).mpr hv,he,by simpa only [pValue_eq] using hp⟩

lemma upper_value (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : α ≤ 1) :
    ∃ r : ℤ, (exactUpperRun α o).value = some r ∧ upper α o = (r : ℝ)/o.total := by
  simpa only [exactUpperRun_eq,toEndpoint,upper_eq,total_eq] using
    AronowAudit.P003.Wave1.glp0032b2_exact_value (toCounts o) α ho hα

lemma reflect_upper (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1) :
    upper α (complementObserved o) = -lower α o := by
  have hc := (T30_base o α ho hα).1
  have hne : (AronowAudit.P003.accepted α (toCounts o)).Nonempty := by
    simpa only [accepted_eq] using (show (accepted α o).Nonempty from ⟨estimate o,hc⟩)
  simpa only [complement_eq,upper_eq,lower_eq] using
    AronowAudit.P003.Wave1.glp0032b2_reflect_complement_upper α (toCounts o)
      ⟨ho.1,by change 0 < o.c+o.d; omega⟩ hne

lemma allStartBudget (o : Counts) (r : Counts → ℕ → Bool) (idx : ℕ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) :
    (upperRun true o r idx).value.isSome ∧
    (upperRun true o r idx).trace.length ≤ testBudget o.total := by
  have h := AronowAudit.P003.Wave1.glp0032b2_upperRun_budget (toCounts o)
    (fun v i => r (fromCounts v) i) idx ho
  simp only [upperRun_eq,from_to,toEndpoint,List.length_map,total_eq] at h
  refine ⟨h.1,h.2.trans ?_⟩
  unfold testBudget
  exact Nat.mul_le_mul_left _ (by omega)

lemma t32Oracle : W1T32Oracle := by
  intro o α ho hα
  refine ⟨oracle_exists o α ho,?_,?_,?_,?_,?_⟩
  · obtain ⟨r,hrlo,hrhi,hu,hp⟩ :=
      AronowAudit.P003.Wave1.glp0032b2_prefix (toCounts o) α ho hα.2.le
    refine ⟨r,hrlo,hrhi,by simpa only [upper_eq,total_eq] using hu,?_⟩
    intro x hx
    rw [← hp x hx, AronowAudit.P003.Wave1.glp0032b2_effects_spec]
    constructor
    · rintro ⟨v,hv,he,hvp⟩
      exact ⟨toCounts v,(possible_eq _ _).mpr hv,he,by simpa only [pValue_eq] using hvp⟩
    · rintro ⟨v,hv,he,hvp⟩
      exact ⟨fromCounts v,(possible_any _ _).mp hv,he,by simpa only [pValue_any,from_to] using hvp⟩
  · obtain ⟨r,hr,hu⟩ := upper_value o α ho hα.2.le
    simp only [hr,Option.map_some,hu]
  · have hoC : 0 < (complementObserved o).a+(complementObserved o).b ∧
        (complementObserved o).a+(complementObserved o).b =
          (complementObserved o).c+(complementObserved o).d := by
      simp only [complementObserved]; omega
    obtain ⟨r,hr,hu⟩ := upper_value (complementObserved o) α hoC hα.2.le
    have ht : (complementObserved o).total = o.total := by simp [complementObserved,Counts.total]; omega
    simp only [hr,Option.map_some]
    congr 1
    have hh := reflect_upper o α ho hα
    rw [hu,ht] at hh
    rw [neg_div]
    linarith
  · exact (allStartBudget o _ 0 ho).2
  · have hoC : 0 < (complementObserved o).a+(complementObserved o).b ∧
        (complementObserved o).a+(complementObserved o).b =
          (complementObserved o).c+(complementObserved o).d := by
      simp only [complementObserved]; omega
    have h := (allStartBudget (complementObserved o) (fun v _ => decide ((pValue v (complementObserved o) : ℝ) < α)) 0 hoC).2
    simpa only [exactUpperRun,complementObserved,Counts.total,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma t18Finite : W1T18Finite := by
  intro n K t c O hc ht hO
  have h := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  refine ⟨by nlinarith [h],?_,by ring⟩
  calc
    O ≤ (t : ℝ)*K*(c*n) := hO
    _ ≤ (4*(n : ℝ)*logTwo n)*K*(c*n) :=
      mul_le_mul_of_nonneg_right h (mul_nonneg hc (Nat.cast_nonneg n))
    _ = _ := by ring

lemma t18General : W1T18General := by
  refine ⟨?_,T36_base.2⟩
  intro o K c₀ c₁ c₂ hc
  have h := AronowAudit.P003.general_finite_counts (toCounts o) K c₀ c₁ c₂ hc
  simp only [drawCount_eq,updateCount_eq,operations_eq,total_eq] at h
  refine ⟨h.1,h.2.1,h.2.2,?_⟩
  intro hn hK
  exact h.2.2.trans (AronowAudit.P003.general_envelope_bound o.total K hn hK c₀ c₁ c₂ hc)

lemma t18Budgets : W1T18Budgets := by
  intro n ε hn hε
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hp : 0 < 4*(n : ℝ)*logTwo n/ε := by
    unfold logTwo
    exact div_pos (mul_pos (mul_pos (by norm_num) (by linarith))
      (div_pos (Real.log_pos hn1) h2)) hε
  have hdom := AronowAudit.P003.squared_log_dominates n hn
  have hh : 4*(n : ℝ)*logTwo n/ε ≤ 4*(n : ℝ)*(Real.log n)^2/ε :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdom (by positivity)) hε.le
  have hlog := Real.log_le_log hp hh
  have hbudget := div_le_div_of_nonneg_right hlog (show 0 ≤ 2*ε^2 by positivity)
  exact ⟨hbudget,Nat.ceil_mono hbudget⟩

lemma t18AllExponents : ∀ q : ℝ, ¬ (fun r : ℕ =>
    let n : ℕ := 2^r
    expectedUpperShuffleCost (1/2) (1/8) n (recommendedK (1/8) n) ⟨0,n/2,0,n/2⟩)
      =O[Filter.atTop] (fun r : ℕ =>
        let n : ℕ := 2^r
        (n : ℝ)*Real.rpow (Real.log n) q) := by
  intro q
  simp only [← expectedShuffleCost_eq, ← recommendedK_eq]
  apply AronowAudit.P003.Wave1.GP0031B1b_balanced_shuffle_not_linear_polylog_of_quadratic
  filter_upwards [Filter.eventually_ge_atTop 6] with r hr
  obtain ⟨hK,hKlog⟩ := AronowAudit.P003.Wave1.GP0031B1b_balanced_shuffle_not_linear_polylog_recommendedK r hr
  apply AronowAudit.P003.Wave1.GP0031B1b_balanced_shuffle_not_linear_polylog_quadratic r _ hr hK
  exact (AronowAudit.P003.Wave1.balanced_shuffle_lower_bounds_proof r _ (by omega) hK).2 hr hKlog

end
end SAP.P003b.WH.W1
