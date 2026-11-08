import SAP.P003b.WH.W1.Exports

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1
open SAP.P003b SAP.P003b.Bridge
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

lemma noRejection (o : Counts) (α : ℝ) (r : Counts → ℕ → Bool) (idx : ℕ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1)
    (hg : ∀ v, (v,true) ∈ (upperRun true o r idx).trace → (pValue v o : ℝ) < α) :
    ∃ x, (upperRun true o r idx).value = some x ∧ upper α o ≤ (x : ℝ)/o.total := by
  have hh : ∀ v, (v,true) ∈ (AronowAudit.P003.upperRun true (toCounts o)
      (fun v i => r (fromCounts v) i) idx).trace → (AronowAudit.P003.pValue v (toCounts o) : ℝ) < α := by
    intro v hv
    simp only [upperRun_eq,from_to,toEndpoint] at hv
    obtain ⟨⟨w,b⟩,hw,he⟩ := List.mem_map.mp hv
    change (toCounts w,b) = (v,true) at he
    obtain ⟨he,hb⟩ := Prod.mk.inj he
    rw [← he,pValue_eq]
    exact hg w (by simpa only [hb] using hw)
  simpa only [upperRun_eq,from_to,toEndpoint,upper_eq,total_eq] using
    AronowAudit.P003.Wave1.GLP0032B6_upper_no_rejection (toCounts o) α
      (fun v i => r (fromCounts v) i) idx ho hα hh

lemma noAcceptance (o : Counts) (α : ℝ) (r : Counts → ℕ → Bool) (idx : ℕ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1)
    (hg : ∀ v, (v,false) ∈ (upperRun true o r idx).trace → α ≤ (pValue v o : ℝ)) :
    ∃ x, (upperRun true o r idx).value = some x ∧ (x : ℝ)/o.total ≤ upper α o := by
  have hh : ∀ v, (v,false) ∈ (AronowAudit.P003.upperRun true (toCounts o)
      (fun v i => r (fromCounts v) i) idx).trace → α ≤ (AronowAudit.P003.pValue v (toCounts o) : ℝ) := by
    intro v hv
    simp only [upperRun_eq,from_to,toEndpoint] at hv
    obtain ⟨⟨w,b⟩,hw,he⟩ := List.mem_map.mp hv
    change (toCounts w,b) = (v,false) at he
    obtain ⟨he,hb⟩ := Prod.mk.inj he
    rw [← he,pValue_eq]
    exact hg w (by simpa only [hb] using hw)
  simpa only [upperRun_eq,from_to,toEndpoint,upper_eq,total_eq] using
    AronowAudit.P003.Wave1.GLP0032B6_upper_no_acceptance (toCounts o) α
      (fun v i => r (fromCounts v) i) idx ho hα hh

lemma t7Comparisons : W1T7Comparisons := by
  intro o α r idx ho hα
  have hoC : 0 < (complementObserved o).a+(complementObserved o).b ∧
      (complementObserved o).a+(complementObserved o).b =
        (complementObserved o).c+(complementObserved o).d := by
    simp only [complementObserved]; omega
  have ht : (complementObserved o).total = o.total := by
    simp only [complementObserved,Counts.total]; omega
  have href := reflect_upper o α ho hα
  refine ⟨noRejection o α r idx ho hα,noAcceptance o α r idx ho hα,?_,?_⟩
  · intro hg
    obtain ⟨x,hx,hb⟩ := noRejection (complementObserved o) α r idx hoC hα hg
    rw [href,ht] at hb
    refine ⟨x,hx,?_⟩
    rw [neg_div]
    linarith
  · intro hg
    obtain ⟨x,hx,hb⟩ := noAcceptance (complementObserved o) α r idx hoC hα hg
    rw [href,ht] at hb
    refine ⟨x,hx,?_⟩
    rw [neg_div]
    linarith

lemma conditionalInclusions : W1T7ConditionalInclusions := by
  intro n m K o α ε ht hm ho hK hα hε
  have hmn : m ≤ n := by dsimp [Counts.total] at ht; omega
  letI : Nonempty (Assignment n m) :=
    AronowAudit.P003.Wave1.GLP0032B6_assignment_nonempty n m hmn
  have hf := AronowAudit.P003.Wave1.GLP0032B6_conditional_failure
    (toCounts o) α ε ht hm ho hmn hK hα hε.1
  simp only [testBudget_eq] at hf
  simp only [uniformProb_eq,interval_eq,monteInterval_eq,monteInterval_nativePool] at hf
  change (uniformProb (fun p : W1Pool n m K => ¬exactInterval α o ⊆ monteInterval true α ε o p)) ≤
      2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) ∧
    (0 < α-2*ε → (uniformProb (fun p : W1Pool n m K =>
      ¬monteInterval true α ε o p ⊆ exactInterval (α-2*ε) o)) ≤
      2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2)) at hf
  constructor
  · have hc := AronowAudit.P003.Wave1.GLP0032B6_prob_compl
      (fun p : W1Pool n m K => exactInterval α o ⊆ monteInterval true α ε o p)
    simp only [uniformProb_eq] at hc
    linarith [hf.1]
  · intro hb
    have hc := AronowAudit.P003.Wave1.GLP0032B6_prob_compl
      (fun p : W1Pool n m K => monteInterval true α ε o p ⊆ exactInterval (α-2*ε) o)
    simp only [uniformProb_eq] at hc
    linarith [hf.2 hb]

lemma observedArms {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) :
    (w1Observed w z).a+(w1Observed w z).b = z.card ∧
    (w1Observed w z).c+(w1Observed w z).d = n-z.card := by
  have htrue (s : Finset (Fin n)) (f : Fin n → Bool) :
      (s.filter (fun i => f i = true)).card+(s.filter (fun i => f i = false)).card = s.card := by
    convert Finset.card_filter_add_card_filter_not (s := s) (fun i => f i = true) using 2
    congr 1
    ext i
    cases h : f i <;> simp [h]
  have ht (f : Fin n → Bool) (b : Bool) :
      (Finset.univ.filter (fun i => i ∈ z ∧ f i = b)).card =
        (z.filter (fun i => f i = b)).card := by
    congr 1
    ext i
    simp
  have hc (f : Fin n → Bool) (b : Bool) :
      (Finset.univ.filter (fun i => i ∉ z ∧ f i = b)).card =
        (zᶜ.filter (fun i => f i = b)).card := by
    congr 1
    ext i
    simp
  constructor
  · simpa only [w1Observed,ht] using htrue z (fun i => (w i).1)
  · simpa only [w1Observed,hc,Finset.card_compl,Fintype.card_fin] using
      htrue zᶜ (fun i => (w i).2)

lemma t7Labeled : W1T7Labeled := by
  intro n m K w α ε hm hn hK hα hε
  letI : Nonempty (Assignment n m) :=
    AronowAudit.P003.Wave1.GLP0032B6_assignment_nonempty n m (by omega)
  have hc (z : Assignment n m) := observedArms w z.val
  have hb (z : Assignment n m) :
      (w1Observed w z.val).total = n ∧
      (w1Observed w z.val).a+(w1Observed w z.val).b = m ∧
      (0 < (w1Observed w z.val).a+(w1Observed w z.val).b ∧
        (w1Observed w z.val).a+(w1Observed w z.val).b =
          (w1Observed w z.val).c+(w1Observed w z.val).d) := by
    have hz := z.property
    have hh := hc z
    refine ⟨?_,by omega,by omega⟩
    dsimp [Counts.total]
    omega
  constructor
  · have hf (z : Assignment n m) :=
      (conditionalInclusions n m K _ α ε (hb z).1 (hb z).2.1 (hb z).2.2 hK hα hε).1
    have hfail (z : Assignment n m) : uniformProb (fun p : W1Pool n m K =>
        ¬exactInterval α (w1Observed w z.val) ⊆ monteInterval true α ε (w1Observed w z.val) p) ≤
          2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) := by
      have hp := AronowAudit.P003.Wave1.GLP0032B6_prob_compl
        (fun p : W1Pool n m K => exactInterval α (w1Observed w z.val) ⊆ monteInterval true α ε (w1Observed w z.val) p)
      simp only [uniformProb_eq] at hp
      linarith [hf z]
    have hh := AronowAudit.P003.Wave1.GLP0032B6_observed_average _ _ hfail
    have hp := AronowAudit.P003.Wave1.GLP0032B6_prob_compl
      (fun ω : Assignment n m × W1Pool n m K =>
        exactInterval α (w1Observed w ω.1.val) ⊆ monteInterval true α ε (w1Observed w ω.1.val) ω.2)
    simp only [uniformProb_eq] at hh hp
    linarith
  · intro hβ
    have hf (z : Assignment n m) :=
      (conditionalInclusions n m K _ α ε (hb z).1 (hb z).2.1 (hb z).2.2 hK hα hε).2 hβ
    have hfail (z : Assignment n m) : uniformProb (fun p : W1Pool n m K =>
        ¬monteInterval true α ε (w1Observed w z.val) p ⊆ exactInterval (α-2*ε) (w1Observed w z.val)) ≤
          2*(testBudget n : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) := by
      have hp := AronowAudit.P003.Wave1.GLP0032B6_prob_compl
        (fun p : W1Pool n m K => monteInterval true α ε (w1Observed w z.val) p ⊆ exactInterval (α-2*ε) (w1Observed w z.val))
      simp only [uniformProb_eq] at hp
      linarith [hf z]
    have hh := AronowAudit.P003.Wave1.GLP0032B6_observed_average _ _ hfail
    have hp := AronowAudit.P003.Wave1.GLP0032B6_prob_compl
      (fun ω : Assignment n m × W1Pool n m K =>
        monteInterval true α ε (w1Observed w ω.1.val) ω.2 ⊆ exactInterval (α-2*ε) (w1Observed w ω.1.val))
    simp only [uniformProb_eq] at hh hp
    linarith

end
end SAP.P003b.WH.W1
