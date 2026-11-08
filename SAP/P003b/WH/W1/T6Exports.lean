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

lemma mapIdentity {A : Type*} (xs : List A) : xs.map (fun x => x) = xs := by
  exact List.map_id xs

lemma packCounts (v : Counts) : (⟨v.a,v.b,v.c,v.d⟩ : Counts) = v := by
  cases v
  rfl

lemma packEndpoint (v : EndpointResult) : (⟨v.value,v.trace⟩ : EndpointResult) = v := by
  cases v
  rfl

lemma t6Candidates : W1T6Candidates := by
  unfold W1T6Candidates
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have h := congrArg (List.map fromCounts) AronowAudit.P003.Wave1.atr_candidates_9
    simpa only [adaptiveData_eq,candidates_eq,List.map_map,Function.comp_def,
      from_to,List.map_id,fromCounts,List.map_cons,List.map_nil,packCounts,mapIdentity] using h
  · have h := congrArg (List.map fromCounts) AronowAudit.P003.Wave1.atr_candidates_10
    simpa only [adaptiveData_eq,candidates_eq,List.map_map,Function.comp_def,
      from_to,List.map_id,fromCounts,List.map_cons,List.map_nil,packCounts,mapIdentity] using h
  · have h := congrArg (List.map fromCounts) AronowAudit.P003.Wave1.atr_candidates_11
    simpa only [adaptiveData_eq,candidates_eq,List.map_map,Function.comp_def,
      from_to,List.map_id,fromCounts,List.map_cons,List.map_nil,packCounts,mapIdentity] using h
  · have h := congrArg (List.map fromCounts) AronowAudit.P003.Wave1.atr_candidates_12
    simpa only [adaptiveData_eq,candidates_eq,List.map_map,Function.comp_def,
      from_to,List.map_id,fromCounts,List.map_cons,List.map_nil,packCounts,mapIdentity] using h
  · have h := congrArg (List.map fromCounts) AronowAudit.P003.Wave1.atr_candidates_14
    simpa only [adaptiveData_eq,candidates_eq,List.map_map,Function.comp_def,
      from_to,List.map_id,fromCounts,List.map_cons,List.map_nil,packCounts,mapIdentity] using h
  · have h := congrArg (List.map fromCounts) AronowAudit.P003.Wave1.atr_candidates_15
    simpa only [adaptiveData_eq,candidates_eq,List.map_map,Function.comp_def,
      from_to,List.map_id,fromCounts,List.map_cons,List.map_nil,packCounts,mapIdentity] using h
  · have h := congrArg (List.map fromCounts) AronowAudit.P003.Wave1.atr_candidates_16
    simpa only [adaptiveData_eq,candidates_eq,List.map_map,Function.comp_def,
      from_to,List.map_id,fromCounts,List.map_cons,List.map_nil,packCounts,mapIdentity] using h

lemma t6PValues : W1T6PValues := by
  unfold W1T6PValues
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_00
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_01
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_02
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_03
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_04
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_05
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_06
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_07
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_08
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_09
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_10
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_11
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_12
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_13
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_14
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_15
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_16
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_17
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_18
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_19
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_20
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_21
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_22
  · simpa only [pValue_any,AronowAudit.P003.adaptiveData,fromCounts,adaptiveData] using
      AronowAudit.P003.Wave1.atr_p_23

def backEndpoint (r : AronowAudit.P003.EndpointResult) : EndpointResult :=
  ⟨r.value,r.trace.map (fun t => (fromCounts t.1,t.2))⟩

lemma t6Traces : W1T6Traces := by
  unfold W1T6Traces
  refine ⟨?_,?_,?_,?_,?_,by decide,by decide,by decide⟩
  · have h := congrArg backEndpoint AronowAudit.P003.Wave1.atr_run_exact
    simpa only [adaptiveData_eq,upperRun_eq,exactRejectQ_fn,from_to,backEndpoint,toEndpoint,
      List.map_map,Function.comp_def,fromCounts,AronowAudit.P003.Wave1.atr_trace_exact,
      w1Trace_exact,List.map_cons,List.map_nil,List.map_id,toTrace,toCounts,packCounts,Prod.eta,packEndpoint,mapIdentity] using h
  · have h := congrArg backEndpoint AronowAudit.P003.Wave1.atr_run_low
    simpa only [adaptiveData_eq,upperRun_eq,exactRejectQ_fn,from_to,backEndpoint,toEndpoint,
      List.map_map,Function.comp_def,fromCounts,AronowAudit.P003.Wave1.atr_trace_low,
      w1Trace_low,List.map_cons,List.map_nil,List.map_id,toTrace,toCounts,packCounts,Prod.eta,packEndpoint,mapIdentity] using h
  · have h := congrArg backEndpoint AronowAudit.P003.Wave1.atr_run_A
    simpa only [adaptiveData_eq,upperRun_eq,exactRejectQ_fn,from_to,backEndpoint,toEndpoint,
      List.map_map,Function.comp_def,fromCounts,AronowAudit.P003.Wave1.atr_trace_A,
      w1Trace_A,List.map_cons,List.map_nil,List.map_id,toTrace,toCounts,packCounts,Prod.eta,packEndpoint,mapIdentity] using h
  · have h := congrArg backEndpoint AronowAudit.P003.Wave1.atr_run_B
    simpa only [adaptiveData_eq,upperRun_eq,exactRejectQ_fn,from_to,backEndpoint,toEndpoint,
      List.map_map,Function.comp_def,fromCounts,AronowAudit.P003.Wave1.atr_trace_B,
      w1Trace_B,List.map_cons,List.map_nil,List.map_id,toTrace,toCounts,packCounts,Prod.eta,packEndpoint,mapIdentity] using h
  · have h := congrArg backEndpoint AronowAudit.P003.Wave1.atr_run_D
    simpa only [adaptiveData_eq,upperRun_eq,exactRejectQ_fn,from_to,backEndpoint,toEndpoint,
      List.map_map,Function.comp_def,fromCounts,AronowAudit.P003.Wave1.atr_trace_D,
      w1Trace_D,List.map_cons,List.map_nil,List.map_id,toTrace,toCounts,packCounts,Prod.eta,packEndpoint,mapIdentity] using h

lemma t6Range : candidateNumerators adaptiveData =
    (List.range 31).map (fun k : ℕ => (k : ℤ)-14) := by
  decide +kernel


lemma prob_nonneg {A : Type*} [Fintype A] (E : A → Prop) : 0 ≤ uniformProb E := by
  unfold uniformProb
  positivity

lemma t6Aggregate : W1T6Aggregate := by
  have h := T6_base.2.2.2
  have ht := t6Traces.1
  dsimp only [W1T6Aggregate]
  rw [ht]
  let bad := fun (i : ℕ) (pool : W1Pool 30 15 5000) =>
    let b := upperRun false adaptiveData (approximateReject (1/20) (1/50) adaptiveData pool)
    i < b.trace.length ∧ b.trace[i]!.2 = true ∧ w1Trace_exact[i]!.2 = false
  change _ ≤ ∑ i ∈ Finset.range 16, uniformProb (bad i) ∧
    (16 : ℝ)*Real.exp (-2*(5000 : ℝ)*(1/50)^2) = 16*Real.exp (-4) ∧
    (16 : ℝ)*Real.exp (-2*(5000 : ℝ)*(1/50)^2) <
      ∑ i ∈ Finset.range 16, uniformProb (bad i)
  have hterm : (4693104776190294207 : ℝ)/5012394999999664375 ≤ uniformProb (bad 1) := by
    refine h.1.trans (le_of_eq ?_)
    apply congrArg (@uniformProb (W1Pool 30 15 5000) _)
    funext pool
    apply propext
    simp only [bad,w1Trace_exact,List.getElem!_cons_succ,List.getElem!_cons_zero,and_true]
    constructor
    · rintro ⟨hl,hb⟩
      exact ⟨by omega,hb⟩
    · rintro ⟨hl,hb⟩
      exact ⟨by omega,hb⟩
  have hsum : uniformProb (bad 1) ≤ ∑ i ∈ Finset.range 16, uniformProb (bad i) :=
    Finset.single_le_sum (fun i _ => prob_nonneg (bad i)) (by decide)
  have he : (-2*(5000 : ℝ)*(1/50)^2) = -4 := by norm_num
  refine ⟨hterm.trans hsum,?_,?_⟩
  · norm_num only [Nat.cast_ofNat,he]
  · rw [he]
    norm_num only [Nat.cast_ofNat]
    linarith [h.2.1,h.2.2.1,h.2.2.2]

end
end SAP.P003b.WH.W1
