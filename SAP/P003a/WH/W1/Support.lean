import SAP.P003a.Defs.WholeW1
import SAP.P003a.Bridge
import AronowAudit.P003.P003_ConfidenceCompletion
import AronowAudit.P003.Wave1.Gap.GLP0032B6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W1

open SAP.P003a.Bridge
open scoped BigOperators

theorem retained_T21 : T21Statement := by
  simpa [T21Statement, decode_acceptedEffectsQ, decode_intervalQ, decode_estimateQ,
    decode_pValue] using AronowAudit.P003.unbalanced_footnote_corrected

theorem retained_T22 : T22Statement := by
  constructor
  · intro o u hu
    have hu' := (to_possible o u).mpr hu
    obtain ⟨hx,hj,v,hv,k,hk,ha,hd,he⟩ :=
      AronowAudit.P003.corrected_general_loop (toAudit o) (toAudit u) hu'
    refine ⟨by simpa [to_effect,to_candidateNumerators] using hx, hj,
      fromAudit v, ?_, k, hk, ha, hd, ?_⟩
    · have h := congrArg (Option.map fromAudit) hv
      simpa [decode_firstOnLine, from_to, to_effect, to_a, to_b, Option.map_some] using h
    · have h := congrArg fromAudit he
      simpa [from_to, decode_reuseVector] using h
  · obtain ⟨hset,h0,h1⟩ := AronowAudit.P003.omitted_loop_witness
    refine ⟨?_, ?_, ?_⟩
    · have h := congrArg (fun s : Finset A => s.image fromAudit) hset
      simpa [decode_possibleTablesFinset, Finset.image_insert, Finset.image_singleton] using h
    · have h := congrArg (Option.map fromAudit) h0
      simpa [decode_firstOnLine, Option.map_some] using h
    · have h := congrArg (Option.map fromAudit) h1
      simpa [decode_firstOnLine, Option.map_some] using h

theorem retained_T23 : T23Statement := by
  intro k₁ k₂ u f hk
  simpa [sentinelSearch_eq] using
    AronowAudit.P003.rejected_query_cuts_endpoint k₁ k₂ u f hk

theorem retained_T1 : T1Statement := by
  constructor
  · simpa [to_badPopulation, to_total, to_tauQ, decode_intervalQ,
      decode_missingIntervalQ, to_badCoverage, to_randomStates, List.map_map,
      Function.comp_def, to_multiplicity, forall_audit, to_badMask, to_observed,
      to_missingMasks, List.mem_map, to_inj, exists_eq_right, from_to] using
        AronowAudit.P003.missing_counterexample
  · simpa [decode_pValue, decode_Possible, decode_estimateQ, to_badPopulation,
      from_to] using AronowAudit.P003.missing_critical_tail_counterexample

theorem retained_T4 : T4Statement := by
  constructor
  · simpa [printedSearch_eq] using AronowAudit.P003.printed_search_counterexample
  · simpa [decode_estimateQ, decode_Possible, decode_pValue, decode_intervalQ,
      decode_upperRun] using AronowAudit.P003.balanced_search_counterexample

/-- A nonempty finite accepted set has its usual closed interval hull. -/
theorem interval_eq_Icc (α : ℝ) (o : Counts) (hne : (accepted α o).Nonempty) :
    exactInterval α o = Set.Icc (lower α o) (upper α o) := by
  classical
  have hl : lower α o ∈ accepted α o := hne.csInf_mem
  have hu : upper α o ∈ accepted α o := hne.csSup_mem
  ext t
  constructor
  · rintro ⟨l,hl',u,hu',hlt,htu⟩
    exact ⟨(csInf_le (Finset.bddBelow _) hl').trans hlt,
      htu.trans (le_csSup (Finset.bddAbove _) hu')⟩
  · intro ht
    exact ⟨lower α o,hl,upper α o,hu,ht.1,ht.2⟩

/-- Transport the existing exact rational certificate to the real hull and extrema. -/
theorem real_interval_certificate (α : ℚ) (o : Counts) (l u : ℚ)
    (h : intervalQ α o = some (l,u)) :
    (accepted (α : ℝ) o).Nonempty ∧
    lower (α : ℝ) o = (l : ℝ) ∧ upper (α : ℝ) o = (u : ℝ) ∧
    exactInterval (α : ℝ) o = Set.Icc (l : ℝ) (u : ℝ) := by
  have h' : AronowAudit.P003.intervalQ α (toAudit o) = some (l,u) := by simpa using h
  have hc := AronowAudit.P003.ConfidenceFollowup.real_extrema_of_intervalQ α (toAudit o) l u h'
  simp only [to_accepted,to_lower,to_upper] at hc
  exact ⟨hc.1,hc.2.1,hc.2.2,by rw [interval_eq_Icc _ _ hc.1,hc.2.1,hc.2.2]⟩

theorem accepted_real_spec (α : ℚ) (o : Counts) (t : ℝ) :
    t ∈ accepted (α : ℝ) o ↔ ∃ d ∈ acceptedEffectsQ α o, t = (d : ℝ)/o.total := by
  simpa only [to_accepted,to_acceptedEffectsQ,to_total] using
    AronowAudit.P003.ConfidenceFollowup.accepted_real_iff α (toAudit o) t

theorem first_line_spec (o : Counts) (x : ℤ) (j : ℕ) (v : Counts)
    (hv : firstOnLine o x j = some v) :
    Possible o v ∧ v.effect = x ∧ v.a+v.b = j := by
  have hv' : AronowAudit.P003.firstOnLine (toAudit o) x j = some (toAudit v) := by
    rw [to_firstOnLine,hv]; rfl
  have h := AronowAudit.P003.first_on_line_spec (toAudit o) x j (toAudit v) hv'
  exact ⟨(to_possible o v).mp h.1,h.2.1,h.2.2.1⟩

theorem first_before_positive_none (o : Counts) (x : ℤ) (j : ℕ) (hj : (j : ℤ) < x) :
    firstOnLine o x j = none := by
  cases h : firstOnLine o x j with
  | none => rfl
  | some v =>
    have hs := first_line_spec o x j v h
    dsimp [Counts.effect] at hs
    omega

theorem zero_rank (K : ℕ) (o v : Counts) (s : Fin K → Counts) :
    rankValue (fun _ _ => 0) o v s = 1 := by
  simp only [rankValue,abs_zero,le_refl,↓reduceIte,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  have h : (K : ℝ)+1 ≠ 0 := by positivity
  rw [add_comm (1 : ℝ),div_self h]

theorem printed_absorbing (fuel : ℕ) :
    w1PrintedRun fuel 1 2 (fun _ => true) 1 1 =
      ⟨none,List.replicate fuel 1,(1,1)⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simpa [w1PrintedRun,searchStep,List.replicate_succ] using
      congrArg (fun r : W1PrintedResult =>
        (⟨r.value,1::r.queries,r.bracket⟩ : W1PrintedResult)) ih

end SAP.P003a.WH.W1
