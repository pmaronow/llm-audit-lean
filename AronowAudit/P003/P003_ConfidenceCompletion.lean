import AronowAudit.P003.P003_Audit

/-! Refutations of the printed search and coverage claims, with exact model identities. -/
namespace AronowAudit.P003.ConfidenceFollowup

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-- T27: the literal execution fails the two-point all-accept claim,
independently of the claimed evaluation bound. -/
theorem printed_search_claim_refuted :
    ¬ (∀ (k₁ k₂ r : ℤ) (f : ℤ → Bool),
      (0 < k₁ ∧ k₁ < k₂) → (k₁-1 ≤ r ∧ r ≤ k₂) →
      (∀ x, k₁ ≤ x → x ≤ k₂ → (f x = false ↔ x ≤ r)) →
      ∃ steps evaluations : ℕ,
        printedExecution steps k₁ k₂ f k₁ k₂ = some (r,evaluations) ∧
        (evaluations : ℝ) ≤ (⌊logTwo (k₂-k₁+1) + 2⌋ : ℤ)) := by
  intro h
  obtain ⟨steps, evaluations, he, _⟩ := h 1 2 2 (fun _ => false)
    (by norm_num) (by norm_num) (by intro x hx hx'; simp [hx'])
  cases steps <;> simp [printedExecution, searchStep] at he


/-- The accepted rational effects and real inversion give the same
finite possible-table calculation. -/
theorem accepted_real_iff (α : ℚ) (o : Counts) (t : ℝ) :
    t ∈ accepted (α : ℝ) o ↔
      ∃ d ∈ acceptedEffectsQ α o, t = (d : ℝ)/o.total := by
  constructor
  · intro ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    have hv' := List.mem_filter.mp (List.mem_toFinset.mp hv)
    have haccR : (α : ℝ) ≤ (pValue v o : ℝ) := of_decide_eq_true hv'.2
    have hacc : α ≤ pValue v o := by exact_mod_cast haccR
    refine ⟨v.effect, (accepted_effects_spec α o v.effect).mpr ⟨v,hv'.1,hacc,rfl⟩, ?_⟩
    have htot := (possible_table_facts o v hv'.1).1
    simp only [tau, tauQ, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, htot]
  · rintro ⟨d,hd,rfl⟩
    obtain ⟨v,hv,hacc,he⟩ := (accepted_effects_spec α o d).mp hd
    apply Finset.mem_image.mpr
    refine ⟨v,List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hv,?_⟩),?_⟩
    · apply decide_eq_true
      exact_mod_cast hacc
    · have htot := (possible_table_facts o v hv).1
      simp only [tau, tauQ, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, htot, he]

/-- A certified rational endpoint pair gives precisely the real extrema.
No approximate arithmetic or alternate interval is introduced. -/
theorem real_extrema_of_intervalQ (α : ℚ) (o : Counts) (l u : ℚ)
    (hI : intervalQ α o = some (l,u)) :
    (accepted (α : ℝ) o).Nonempty ∧
      lower (α : ℝ) o = (l : ℝ) ∧ upper (α : ℝ) o = (u : ℝ) := by
  cases he : acceptedEffectsQ α o with
  | nil => simp [intervalQ, he] at hI
  | cons d ds =>
    let lo := ds.foldl min d
    let hi := ds.foldl max d
    have hmin : (d::ds).min? = some lo := by simp only [List.min?_cons']; rfl
    have hmax : (d::ds).max? = some hi := by simp only [List.max?_cons']; rfl
    have hlo := List.min?_eq_some_iff.mp hmin
    have hhi := List.max?_eq_some_iff.mp hmax
    have hlow : (lo : ℝ)/o.total ∈ accepted (α : ℝ) o :=
      (accepted_real_iff α o _).mpr ⟨lo,he ▸ hlo.1,rfl⟩
    have hhigh : (hi : ℝ)/o.total ∈ accepted (α : ℝ) o :=
      (accepted_real_iff α o _).mpr ⟨hi,he ▸ hhi.1,rfl⟩
    have hL : lower (α : ℝ) o = (lo : ℝ)/o.total := by
      apply IsLeast.csInf_eq
      refine ⟨hlow,?_⟩
      intro t ht
      obtain ⟨e,he',rfl⟩ := (accepted_real_iff α o t).mp ht
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hlo.2 e (he ▸ he')
    have hU : upper (α : ℝ) o = (hi : ℝ)/o.total := by
      apply IsGreatest.csSup_eq
      refine ⟨hhigh,?_⟩
      intro t ht
      obtain ⟨e,he',rfl⟩ := (accepted_real_iff α o t).mp ht
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hhi.2 e (he ▸ he')
    have hlq : (ds.map (fun x : ℤ => (x : ℚ))).foldl min (d : ℚ) = (lo : ℚ) := by
      simpa only [lo] using (List.foldl_map_hom (g := fun x : ℤ => (x:ℚ))
        (f := min) (f' := min) (a := d) (l := ds) (fun x y => Int.cast_min.symm))
    have huq : (ds.map (fun x : ℤ => (x : ℚ))).foldl max (d : ℚ) = (hi : ℚ) := by
      simpa only [hi] using (List.foldl_map_hom (g := fun x : ℤ => (x:ℚ))
        (f := max) (f' := max) (a := d) (l := ds) (fun x y => Int.cast_max.symm))
    simp only [intervalQ, he, bind_pure_comp] at hI
    change some (((ds.map (fun x : ℤ => (x:ℚ))).foldl min (d:ℚ))/o.total,
      ((ds.map (fun x : ℤ => (x:ℚ))).foldl max (d:ℚ))/o.total) = _ at hI
    rw [hlq,huq] at hI
    change some ((lo : ℚ)/o.total,(hi : ℚ)/o.total) = some (l,u) at hI
    have hl := congrArg Prod.fst (Option.some.inj hI)
    have hu := congrArg Prod.snd (Option.some.inj hI)
    refine ⟨⟨_,hlow⟩, hL.trans ?_, hU.trans ?_⟩
    · exact_mod_cast hl
    · exact_mod_cast hu

/-- For nonempty certified endpoint inversions, the real missing interval
agrees exactly with the rational implementation. -/
theorem missing_mem_real_iff (α : ℚ) (o r : Counts) (l₀ u₀ l₁ u₁ t : ℚ)
    (h₀ : intervalQ α (minusCompletion o r) = some (l₀,u₀))
    (h₁ : intervalQ α (plusCompletion o r) = some (l₁,u₁)) :
    (t : ℝ) ∈ missingInterval (α : ℝ) o r ↔
      (missingIntervalQ α o r).1 ≤ t ∧ t ≤ (missingIntervalQ α o r).2 := by
  obtain ⟨hn₀,hl₀,hu₀⟩ := real_extrema_of_intervalQ α (minusCompletion o r) l₀ u₀ h₀
  obtain ⟨hn₁,hl₁,hu₁⟩ := real_extrema_of_intervalQ α (plusCompletion o r) l₁ u₁ h₁
  simp only [missingInterval, hn₀, hn₁, ↓reduceIte, hl₀, hu₁, Set.mem_Icc,
    missingIntervalQ, h₀, h₁, estimate]
  norm_cast

/-- Missing masks are enumerated once each, with their four genuine cell
counts; this is needed to construct the concrete deterministic joint law. -/
theorem missingMasks_nodup (o : Counts) : (missingMasks o).Nodup := by
  let f : (ℕ × ℕ) × (ℕ × ℕ) → Counts := fun x => ⟨x.1.1,x.1.2,x.2.1,x.2.2⟩
  have hf : Function.Injective f := by
    intro x y h
    have ha := congrArg Counts.a h
    have hb := congrArg Counts.b h
    have hc := congrArg Counts.c h
    have hd := congrArg Counts.d h
    exact Prod.ext (Prod.ext ha hb) (Prod.ext hc hd)
  have he : missingMasks o =
      (((List.range (o.a+1)).product (List.range (o.b+1))).product
        ((List.range (o.c+1)).product (List.range (o.d+1)))).map f := by
    simp [missingMasks,List.product,List.map_flatMap,List.flatMap_assoc,List.flatMap_map,
      List.map_map,Function.comp_def,f]
  rw [he]
  exact ((List.nodup_range.product List.nodup_range).product
    (List.nodup_range.product List.nodup_range)).map hf

/-- A list containing each atom once has the expected deterministic mass. -/
theorem sum_single_atom {A : Type*} [DecidableEq A] (xs : List A) (hn : xs.Nodup)
    (a : A) (ha : a ∈ xs) (c : ℝ) :
    (xs.map fun x => if x = a then c else 0).sum = c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp hn
    by_cases hx : x = a
    · subst x
      have hz : (xs.map fun x => if x = a then c else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro b hb
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
        apply if_neg
        intro he
        subst y
        exact hnd.1 hy
      simp only [List.map_cons,List.sum_cons,ite_true,hz,add_zero]
    · have hat : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hx)
      simp only [List.map_cons,List.sum_cons,if_neg hx,zero_add]
      exact ih hnd.2 hat

/-- The concrete missingness rule keeps precisely one mask at each design
state, with that state's actual complete-randomization probability. -/
noncomputable def badJointLaw (q r : Counts) : ℝ :=
  if r = badMask q then (multiplicity badPopulation q : ℝ) / badPopulation.total.choose 3
    else 0

theorem badJointLaw_legal : IsMissingLaw badPopulation 3 badJointLaw := by
  constructor
  · intro q hq r hr
    unfold badJointLaw
    split_ifs
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact le_rfl
  · intro q hq
    exact sum_single_atom _ (missingMasks_nodup _) (badMask q) (bad_mask_legal q) _

theorem badJointLaw_probability (E : Counts → Counts → Prop) :
    missingProb badPopulation 3 badJointLaw E =
      designProb badPopulation 3 (fun q => E q (badMask q)) := by
  have hi (q : Counts) :
      ((missingMasks (observed badPopulation q)).map fun r =>
        if E q r then badJointLaw q r else 0).sum =
      if E q (badMask q) then
        (multiplicity badPopulation q : ℝ)/badPopulation.total.choose 3 else 0 := by
    have he : (fun r => if E q r then badJointLaw q r else 0) =
        (fun r => if r = badMask q then
          (if E q (badMask q) then
            (multiplicity badPopulation q : ℝ)/badPopulation.total.choose 3 else 0) else 0) := by
      funext r
      by_cases hr : r = badMask q
      · subst r; simp only [badJointLaw,ite_true]
      · simp only [badJointLaw,hr,↓reduceIte,ite_self]
    rw [he]
    exact sum_single_atom _ (missingMasks_nodup _) (badMask q) (bad_mask_legal q) _
  unfold missingProb
  simp_rw [hi]
  unfold designProb
  rw [list_event_ratio]
  exact list_sum_as_fin _ _

theorem bad_event_real_iff (q : Counts) (hq : q ∈ randomStates badPopulation 3) :
    tau badPopulation ∈ missingInterval ((109/500 : ℚ) : ℝ) (observed badPopulation q) (badMask q) ↔
      (missingIntervalQ (109/500) (observed badPopulation q) (badMask q)).1 ≤ tauQ badPopulation ∧
      tauQ badPopulation ≤ (missingIntervalQ (109/500) (observed badPopulation q) (badMask q)).2 := by
  rw [bad_random_states_certificate] at hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_0_3_14_3 interval_obs_0_3_14_3
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_0_3_13_4 interval_obs_0_3_13_4
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_0_3_12_5 interval_obs_0_3_12_5
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_0_3_11_6 interval_obs_0_3_10_7
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_1_2_13_4 interval_obs_1_2_13_4
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_1_2_12_5 interval_obs_1_2_12_5
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_1_2_11_6 interval_obs_1_2_11_6
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_2_1_12_5 interval_obs_2_1_12_5
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_2_1_11_6 interval_obs_2_1_11_6
  · exact missing_mem_real_iff _ _ _ _ _ _ _ _ interval_obs_3_0_11_6 interval_obs_3_0_11_6

/-- The real-valued joint probability equals the exact rational coverage,
including all ten design-count states. -/
theorem badJointLaw_coverage :
    missingProb badPopulation 3 badJointLaw (fun q r =>
      tau badPopulation ∈ missingInterval ((109/500 : ℚ) : ℝ) (observed badPopulation q) r) =
      (297 : ℝ)/380 := by
  rw [badJointLaw_probability]
  have he : designProb badPopulation 3 (fun q =>
      tau badPopulation ∈ missingInterval ((109/500 : ℚ) : ℝ)
        (observed badPopulation q) (badMask q)) = (badCoverage : ℝ) := by
    unfold designProb badCoverage
    norm_num only [badPopulation,Counts.total,Nat.choose_zero_right,Nat.choose_succ_succ,
      Nat.choose_self,Nat.choose_zero_succ,Nat.reduceAdd,Nat.reduceMul,Rat.cast_div,
      Rat.cast_ofNat,Rat.cast_list_sum]
    congr 1
    simp only [Rat.cast_natCast,Nat.cast_list_sum,Rat.cast_list_sum,List.map_map,Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    have hh := bad_event_real_iff q hq
    by_cases hp : tau badPopulation ∈ missingInterval ((109/500 : ℚ) : ℝ)
        (observed badPopulation q) (badMask q)
    · norm_num only [badPopulation,Rat.cast_div,Rat.cast_ofNat] at hh hp
      simp only [if_pos hp,if_pos (hh.mp hp)]
    · norm_num only [badPopulation,Rat.cast_div,Rat.cast_ofNat] at hh hp
      simp only [if_neg hp,if_neg (mt hh.mpr hp),Nat.cast_zero]
  rw [he,badCoverage_certificate]
  norm_num

/-- T26: exact full negation of the unbalanced printed coverage claim.
The witness has deterministic missingness and nonempty endpoint inversions,
so neither its random-J wording nor its empty-endpoint convention is used. -/
theorem printed_missing_coverage_refuted :
    ¬ (∀ (v : Counts) (m : ℕ) (α : ℝ),
      (0 < m ∧ m < v.total) → (0 < α ∧ α < 1) →
      ∀ μ : Counts → Counts → ℝ, IsMissingLaw v m μ →
        missingProb v m μ (fun q r => tau v ∈ missingInterval α (observed v q) r) ≥ 1-α) := by
  intro h
  have hb := h badPopulation 3 ((109/500 : ℚ) : ℝ)
    (by norm_num [badPopulation,Counts.total]) (by norm_num) badJointLaw badJointLaw_legal
  rw [badJointLaw_coverage] at hb
  norm_num at hb

end AronowAudit.P003.ConfidenceFollowup
