import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1.P.T7_L3

open Finset
open scoped Classical
noncomputable section

open SAP.P012a
open SAP.P012a.WH.W1

private theorem time_lt_of_mem_prefix (D : Data) (order pre post : List ℕ) (j x : ℕ)
    (hchron : WholeChronological D order) (horder : order = pre ++ j :: post)
    (hx : x ∈ pre) : D.time x < D.time j := by
  have hp := hchron.2.2
  rw [horder] at hp
  have hp' := (List.pairwise_append.mp hp).2.2
  exact hp' x hx j (by simp)

private theorem time_lt_of_mem_suffix (D : Data) (order pre post : List ℕ) (j x : ℕ)
    (hchron : WholeChronological D order) (horder : order = pre ++ j :: post)
    (hx : x ∈ post) : D.time j < D.time x := by
  have hp := hchron.2.2
  rw [horder] at hp
  have hp' : ((pre ++ [j]) ++ post).Pairwise (fun i j => D.time i < D.time j) := by
    simpa [List.append_assoc] using hp
  have hcross := (List.pairwise_append.mp hp').2.2
  exact hcross j (by simp) x hx

private theorem childrenBefore_self_empty (D : Data) (order pre post : List ℕ) (j : ℕ)
    (hD : Admissible D) (hchron : WholeChronological D order)
    (horder : order = pre ++ j :: post) :
    pWholeChildrenBefore D pre j = ∅ := by
  classical
  ext k
  constructor
  · intro hk
    rcases mem_filter.mp hk with ⟨hkpre, hkcond⟩
    rcases hkcond with ⟨hkn, hparent⟩
    have hlt₁ := time_lt_of_mem_prefix D order pre post j k hchron horder
      (List.mem_toFinset.mp hkpre)
    have hlt₂ := (hD.2.2.1 k hkn).2
    rw [hparent] at hlt₂
    omega
  · simp

private theorem past_eq_prefix (D : Data) (order pre post : List ℕ) (j : ℕ)
    (hchron : WholeChronological D order) (horder : order = pre ++ j :: post)
    (hj : j ∈ nonseeds D) :
    pWholePastReciprocal D j = pWholePrefixReciprocal D (pre ++ [j]) (D.parent j) := by
  have hmemOrder : ∀ k ∈ nonseeds D, k ∈ order := by
    intro k hk
    have hkS : k ∈ D.sampled := (mem_sdiff.mp hk).1
    have hkT : k ∈ order.toFinset := by rw [hchron.2.1]; exact hkS
    simpa using hkT
  have hsets :
      (nonseeds D).filter
        (fun k => D.parent k = D.parent j ∧ D.time k ≤ D.time j) =
      pWholeChildrenBefore D (pre ++ [j]) (D.parent j) := by
    ext k
    constructor
    · intro hk
      rcases mem_filter.mp hk with ⟨hkn, hcond⟩
      have hko := hmemOrder k hkn
      rw [horder] at hko
      rcases List.mem_append.mp hko with hkp | hkr
      · exact mem_filter.mpr ⟨by simp [List.mem_toFinset, hkp], hkn, hcond.1⟩
      · rcases List.mem_cons.mp hkr with hkj | hkt
        · subst k
          simp [pWholeChildrenBefore, hj]
        · have hlt := time_lt_of_mem_suffix D order pre post j k hchron horder hkt
          omega
    · intro hk
      unfold pWholeChildrenBefore at hk
      rcases mem_filter.mp hk with ⟨hkL, hrest⟩
      rcases hrest with ⟨hkn, hpar⟩
      have hmemCases : k = j ∨ k ∈ pre := by simpa using hkL
      rcases hmemCases with hkj | hkp
      · subst k
        simp [hj]
      · have hlt := time_lt_of_mem_prefix D order pre post j k hchron horder hkp
        exact mem_filter.mpr ⟨hkn, hpar, le_of_lt hlt⟩
  unfold pWholePastReciprocal pWholePrefixReciprocal
  rw [hsets]

private theorem filter_toFinset_append_singleton {α : Type} [DecidableEq α]
    (l : List α) (a : α) (p : α → Prop) [DecidablePred p] (ha : a ∉ l) :
    (l ++ [a]).toFinset.filter p =
      if p a then insert a (l.toFinset.filter p) else l.toFinset.filter p := by
  classical
  simp [List.toFinset_append, Finset.filter_union, Finset.filter_insert, ha]

private theorem childrenBefore_append (D : Data) (pre : List ℕ) (j r : ℕ)
    (hjnot : j ∉ pre) :
    pWholeChildrenBefore D (pre ++ [j]) r =
      if j ∈ nonseeds D ∧ D.parent j = r then
        insert j (pWholeChildrenBefore D pre r)
      else pWholeChildrenBefore D pre r := by
  classical
  unfold pWholeChildrenBefore
  simp [List.toFinset_append, Finset.filter_union, Finset.filter_insert, hjnot]

private theorem prefixReciprocal_append (D : Data) (pre : List ℕ) (j r : ℕ)
    (hjnot : j ∉ pre) :
    pWholePrefixReciprocal D (pre ++ [j]) r =
      if j ∈ nonseeds D ∧ D.parent j = r then
        pWholePrefixReciprocal D pre r + 1 / (pWholeDenom D j : ℚ)
      else pWholePrefixReciprocal D pre r := by
  classical
  unfold pWholePrefixReciprocal
  rw [childrenBefore_append D pre j r hjnot]
  split_ifs with h
  · rw [Finset.sum_insert]
    · simp [pWholeDenom]
      ring
    · intro hmem
      have : j ∈ pre.toFinset := by
        have := (mem_filter.mp hmem).1
        exact this
      exact hjnot (List.mem_toFinset.mp this)
  · rfl

private theorem forwardLow_append (D : Data) (pre : List ℕ) (j : ℕ)
    (hjnot : j ∉ pre) :
    pWholeForwardLow D (pre ++ [j]) =
      pWholeForwardLow D pre +
        (if j ∈ nonseeds D then
          (1-pWholeMatch D j) *
            (pWholePastReciprocal D j - 1) else 0) := by
  classical
  unfold pWholeForwardLow
  rw [filter_toFinset_append_singleton pre j
    (fun j => j ∈ nonseeds D) hjnot]
  split_ifs with hj
  · rw [Finset.sum_insert]
    · simp [pWholeMatch]
      ring
    · intro hmem
      exact hjnot (List.mem_toFinset.mp (mem_filter.mp hmem).1)
  · simp

private theorem forwardHigh_append (D : Data) (pre : List ℕ) (j : ℕ)
    (hjnot : j ∉ pre) :
    pWholeForwardHigh D (pre ++ [j]) =
      pWholeForwardHigh D pre +
        (if j ∈ nonseeds D then
          pWholeMatch D j * (1-pWholePastReciprocal D j) else 0) := by
  classical
  unfold pWholeForwardHigh
  rw [filter_toFinset_append_singleton pre j
    (fun j => j ∈ nonseeds D) hjnot]
  split_ifs with hj
  · rw [Finset.sum_insert]
    · simp [pWholeMatch]
      ring
    · intro hmem
      exact hjnot (List.mem_toFinset.mp (mem_filter.mp hmem).1)
  · simp

private theorem prefix_core (D : Data) (order : List ℕ) (hD : Admissible D)
    (hchron : WholeChronological D order) (hsched : PWholeSchedule D order) :
    ∀ pre post, order = pre ++ post →
      (pWholeRun D pre).count = (pre.toFinset.filter (fun j => j ∈ nonseeds D)).card ∧
      (pWholeRun D pre).low = pWholeForwardLow D pre ∧
      (pWholeRun D pre).high = pWholeForwardHigh D pre ∧
      ∀ r, (pWholeRun D pre).cells r = if r ∈ pre.toFinset then
        some ⟨D.degree r - pWholeDelta D r -
          (pWholeChildrenBefore D pre r).card,
          pWholePrefixReciprocal D pre r, D.trait r⟩ else none := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
      intro post horder
      simp [pWholeRun, pWholeInitial, pWholeForwardLow, pWholeForwardHigh,
        pWholePrefixReciprocal, pWholeChildrenBefore]
  | append_singleton pre j ih =>
      intro post horder
      have hsplit : order = pre ++ j :: post := by
        simpa [List.append_assoc] using horder
      have hprev := ih (j :: post) hsplit
      rcases hprev with ⟨hcount, hlow, hhigh, hcells⟩
      have hjnot : j ∉ pre := by
        intro hjpre
        have hlt := time_lt_of_mem_prefix D order pre post j j hchron hsplit hjpre
        omega
      have hjSample : j ∈ D.sampled := by
        have hjord : j ∈ order := by rw [hsplit]; simp
        have hjto : j ∈ order.toFinset := by simpa using hjord
        rw [hchron.2.1] at hjto
        exact hjto
      have hchildrenJ : pWholeChildrenBefore D pre j = ∅ :=
        childrenBefore_self_empty D order pre post j hD hchron hsplit
      have hrecipJold : pWholePrefixReciprocal D pre j = 0 := by
        simp [pWholePrefixReciprocal, hchildrenJ]
      have hfold : pWholeRun D (pre ++ [j]) =
          pWholeStep (pWholeRun D pre) (pWholeRecord D j) := by
        simp [pWholeRun, List.map_append, List.foldl_append]
      have hcountSet :
          ((pre ++ [j]).toFinset.filter (fun k => k ∈ nonseeds D)).card =
            if j ∈ nonseeds D then
              (pre.toFinset.filter (fun k => k ∈ nonseeds D)).card + 1
            else (pre.toFinset.filter (fun k => k ∈ nonseeds D)).card := by
        rw [filter_toFinset_append_singleton pre j (fun k => k ∈ nonseeds D) hjnot]
        split_ifs <;> simp [Finset.card_insert_of_notMem, hjnot]
      by_cases hjSeed : j ∈ D.seeds
      · have hjNon : j ∉ nonseeds D := by
          intro h
          exact (mem_sdiff.mp h).2 hjSeed
        have hchildrenCurrent : pWholeChildrenBefore D (pre ++ [j]) j = ∅ := by
          rw [childrenBefore_append D pre j j hjnot]
          simp [hjNon, hchildrenJ]
        have hrecipCurrent : pWholePrefixReciprocal D (pre ++ [j]) j = 0 := by
          simp [pWholePrefixReciprocal, hchildrenCurrent]
        have hchildrenSame : ∀ r,
            pWholeChildrenBefore D (pre ++ [j]) r = pWholeChildrenBefore D pre r := by
          intro r
          rw [childrenBefore_append D pre j r hjnot]
          simp [hjNon]
        have hrecipSame : ∀ r,
            pWholePrefixReciprocal D (pre ++ [j]) r = pWholePrefixReciprocal D pre r := by
          intro r
          rw [prefixReciprocal_append D pre j r hjnot]
          simp [hjNon]
        have hcellsNew : ∀ r,
            (pWholeStep (pWholeRun D pre) (pWholeRecord D j)).cells r =
              if r ∈ (pre ++ [j]).toFinset then
                some ⟨D.degree r - pWholeDelta D r -
                  (pWholeChildrenBefore D (pre ++ [j]) r).card,
                  pWholePrefixReciprocal D (pre ++ [j]) r, D.trait r⟩ else none := by
          intro r
          by_cases hr : r = j
          · subst r
            have holdj : (pWholeRun D pre).cells j = none := by
              rw [hcells j]
              simp [List.mem_toFinset, hjnot]
            simp [pWholeStep, pWholeRecord, hjSeed, Function.update,
              hchildrenSame, hrecipSame, hchildrenCurrent, hrecipCurrent,
              hchildrenJ, hrecipJold, holdj,
              pWholeDelta, List.mem_toFinset]
          · simp [pWholeStep, pWholeRecord, hjSeed, Function.update, hr,
              hcells, hchildrenSame, hrecipSame, List.mem_toFinset]
        rw [hfold]
        refine ⟨?_, ?_, ?_, hcellsNew⟩
        · calc
            (pWholeStep (pWholeRun D pre) (pWholeRecord D j)).count =
                (pWholeRun D pre).count := by simp [pWholeStep, pWholeRecord, hjSeed]
            _ = (pre.toFinset.filter (fun k => k ∈ nonseeds D)).card := hcount
            _ = ((pre ++ [j]).toFinset.filter (fun k => k ∈ nonseeds D)).card := by
              rw [hcountSet]
              simp [hjNon]
        · simp [pWholeStep, pWholeRecord, hjSeed, hjNon, hlow,
            forwardLow_append D pre j hjnot]
        · simp [pWholeStep, pWholeRecord, hjSeed, hjNon, hhigh,
            forwardHigh_append D pre j hjnot]
      · have hjNon : j ∈ nonseeds D := mem_sdiff.mpr ⟨hjSample, hjSeed⟩
        have hSched := hsched.2 pre j post hsplit hjNon
        rcases hSched with ⟨hparentIn, hresidual, hpositive⟩
        have hparentNe : D.parent j ≠ j := by
          intro heq
          apply hjnot
          simpa [heq] using hparentIn
        have hchildrenCurrent : pWholeChildrenBefore D (pre ++ [j]) j = ∅ := by
          rw [childrenBefore_append D pre j j hjnot]
          simp [hjNon, hparentNe, hchildrenJ]
        have hrecipCurrent : pWholePrefixReciprocal D (pre ++ [j]) j = 0 := by
          simp [pWholePrefixReciprocal, hchildrenCurrent]
        let c₀ : PWholeCell := ⟨D.degree (D.parent j) -
            pWholeDelta D (D.parent j) -
              (pWholeChildrenBefore D pre (D.parent j)).card,
            pWholePrefixReciprocal D pre (D.parent j), D.trait (D.parent j)⟩
        have hparentOld : (pWholeRun D pre).cells (D.parent j) = some c₀ := by
          rw [hcells]
          simp [c₀, List.mem_toFinset, hparentIn]
        have hparentResidual : c₀.remaining = pWholeDenom D j := by
          change D.degree (D.parent j) - pWholeDelta D (D.parent j) -
            (pWholeChildrenBefore D pre (D.parent j)).card = pWholeDenom D j
          exact hresidual
        have hparentRecip :
            c₀.reciprocal + 1 / (c₀.remaining : ℚ) = pWholePastReciprocal D j := by
          calc
            c₀.reciprocal + 1 / (c₀.remaining : ℚ) =
                pWholePrefixReciprocal D pre (D.parent j) +
                  1 / (pWholeDenom D j : ℚ) := by
              rw [hparentResidual]
            _ = pWholePrefixReciprocal D (pre ++ [j]) (D.parent j) := by
              rw [prefixReciprocal_append D pre j (D.parent j) hjnot]
              simp [hjNon]
            _ = pWholePastReciprocal D j :=
              (past_eq_prefix D order pre post j hchron hsplit hjNon).symm
        have hparentRecipPrefix :
            c₀.reciprocal + 1 / (c₀.remaining : ℚ) =
              pWholePrefixReciprocal D (pre ++ [j]) (D.parent j) := by
          rw [prefixReciprocal_append D pre j (D.parent j) hjnot]
          have hcond : j ∈ nonseeds D ∧ D.parent j = D.parent j := ⟨hjNon, rfl⟩
          rw [if_pos hcond, hparentResidual]
        have hparentRecipPrefixRaw :
            pWholePrefixReciprocal D pre (D.parent j) +
              1 / (↑(D.degree (D.parent j) - pWholeDelta D (D.parent j) -
                (pWholeChildrenBefore D pre (D.parent j)).card)) =
              pWholePrefixReciprocal D (pre ++ [j]) (D.parent j) := by
          rw [prefixReciprocal_append D pre j (D.parent j) hjnot]
          have hcond : j ∈ nonseeds D ∧ D.parent j = D.parent j := ⟨hjNon, rfl⟩
          rw [if_pos hcond, ← hresidual]
        have hparentRecipInv :
            c₀.reciprocal + (↑c₀.remaining)⁻¹ = pWholePastReciprocal D j := by
          simpa [one_div] using hparentRecip
        have hchildrenParent :
            (pWholeChildrenBefore D (pre ++ [j]) (D.parent j)).card =
              (pWholeChildrenBefore D pre (D.parent j)).card + 1 := by
          rw [childrenBefore_append D pre j (D.parent j) hjnot]
          have hcond : j ∈ nonseeds D ∧ D.parent j = D.parent j := ⟨hjNon, rfl⟩
          rw [if_pos hcond]
          apply Finset.card_insert_of_notMem
          intro hmem
          exact hjnot (List.mem_toFinset.mp (mem_filter.mp hmem).1)
        have hremainingNew :
            c₀.remaining - 1 = D.degree (D.parent j) -
              pWholeDelta D (D.parent j) -
                (pWholeChildrenBefore D (pre ++ [j]) (D.parent j)).card := by
          rw [hparentResidual, hchildrenParent]
          omega
        have hgetC :
            (Function.update (pWholeRun D pre).cells j
              (some ⟨D.degree j - 1, 0, D.trait j⟩) (D.parent j)).getD default = c₀ := by
          simp [Function.update, hparentNe, hparentOld]
        have hI :
            (if D.trait j = c₀.trait then (1 : ℚ) else 0) =
              pWholeMatch D j := rfl
        have hcellsNew : ∀ r,
            (pWholeStep (pWholeRun D pre) (pWholeRecord D j)).cells r =
              if r ∈ (pre ++ [j]).toFinset then
                some ⟨D.degree r - pWholeDelta D r -
                  (pWholeChildrenBefore D (pre ++ [j]) r).card,
                  pWholePrefixReciprocal D (pre ++ [j]) r, D.trait r⟩ else none := by
          intro r
          by_cases hrj : r = j
          · subst r
            have holdj : (pWholeRun D pre).cells j = none := by
              rw [hcells j]
              simp [List.mem_toFinset, hjnot]
            simp [pWholeStep, pWholeRecord, hjSeed, Function.update,
              hchildrenCurrent, hrecipCurrent, holdj, pWholeDelta,
              List.mem_toFinset, Ne.symm hparentNe]
          · by_cases hrp : r = D.parent j
            · subst r
              simp [pWholeStep, pWholeRecord, hjSeed, Function.update,
                hparentNe, Ne.symm hparentNe, hparentOld, c₀,
                hremainingNew, hparentRecip, hparentRecipPrefixRaw, hgetC, hI,
                hchildrenParent, List.mem_toFinset, hparentIn]
              simpa [one_div] using hparentRecipPrefixRaw
            · have hchildSame :
                  pWholeChildrenBefore D (pre ++ [j]) r = pWholeChildrenBefore D pre r := by
                rw [childrenBefore_append D pre j r hjnot]
                have hpr : D.parent j ≠ r := fun h => hrp h.symm
                simp [hjNon, hpr]
              have hrecipSame :
                  pWholePrefixReciprocal D (pre ++ [j]) r = pWholePrefixReciprocal D pre r := by
                rw [prefixReciprocal_append D pre j r hjnot]
                have hpr : D.parent j ≠ r := fun h => hrp h.symm
                simp [hjNon, hpr]
              simp [pWholeStep, pWholeRecord, hjSeed, Function.update,
                hparentNe, hrj, hrp, hcells, hchildSame, hrecipSame,
                List.mem_toFinset]
        rw [hfold]
        refine ⟨?_, ?_, ?_, hcellsNew⟩
        · calc
            (pWholeStep (pWholeRun D pre) (pWholeRecord D j)).count =
                (pWholeRun D pre).count + 1 := by
                  simp [pWholeStep, pWholeRecord, hjSeed]
            _ = (pre.toFinset.filter (fun k => k ∈ nonseeds D)).card + 1 := by rw [hcount]
            _ = ((pre ++ [j]).toFinset.filter (fun k => k ∈ nonseeds D)).card := by
                  rw [hcountSet]
                  simp [hjNon]
        · have hstepLow :
              (pWholeStep (pWholeRun D pre) (pWholeRecord D j)).low =
                (pWholeRun D pre).low +
                  (1-pWholeMatch D j)*(pWholePastReciprocal D j-1) := by
              simp [pWholeStep, pWholeRecord, hjSeed, hgetC]
              rw [hI, hparentRecipInv]
          rw [hstepLow, hlow, forwardLow_append D pre j hjnot]
          simp [hjNon]
        · have hstepHigh :
              (pWholeStep (pWholeRun D pre) (pWholeRecord D j)).high =
                (pWholeRun D pre).high +
                  pWholeMatch D j*(1-pWholePastReciprocal D j) := by
              simp [pWholeStep, pWholeRecord, hjSeed, hgetC]
              by_cases hm : D.trait j = D.trait (D.parent j)
              · simp [pWholeStep, pWholeRecord, hjSeed, hgetC, c₀,
                  hm, pWholeMatch, hparentRecipInv]
              · simp [pWholeStep, pWholeRecord, hjSeed, hgetC, c₀,
                  hm, pWholeMatch]
          rw [hstepHigh, hhigh, forwardHigh_append D pre j hjnot]
          simp [hjNon]

end
end SAP.P012a.WH.W1.P.T7_L3

open SAP.P012a
open SAP.P012a.WH.W1

theorem SAP.P012a.WH.W1.T7_L3_proof : SAP.P012a.WH.W1.T7_L3 := by
  intro D hD order hchron hsched
  unfold PWholeInvariant
  constructor
  · intro pre post horder
    exact SAP.P012a.WH.W1.P.T7_L3.prefix_core D order hD hchron hsched
      pre post horder
  · intro pre j post horder hj
    have hS := hsched.2 pre j post horder hj
    rcases hS with ⟨hparentIn, hresidual, hpositive⟩
    let c : PWholeCell := ⟨D.degree (D.parent j) - pWholeDelta D (D.parent j) -
      (pWholeChildrenBefore D pre (D.parent j)).card,
      pWholePrefixReciprocal D pre (D.parent j), D.trait (D.parent j)⟩
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · dsimp [c]
      rw [(SAP.P012a.WH.W1.P.T7_L3.prefix_core D order hD hchron hsched
        pre (j :: post) horder).2.2.2 (D.parent j)]
      simp [List.mem_toFinset, hparentIn]
    · rfl
    · change D.degree (D.parent j) - pWholeDelta D (D.parent j) -
        (pWholeChildrenBefore D pre (D.parent j)).card = pWholeDenom D j
      exact hresidual
    · dsimp [c]
      rw [hresidual]
      exact hpositive

