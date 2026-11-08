import SAP.P003b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace SAP.P003b.WH.W1.P.T7_L2

open SAP.P003b SAP.P003b.Bridge
open scoped BigOperators
attribute [local instance 100] Classical.propDecidable
noncomputable section

lemma uniformProb_card {A : Type*} [Fintype A] (P : A → Prop)
    [Fintype {a : A // P a}] :
    SAP.P003b.uniformProb P =
      (Fintype.card {a : A // P a} : ℝ) / (Fintype.card A : ℝ) := by
  letI : DecidablePred P := fun a => Classical.propDecidable (P a)
  unfold SAP.P003b.uniformProb
  have hc : Fintype.card {a : A // P a} = (Finset.univ.filter P).card := by
    simpa using (Fintype.card_subtype P)
  rw [← congrArg (fun n : ℕ => (n : ℝ)) hc]

lemma cylinder_next_uniform {B : Type*} [Fintype B] [Nonempty B]
    {L : ℕ} (i : Fin L) (H : (Fin L → B) → Prop) (E : B → Prop)
    (hInv : ∀ b q, H ((Equiv.funSplitAt i B).symm (b,q)) ↔
      H ((Equiv.funSplitAt i B).symm (Classical.choice (inferInstance : Nonempty B),q)))
    (hpos : 0 < SAP.P003b.uniformProb H) :
    SAP.P003b.uniformProb (fun p => H p ∧ E (p i)) /
      SAP.P003b.uniformProb H = SAP.P003b.uniformProb E := by
  classical
  let e := Equiv.funSplitAt i B
  let Q := {j : Fin L // j ≠ i} → B
  let b₀ : B := Classical.choice (inferInstance : Nonempty B)
  have hinv (b : B) (q : Q) : H (e.symm (b,q)) ↔ H (e.symm (b₀,q)) := by
    simpa [e, b₀, Q] using hInv b q
  let C := {q : Q // H (e.symm (b₀,q))}
  let histEquiv : {p : Fin L → B // H p} ≃ B × C :=
    { toFun := fun p =>
        ((e p.val).1, ⟨(e p.val).2, (hinv (e p.val).1 (e p.val).2).mp (by simpa using p.property)⟩)
      invFun := fun z => ⟨e.symm (z.1,z.2.1), (hinv z.1 z.2.1).mpr z.2.2⟩
      left_inv := by intro p; apply Subtype.ext; exact e.symm_apply_apply p.val
      right_inv := by
        intro z
        apply Prod.ext
        · change (e (e.symm (z.1,z.2.1))).1 = z.1
          exact congrArg Prod.fst (e.apply_symm_apply (z.1,z.2.1))
        · apply Subtype.ext
          change (e (e.symm (z.1,z.2.1))).2 = z.2.1
          exact congrArg Prod.snd (e.apply_symm_apply (z.1,z.2.1)) }
  have hcoord (p : Fin L → B) : p i = (e p).1 := by
    have hh := congrArg (fun z : Fin L → B => z i) (e.symm_apply_apply p)
    simpa [e, Equiv.funSplitAt, Equiv.piSplitAt] using hh.symm
  let eventEquiv : {p : Fin L → B // H p ∧ E (p i)} ≃ C × {b : B // E b} :=
    { toFun := fun p =>
        ((⟨(e p.val).2, (hinv (e p.val).1 (e p.val).2).mp (by simpa using p.property.1)⟩),
         ⟨(e p.val).1, (hcoord p.val) ▸ p.property.2⟩)
      invFun := fun z =>
        ⟨e.symm (z.2.1,z.1.1),
          ⟨(hinv z.2.1 z.1.1).mpr z.1.2,
            (by
              have hi : (e.symm (z.2.1,z.1.1)) i = z.2.1 := by
                simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
              simpa [hi] using z.2.2)⟩⟩
      left_inv := by intro p; apply Subtype.ext; exact e.symm_apply_apply p.val
      right_inv := by
        intro z
        apply Prod.ext
        · apply Subtype.ext
          simp
        · apply Subtype.ext
          simp }
  have hdenCard : Fintype.card {p : Fin L → B // H p} =
      Fintype.card B * Fintype.card C := by
    simpa [Fintype.card_prod] using Fintype.card_congr histEquiv
  have hnumCard : Fintype.card {p : Fin L → B // H p ∧ E (p i)} =
      Fintype.card C * Fintype.card {b : B // E b} := by
    simpa [Fintype.card_prod] using Fintype.card_congr eventEquiv
  have hprob (P : (Fin L → B) → Prop) [Fintype {p : Fin L → B // P p}] :
      SAP.P003b.uniformProb P =
        (Fintype.card {p : Fin L → B // P p} : ℝ) /
          (Fintype.card (Fin L → B) : ℝ) := by
    exact uniformProb_card P
  have hprobE : SAP.P003b.uniformProb E =
      (Fintype.card {b : B // E b} : ℝ) / (Fintype.card B : ℝ) :=
    uniformProb_card E
  have hA : (Fintype.card (Fin L → B) : ℝ) ≠ 0 := by
    positivity
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    positivity
  have hnumCast : (Fintype.card {p : Fin L → B // H p ∧ E (p i)} : ℝ) =
      (Fintype.card C : ℝ) * (Fintype.card {b : B // E b} : ℝ) := by
    exact_mod_cast hnumCard
  have hdenCast : (Fintype.card {p : Fin L → B // H p} : ℝ) =
      (Fintype.card B : ℝ) * (Fintype.card C : ℝ) := by
    exact_mod_cast hdenCard
  have hmul : SAP.P003b.uniformProb (fun p => H p ∧ E (p i)) =
      SAP.P003b.uniformProb H * SAP.P003b.uniformProb E := by
    rw [hprob (fun p => H p ∧ E (p i)), hprob H, hprobE, hnumCast, hdenCast]
    field_simp [hA, hB]
  rw [hmul]
  exact mul_div_cancel_left₀ _ (ne_of_gt hpos)

lemma history_eq_of_prefix {n m K i : ℕ} {α ε : ℝ} {o : Counts}
    (hi : i < testBudget n) (p q : W1Pool n m K)
    (hslot : ∀ j : Fin (2*testBudget n+1), j.val < i → p j = q j) :
    w1History false i α ε o p = w1History false i α ε o q := by
  have hp : w1Start false α ε o p = 0 := by simp [w1Start]
  have hq : w1Start false α ε o q = 0 := by simp [w1Start]
  simp only [w1History, hp, hq, Nat.zero_add]
  apply List.map_congr_left
  intro j hj
  have hji : j < i := List.mem_range.mp hj
  have hjL : j < 2*testBudget n+1 := by omega
  simpa [Nat.mod_eq_of_lt hjL] using hslot ⟨j,hjL⟩ hji

lemma history_prefix_of_eq {n m K i : ℕ} {α ε : ℝ} {o : Counts}
    (hi : i < testBudget n) (p q : W1Pool n m K) (h : List (Fin K → Assignment n m))
    (hp : w1History false i α ε o p = h) (hq : w1History false i α ε o q = h)
    (j : ℕ) (hj : j < i) :
    p ⟨j, by omega⟩ = q ⟨j, by omega⟩ := by
  have heq : w1History false i α ε o p = w1History false i α ε o q := hp.trans hq.symm
  have hstartp : w1Start false α ε o p = 0 := by simp [w1Start]
  have hstartq : w1Start false α ε o q = 0 := by simp [w1Start]
  have hget := congrArg (fun xs : List (Fin K → Assignment n m) => xs[j]?) heq
  simpa [w1History, hstartp, hstartq, Nat.mod_eq_of_lt (show j < 2*testBudget n+1 by omega),
    List.getElem?_map, List.getElem?_range, hj] using hget

lemma upper_selected_prefix {n m K i : ℕ} {α ε : ℝ} {o : Counts}
    (hi : i < testBudget n) (p q : W1Pool n m K)
    (hslot : ∀ j : Fin (2*testBudget n+1), j.val < i → p j = q j) :
    w1Selected false i α ε o p = w1Selected false i α ε o q := by
  let r : AronowAudit.P003.Counts → ℕ → Bool := fun v j =>
    approximateReject α ε o p (fromCounts v) j
  let s : AronowAudit.P003.Counts → ℕ → Bool := fun v j =>
    approximateReject α ε o q (fromCounts v) j
  have hAgree : ∀ v j, j < i → r v j = s v j := by
    intro v j hj
    have hjL : j < 2*testBudget n+1 := by omega
    have hb : batch p j = batch q j := by
      funext k
      simp [batch, Nat.mod_eq_of_lt hjL, hslot ⟨j,hjL⟩ hj]
    change approximateReject α ε o p (fromCounts v) j =
      approximateReject α ε o q (fromCounts v) j
    unfold approximateReject
    rw [hb]
  have hpre := AronowAudit.P003.Wave1.GLP0032B6_upperRun_prefix
    (toCounts o) r s 0 i (by simpa using hAgree)
  have hnative : (upperRun true o (approximateReject α ε o p) 0).trace[i]?.map Prod.fst =
      (upperRun true o (approximateReject α ε o q) 0).trace[i]?.map Prod.fst := by
    have hmap := congrArg (Option.map fromCounts) hpre.1
    simpa [AronowAudit.P003.Wave1.GLP0032B6_peek, upperRun_eq, toEndpoint, toTrace,
      Function.comp_def, List.getElem?_map, Option.map_map, r, s,
      approximateReject_fn, from_to] using hmap
  simpa [w1Selected, w1Endpoint, w1Start] using hnative

lemma upper_entry_reply {n m K i : ℕ} {α ε : ℝ} {o : Counts}
    (p : W1Pool n m K) (v : Counts) (b : Bool)
    (hentry : (upperRun true o (approximateReject α ε o p) 0).trace[i]? = some (v,b)) :
    approximateReject α ε o p v i = b := by
  let r : AronowAudit.P003.Counts → ℕ → Bool := fun w j =>
    approximateReject α ε o p (fromCounts w) j
  have hmap := congrArg (Option.map (fun z : Counts × Bool => (toCounts z.1,z.2))) hentry
  have hd : (AronowAudit.P003.upperRun true (toCounts o) r 0).trace[i]? =
      some (toCounts v,b) := by
    simpa [upperRun_eq, toEndpoint, toTrace, r, from_to, List.getElem?_map] using hmap
  have hr := AronowAudit.P003.Wave1.GLP0032B6_upperRun_reply
    (toCounts o) r 0 i (toCounts v) b hd
  simpa [r, from_to] using hr

lemma upper_error_iff {n m K i : ℕ} {α ε : ℝ} {o : Counts}
    (hi : i < testBudget n) (p : W1Pool n m K) (v : Counts)
    (hsel : w1Selected false i α ε o p = some v) (badReject : Bool) :
    w1Error false badReject i α ε o p ↔
      if badReject then
        α ≤ (pValue v o : ℝ) ∧
          (monteMean v o (fun j => (w1NextBatch false i α ε o p j).val : Fin K → Finset (Fin n)) : ℝ)+ε < α
      else
        (pValue v o : ℝ) < α-2*ε ∧
          α ≤ (monteMean v o (fun j => (w1NextBatch false i α ε o p j).val : Fin K → Finset (Fin n)) : ℝ)+ε := by
  have hmap : (upperRun true o (approximateReject α ε o p) 0).trace[i]?.map Prod.fst = some v := by
    simpa [w1Selected, w1Endpoint, w1Start] using hsel
  obtain ⟨⟨v',b⟩,hentry,hfst⟩ := Option.map_eq_some_iff.mp hmap
  have hv : v' = v := by simpa using hfst
  subst v'
  have hreply := upper_entry_reply p v b hentry
  have hnext (j : Fin K) : w1NextBatch false i α ε o p j = (p ⟨i, by omega⟩) j := by
    simp [w1NextBatch, w1Start, Nat.mod_eq_of_lt (show i < 2*testBudget n+1 by omega)]
  have hdraw : batch p i = fun j => (w1NextBatch false i α ε o p j).val := by
    funext j
    simp [batch, w1NextBatch, w1Start,
      Nat.mod_eq_of_lt (show i < 2*testBudget n+1 by omega)]
  have hdecision : approximateReject α ε o p v i =
      decide ((monteMean v o (fun j => (w1NextBatch false i α ε o p j).val) : ℝ)+ε < α) := by
    unfold approximateReject
    rw [hdraw]
  have hbFalse : b = false ↔
      α ≤ (monteMean v o (fun j => (w1NextBatch false i α ε o p j).val) : ℝ)+ε := by
    rw [← hreply, hdecision]
    simp [not_lt]
  have hbTrue : b = true ↔
      (monteMean v o (fun j => (w1NextBatch false i α ε o p j).val) : ℝ)+ε < α := by
    rw [← hreply, hdecision]
    simp
  cases badReject
  · have he : w1Error false false i α ε o p ↔
        (pValue v o : ℝ) < α-2*ε ∧ b = false := by
      simp [w1Error, w1Endpoint, w1Start, hentry, and_comm]
    rw [he, hbFalse]
    simp
  · have he : w1Error false true i α ε o p ↔
        b = true ∧ α ≤ (pValue v o : ℝ) := by
      simp [w1Error, w1Endpoint, w1Start, hentry, and_comm]
    rw [he, hbTrue]
    simp [and_comm]

lemma upper_selected_possible {n m K i : ℕ} {α ε : ℝ} {o : Counts}
    (p : W1Pool n m K) (v : Counts)
    (hsel : w1Selected false i α ε o p = some v) : Possible o v := by
  have hmapped : (upperRun true o (approximateReject α ε o p) 0).trace[i]?.map Prod.fst = some v := by
    simpa [w1Selected, w1Endpoint, w1Start] using hsel
  obtain ⟨⟨w,b⟩,hw,hfst⟩ := Option.map_eq_some_iff.mp hmapped
  have hwv : w = v := by simpa using hfst
  subst w
  let r : AronowAudit.P003.Counts → ℕ → Bool := fun x j =>
    approximateReject α ε o p (fromCounts x) j
  have hd : (AronowAudit.P003.upperRun true (toCounts o) r 0).trace[i]? =
      some (toCounts v,b) := by
    have hmap := congrArg (Option.map (fun z : Counts × Bool => (toCounts z.1,z.2))) hw
    simpa [upperRun_eq, toEndpoint, toTrace, r, from_to, List.getElem?_map] using hmap
  have hp := AronowAudit.P003.Wave1.GLP0032B6_peek_possible
    (toCounts o) r 0 i (toCounts v) (by
      rw [AronowAudit.P003.Wave1.GLP0032B6_peek,hd]
      rfl)
  exact (possible_eq o v).mp hp

lemma upper_error_selected {n m K i : ℕ} {α ε : ℝ} {o : Counts}
    (p : W1Pool n m K) (badReject : Bool)
    (herror : w1Error false badReject i α ε o p) :
    ∃ v, w1Selected false i α ε o p = some v := by
  rcases herror with ⟨v,htrace,_⟩
  have hmapped : (w1Endpoint false α ε o p).trace[i]?.map Prod.fst = some v := by
    rw [htrace]
    rfl
  exact ⟨v, by simpa [w1Selected] using hmapped⟩

end

end SAP.P003b.WH.W1.P.T7_L2

open SAP.P003b SAP.P003b.Bridge

theorem SAP.P003b.WH.W1.T7_L2_proof : SAP.P003b.WH.W1.T7_L2 := by
  classical
  change SAP.P003b.W1T7Conditional false
  intro n m K o α ε ht hm ho hK hα hε
  intro i hi h hp
  have hmn : m ≤ n := by dsimp [Counts.total] at ht; omega
  letI : Nonempty (Assignment n m) :=
    AronowAudit.P003.Wave1.GLP0032B6_assignment_nonempty n m hmn
  let B := Fin K → Assignment n m
  let L := 2*testBudget n+1
  let iFin : Fin L := ⟨i, by change i < 2*testBudget n+1; omega⟩
  letI : Nonempty B := ⟨fun _ => Classical.choice (inferInstance : Nonempty (Assignment n m))⟩
  let H : W1Pool n m K → Prop := fun p => w1History false i α ε o p = h
  have hpos : 0 < uniformProb H := hp
  have hden : 0 < (Fintype.card (W1Pool n m K) : ℝ) := by positivity
  have hnumPos : 0 < (Fintype.card {p : W1Pool n m K // H p} : ℝ) := by
    have hh : 0 < (Fintype.card {p : W1Pool n m K // H p} : ℝ) /
        (Fintype.card (W1Pool n m K) : ℝ) := by
      rw [← SAP.P003b.WH.W1.P.T7_L2.uniformProb_card H]
      exact hpos
    have hmul := mul_pos hh hden
    field_simp [ne_of_gt hden] at hmul
    exact hmul
  have hnumNat : 0 < Fintype.card {p : W1Pool n m K // H p} := by exact_mod_cast hnumPos
  have hsubNonempty : Nonempty {p : W1Pool n m K // H p} := Fintype.card_pos_iff.mp hnumNat
  let p₀ : W1Pool n m K := (Classical.choice hsubNonempty).val
  have hp₀ : H p₀ := (Classical.choice hsubNonempty).property
  have hslot_of_history (p q : W1Pool n m K) (hp : H p) (hq : H q) :
      ∀ j : Fin (2*testBudget n+1), j.val < i → p j = q j := by
    intro j hj
    exact SAP.P003b.WH.W1.P.T7_L2.history_prefix_of_eq hi p q h hp hq j.val hj
  have hselected_of_history (p : W1Pool n m K) (hp : H p) :
      w1Selected false i α ε o p = w1Selected false i α ε o p₀ :=
    SAP.P003b.WH.W1.P.T7_L2.upper_selected_prefix hi p p₀
      (hslot_of_history p p₀ hp hp₀)
  have hInv : ∀ b q,
      H ((Equiv.funSplitAt iFin B).symm (b,q)) ↔
        H ((Equiv.funSplitAt iFin B).symm (Classical.choice (inferInstance : Nonempty B),q)) := by
    let b₀ : B := Classical.choice (inferInstance : Nonempty B)
    intro b q
    have hslots : ∀ j : Fin L, j.val < i →
        (Equiv.funSplitAt iFin B).symm (b,q) j =
          (Equiv.funSplitAt iFin B).symm (b₀,q) j := by
      intro j hj
      have hji : j ≠ iFin := by
        intro heq
        have hval : j.val = i := by simpa [iFin] using congrArg Fin.val heq
        omega
      simp [Equiv.funSplitAt, Equiv.piSplitAt, hji]
    have hhist := SAP.P003b.WH.W1.P.T7_L2.history_eq_of_prefix
      (n := n) (m := m) (K := K) (i := i) (α := α) (ε := ε) (o := o) hi
      ((Equiv.funSplitAt iFin B).symm (b,q))
      ((Equiv.funSplitAt iFin B).symm (b₀,q)) hslots
    change (w1History false i α ε o ((Equiv.funSplitAt iFin B).symm (b,q)) = h) ↔
      (w1History false i α ε o ((Equiv.funSplitAt iFin B).symm (b₀,q)) = h)
    constructor
    · intro hh
      exact hhist.symm.trans hh
    · intro hh
      exact hhist.trans hh
  have hnext (p : W1Pool n m K) :
      w1NextBatch false i α ε o p = p iFin := by
    funext j
    have hstart : w1Start false α ε o p = 0 := by simp [w1Start]
    simp [w1NextBatch, hstart,
      Nat.mod_eq_of_lt (show i < 2*testBudget n+1 by omega)]
    exact congrArg (fun z : Fin L => p z j) (Fin.ext rfl)
  refine ⟨?_, ?_, ?_⟩
  · intro p q hp hq
    refine ⟨by simp [w1Start], ?_⟩
    exact SAP.P003b.WH.W1.P.T7_L2.upper_selected_prefix hi p q
      (hslot_of_history p q hp hq)
  · intro b
    letI : Nonempty (W1Pool n m K) := ⟨fun _ => Classical.choice inferInstance⟩
    have hcyl := SAP.P003b.WH.W1.P.T7_L2.cylinder_next_uniform
      (B := B) iFin H (fun x => x = b) hInv hpos
    calc
      uniformProb (fun p : W1Pool n m K => H p ∧ w1NextBatch false i α ε o p = b) /
          uniformProb H
        = uniformProb (fun p : W1Pool n m K => H p ∧ p iFin = b) /
            uniformProb H := by
              congr 1
              apply congrArg uniformProb
              funext p
              simp [hnext p]
      _ = uniformProb (fun x : B => x = b) := hcyl
      _ = 1/(Fintype.card B : ℝ) := by
        rw [SAP.P003b.WH.W1.P.T7_L2.uniformProb_card]
        have hsingle : Fintype.card {x : B // x = b} = 1 := by simp
        rw [hsingle]
        norm_num
  · intro badReject
    cases hs : w1Selected false i α ε o p₀ with
    | none =>
      have hzero : uniformProb (fun p : W1Pool n m K => H p ∧
          w1Error false badReject i α ε o p) = 0 := by
        let G : W1Pool n m K → Prop := fun p => H p ∧
          w1Error false badReject i α ε o p
        have hnonempty : ¬ Nonempty {p : W1Pool n m K // G p} := by
          rintro ⟨⟨p,hp,he⟩⟩
          obtain ⟨v,hv⟩ := SAP.P003b.WH.W1.P.T7_L2.upper_error_selected p badReject he
          have hnone : w1Selected false i α ε o p = none := by
            rw [hselected_of_history p hp, hs]
          rw [hnone] at hv
          simp at hv
        have hcard : Fintype.card {p : W1Pool n m K // G p} = 0 := by
          by_contra hne
          exact hnonempty (Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hne))
        rw [SAP.P003b.WH.W1.P.T7_L2.uniformProb_card G, hcard]
        simp
      rw [hzero]
      simp only [zero_div]
      exact (Real.exp_pos _).le
    | some v =>
      have hselFiber (p : W1Pool n m K) (hp : H p) :
          w1Selected false i α ε o p = some v := by
        simpa [hs] using hselected_of_history p hp
      have hvPoss : Possible o v :=
        SAP.P003b.WH.W1.P.T7_L2.upper_selected_possible p₀ v hs
      have hvTotal : (toCounts v).total = n := by
        have hoNative : (toCounts o).total = n := by simpa using ht
        have hpDonor := (AronowAudit.P003.possible_table_facts (toCounts o) (toCounts v)
          ((possible_eq o v).mpr hvPoss)).1
        exact hpDonor.trans hoNative
      have hmNative : (toCounts o).a+(toCounts o).b = m := by simpa using hm
      have hfixed := AronowAudit.P003.Wave1.GLP0032B6_fixed_errors
        (toCounts o) (toCounts v) α ε hvTotal hmNative hmn hK hε.1.le
      let E : B → Prop := fun x =>
        if badReject then
          α ≤ (pValue v o : ℝ) ∧
            (monteMean v o (fun j => (x j).val) : ℝ)+ε < α
        else
          (pValue v o : ℝ) < α-2*ε ∧
            α ≤ (monteMean v o (fun j => (x j).val) : ℝ)+ε
      have hbound : uniformProb E ≤ Real.exp (-2*(K : ℝ)*ε^2) := by
        cases badReject with
        | false =>
          simpa [E, SAP.P003b.Bridge.uniformProb_eq, SAP.P003b.Bridge.pValue_eq,
            SAP.P003b.Bridge.monteMean_eq] using hfixed.2
        | true =>
          simpa [E, SAP.P003b.Bridge.uniformProb_eq, SAP.P003b.Bridge.pValue_eq,
            SAP.P003b.Bridge.monteMean_eq] using hfixed.1
      have herrorEquiv (p : W1Pool n m K) (hp : H p) :
          w1Error false badReject i α ε o p ↔ E (p iFin) := by
        have he := SAP.P003b.WH.W1.P.T7_L2.upper_error_iff hi p v (hselFiber p hp) badReject
        simpa [E, hnext p] using he
      have hevents : ∀ p : W1Pool n m K,
          (H p ∧ w1Error false badReject i α ε o p) ↔
            (H p ∧ E (p iFin)) := by
        intro p
        constructor
        · rintro ⟨hp,he⟩
          exact ⟨hp,(herrorEquiv p hp).mp he⟩
        · rintro ⟨hp,he⟩
          exact ⟨hp,(herrorEquiv p hp).mpr he⟩
      have hprobEq :
          uniformProb (fun p : W1Pool n m K => H p ∧ w1Error false badReject i α ε o p) =
            uniformProb (fun p : W1Pool n m K => H p ∧ E (p iFin)) := by
        congr 1
        funext p
        exact propext (hevents p)
      have hcyl := SAP.P003b.WH.W1.P.T7_L2.cylinder_next_uniform
        (B := B) iFin H E hInv hpos
      calc
        uniformProb (fun p : W1Pool n m K => H p ∧ w1Error false badReject i α ε o p) /
            uniformProb H
          = uniformProb (fun p : W1Pool n m K => H p ∧ E (p iFin)) /
              uniformProb H := by rw [hprobEq]
        _ = uniformProb E := hcyl
        _ ≤ Real.exp (-2*(K : ℝ)*ε^2) := hbound
