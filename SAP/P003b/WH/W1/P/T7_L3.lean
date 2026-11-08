import SAP.P003b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1.P.T7_L3

open SAP.P003b SAP.P003b.Bridge
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

private abbrev avg {A : Type*} [Fintype A] (f : A → ℝ) :=
  AronowAudit.P003.Wave1.GLP0032B6_avg f

private lemma prob_avg_local {A : Type*} [Fintype A] (P : A → Prop) :
    uniformProb P = avg (fun a => if P a then (1 : ℝ) else 0) := by
  simp [uniformProb, avg, AronowAudit.P003.Wave1.GLP0032B6_avg,
    Finset.sum_boole]

lemma exists_of_prob_pos {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop)
    (hp : 0 < uniformProb P) : ∃ a, P a := by
  unfold uniformProb at hp
  have hden : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnum : 0 < ((Finset.univ.filter P).card : ℝ) := by
    by_contra hn
    have hnle : ((Finset.univ.filter P).card : ℝ) ≤ 0 := le_of_not_gt hn
    have hquot : ((Finset.univ.filter P).card : ℝ) / (Fintype.card A : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnle hden.le
    exact (not_lt_of_ge hquot) hp
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by exact_mod_cast hnum)
  exact ⟨a,(Finset.mem_filter.mp ha).2⟩

private lemma split_avg_prod {B : Type*} [Fintype B] {L : ℕ}
    (i : Fin L) (e : (Fin L → B) ≃ B × ({j : Fin L // j ≠ i} → B))
    (f : (Fin L → B) → ℝ) :
    avg f = avg (fun q : {j : Fin L // j ≠ i} → B =>
      avg (fun b : B => f (e.symm (b,q)))) := by
  calc
    avg f = avg (fun z : B × ({j : Fin L // j ≠ i} → B) => f (e.symm z)) :=
      (AronowAudit.P003.Wave1.GLP0032B6_avg_reindex e.symm f).symm
    _ = _ := AronowAudit.P003.Wave1.GLP0032B6_avg_prod _

private lemma split_avg {B : Type*} [Fintype B] [Nonempty B]
    {L : ℕ} (i : Fin L)
    (e : (Fin L → B) ≃ B × ({j : Fin L // j ≠ i} → B))
    (E : (Fin L → B) → Prop) :
    uniformProb E = avg (fun q : {j : Fin L // j ≠ i} → B =>
      avg (fun b : B => if E (e.symm (b,q)) then 1 else 0)) := by
  rw [prob_avg_local]
  calc
    _ = avg (fun z : B × ({j : Fin L // j ≠ i} → B) =>
        if E (e.symm z) then 1 else 0) := by
      simpa only [avg] using
        (AronowAudit.P003.Wave1.GLP0032B6_avg_reindex e.symm
          (fun p => if E p then 1 else 0)).symm
    _ = _ := AronowAudit.P003.Wave1.GLP0032B6_avg_prod _

private lemma split_inner_invariant {B : Type*} [Fintype B] [Nonempty B]
    {L : ℕ} (i : Fin L)
    (e : (Fin L → B) ≃ B × ({j : Fin L // j ≠ i} → B))
    (E : (Fin L → B) → Prop)
    (hinv : ∀ b₁ b₂ (q : {j : Fin L // j ≠ i} → B),
      E (e.symm (b₁,q)) ↔ E (e.symm (b₂,q)))
    (b₀ : B) (q : {j : Fin L // j ≠ i} → B) :
    avg (fun b : B => if E (e.symm (b,q)) then 1 else 0) =
      if E (e.symm (b₀,q)) then 1 else 0 := by
  by_cases h : E (e.symm (b₀,q))
  · have he (b : B) : E (e.symm (b,q)) :=
      (hinv b b₀ q).mpr h
    simpa [avg, he] using
      AronowAudit.P003.Wave1.GLP0032B6_avg_const (A := B) (1 : ℝ)
  · have he (b : B) : ¬ E (e.symm (b,q)) := by
      intro hb
      exact h ((hinv b₀ b q).mpr hb)
    simpa [avg, he] using
      AronowAudit.P003.Wave1.GLP0032B6_avg_const (A := B) (0 : ℝ)

private lemma split_inner_coordinate {B : Type*} [Fintype B] [Nonempty B]
    {L : ℕ} (i : Fin L)
    (e : (Fin L → B) ≃ B × ({j : Fin L // j ≠ i} → B))
    (E : (Fin L → B) → Prop)
    (hinv : ∀ b₁ b₂ (q : {j : Fin L // j ≠ i} → B),
      E (e.symm (b₁,q)) ↔ E (e.symm (b₂,q)))
    (hcoord : ∀ b (q : {j : Fin L // j ≠ i} → B), e.symm (b,q) i = b)
    (b₀ b : B) (q : {j : Fin L // j ≠ i} → B) :
    avg (fun a : B => if E (e.symm (a,q)) ∧ a = b then 1 else 0) =
      (if E (e.symm (b₀,q)) then 1 else 0) /
        (Fintype.card B : ℝ) := by
  by_cases h : E (e.symm (b₀,q))
  · have he (a : B) : E (e.symm (a,q)) :=
      (hinv a b₀ q).mpr h
    have hfun : (fun a : B => if E (e.symm (a,q)) ∧ a = b then (1 : ℝ) else 0) =
        fun a => if a = b then 1 else 0 := by
      funext a
      simp [he a]
    rw [hfun]
    have hsum : ∑ a : B, (if a = b then (1 : ℝ) else 0) = 1 := by simp
    unfold avg AronowAudit.P003.Wave1.GLP0032B6_avg
    rw [hsum]
    simp [h, Fintype.card_ne_zero]
  · have he (a : B) : ¬ E (e.symm (a,q)) := by
      intro ha
      exact h ((hinv b₀ a q).mpr ha)
    simpa [avg, he] using
      AronowAudit.P003.Wave1.GLP0032B6_avg_const (A := B) (0 : ℝ)

lemma conditional_slot_law {B : Type*} [Fintype B] [Nonempty B]
    {L : ℕ} (i : Fin L)
    (e : (Fin L → B) ≃ B × ({j : Fin L // j ≠ i} → B))
    (E : (Fin L → B) → Prop)
    (hinv : ∀ b₁ b₂ (q : {j : Fin L // j ≠ i} → B),
      E (e.symm (b₁,q)) ↔ E (e.symm (b₂,q)))
    (hcoord : ∀ b (q : {j : Fin L // j ≠ i} → B), e.symm (b,q) i = b)
    (hpos : 0 < uniformProb E) (b : B) :
    uniformProb (fun p => E p ∧ p i = b) / uniformProb E =
      1/(Fintype.card B : ℝ) := by
  classical
  let b₀ : B := Classical.choice ‹Nonempty B›
  have hden : uniformProb E = avg (fun q : {j : Fin L // j ≠ i} → B =>
      if E (e.symm (b₀,q)) then 1 else 0) := by
    rw [split_avg i e]
    apply congrArg (avg)
    funext q
    exact split_inner_invariant i e E hinv b₀ q
  have hnum : uniformProb (fun p => E p ∧ p i = b) =
      avg (fun q : {j : Fin L // j ≠ i} → B =>
        (if E (e.symm (b₀,q)) then 1 else 0)/(Fintype.card B : ℝ)) := by
    let f : (Fin L → B) → ℝ := fun p =>
      @ite ℝ (E p ∧ p i = b) (Classical.propDecidable _) 1 0
    calc
      uniformProb (fun p => E p ∧ p i = b) = avg f := by
        simpa [f] using prob_avg_local (fun p => E p ∧ p i = b)
      _ =
          avg (fun q : {j : Fin L // j ≠ i} → B =>
            avg (fun a : B => if E (e.symm (a,q)) ∧ a = b then 1 else 0)) := by
        rw [split_avg_prod i e f]
        congr 1
        funext q
        congr 1
        funext a
        simp [f, hcoord]
      _ = avg (fun q : {j : Fin L // j ≠ i} → B =>
            (if E (e.symm (b₀,q)) then 1 else 0)/(Fintype.card B : ℝ)) := by
        congr 1
        funext q
        exact split_inner_coordinate i e E hinv hcoord b₀ b q
  have hcard : 0 < (Fintype.card B : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [hnum, hden]
  have hscaled : avg (fun q : {j : Fin L // j ≠ i} → B =>
      (if E (e.symm (b₀,q)) then 1 else 0)/(Fintype.card B : ℝ)) =
      (avg (fun q : {j : Fin L // j ≠ i} → B =>
        if E (e.symm (b₀,q)) then 1 else 0))/(Fintype.card B : ℝ) := by
    simp only [avg, AronowAudit.P003.Wave1.GLP0032B6_avg]
    rw [← Finset.sum_div]
    field_simp [Fintype.card_ne_zero]
  rw [hscaled]
  have hden0 : avg (fun q : {j : Fin L // j ≠ i} → B =>
      if E (e.symm (b₀,q)) then 1 else 0) ≠ 0 := by
    rw [← hden]
    exact ne_of_gt hpos
  field_simp [hden0, ne_of_gt hcard]

lemma conditional_slot_bound {B T : Type*} [Fintype B] [Nonempty B] [Nonempty T]
    {L : ℕ} (i : Fin L)
    (e : (Fin L → B) ≃ B × ({j : Fin L // j ≠ i} → B))
    (E : (Fin L → B) → Prop)
    (select : (Fin L → B) → Option T) (bad : T → B → Prop) (δ : ℝ)
    (hinvE : ∀ b₁ b₂ (q : {j : Fin L // j ≠ i} → B),
      E (e.symm (b₁,q)) ↔ E (e.symm (b₂,q)))
    (hinvS : ∀ b₁ b₂ (q : {j : Fin L // j ≠ i} → B),
      select (e.symm (b₁,q)) = select (e.symm (b₂,q)))
    (hcoord : ∀ b (q : {j : Fin L // j ≠ i} → B), e.symm (b,q) i = b)
    (hbad : ∀ t, uniformProb (bad t) ≤ δ)
    (hpos : 0 < uniformProb E) :
    uniformProb (fun p => E p ∧ ∃ t, select p = some t ∧ bad t (p i)) /
      uniformProb E ≤ δ := by
  classical
  let b₀ : B := Classical.choice ‹Nonempty B›
  have hδ : 0 ≤ δ := by
    have ht := hbad (Classical.choice ‹Nonempty T›)
    have hn : 0 ≤ uniformProb (bad (Classical.choice ‹Nonempty T›)) := by
      unfold uniformProb
      positivity
    exact hn.trans ht
  have hnum : uniformProb (fun p => E p ∧ ∃ t, select p = some t ∧ bad t (p i)) ≤
      δ * uniformProb E := by
    let f : (Fin L → B) → ℝ := fun p =>
      @ite ℝ (E p ∧ ∃ t, select p = some t ∧ bad t (p i)) (Classical.propDecidable _) 1 0
    calc
      uniformProb (fun p => E p ∧ ∃ t, select p = some t ∧ bad t (p i)) = avg f := by
        simpa [f] using prob_avg_local (fun p => E p ∧ ∃ t, select p = some t ∧ bad t (p i))
      _ =
        avg (fun q : {j : Fin L // j ≠ i} → B =>
        avg (fun b : B => if E (e.symm (b,q)) ∧
          ∃ t, select (e.symm (b,q)) = some t ∧ bad t b then 1 else 0)) := by
        rw [split_avg_prod i e f]
        congr 1
        funext q
        congr 1
        funext b
        simp [f, hcoord]
      _ ≤ δ * uniformProb E := by
        have hden : uniformProb E = avg (fun q : {j : Fin L // j ≠ i} → B =>
            if E (e.symm (b₀,q)) then 1 else 0) := by
          rw [split_avg i e]
          apply congrArg avg
          funext q
          exact split_inner_invariant i e E hinvE b₀ q
        calc
          _ ≤ avg (fun q : {j : Fin L // j ≠ i} → B =>
              δ * (if E (e.symm (b₀,q)) then 1 else 0)) := by
            apply AronowAudit.P003.Wave1.GLP0032B6_avg_mono
            intro q
            by_cases he0 : E (e.symm (b₀,q))
            · have he (b : B) : E (e.symm (b,q)) := (hinvE b₀ b q).mp he0
              cases hs : select (e.symm (b₀,q)) with
              | none =>
                  have hsameS (b : B) : select (e.symm (b,q)) = none := by
                    rw [hinvS b b₀ q, hs]
                  have hzero : avg (fun b : B => if E (e.symm (b,q)) ∧
                    ∃ t, select (e.symm (b,q)) = some t ∧ bad t b then 1 else 0) =
                    0 := by
                    have hz : avg (fun _ : B => (0 : ℝ)) = 0 :=
                      AronowAudit.P003.Wave1.GLP0032B6_avg_const (A := B) 0
                    calc
                      _ = avg (fun _ : B => (0 : ℝ)) := by
                        congr 1
                        funext b
                        simp [hsameS]
                      _ = 0 := hz
                  rw [hzero]
                  simpa [he0] using hδ
              | some t =>
                  have hsameS (b : B) : select (e.symm (b,q)) = some t := by
                    rw [hinvS b b₀ q, hs]
                  have hbavg : avg (fun b : B => if bad t b then 1 else 0) ≤ δ := by
                    rw [← prob_avg_local (bad t)]
                    exact hbad t
                  simpa [avg, he, hsameS, hcoord, he0] using hbavg
            · have hnot (b : B) : ¬ E (e.symm (b,q)) := by
                intro hb
                exact he0 ((hinvE b₀ b q).mpr hb)
              have hz : avg (fun b : B => (0 : ℝ)) = 0 :=
                AronowAudit.P003.Wave1.GLP0032B6_avg_const (A := B) 0
              simpa [hnot] using le_of_eq hz
          _ = δ * avg (fun q : {j : Fin L // j ≠ i} → B =>
              if E (e.symm (b₀,q)) then 1 else 0) := by
            simp only [avg, AronowAudit.P003.Wave1.GLP0032B6_avg]
            rw [← Finset.mul_sum]
            ring
          _ = δ * uniformProb E := by rw [← hden]
  exact (div_le_iff₀ hpos).2 hnum

end
end SAP.P003b.WH.W1.P.T7_L3

open SAP.P003b SAP.P003b.Bridge

theorem SAP.P003b.WH.W1.T7_L3_proof : SAP.P003b.WH.W1.T7_L3 := by
  intro n m K o α ε ht hm ho hK hα hε i hi h hpos
  have hmn : m ≤ n := by
    dsimp [Counts.total] at ht
    omega
  letI : Nonempty (Assignment n m) :=
    AronowAudit.P003.Wave1.GLP0032B6_assignment_nonempty n m hmn
  let Ω := W1Pool n m K
  haveI : Nonempty Ω := ⟨fun _ _ => Classical.choice inferInstance⟩
  let E : Ω → Prop := fun p => w1History true i α ε o p = h
  have hposE : 0 < uniformProb E := by simpa [E] using hpos
  have hpick : ∃ p : Ω, E p :=
    SAP.P003b.WH.W1.P.T7_L3.exists_of_prob_pos E hposE
  let p₀ : Ω := Classical.choose hpick
  have hp₀ : E p₀ := Classical.choose_spec hpick
  let s : ℕ := w1Start true α ε o p₀
  have hstart (p : Ω) (hp : E p) : w1Start true α ε o p = s := by
    have hlenP : (w1History true i α ε o p).length =
        w1Start true α ε o p+i := by simp [w1History]
    have hlen0 : (w1History true i α ε o p₀).length = s+i := by
      simp [w1History,s]
    have heq := congrArg List.length hp
    rw [hlenP] at heq
    have heq0 := congrArg List.length hp₀
    rw [hlen0] at heq0
    have hlenH : h.length = s+i := by simpa using heq0.symm
    dsimp [s]
    omega
  have hstartTrace : (upperRun true o (approximateReject α ε o p₀)).trace.length = s := by
    simpa [s,w1Start] using rfl
  have hbudget0 := allStartBudget o (approximateReject α ε o p₀) 0 ho
  have hsBound : s ≤ testBudget n := by
    have hb := hbudget0.2
    rw [ht] at hb
    simpa [s,w1Start] using hb
  let k := s+i
  let L := 2*testBudget n+1
  have hkL : k < L := by
    dsimp [k,L]
    omega
  let B := Fin K → Assignment n m
  let e : (Fin L → B) ≃ B × ({j : Fin L // j ≠ ⟨k,hkL⟩} → B) :=
    Equiv.funSplitAt (⟨k,hkL⟩ : Fin L) B
  have hcoord (b : B) (q : {j : Fin L // j ≠ ⟨k,hkL⟩} → B) :
      e.symm (b,q) ⟨k,hkL⟩ = b := by
    simp [e,Equiv.funSplitAt,Equiv.piSplitAt]
  have hsplit (b₁ b₂ : B) (q : {j : Fin L // j ≠ ⟨k,hkL⟩} → B)
      (j : Fin L) (hji : j ≠ ⟨k,hkL⟩) :
      e.symm (b₁,q) j = e.symm (b₂,q) j := by
    simp [e,Equiv.funSplitAt,Equiv.piSplitAt,hji]
  have hpoolAgree {p q : Ω} (hpq : ∀ j : Fin L, j.val < k → p j = q j) :
      ∀ j : Fin L, j.val < k → p j = q j := hpq
  have hdecAgree (oo : Counts) {p q : Ω} (hpq : ∀ j : Fin L, j.val < k → p j = q j)
      (v : Counts) (j : ℕ) (hj : j < k) :
      approximateReject α ε oo p v j = approximateReject α ε oo q v j := by
    have hjL : j < L := by dsimp [L,k] at *; omega
    have hbatch : batch p j = batch q j := by
      have hpoolIdx : p ⟨j % L, Nat.mod_lt _ (by omega)⟩ =
          q ⟨j % L, Nat.mod_lt _ (by omega)⟩ := by
        have heq := hpq ⟨j,hjL⟩ hj
        simpa [Nat.mod_eq_of_lt hjL] using heq
      funext z
      simpa [batch] using congrArg (fun f : B => (f z).val) hpoolIdx
    simp [approximateReject,hbatch]
  have hstopPreserve {p q : Ω} (hp : w1Start true α ε o p = s)
      (hpq : ∀ j : Fin L, j.val < k → p j = q j) :
      w1Start true α ε o q = s := by
    have hpLen : (upperRun true o (approximateReject α ε o p)).trace.length = s := by
      simpa [w1Start] using hp
    let rP : AronowAudit.P003.Counts → ℕ → Bool := fun v j =>
      AronowAudit.P003.approximateReject α ε (toCounts o) p v j
    let rQ : AronowAudit.P003.Counts → ℕ → Bool := fun v j =>
      AronowAudit.P003.approximateReject α ε (toCounts o) q v j
    have hprefix : ∀ v j, j < s → rP v j = rQ v j := by
      intro v j hj
      have hloc := hdecAgree o hpq (fromCounts v) j (by omega)
      have hpbridge := SAP.P003b.Bridge.approximateReject_eq α ε o (fromCounts v) p j
      have hqbridge := SAP.P003b.Bridge.approximateReject_eq α ε o (fromCounts v) q j
      simpa only [rP,rQ,to_from] using hpbridge.trans (hloc.trans hqbridge.symm)
    have hd := AronowAudit.P003.Wave1.GLP0032B6_upperRun_prefix
      (toCounts o) rP rQ 0 s (by simpa using hprefix)
    have hlenD : (AronowAudit.P003.upperRun true (toCounts o) rP 0).trace.length = s := by
      simpa only [upperRun_eq,toEndpoint,List.length_map,rP,approximateReject_fn] using hpLen
    have heq := hd.2 (by omega)
    have heqLen := congrArg (fun z : AronowAudit.P003.EndpointResult => z.trace.length) heq
    have hlenQ : (AronowAudit.P003.upperRun true (toCounts o) rQ 0).trace.length = s := by
      exact heqLen.symm.trans hlenD
    have hlocal : (upperRun true o (approximateReject α ε o q)).trace.length = s := by
      simpa only [upperRun_eq,toEndpoint,List.length_map,rQ,approximateReject_fn] using hlenQ
    simpa [w1Start] using hlocal
  have hinvE : ∀ b₁ b₂ (q : {j : Fin L // j ≠ ⟨k,hkL⟩} → B),
      E (e.symm (b₁,q)) ↔ E (e.symm (b₂,q)) := by
    intro b₁ b₂ q
    let p := e.symm (b₁,q)
    let q' := e.symm (b₂,q)
    change (w1History true i α ε o p = h) ↔ (w1History true i α ε o q' = h)
    constructor
    · intro hp
      have hsP := hstart p hp
      have hsQ := hstopPreserve hsP (fun j hj => hsplit b₁ b₂ q j (by
        intro he
        exact (Nat.ne_of_lt hj) (by simpa using congrArg Fin.val he)))
      have hhist : w1History true i α ε o p = w1History true i α ε o q' := by
        unfold w1History
        rw [hsP,hsQ]
        apply List.map_congr_left
        intro j hj
        have hjk : j < k := by simp only [List.mem_range] at hj; omega
        have jL : j < L := by dsimp [L,k] at *; omega
        let jf : Fin L := ⟨j % L, Nat.mod_lt _ (by omega)⟩
        have hji : jf ≠ ⟨k,hkL⟩ := by
          intro he
          have hval : jf.val = k := congrArg Fin.val he
          have hjeq : j = k := by
            dsimp [jf] at hval
            rw [Nat.mod_eq_of_lt jL] at hval
            exact hval
          exact (Nat.ne_of_lt hjk) hjeq
        have hslot := hsplit b₁ b₂ q jf hji
        change e.symm (b₁,q) jf = e.symm (b₂,q) jf
        exact hslot
      rw [← hhist]
      exact hp
    · intro hp
      have hsQ := hstart q' hp
      have hsP := hstopPreserve hsQ (fun j hj => (hsplit b₁ b₂ q j (by
        intro he
        exact (Nat.ne_of_lt hj) (by simpa using congrArg Fin.val he))).symm)
      have hhist : w1History true i α ε o p = w1History true i α ε o q' := by
        unfold w1History
        rw [hsP,hsQ]
        apply List.map_congr_left
        intro j hj
        have hjk : j < k := by simp only [List.mem_range] at hj; omega
        have jL : j < L := by dsimp [L,k] at *; omega
        let jf : Fin L := ⟨j % L, Nat.mod_lt _ (by omega)⟩
        have hji : jf ≠ ⟨k,hkL⟩ := by
          intro he
          have hval : jf.val = k := congrArg Fin.val he
          have hjeq : j = k := by
            dsimp [jf] at hval
            rw [Nat.mod_eq_of_lt jL] at hval
            exact hval
          exact (Nat.ne_of_lt hjk) hjeq
        have hslot := hsplit b₁ b₂ q jf hji
        change e.symm (b₁,q) jf = e.symm (b₂,q) jf
        exact hslot
      rw [hhist]
      exact hp
  have hselected : ∀ p q : Ω, E p → E q →
      w1Selected true i α ε o p = w1Selected true i α ε o q := by
    intro p q hp hq
    have hsP := hstart p hp
    have hsQ := hstart q hq
    have hhist : w1History true i α ε o p = w1History true i α ε o q := hp.trans hq.symm
    have hpoolPrefix : ∀ j : Fin L, j.val < k → p j = q j := by
      intro j hj
      have hjL : j.val < L := lt_trans hj hkL
      have hhist' : (List.range (s+i)).map
          (fun t => p ⟨t % L, Nat.mod_lt _ (by omega)⟩) =
          (List.range (s+i)).map
          (fun t => q ⟨t % L, Nat.mod_lt _ (by omega)⟩) := by
        simpa [w1History,hsP,hsQ] using hhist
      have hget := congrArg (fun xs : List B => xs[j.val]?) hhist'
      rw [List.getElem?_map, List.getElem?_map] at hget
      rw [List.getElem?_range (by omega)] at hget
      simp only [Option.map_some] at hget
      have hget' : p j = q j := by
        simpa [Nat.mod_eq_of_lt hjL] using Option.some.inj hget
      simpa using hget'
    let rP : AronowAudit.P003.Counts → ℕ → Bool := fun v j =>
      AronowAudit.P003.approximateReject α ε (toCounts (complementObserved o)) p v j
    let rQ : AronowAudit.P003.Counts → ℕ → Bool := fun v j =>
      AronowAudit.P003.approximateReject α ε (toCounts (complementObserved o)) q v j
    have hprefix : ∀ v j, j < s+i → rP v j = rQ v j := by
      intro v j hj
      have hloc := hdecAgree (complementObserved o) hpoolPrefix (fromCounts v) j
        (by simpa [k] using hj)
      have hpbridge := SAP.P003b.Bridge.approximateReject_eq α ε
        (complementObserved o) (fromCounts v) p j
      have hqbridge := SAP.P003b.Bridge.approximateReject_eq α ε
        (complementObserved o) (fromCounts v) q j
      simpa only [rP,rQ,to_from,complement_eq] using hpbridge.trans (hloc.trans hqbridge.symm)
    have hd := AronowAudit.P003.Wave1.GLP0032B6_upperRun_prefix
      (toCounts (complementObserved o)) rP rQ s i (by simpa using hprefix)
    have hlocal :
        ((upperRun true (complementObserved o) (approximateReject α ε (complementObserved o) p) s).trace[i]?).map Prod.fst =
        ((upperRun true (complementObserved o) (approximateReject α ε (complementObserved o) q) s).trace[i]?).map Prod.fst := by
      simpa only [AronowAudit.P003.Wave1.GLP0032B6_peek,upperRun_eq,toEndpoint,
        toTrace,List.getElem?_map,Option.map_map,Function.comp_def,rP,rQ,
        approximateReject_fn] using congrArg (Option.map fromCounts) hd.1
    simpa [w1Selected,w1Endpoint,hsP,hsQ] using hlocal
  let select : Ω → Option Counts := fun p =>
    ((upperRun true (complementObserved o)
      (approximateReject α ε (complementObserved o) p) s).trace[i]?).map Prod.fst
  have hfixedSelectPrefix {p q : Ω}
      (hpq : ∀ j : Fin L, j.val < k → p j = q j) : select p = select q := by
    let rP : AronowAudit.P003.Counts → ℕ → Bool := fun v j =>
      AronowAudit.P003.approximateReject α ε
        (toCounts (complementObserved o)) p v j
    let rQ : AronowAudit.P003.Counts → ℕ → Bool := fun v j =>
      AronowAudit.P003.approximateReject α ε
        (toCounts (complementObserved o)) q v j
    have hprefix : ∀ v j, j < s+i → rP v j = rQ v j := by
      intro v j hj
      have hloc := hdecAgree (complementObserved o) hpq (fromCounts v) j (by
        simpa [k] using hj)
      have hpbridge := SAP.P003b.Bridge.approximateReject_eq α ε
        (complementObserved o) (fromCounts v) p j
      have hqbridge := SAP.P003b.Bridge.approximateReject_eq α ε
        (complementObserved o) (fromCounts v) q j
      simpa only [rP,rQ,to_from,complement_eq] using hpbridge.trans (hloc.trans hqbridge.symm)
    have hd := AronowAudit.P003.Wave1.GLP0032B6_upperRun_prefix
      (toCounts (complementObserved o)) rP rQ s i (by simpa using hprefix)
    have hlocal :
        ((upperRun true (complementObserved o) (approximateReject α ε (complementObserved o) p) s).trace[i]?).map Prod.fst =
        ((upperRun true (complementObserved o) (approximateReject α ε (complementObserved o) q) s).trace[i]?).map Prod.fst := by
      simpa only [AronowAudit.P003.Wave1.GLP0032B6_peek,upperRun_eq,toEndpoint,
        toTrace,List.getElem?_map,Option.map_map,Function.comp_def,rP,rQ,
        approximateReject_fn] using congrArg (Option.map fromCounts) hd.1
    simpa only [select] using hlocal
  have hnext (p : Ω) (hp : E p) :
      w1NextBatch true i α ε o p = p ⟨k,hkL⟩ := by
    apply congrArg p
    apply Fin.ext
    simp [w1NextBatch,hstart p hp,k,L,Nat.mod_eq_of_lt hkL]
  have hselectFiber (p : Ω) (hp : E p) :
      select p = w1Selected true i α ε o p := by
    simp [select,w1Selected,w1Endpoint,hstart p hp]
  have hinvS : ∀ b₁ b₂ (q : {j : Fin L // j ≠ ⟨k,hkL⟩} → B),
      select (e.symm (b₁,q)) = select (e.symm (b₂,q)) := by
    intro b₁ b₂ q
    have hpref : ∀ j : Fin L, j.val < k →
        e.symm (b₁,q) j = e.symm (b₂,q) j := by
      intro j hj
      have hji : j ≠ ⟨k,hkL⟩ := by
        intro he
        have : j.val = k := congrArg Fin.val he
        omega
      exact hsplit b₁ b₂ q j hji
    exact hfixedSelectPrefix hpref
  have hcompM : (complementObserved o).a+(complementObserved o).b = m := by
    simpa [complementObserved,Nat.add_comm] using hm
  have hdelta : 0 ≤ Real.exp (-2*(K : ℝ)*ε^2) := (Real.exp_pos _).le
  have hbadBound (badReject : Bool) :
      ∀ v : Counts,
        uniformProb (fun b : B =>
          if v.total = n then
            if badReject then
              α ≤ (pValue v (complementObserved o) : ℝ) ∧
                (monteMean v (complementObserved o) (fun z => (b z).val) : ℝ)+ε < α
            else
              (pValue v (complementObserved o) : ℝ) < α-2*ε ∧
                α ≤ (monteMean v (complementObserved o) (fun z => (b z).val) : ℝ)+ε
          else False) ≤ Real.exp (-2*(K : ℝ)*ε^2) := by
    intro v
    by_cases hv : v.total = n
    · have hfix := AronowAudit.P003.Wave1.GLP0032B6_fixed_errors
        (toCounts (complementObserved o)) (toCounts v) α ε
        (by simpa using hv) (by simpa using hcompM) hmn hK hε.1.le
      cases badReject
      · simpa [hv,SAP.P003b.Bridge.uniformProb_eq,SAP.P003b.Bridge.pValue_eq,
          SAP.P003b.Bridge.monteMean_eq] using hfix.2
      · simpa [hv,SAP.P003b.Bridge.uniformProb_eq,SAP.P003b.Bridge.pValue_eq,
          SAP.P003b.Bridge.monteMean_eq] using hfix.1
    · simpa [hv,uniformProb] using hdelta
  have hprobError (badReject : Bool) :
      uniformProb (fun p : Ω => E p ∧ w1Error true badReject i α ε o p) /
        uniformProb E ≤ Real.exp (-2*(K : ℝ)*ε^2) := by
    let bad : Counts → B → Prop := fun v b =>
      if v.total = n then
        if badReject then
          α ≤ (pValue v (complementObserved o) : ℝ) ∧
            (monteMean v (complementObserved o) (fun z => (b z).val) : ℝ)+ε < α
        else
          (pValue v (complementObserved o) : ℝ) < α-2*ε ∧
            α ≤ (monteMean v (complementObserved o) (fun z => (b z).val) : ℝ)+ε
      else False
    haveI : Nonempty Counts := ⟨⟨0,0,0,0⟩⟩
    have hcb := SAP.P003b.WH.W1.P.T7_L3.conditional_slot_bound
      (B:=B) (T:=Counts) (i:=⟨k,hkL⟩)
      e E select bad (Real.exp (-2*(K : ℝ)*ε^2)) hinvE hinvS hcoord
      (by simpa [bad] using hbadBound badReject) hposE
    have hinc : ∀ p : Ω, E p → w1Error true badReject i α ε o p →
        E p ∧ ∃ v, select p = some v ∧ bad v (p ⟨k,hkL⟩) := by
      intro p hpE herr
      rcases herr with ⟨v,htrace,hvalue⟩
      have hsP := hstart p hpE
      have htraceLocal :
          (upperRun true (complementObserved o)
            (approximateReject α ε (complementObserved o) p) s).trace[i]? =
              some (v,badReject) := by
        simpa [w1Endpoint,hsP] using htrace
      have hsel : select p = some v := by
        simp [select,htraceLocal]
      let rr : AronowAudit.P003.Counts → ℕ → Bool := fun u j =>
        AronowAudit.P003.approximateReject α ε
          (toCounts (complementObserved o)) p u j
      have htraceD :
          (AronowAudit.P003.upperRun true (toCounts (complementObserved o)) rr s).trace[i]? =
            some (toCounts v,badReject) := by
        simpa only [SAP.P003b.Bridge.upperRun_eq,toEndpoint,toTrace,rr,
          SAP.P003b.Bridge.approximateReject_fn,List.getElem?_map,Option.map_some] using
          congrArg (Option.map toTrace) htraceLocal
      have hreplyD := AronowAudit.P003.Wave1.GLP0032B6_upperRun_reply
        (toCounts (complementObserved o)) rr s i (toCounts v) badReject htraceD
      have hreply :
          approximateReject α ε (complementObserved o) p v (s+i) = badReject := by
        simpa only [rr,SAP.P003b.Bridge.approximateReject_eq,SAP.P003b.Bridge.to_from]
          using hreplyD
      have hpossible := AronowAudit.P003.Wave1.GLP0032B6_upperRun_trace_possible
        (toCounts (complementObserved o)) rr s (toCounts v) badReject
        (List.mem_of_getElem? htraceD)
      have hvtotal : v.total = n := by
        have htf := (AronowAudit.P003.possible_table_facts
          (toCounts (complementObserved o)) (toCounts v) hpossible).1
        have hvcomp : v.total = (complementObserved o).total := by simpa using htf
        calc
          v.total = (complementObserved o).total := hvcomp
          _ = o.total := by simp [complementObserved,Counts.total,Nat.add_comm,
            Nat.add_left_comm,Nat.add_assoc]
          _ = n := ht
      have hbatch : batch p (s+i) = fun z => (p ⟨k,hkL⟩ z).val := by
        funext z
        simp [batch,k,L,Nat.mod_eq_of_lt hkL]
      have hbad : bad v (p ⟨k,hkL⟩) := by
        cases badReject
        · simp at hvalue
          change decide ((monteMean v (complementObserved o)
            (batch p (s+i)) : ℝ)+ε < α) = false at hreply
          have hnot : ¬ ((monteMean v (complementObserved o)
              (batch p (s+i)) : ℝ)+ε < α) := by
            intro hlt
            have htrue : decide ((monteMean v (complementObserved o)
                (batch p (s+i)) : ℝ)+ε < α) = true := decide_eq_true hlt
            rw [hreply] at htrue
            cases htrue
          have hle := le_of_not_gt hnot
          have hbad' : (pValue v (complementObserved o) : ℝ) < α-2*ε ∧
              α ≤ (monteMean v (complementObserved o)
                (fun z => (p ⟨k,hkL⟩ z).val) : ℝ)+ε := by
            exact ⟨hvalue,by simpa [hbatch] using hle⟩
          simpa [bad,hvtotal] using hbad'
        · simp at hvalue
          change decide ((monteMean v (complementObserved o)
            (batch p (s+i)) : ℝ)+ε < α) = true at hreply
          have hlt := of_decide_eq_true hreply
          have hbad' : α ≤ (pValue v (complementObserved o) : ℝ) ∧
              (monteMean v (complementObserved o)
                (fun z => (p ⟨k,hkL⟩ z).val) : ℝ)+ε < α := by
            exact ⟨hvalue,by simpa [hbatch] using hlt⟩
          simpa [bad,hvtotal] using hbad'
      exact ⟨hpE,v,hsel,by simpa [bad] using hbad⟩
    have hnum : uniformProb (fun p : Ω => E p ∧ w1Error true badReject i α ε o p) ≤
        uniformProb (fun p : Ω => E p ∧ ∃ v, select p = some v ∧ bad v (p ⟨k,hkL⟩)) := by
      apply AronowAudit.P003.Wave1.GLP0032B6_prob_mono
      intro p hp
      exact hinc p hp.1 hp.2
    have hratio :
        uniformProb (fun p : Ω => E p ∧ w1Error true badReject i α ε o p) /
          uniformProb E ≤
        uniformProb (fun p : Ω => E p ∧ ∃ v, select p = some v ∧ bad v (p ⟨k,hkL⟩)) /
          uniformProb E := div_le_div_of_nonneg_right hnum hposE.le
    exact hratio.trans (by simpa [bad] using hcb)
  refine ⟨?_, ?_, ?_⟩
  · intro p q hp hq
    exact ⟨(hstart p hp).trans (hstart q hq).symm,hselected p q hp hq⟩
  · intro b
    have hlaw := SAP.P003b.WH.W1.P.T7_L3.conditional_slot_law
      (B:=B) (i:=⟨k,hkL⟩) e E hinvE hcoord hposE b
    have hpred : (fun p : Ω => E p ∧ w1NextBatch true i α ε o p = b) =
        fun p => E p ∧ p ⟨k,hkL⟩ = b := by
      funext p
      apply propext
      constructor
      · intro hp
        exact ⟨hp.1,(hnext p hp.1).symm.trans hp.2⟩
      · intro hp
        exact ⟨hp.1,(hnext p hp.1).trans hp.2⟩
    rw [hpred]
    exact hlaw
  · intro badReject
    exact hprobError badReject
