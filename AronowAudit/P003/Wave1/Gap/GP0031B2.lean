import AronowAudit.P003.P003_Audit
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.ConditionallyCompleteLattice.Finset



namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-! Fixed-stratum counts. -/

lemma corrected_stratum_count_randomStates_iff (v q : Counts) (m : ℕ) :
    q ∈ randomStates v m ↔
      q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = m := by
  constructor
  · exact random_state_facts v m q
  · rintro ⟨ha, hb, hc, hd, ht⟩
    have hs : q.a + q.b + q.c + q.d = m := ht
    simp only [randomStates, List.mem_flatMap, List.mem_filterMap, List.mem_range]
    refine ⟨q.a, ?_, q.b, ?_, q.c, ?_, ?_⟩
    · exact Nat.lt_succ_of_le (le_min ha (by omega))
    · exact Nat.lt_succ_of_le (le_min hb (by omega))
    · exact Nat.lt_succ_of_le (le_min hc (by omega))
    · have he : m-q.a-q.b-q.c = q.d := by omega
      simp only [he, if_pos hd]

lemma corrected_stratum_count_mem (n : ℕ) (v : Counts) :
    v ∈ allCounts n ↔ v.total = n := by
  rw [allCounts, List.mem_toFinset, corrected_stratum_count_randomStates_iff]
  change (v.a ≤ n ∧ v.b ≤ n ∧ v.c ≤ n ∧ v.d ≤ n ∧ v.total = n) ↔ _
  constructor
  · exact fun h => h.2.2.2.2
  · intro ht
    dsimp [Counts.total] at ht
    exact ⟨by omega, by omega, by omega, by omega, ht⟩

private def corrected_stratum_count_unpack (v : Counts) : Bool × Bool → ℕ :=
  fun u => if u.1 then (if u.2 then v.a else v.b)
    else (if u.2 then v.c else v.d)

private def corrected_stratum_count_pack (f : Bool × Bool → ℕ) : Counts :=
  ⟨f (true,true), f (true,false), f (false,true), f (false,false)⟩

private lemma corrected_stratum_count_pack_unpack (v : Counts) :
    corrected_stratum_count_pack (corrected_stratum_count_unpack v) = v := by
  cases v
  rfl

private lemma corrected_stratum_count_unpack_pack (f : Bool × Bool → ℕ) :
    corrected_stratum_count_unpack (corrected_stratum_count_pack f) = f := by
  funext u
  rcases u with ⟨a,b⟩
  cases a <;> cases b <;> rfl

private lemma corrected_stratum_count_sum_unpack (v : Counts) :
    (∑ u, corrected_stratum_count_unpack v u) = v.total := by
  simp [Fintype.sum_prod_type, Fintype.sum_bool,
    corrected_stratum_count_unpack, Counts.total, add_assoc]

private lemma corrected_stratum_count_total_pack (f : Bool × Bool → ℕ) :
    (corrected_stratum_count_pack f).total = ∑ u, f u := by
  simp [Fintype.sum_prod_type, Fintype.sum_bool,
    corrected_stratum_count_pack, Counts.total, add_assoc]

/-- Four-colour weak compositions, with the finite carrier supplied by the
actual `allCounts` enumeration rather than by a new model. -/
noncomputable def corrected_stratum_count_sym_equiv (n : ℕ) :
    ↥(allCounts n) ≃ Sym (Bool × Bool) n := by
  let e : ↥(allCounts n) ≃ {f : Bool × Bool → ℕ // ∑ u, f u = n} :=
    { toFun := fun v => ⟨corrected_stratum_count_unpack v.val, by
        rw [corrected_stratum_count_sum_unpack]
        exact (corrected_stratum_count_mem n v.val).mp v.property⟩
      invFun := fun f => ⟨corrected_stratum_count_pack f.val, by
        rw [corrected_stratum_count_mem, corrected_stratum_count_total_pack]
        exact f.property⟩
      left_inv := fun v => Subtype.ext (corrected_stratum_count_pack_unpack v.val)
      right_inv := fun f => Subtype.ext (corrected_stratum_count_unpack_pack f.val) }
  exact e.trans (Sym.equivNatSumOfFintype (Bool × Bool) n).symm

lemma corrected_stratum_count_card (n : ℕ) :
    (allCounts n).card = (n+3).choose 3 := by
  have he := Fintype.card_congr (corrected_stratum_count_sym_equiv n)
  rw [Fintype.card_coe, Sym.card_sym_eq_choose] at he
  have hc : Fintype.card (Bool × Bool) = 4 := by decide
  rw [hc] at he
  have ha : 4+n-1 = n+3 := by omega
  rw [ha] at he
  calc
    (allCounts n).card = (n+3).choose n := he
    _ = (n+3).choose 3 := by
      have h := Nat.choose_symm (show n ≤ n+3 by omega)
      simpa using h.symm

/-- Split the eight coordinates into two genuine four-cell vectors. The
index remembers the first vector's total, so no multiplicity is introduced. -/
noncomputable def corrected_stratum_count_eight_equiv (n : ℕ) :
    (Σ r : Fin (n+1), ↥(allCounts r.val) × ↥(allCounts (n-r.val))) ≃
      Sym ((Bool × Bool) ⊕ (Bool × Bool)) n := by
  let e : (Σ r : Fin (n+1), ↥(allCounts r.val) × ↥(allCounts (n-r.val))) ≃
      {f : ((Bool × Bool) ⊕ (Bool × Bool)) → ℕ // ∑ u, f u = n} :=
    { toFun := fun x =>
        ⟨Sum.elim (corrected_stratum_count_unpack x.2.1.val)
          (corrected_stratum_count_unpack x.2.2.val), by
          rw [Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr]
          rw [corrected_stratum_count_sum_unpack,
            corrected_stratum_count_sum_unpack,
            (corrected_stratum_count_mem _ _).mp x.2.1.property,
            (corrected_stratum_count_mem _ _).mp x.2.2.property]
          omega⟩
      invFun := fun f => by
        let v₀ := corrected_stratum_count_pack (fun u => f.val (.inl u))
        let v₁ := corrected_stratum_count_pack (fun u => f.val (.inr u))
        have ht : v₀.total + v₁.total = n := by
          dsimp [v₀, v₁]
          rw [corrected_stratum_count_total_pack, corrected_stratum_count_total_pack]
          simpa only [Fintype.sum_sum_type] using f.property
        refine ⟨⟨v₀.total, by omega⟩, ⟨v₀, ?_⟩, ⟨v₁, ?_⟩⟩
        · exact (corrected_stratum_count_mem _ _).mpr rfl
        · apply (corrected_stratum_count_mem _ _).mpr
          dsimp
          omega
      left_inv := by
        intro x
        rcases x with ⟨r,v₀,v₁⟩
        have ht₀ := (corrected_stratum_count_mem _ _).mp v₀.property
        -- All dependent casts here concern proof fields and the recovered index.
        dsimp
        simp only [Sum.elim_inl, Sum.elim_inr,
          corrected_stratum_count_pack_unpack]
        cases v₀ with
        | mk v₀ hv₀ =>
          cases v₁ with
          | mk v₁ hv₁ =>
            dsimp at ht₀
            cases r with
            | mk r hr =>
              dsimp at ht₀
              subst r
              rfl
      right_inv := by
        intro f
        apply Subtype.ext
        funext u
        cases u with
        | inl u =>
          change corrected_stratum_count_unpack
            (corrected_stratum_count_pack (fun u => f.val (.inl u))) u = _
          rw [corrected_stratum_count_unpack_pack]
        | inr u =>
          change corrected_stratum_count_unpack
            (corrected_stratum_count_pack (fun u => f.val (.inr u))) u = _
          rw [corrected_stratum_count_unpack_pack] }
  exact e.trans
    (Sym.equivNatSumOfFintype ((Bool × Bool) ⊕ (Bool × Bool)) n).symm

lemma corrected_stratum_count_eight_sum (n : ℕ) :
    (∑ r ∈ Finset.range (n+1), (r+3).choose 3 * (n-r+3).choose 3) =
      (n+7).choose 7 := by
  have he := Fintype.card_congr (corrected_stratum_count_eight_equiv n)
  rw [Fintype.card_sigma] at he
  simp only [Fintype.card_prod, Fintype.card_coe,
    corrected_stratum_count_card] at he
  rw [Sym.card_sym_eq_choose] at he
  have hc : Fintype.card ((Bool × Bool) ⊕ (Bool × Bool)) = 8 := by decide
  rw [hc, show 8+n-1 = n+7 by omega] at he
  have hsum : (∑ r : Fin (n+1), (r.val+3).choose 3 * (n-r.val+3).choose 3) =
      ∑ r ∈ Finset.range (n+1), (r+3).choose 3 * (n-r+3).choose 3 := by
    exact Fin.sum_univ_eq_sum_range
      (fun r => (r+3).choose 3 * (n-r+3).choose 3) (n+1)
  rw [hsum] at he
  calc
    _ = (n+7).choose n := he
    _ = (n+7).choose 7 := by
      have h := Nat.choose_symm (show n ≤ n+7 by omega)
      simpa using h.symm

lemma corrected_stratum_count_choose_three (k : ℕ) :
    ((k+3).choose 3 : ℝ) = ((k : ℝ)+3)*((k : ℝ)+2)*((k : ℝ)+1)/6 := by
  have hN : (k+3)*(k+2)*(k+1) = 6 * (k+3).choose 3 := by
    simpa [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial,
      Nat.add_assoc, Nat.mul_assoc] using (Nat.ascFactorial_eq_factorial_mul_choose k 3)
  have hR : ((k : ℝ)+3)*((k : ℝ)+2)*((k : ℝ)+1) =
      6 * ((k+3).choose 3 : ℝ) := by
    exact_mod_cast hN
  linarith

lemma corrected_stratum_count_cubic_bound (k n : ℕ) (hkn : k ≤ n) :
    ((k+3).choose 3 : ℝ) ≤ ((n : ℝ)+3)^3/6 := by
  rw [corrected_stratum_count_choose_three]
  have hR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have h₀ : 0 ≤ (k : ℝ)+1 := by positivity
  have h₁ : 0 ≤ (k : ℝ)+2 := by positivity
  have h₂ : 0 ≤ (k : ℝ)+3 := by positivity
  have hn : 0 ≤ (n : ℝ)+3 := by positivity
  have hprod : ((k : ℝ)+3)*((k : ℝ)+2)*((k : ℝ)+1) ≤
      ((n : ℝ)+3)*((n : ℝ)+3)*((n : ℝ)+3) := by
    apply mul_le_mul
    · exact mul_le_mul (by linarith) (by linarith) h₁ hn
    · linarith
    · exact h₀
    · positivity
  nlinarith

theorem corrected_stratum_count_proof (N₀ N₁ : ℕ) :
    (∀ v ∈ stratifiedCounts N₀ N₁, v.1.total = N₀ ∧ v.2.total = N₁) ∧
    (stratifiedCounts N₀ N₁).card = (N₀+3).choose 3 * (N₁+3).choose 3 ∧
    ((stratifiedCounts N₀ N₁).card : ℝ) ≤ ((N₀+N₁+3 : ℕ) : ℝ)^6/36 ∧
    (allCounts (N₀+N₁)).card = (N₀+N₁+3).choose 3 ∧
    (∑ r ∈ Finset.range (N₀+N₁+1), (r+3).choose 3 * (N₀+N₁-r+3).choose 3) =
      (N₀+N₁+7).choose 7 := by
  have hcard : (stratifiedCounts N₀ N₁).card =
      (N₀+3).choose 3 * (N₁+3).choose 3 := by
    rw [stratifiedCounts, show (allCounts N₀).product (allCounts N₁) =
      allCounts N₀ ×ˢ allCounts N₁ from rfl, Finset.card_product,
      corrected_stratum_count_card, corrected_stratum_count_card]
  refine ⟨?_, hcard, ?_, corrected_stratum_count_card _,
    corrected_stratum_count_eight_sum _⟩
  · intro v hv
    obtain ⟨h₀,h₁⟩ := Finset.mem_product.mp hv
    exact ⟨(corrected_stratum_count_mem _ _).mp h₀,
      (corrected_stratum_count_mem _ _).mp h₁⟩
  · rw [hcard, Nat.cast_mul]
    have h₀ := corrected_stratum_count_cubic_bound N₀ (N₀+N₁) (by omega)
    have h₁ := corrected_stratum_count_cubic_bound N₁ (N₀+N₁) (by omega)
    have hprod := mul_le_mul h₀ h₁ (Nat.cast_nonneg ((N₁+3).choose 3))
      (show (0 : ℝ) ≤ ((↑(N₀+N₁) : ℝ)+3)^3/6 by positivity)
    calc
      _ ≤ (((↑(N₀+N₁) : ℝ)+3)^3/6)^2 := by simpa only [pow_two] using hprod
      _ = _ := by push_cast; ring

/-! Guarded outcome complementation.

The outcome-complementation p-value identity requires equality of the table totals.
-/

def balanced_completion_inclusion_reverse (v : Counts) : Counts :=
  ⟨v.d, v.c, v.b, v.a⟩

lemma balanced_completion_inclusion_reverse_reverse (v : Counts) :
    balanced_completion_inclusion_reverse (balanced_completion_inclusion_reverse v) = v := by
  cases v
  rfl

lemma balanced_completion_inclusion_complement_complement (o : Counts) :
    complementObserved (complementObserved o) = o := by
  cases o
  rfl

lemma balanced_completion_inclusion_reverse_total (v : Counts) :
    (balanced_completion_inclusion_reverse v).total = v.total := by
  dsimp [balanced_completion_inclusion_reverse, Counts.total]
  omega


lemma balanced_completion_inclusion_reverse_effect (v : Counts) :
    (balanced_completion_inclusion_reverse v).effect = -v.effect := by
  dsimp [balanced_completion_inclusion_reverse, Counts.effect]
  ring

lemma balanced_completion_inclusion_reverse_tau (v : Counts) :
    tau (balanced_completion_inclusion_reverse v) = -tau v := by
  have hQ : tauQ (balanced_completion_inclusion_reverse v) = -tauQ v := by
    unfold tauQ
    rw [balanced_completion_inclusion_reverse_total,
      balanced_completion_inclusion_reverse_effect]
    push_cast
    ring
  simpa only [tau, Rat.cast_neg] using congrArg (fun x : ℚ => (x : ℝ)) hQ


lemma balanced_completion_inclusion_possible_forward (o v : Counts)
    (hv : Possible o v) :
    Possible (complementObserved o) (balanced_completion_inclusion_reverse v) := by
  simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map,
    List.mem_range] at hv ⊢
  rcases hv with ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩
  dsimp [complementObserved]
  refine ⟨o.b-j, by omega, o.a-i, by omega,
    o.d-l, by omega, o.c-k, by omega, ?_⟩
  ext <;> dsimp [balanced_completion_inclusion_reverse] <;> omega


/-- A generic disjointness argument used only to certify that the concrete
random-state list contains each state once. -/
private lemma balanced_completion_inclusion_flatMap_nodup
    {A B : Type*} (xs : List A) (f : A → List B) (g : B → A)
    (hx : xs.Nodup) (hf : ∀ a ∈ xs, (f a).Nodup)
    (hg : ∀ a ∈ xs, ∀ b ∈ f a, g b = a) : (xs.flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨hf, ?_⟩
  -- Strengthen the pairwise relation only on members of the source list.
  apply (List.pairwise_iff_getElem).mpr
  intro i j hi hj hij
  intro b hbi hbj
  have hgi := hg xs[i] (List.getElem_mem hi) b hbi
  have hgj := hg xs[j] (List.getElem_mem hj) b hbj
  have he : xs[i] = xs[j] := hgi.symm.trans hgj
  have hidx : i = j := (List.Nodup.getElem_inj_iff hx).mp he
  omega

lemma balanced_completion_inclusion_randomStates_nodup (v : Counts) (m : ℕ) :
    (randomStates v m).Nodup := by
  let inner (a b : ℕ) : List Counts :=
    (List.range (min v.c (m-a-b)+1)).filterMap fun c =>
      if m-a-b-c ≤ v.d then some ⟨a,b,c,m-a-b-c⟩ else none
  have hinner (a b : ℕ) : (inner a b).Nodup := by
    apply List.Nodup.filterMap (l := List.range (min v.c (m-a-b)+1))
      (f := fun c => if m-a-b-c ≤ v.d then some (⟨a,b,c,m-a-b-c⟩ : Counts) else none)
      ?_ List.nodup_range
    intro c c' q hc hc'
    split_ifs at hc hc' with h1 h2
    · simp only [Option.mem_def, Option.some.injEq] at hc hc'
      exact (Counts.mk.inj (hc.trans hc'.symm)).2.2.1
    all_goals simp_all
  have hinner_coords (a b : ℕ) (q : Counts) (hq : q ∈ inner a b) :
      q.a = a ∧ q.b = b := by
    simp only [inner, List.mem_filterMap] at hq
    obtain ⟨c,hc,hret⟩ := hq
    split_ifs at hret with hd
    · simp only [Option.some.injEq] at hret
      subst q
      exact ⟨rfl,rfl⟩
  let middle (a : ℕ) : List Counts :=
    (List.range (min v.b (m-a)+1)).flatMap (inner a)
  have hmiddle (a : ℕ) : (middle a).Nodup := by
    apply balanced_completion_inclusion_flatMap_nodup _ (inner a) Counts.b
      List.nodup_range (fun b _ => hinner a b)
    intro b hb q hq
    exact (hinner_coords a b q hq).2
  have hmiddle_coord (a : ℕ) (q : Counts) (hq : q ∈ middle a) : q.a = a := by
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    exact (hinner_coords a b q hq).1
  change ((List.range (min v.a m+1)).flatMap middle).Nodup
  apply balanced_completion_inclusion_flatMap_nodup _ middle Counts.a
    List.nodup_range (fun a _ => hmiddle a)
  intro a ha q hq
  exact hmiddle_coord a q hq

lemma balanced_completion_inclusion_reverse_state (v q : Counts) (m : ℕ)
    (hq : q ∈ randomStates v m) :
    balanced_completion_inclusion_reverse q ∈
      randomStates (balanced_completion_inclusion_reverse v) m := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  apply (corrected_stratum_count_randomStates_iff _ _ _).mpr
  exact ⟨hd,hc,hb,ha, by rw [balanced_completion_inclusion_reverse_total, ht]⟩

lemma balanced_completion_inclusion_reverse_observed (v q : Counts)
    (ha : q.a ≤ v.a) (hb : q.b ≤ v.b) (hc : q.c ≤ v.c) (hd : q.d ≤ v.d) :
    observed (balanced_completion_inclusion_reverse v)
      (balanced_completion_inclusion_reverse q) = complementObserved (observed v q) := by
  ext <;> dsimp [observed, balanced_completion_inclusion_reverse, complementObserved] <;> omega

lemma balanced_completion_inclusion_reverse_multiplicity (v q : Counts) :
    multiplicity (balanced_completion_inclusion_reverse v)
      (balanced_completion_inclusion_reverse q) = multiplicity v q := by
  dsimp [multiplicity, balanced_completion_inclusion_reverse]
  ring

lemma balanced_completion_inclusion_complement_deviation (v o : Counts)
    (hn : v.total = o.total) :
    deviationNumerator (balanced_completion_inclusion_reverse v)
      (complementObserved o) (o.a+o.b) = -deviationNumerator v o (o.a+o.b) := by
  have hZ : (v.total : ℤ) = (o.a : ℤ)+o.b+o.c+o.d := by
    exact_mod_cast hn
  unfold deviationNumerator
  rw [balanced_completion_inclusion_reverse_total,
    balanced_completion_inclusion_reverse_effect]
  dsimp [complementObserved]
  push_cast
  rw [hZ]
  ring

/-- The outcome-complementation p-value identity requires equal table totals,
even when both observed arms are positive. -/
lemma balanced_completion_inclusion_complement_pValue (v o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hn : v.total = o.total) :
    pValue (⟨v.d,v.c,v.b,v.a⟩ : Counts) (complementObserved o) = pValue v o := by
  change pValue (balanced_completion_inclusion_reverse v) (complementObserved o) = _
  have hm : (complementObserved o).a+(complementObserved o).b = o.a+o.b := by
    dsimp [complementObserved]
    omega
  have htail : tailCount (balanced_completion_inclusion_reverse v) (complementObserved o) =
      tailCount v o := by
    unfold tailCount
    rw [hm]
    rw [← List.sum_toFinset _ (balanced_completion_inclusion_randomStates_nodup _ _),
      ← List.sum_toFinset _ (balanced_completion_inclusion_randomStates_nodup _ _)]
    symm
    apply Finset.sum_nbij' balanced_completion_inclusion_reverse
      balanced_completion_inclusion_reverse
    · intro q hq
      exact List.mem_toFinset.mpr (balanced_completion_inclusion_reverse_state _ _ _
        (List.mem_toFinset.mp hq))
    · intro q hq
      have h := balanced_completion_inclusion_reverse_state _ _ _ (List.mem_toFinset.mp hq)
      simpa only [balanced_completion_inclusion_reverse_reverse, List.mem_toFinset] using h
    · intro q hq
      exact balanced_completion_inclusion_reverse_reverse q
    · intro q hq
      exact balanced_completion_inclusion_reverse_reverse q
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
      rw [balanced_completion_inclusion_reverse_observed v q ha hb hc hd,
        balanced_completion_inclusion_reverse_multiplicity]
      have hdev := balanced_completion_inclusion_complement_deviation v (observed v q) hobs
      rw [hmq] at hdev
      rw [hdev, balanced_completion_inclusion_complement_deviation v o hn,
        Int.natAbs_neg, Int.natAbs_neg]
  unfold pValue
  rw [htail, balanced_completion_inclusion_reverse_total, hm]

lemma balanced_completion_inclusion_accepted_spec (α : ℝ) (o : Counts) (t : ℝ) :
    t ∈ accepted α o ↔ ∃ v, Possible o v ∧ α ≤ (pValue v o : ℝ) ∧ tau v = t := by
  simp only [accepted, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq, Possible, exists_prop, and_assoc]

/-- Acceptance is transported through the possibility bijection. Every
p-value call gets its total equality from the actual possible-table witness. -/
lemma balanced_completion_inclusion_complement_accepted (α : ℝ) (o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) :
    accepted α (complementObserved o) = (accepted α o).image (fun t => -t) := by
  have hoC : 0 < (complementObserved o).a+(complementObserved o).b ∧
      0 < (complementObserved o).c+(complementObserved o).d := by
    dsimp [complementObserved]
    constructor <;> omega
  ext t
  constructor
  · intro ht
    obtain ⟨v,hv,hp,rfl⟩ := (balanced_completion_inclusion_accepted_spec _ _ _).mp ht
    have hn : v.total = (complementObserved o).total := (possible_table_facts _ _ hv).1
    have hvC := balanced_completion_inclusion_possible_forward _ _ hv
    rw [balanced_completion_inclusion_complement_complement] at hvC
    have hpC := balanced_completion_inclusion_complement_pValue v (complementObserved o) hoC hn
    rw [balanced_completion_inclusion_complement_complement] at hpC
    have hacc : tau (balanced_completion_inclusion_reverse v) ∈ accepted α o := by
      apply accepted_of_possible _ _ _ hvC
      change α ≤ ((pValue (⟨v.d,v.c,v.b,v.a⟩ : Counts) o : ℚ) : ℝ)
      rw [hpC]
      exact hp
    apply Finset.mem_image.mpr
    exact ⟨_,hacc,by rw [balanced_completion_inclusion_reverse_tau, neg_neg]⟩
  · intro ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v,hv,hp,rfl⟩ := (balanced_completion_inclusion_accepted_spec _ _ _).mp hs
    have hn : v.total = o.total := (possible_table_facts _ _ hv).1
    rw [← balanced_completion_inclusion_reverse_tau]
    apply accepted_of_possible _ _ _ (balanced_completion_inclusion_possible_forward _ _ hv)
    change α ≤ ((pValue (⟨v.d,v.c,v.b,v.a⟩ : Counts) (complementObserved o) : ℚ) : ℝ)
    rw [balanced_completion_inclusion_complement_pValue v o ho hn]
    exact hp


lemma balanced_completion_inclusion_complement_upper (α : ℝ) (o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hne : (accepted α o).Nonempty) :
    upper α (complementObserved o) = -lower α o := by
  change sSup (↑(accepted α (complementObserved o)) : Set ℝ) = _
  apply IsGreatest.csSup_eq
  constructor
  · rw [balanced_completion_inclusion_complement_accepted α o ho]
    exact Finset.mem_image.mpr ⟨lower α o, hne.csInf_mem, rfl⟩
  · intro t ht
    rw [balanced_completion_inclusion_complement_accepted α o ho] at ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    apply neg_le_neg
    exact csInf_le (accepted α o).finite_toSet.bddBelow hs


/-! Balanced design arms. -/

lemma balanced_missing_coverage_observed_arms (v : Counts) (m : ℕ)
    (hn : v.total = 2*m) (q : Counts) (hq : q ∈ randomStates v m) :
    (observed v q).a+(observed v q).b = m ∧
      (observed v q).c+(observed v q).d = m := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  dsimp [observed]
  dsimp [Counts.total] at hn ht
  constructor <;> omega

/-! Relabelling leaves the distribution unchanged. -/

lemma count_distribution_invariance_fiber_card {n : ℕ}
    (w w' : PotentialTable n) (hc : tableCounts w = tableCounts w')
    (u : Bool × Bool) :
    Fintype.card {i : Fin n // w i = u} =
      Fintype.card {i : Fin n // w' i = u} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  rcases u with ⟨a,b⟩
  cases a <;> cases b
  · exact congrArg Counts.d hc
  · exact congrArg Counts.c hc
  · exact congrArg Counts.b hc
  · exact congrArg Counts.a hc

noncomputable def count_distribution_invariance_label_equiv {n : ℕ}
    (w w' : PotentialTable n) (hc : tableCounts w = tableCounts w') :
    Fin n ≃ Fin n :=
  Equiv.ofFiberEquiv (fun u =>
    Fintype.equivOfCardEq (count_distribution_invariance_fiber_card w w' hc u))

lemma count_distribution_invariance_label_property {n : ℕ}
    (w w' : PotentialTable n) (hc : tableCounts w = tableCounts w') (i : Fin n) :
    w' (count_distribution_invariance_label_equiv w w' hc i) = w i := by
  exact Equiv.ofFiberEquiv_map
    (fun u => Fintype.equivOfCardEq
      (count_distribution_invariance_fiber_card w w' hc u)) i

def count_distribution_invariance_assignment_equiv {n : ℕ}
    (m : ℕ) (π : Fin n ≃ Fin n) : Assignment n m ≃ Assignment n m where
  toFun z := ⟨z.val.map π.toEmbedding, by rw [Finset.card_map]; exact z.property⟩
  invFun z := ⟨z.val.map π.symm.toEmbedding, by rw [Finset.card_map]; exact z.property⟩
  left_inv z := by
    apply Subtype.ext
    simp [Finset.map_map]
  right_inv z := by
    apply Subtype.ext
    simp [Finset.map_map]

lemma count_distribution_invariance_estimator {n : ℕ}
    (w w' : PotentialTable n) (π : Fin n ≃ Fin n)
    (hπ : ∀ i, w' (π i) = w i) (z : Finset (Fin n)) :
    tableEstimator w' (z.map π.toEmbedding) = tableEstimator w z := by
  have hmem (i : Fin n) : π i ∈ z.map π.toEmbedding ↔ i ∈ z := by simp
  have hT : (∑ i, if i ∈ z then bit (w i).1 else 0) =
      ∑ j, if j ∈ z.map π.toEmbedding then bit (w' j).1 else 0 := by
    apply Fintype.sum_equiv π
    intro i
    simp only [hmem i, hπ i]
  have hC : (∑ i, if i ∈ z then 0 else bit (w i).2) =
      ∑ j, if j ∈ z.map π.toEmbedding then 0 else bit (w' j).2 := by
    apply Fintype.sum_equiv π
    intro i
    simp only [hmem i, hπ i]
  unfold tableEstimator
  rw [Finset.card_map, ← hT, ← hC]

lemma count_distribution_invariance_level_card {n : ℕ} (m : ℕ)
    (w w' : PotentialTable n) (hc : tableCounts w = tableCounts w') (t : ℝ) :
    (Finset.univ.filter fun z : Assignment n m => tableEstimator w z.val = t).card =
      (Finset.univ.filter fun z : Assignment n m => tableEstimator w' z.val = t).card := by
  let π := count_distribution_invariance_label_equiv w w' hc
  let e := count_distribution_invariance_assignment_equiv m π
  have hπ : ∀ i, w' (π i) = w i :=
    count_distribution_invariance_label_property w w' hc
  have hE (z : Assignment n m) : tableEstimator w' (e z).val =
      tableEstimator w z.val := by
    exact count_distribution_invariance_estimator w w' π hπ z.val
  let e' : {z : Assignment n m // tableEstimator w z.val = t} ≃
      {z : Assignment n m // tableEstimator w' z.val = t} :=
    e.subtypeEquiv (fun z => by rw [hE z])
  have hcard := Fintype.card_congr e'
  simpa only [Fintype.card_subtype] using hcard

theorem count_distribution_invariance_proof {n : ℕ} (m : ℕ)
    (hm : 0 < m ∧ m < n) (w w' : PotentialTable n)
    (hc : tableCounts w = tableCounts w') :
    ∀ t : ℝ,
    ((Finset.univ.filter fun z : Assignment n m => tableEstimator w z.val = t).card : ℝ) /
      Fintype.card (Assignment n m) =
    ((Finset.univ.filter fun z : Assignment n m => tableEstimator w' z.val = t).card : ℝ) /
      Fintype.card (Assignment n m) := by
  intro t
  rw [count_distribution_invariance_level_card m w w' hc t]

end AronowAudit.P003.Wave1
