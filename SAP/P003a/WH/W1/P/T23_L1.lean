import SAP.P003a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W1.P.T23_L1

open SAP.P003a
open SAP.P003a.Bridge
open AronowAudit.P003.Wave1

lemma adaptiveSearch_succ (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) :
    adaptiveSearch (fuel + 1) true o k₁ k₂ reject a b idx =
      if b ≤ a + 1 then ⟨some a, []⟩ else
        let c := (a + b) / 2
        let q := runTests reject idx (candidates o c)
        let r := adaptiveSearch fuel true o k₁ k₂ reject
          (if q.compatible then c else a) (if q.compatible then b else c) q.idx
        ⟨r.value, q.trace ++ r.trace⟩ := by
  conv_lhs => rw [adaptiveSearch]
  by_cases h : b ≤ a + 1 <;> simp [h]

lemma effectSearch_succ (fuel : ℕ) (o : Counts) (reject : Counts → ℕ → Bool)
    (a b : ℤ) (idx : ℕ) :
    w1EffectSearch (fuel + 1) o reject a b idx =
      if b ≤ a + 1 then ⟨some a, [], []⟩ else
        let c := (a + b) / 2
        let q := runTests reject idx (candidates o c)
        let r := w1EffectSearch fuel o reject
          (if q.compatible then c else a) (if q.compatible then b else c) q.idx
        ⟨r.value, ⟨c, idx, !q.compatible⟩ :: r.queries, q.trace ++ r.tests⟩ := by
  conv_lhs => rw [w1EffectSearch]

lemma effectSearch_erase (fuel : ℕ) (o : Counts) (reject : Counts → ℕ → Bool)
    (k₁ k₂ a b : ℤ) (idx : ℕ) :
    (w1EffectSearch fuel o reject a b idx).value =
        (adaptiveSearch fuel true o k₁ k₂ reject a b idx).value ∧
    (w1EffectSearch fuel o reject a b idx).tests =
        (adaptiveSearch fuel true o k₁ k₂ reject a b idx).trace ∧
    (∀ q ∈ (w1EffectSearch fuel o reject a b idx).queries,
      q.rejected = !(runTests reject q.start (candidates o q.x)).compatible) := by
  induction fuel generalizing a b idx with
  | zero =>
      by_cases h : b ≤ a + 1 <;> simp [w1EffectSearch, adaptiveSearch, h]
  | succ fuel ih =>
      rw [effectSearch_succ, adaptiveSearch_succ]
      by_cases h : b ≤ a + 1
      · simp [h]
      · simp only [if_neg h]
        let c : ℤ := (a + b) / 2
        let q := runTests reject idx (candidates o c)
        let a' := if q.compatible then c else a
        let b' := if q.compatible then b else c
        have hi := ih a' b' q.idx
        dsimp only [c, q, a', b'] at hi ⊢
        rcases hi with ⟨hval, htests, hqueries⟩
        refine ⟨hval, ?_, ?_⟩
        · exact congrArg (fun xs => q.trace ++ xs) htests
        · intro query hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · subst query
            rfl
          · exact hqueries query hmem

lemma to_adaptiveSearch_trace (fuel : ℕ) (o : Counts) (k₁ k₂ : ℤ)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) :
    (AronowAudit.P003.adaptiveSearch fuel true (toAudit o) k₁ k₂
      (fun v i => reject (fromAudit v) i) a b idx).trace =
      ((adaptiveSearch fuel true o k₁ k₂ reject a b idx).trace.map
        fun x => (toAudit x.1, x.2)) := by
  induction fuel generalizing a b idx with
  | zero =>
      by_cases h : b ≤ a + 1
      · simp [AronowAudit.P003.adaptiveSearch, adaptiveSearch, h]
      · simp [AronowAudit.P003.adaptiveSearch, adaptiveSearch, h]
  | succ fuel ih =>
      by_cases h : b ≤ a + 1
      · simp [AronowAudit.P003.adaptiveSearch, adaptiveSearch, h]
      · simp [AronowAudit.P003.adaptiveSearch, adaptiveSearch, h,
          to_candidates, to_runTests, mapQuery, ih, List.map_append]

theorem T23_L1_proof : SAP.P003a.WH.W1.T23_L1 := by
  constructor
  · intro fuel o reject k₁ k₂ a b idx
    have he := effectSearch_erase fuel o reject k₁ k₂ a b idx
    refine ⟨he.1, he.2.1, he.2.2, ?_⟩
    intro i hi
    let z := (w1EffectSearch fuel o reject a b idx).tests[i]!
    have hget : (w1EffectSearch fuel o reject a b idx).tests[i]? =
        some z := by simp [z, hi]
    rw [he.2.1] at hget
    have htrace := to_adaptiveSearch_trace fuel o k₁ k₂ reject a b idx
    have hmap :
        (AronowAudit.P003.adaptiveSearch fuel true (toAudit o) k₁ k₂
          (fun v j => reject (fromAudit v) j) a b idx).trace[i]? =
          some (toAudit z.1, z.2) := by
      rw [htrace]
      simpa [hget]
    have hreply := AronowAudit.P003.Wave1.GLP0032B6_search_reply
      fuel (toAudit o) k₁ k₂ (fun v j => reject (fromAudit v) j) a b idx i
      (toAudit z.1) z.2 hmap
    change z.2 = reject z.1 (idx + i)
    simpa using hreply.symm
  · intro o reject ho
    let k₁ : ℤ := 2 * ((o.a : ℤ) - o.c)
    let k₂ : ℤ := (o.a : ℤ) - o.c + (o.a + o.b)
    have hbudget := T7_upperRun_budget (toAudit o)
      (fun v i => reject (fromAudit v) i) 0 (by simpa using ho)
    have htrace := to_adaptiveSearch_trace (o.total + 3) o k₁ k₂ reject
      (k₁ - 1) (k₂ + 1) 0
    have htraceRun :
        (AronowAudit.P003.upperRun true (toAudit o)
          (fun v i => reject (fromAudit v) i) 0).trace =
          (upperRun true o reject 0).trace.map (fun x => (toAudit x.1, x.2)) := by
      simpa [AronowAudit.P003.upperRun, upperRun, k₁, k₂] using htrace
    have hvbridge := SAP.P003a.Bridge.to_upperRun true o reject 0
    have hlocalSome : (upperRun true o reject 0).value.isSome := by
      rw [← hvbridge]
      exact hbudget.1
    have he := effectSearch_erase (o.total + 3) o reject k₁ k₂
      (k₁ - 1) (k₂ + 1) 0
    have heval : (w1EffectUpperRun o reject).value =
        (upperRun true o reject 0).value := by
      simpa [w1EffectUpperRun, w1UpperBounds, upperRun, k₁, k₂] using he.1
    have hval : (w1EffectUpperRun o reject).value.isSome := by
      rw [heval]
      exact hlocalSome
    have heLen : (w1EffectUpperRun o reject).tests.length =
        (upperRun true o reject 0).trace.length := by
      have ht := congrArg List.length he.2.1
      simpa [w1EffectUpperRun, w1UpperBounds, upperRun, k₁, k₂] using ht
    have htraceLen : (upperRun true o reject 0).trace.length =
        (AronowAudit.P003.upperRun true (toAudit o)
          (fun v i => reject (fromAudit v) i) 0).trace.length := by
      have ht := congrArg List.length htraceRun
      simpa using ht.symm
    have hlen : (w1EffectUpperRun o reject).tests.length ≤
        (o.total + 1) * (Nat.log2 (o.total + 1) + 2) := by
      calc
        (w1EffectUpperRun o reject).tests.length =
            (upperRun true o reject 0).trace.length := heLen
        _ = (AronowAudit.P003.upperRun true (toAudit o)
            (fun v i => reject (fromAudit v) i) 0).trace.length := htraceLen
        _ ≤ (o.total + 1) * (Nat.log2 (o.total + 1) + 2) := by
            simpa using hbudget.2
    refine ⟨hval, le_trans hlen ?_⟩
    unfold w1TestBudget
    exact Nat.mul_le_mul_left (o.total + 1) (by omega)

end SAP.P003a.WH.W1.P.T23_L1

theorem SAP.P003a.WH.W1.T23_L1_proof : SAP.P003a.WH.W1.T23_L1 := by
  exact SAP.P003a.WH.W1.P.T23_L1.T23_L1_proof
