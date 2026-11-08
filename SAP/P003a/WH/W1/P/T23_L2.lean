import SAP.P003a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W1.P.T23_L2

open SAP.P003a.WH.W1

theorem effectSearch_invariant (fuel : ℕ) (o : Counts)
    (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) (hab : a < b) :
    (∀ q ∈ (w1EffectSearch fuel o reject a b idx).queries,
      a < q.x ∧ q.x < b) ∧
    (∀ A, (w1EffectSearch fuel o reject a b idx).value = some A →
      a ≤ A ∧ A < b ∧
        ∀ q ∈ (w1EffectSearch fuel o reject a b idx).queries,
          q.rejected = true → A < q.x) ∧
    (w1EffectSearch fuel o reject a b idx).queries.Pairwise
      (fun q r => q.rejected = true → r.x < q.x) := by
  induction fuel generalizing a b idx with
  | zero =>
      by_cases hs : b ≤ a + 1
      · simp [w1EffectSearch, hs, hab]
      · simp [w1EffectSearch, hs]
  | succ fuel ih =>
      by_cases hs : b ≤ a + 1
      · simp [w1EffectSearch, hs, hab]
      · let c : ℤ := (a + b) / 2
        have hac : a < c := by dsimp [c]; omega
        have hcb : c < b := by dsimp [c]; omega
        let q := runTests reject idx (candidates o c)
        by_cases hq : q.compatible = true
        · have hi := ih c b q.idx hcb
          simp only [w1EffectSearch, if_neg hs, c, q, hq, Bool.not_true]
          refine ⟨?_, ?_, ?_⟩
          · intro r hr
            rcases List.mem_cons.mp hr with heq | htail
            · subst r
              exact ⟨hac, hcb⟩
            · exact ⟨hac.trans (hi.1 r htail).1, (hi.1 r htail).2⟩
          · intro A hA
            have hret := hi.2.1 A hA
            refine ⟨le_of_lt (hac.trans_le hret.1), hret.2.1, ?_⟩
            intro r hr hrej
            rcases List.mem_cons.mp hr with heq | htail
            · subst r
              simp at hrej
            · exact hret.2.2 r htail hrej
          · apply List.pairwise_cons.mpr
            refine ⟨?_, hi.2.2⟩
            intro r hr hrej
            simp at hrej
        · have hi := ih a c q.idx hac
          simp only [w1EffectSearch, if_neg hs, c, q, hq, Bool.not_false]
          refine ⟨?_, ?_, ?_⟩
          · intro r hr
            rcases List.mem_cons.mp hr with heq | htail
            · subst r
              exact ⟨hac, hcb⟩
            · exact ⟨(hi.1 r htail).1, (hi.1 r htail).2.trans hcb⟩
          · intro A hA
            have hret := hi.2.1 A hA
            refine ⟨hret.1, hret.2.1.trans hcb, ?_⟩
            intro r hr hrej
            rcases List.mem_cons.mp hr with heq | htail
            · subst r
              exact hret.2.1
            · exact hret.2.2 r htail hrej
          · apply List.pairwise_cons.mpr
            refine ⟨?_, hi.2.2⟩
            intro r hr hrej
            exact (hi.1 r hr).2

end SAP.P003a.WH.W1.P.T23_L2

theorem SAP.P003a.WH.W1.T23_L2_proof : SAP.P003a.WH.W1.T23_L2 := by
  intro fuel o reject a b idx hab
  dsimp [SAP.P003a.WH.W1.T23_L2]
  obtain ⟨hqueries, hvalue, hpair⟩ :=
    SAP.P003a.WH.W1.P.T23_L2.effectSearch_invariant fuel o reject a b idx hab
  exact ⟨hvalue, hpair⟩
