import SAP.P024.Defs.WholeW2
import SAP.P024.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024.WH.W2
open scoped BigOperators
noncomputable section

/-- Remove the donor's condition on zero-mass assignments. Copy any supported
assignment to the zero-mass points; every expectation and marginal is unchanged.
This proved helper is polymorphic so it also applies to the concrete allocation
space used in the complete-design clause. -/
theorem fixedSupportUnbiasedW2 {J Ω : Type*} [Fintype J] [Fintype Ω]
    (d : Design Ω) (m : ℕ) (hm : 0 < m) (hmN : m < Fintype.card J)
    (z : Ω → J → Bool) (y0 y1 : J → ℝ)
    (hcount : ∀ ω, d.mass ω ≠ 0 → treatedCount (z ω) = m)
    (hp : ∀ j, exposureProbability d z j = (m : ℝ) / Fintype.card J) :
    expectation d (fun ω => clusterDIM (fun _ => 1) y0 y1 (z ω)) =
      averageEffect Finset.univ y0 y1 := by
  classical
  have hex : ∃ ω, d.mass ω ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz : (∑ ω, d.mass ω) = 0 := by simp [hn]
    linarith [d.total]
  obtain ⟨ω0, hω0⟩ := hex
  let z' : Ω → J → Bool := fun ω => if d.mass ω ≠ 0 then z ω else z ω0
  have hcount' : ∀ ω, treatedCount (z' ω) = m := by
    intro ω
    by_cases hω : d.mass ω ≠ 0
    · simpa only [z', ite_eq_left hω] using hcount ω hω
    · simpa only [z', ite_eq_right hω] using hcount ω0 hω0
  have hp' : ∀ j, exposureProbability d z' j = (m : ℝ) / Fintype.card J := by
    intro j
    rw [← hp j]
    unfold exposureProbability expectation
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : d.mass ω ≠ 0
    · simp only [z', ite_eq_left hω]
    · simp only [not_not] at hω
      simp only [hω, zero_mul]
  have he := AronowAudit.P024.individual_observed_dim_unbiased
    (Bridge.toDesign d) m hm hmN z' y0 y1 hcount' hp'
  change expectation d (fun ω => clusterDIM (fun _ => 1) y0 y1 (z' ω)) =
    averageEffect Finset.univ y0 y1 at he
  rw [← he]
  unfold expectation
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : d.mass ω ≠ 0
  · simp only [z', ite_eq_left hω]
  · simp only [not_not] at hω
    simp only [hω, zero_mul]

/-- Assemble unbiasedness for the stated restricted assignment classes.
The project already
proves the required conditional Bernoulli mathematics, so no new leaves are
needed. Derive complete-design counts and marginals from its stated joint law;
then specialize conditional equal-cluster unbiasedness to cluster size one.
For arbitrary count mixtures, equal masses within each count imply permutation
invariance, so the exchangeable-law donor applies directly. -/
theorem T6_assembly : T6WholeStatement_W2 := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro J Ω _ _ d m hm hmN z y0 y1 hcount hp
    exact fixedSupportUnbiasedW2 d m hm hmN z y0 y1 hcount hp
  · intro N m hm hmN d hd y0 y1
    apply fixedSupportUnbiasedW2 d m hm (by simpa using hmN) subsetExposure y0 y1
    · intro s hs
      have hc : s.card = m := by
        by_contra hn
        exact hs (by rw [hd s, ite_eq_right hn])
      simpa [treatedCount, subsetExposure] using hc
    · intro j
      simpa [exposureProbability, expectation, indicator, subsetExposure,
        AronowAudit.P024.expectation, AronowAudit.P024.indicator,
        AronowAudit.P024.subsetExposure, Bridge.toDesign] using
        AronowAudit.P024.complete_marginal (by omega) m hm hmN (Bridge.toDesign d) hd j
  · intro k p hp hp1 d hd y0 y1
    have hd' : Bridge.toDesign d =
        AronowAudit.P024.bernoulliDesign (k + 2) p hp.le hp1.le := by
      change AronowAudit.P024.Design.mk d.mass d.nonneg d.total =
        AronowAudit.P024.Design.mk _ _ _
      congr 1
      exact funext hd
    have he := AronowAudit.P024.equal_cluster_bernoulli_scope_repair
      k p hp hp1 1 (by norm_num) y0 y1
    have hmass : bernoulliNonemptyMass k p =
        AronowAudit.P024.bernoulliNonemptyMass k p hp hp1 := rfl
    have hprob : bernoulliNonemptyMass k p =
        probability d (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) := by
      rw [hmass, AronowAudit.P024.bernoulli_nonempty_mass_probability]
      rw [← hd']
      rfl
    refine ⟨?_, hprob, ?_, ?_⟩
    · rw [← hprob, hmass]
      exact AronowAudit.P024.bernoulli_nonempty_mass_positive k p hp hp1
    · intro s
      rw [bernoulliConditionalMass, ← hprob, hd s]
    · have hmean := he.2.2.2
      change bernoulliConditionalExpectation k p
        (fun s => clusterDIM (fun _ => 1) y0 y1 (subsetExposure s.val)) =
        clusterEffect (fun _ => 1) y0 y1 at hmean
      simpa [clusterEffect, averageEffect] using hmean
  · intro k d hcountlaw y0 y1
    have hsymm : ∀ π : Equiv.Perm (Fin (k + 2)), ∀ s,
        (Bridge.toDesign d).mass (AronowAudit.P024.nonemptyPerm k π s) =
          (Bridge.toDesign d).mass s := by
      intro π s
      apply hcountlaw
      change (s.val.map π.toEmbedding).card = s.val.card
      exact Finset.card_map _
    have he := AronowAudit.P024.equal_cluster_exchangeable_nonempty
      (Bridge.toDesign d) hsymm 1 (by norm_num) y0 y1
    change expectation d
      (fun s => clusterDIM (fun _ => 1) y0 y1 (subsetExposure s.val)) =
        clusterEffect (fun _ => 1) y0 y1 at he
    simpa [clusterEffect, averageEffect] using he

end
end SAP.P024.WH.W2
