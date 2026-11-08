import SAP.P019a.WH.W1.Existing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1
open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical

 theorem t4_extras {E : Type*} [Fintype E] (S : Study E) (hs : S.standing) :
    wholeT4Extras S := by
  have hp := AronowAudit.P019.regularity_probabilities (toStudy S) hs.2.2.2
  have hresponse : S.law.prob (fun ω => S.Y ω = true) = S.mu*S.truthRate :=
    AronowAudit.P019.direct_response_probability (toStudy S) hs.1 hs.2.2.2
  have hmu : 0 < S.mu := lt_of_lt_of_le (hp.2 true)
    (AronowAudit.P019.probability_mono (toLaw S.law)
      (fun ω => S.Y ω = true) (fun ω => S.X ω = true) hs.1)
  have hg : S.gamma < 1 := by
    have h := hp.1 false
    rw [AronowAudit.P019.prob_false] at h
    change 0 < 1-S.gamma at h
    linarith
  have hq : 0 < 1-S.mu*S.truthRate := by
    rw [← hresponse]
    exact (AronowAudit.P019.prob_false (toLaw S.law) S.Y) ▸ hp.2 false
  have hc := AronowAudit.P019.nonconfessor_population_contrast (toStudy S) hs
  refine ⟨?_, hresponse, hmu, hp.1 true, hg, hq, ?_, hc.1, ?_, ?_⟩
  · intro n s
    refine ⟨?_, (fun c1 c0 => AronowAudit.P019.estimator_product_identity (toStudy S) s c1 c0)⟩
    have hsum : (S.negativeCount s : ℝ) = (n : ℝ)-∑ i, bitVal (S.Y (s i)) := by
      unfold Study.negativeCount Study.cellCount
      simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        ← Finset.sum_add_distrib]
      calc
        _ = ∑ i, (1-bitVal (S.Y (s i))) := by
          apply Finset.sum_congr rfl
          intro i _
          cases hy : S.Y (s i) <;> cases hz : S.Z (s i) <;>
            simp [Study.cell, bitVal, hy, hz]
        _ = _ := by simp [Finset.sum_sub_distrib]
    by_cases hn : n = 0
    · subst n; simp [Study.negativeCount, Study.cellCount]
    · rw [hsum]
      unfold Study.sampleA Study.ybar
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp <;> ring
  · intro n hn
    exact AronowAudit.P019.direct_sample_moments (toStudy S) hs n hn
  · have hc' : 1-(S.listMean true false-S.listMean false false) =
        (1-S.mu)/(1-S.mu*S.truthRate) := hc.2
    rw [neg_div, ← hc']
    ring
  · exact AronowAudit.P019.Wave1.corrected_covariance_order_proof (toStudy S) hs

end
end SAP.P019a.WH.W1
