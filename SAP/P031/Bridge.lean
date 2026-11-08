import SAP.P031.Defs
import AronowAudit.P031.P031_Variance
import AronowAudit.P031.Wave1.LargeSampleRefutation
import AronowAudit.P031.Wave1.Gap.GLP027P016P031P031B1
import AronowAudit.P031.Wave1.FootnoteThreeComplete
import AronowAudit.P031.Wave1.FootnoteThreeProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031.Bridge

open SAP.P031 Finset Filter
open scoped BigOperators Matrix Topology

noncomputable section

/-- Preserve the population's data and standing design certificates. -/
def toPopulation (P : Population) : AronowAudit.P031.Population :=
  ⟨P.N, P.M, P.y1, P.y0, P.hM, P.hMN⟩

def fromPopulation (P : AronowAudit.P031.Population) : Population :=
  ⟨P.N, P.M, P.y1, P.y0, P.hM, P.hMN⟩

theorem to_from (P : AronowAudit.P031.Population) :
    toPopulation (fromPopulation P) = P := rfl

theorem from_to (P : Population) : fromPopulation (toPopulation P) = P := rfl

/-- All scalar finite-data definitions agree by reduction of their bodies. -/
theorem hc2_eq {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) (Y : ι → ℝ) :
    AronowAudit.P031.hc2 s Y = hc2 s Y := rfl

theorem trueVariance_eq (P : Population) :
    AronowAudit.P031.trueVariance (toPopulation P) = trueVariance P := rfl

theorem eventProbability_eq (P : Population) (E : Finset (Fin P.N) → Prop) :
    AronowAudit.P031.eventProbability (toPopulation P) E = eventProbability P E := rfl

theorem shiftedPopulation_eq (P : Population) (c d : ℝ) :
    AronowAudit.P031.shiftedPopulation (toPopulation P) c d =
      toPopulation (shiftedPopulation P c d) := rfl

theorem t1 : T1Statement := by
  exact @AronowAudit.P031.hc2_eq_neyman

theorem t2 : T2Statement := by
  exact @AronowAudit.P031.hc2_conservative

theorem t3 : T3Statement := by
  exact @AronowAudit.P031.scaled_ols_eq_constantEffects

theorem t4 : T4Statement := by
  exact @AronowAudit.P031.balanced_equivalences

theorem t7 : T7Statement := by
  exact @AronowAudit.P031.printed_covariance_counterexample

theorem t8 : T8Statement := by
  exact @AronowAudit.P031.corrected_theorem_two_proof

theorem t9 : T9Statement := by
  exact @AronowAudit.P031.corrected_theorem_three_proof

/-- Change population records in the existential witness and universal negation. -/
theorem t5 : T5Statement := by
  obtain ⟨⟨P, hG, hN, hF⟩, hNot⟩ :=
    AronowAudit.P031.Wave1.printed_large_sample_contract_refuted
  refine ⟨⟨(fun n => fromPopulation (P n)), hG, hN, hF⟩, ?_⟩
  intro h
  exact hNot (fun Q => h (fun n => fromPopulation (Q n)))

theorem t6 : T6Statement := by
  obtain ⟨⟨P, a, v, hL, hlt, hN, hC⟩, ⟨Q, b, w, hQ, hgt⟩⟩ :=
    AronowAudit.P031.Wave1.ols_ce_may_be_too_small_or_large_proof
  exact ⟨⟨(fun n => fromPopulation (P n)), a, v, hL, hlt, hN, hC⟩,
    ⟨(fun n => fromPopulation (Q n)), b, w, hQ, hgt⟩⟩

/-- Project the OLS clauses from the credited witness, dropping the extra CE limit. -/
theorem footnoteWitness {a q : ℝ}
    (h : AronowAudit.P031.FootnoteVarianceWitness a q) : FootnoteVarianceWitness a q := by
  obtain ⟨hG, hU, hM, hT, hE, hO, _, hR⟩ := h
  exact ⟨hG, hU, hM, hT, hE, hO, hR⟩

theorem t10 : T10Statement := by
  obtain ⟨h1, h2, hh, hne, hShift⟩ := AronowAudit.P031.footnote_three_counterexample
  refine ⟨footnoteWitness h1, footnoteWitness h2, footnoteWitness hh, hne, ?_⟩
  intro P c d
  exact hShift (toPopulation P) c d

/-- Combine the two credited rows after the structural population correspondence. -/
theorem t11 : T11Statement := by
  intro P hG p v1 v0 c hp hp1 hA h1 h0 hC
  let Q := fun n => toPopulation (P n)
  obtain ⟨hT, hE, hD, hV, hProb, hShift⟩ :=
    AronowAudit.P031.Wave1.footnote_three_complete Q hG p v1 v0 c hp hp1 hA h1 h0 hC
  have hBound :=
    (AronowAudit.P031.Wave1.footnote_three_probability_complete Q hG
      p v1 v0 c hp hp1 hA h1 h0 hC).1
  exact ⟨hT, hE, hD, hV, hBound, hProb, hShift⟩

end
end SAP.P031.Bridge
