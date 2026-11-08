import SAP.P042.Defs.WholeW2
import SAP.P042.Bridge
import AronowAudit.P042.P042_Turnout
import AronowAudit.P029.Wave1.LateIdentity.N1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042.WH.W2

noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

/-- General one-sided contact identification on a probability space.
Prove by applying `AronowAudit.P029.Wave1.LateIdentity.n1_proof` to the
fixed responses `Y(c)`, `Y(false)`, and `1_{c=true}`: these are measurable
functions of the independent tuple `(c,Y(false),Y(true))`. On each assignment
arm the observed response agrees with the corresponding fixed response.
Integrability of `Y(c)` follows by measurable pasting of the two integrable
potential outcomes. The pointwise identity
`Y(c)-Y(false) = 1_{c=true} (Y(true)-Y(false))`, `integral_sub`, and
`integral_indicator` give ITT and its normalization as Complier share times
CACE. The indicator integral is the Complier share; cancel this positive
share for the ratio. There is no independence assumption between compliance
and potential outcomes. Estimated proof size: 100–180 lines. -/
def T6_L1 : Prop := RandomizedContactW2

/-- Binary Never-taker nonidentification, including the Never-taker mean.
For the supplied Never-taker `k`, replace only `Y k true` by `1 - Y k true`.
Every entry remains binary; the new and old schedules give identical observed
outcomes for every assignment because `k` never receives contact. All other
entries agree. The individual effect changes by `1 - 2 * Y k true`, which is
either 1 or -1. Use `Finset.sum_congr` or `Finset.sum_ite_eq'` to show that
the Never-taker-effect numerator changes by the same amount. Membership of
`k` in the Never-taker filter makes its cardinality positive, so division
preserves the inequality. This witnesses observational equivalence within
the binary model, not merely among unrestricted real schedules.
Estimated proof size: 70–120 lines. -/
def T6_L2 : Prop := NeverTakerNonidentificationW2

/-- Assemble the whole printed claim from the two new mathematical steps.
The complete-randomization identities and numerical illustration use existing
proved donors. General balance uses the proved independent-arm-mean lemma.
Sampled-subject independence is finite event factorization using the existing
equal-inclusion calculation. The estimator formula is definitional algebra. -/
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) : T6WholeStatement_W2 := by
  refine ⟨?_, ?_, h1, ?_, h2, ?_⟩
  · refine ⟨?_, AronowAudit.P042.michelson_cace_example⟩
    intro N m hN hm hmN Y
    have hb := AronowAudit.P042.complete_randomization_balance hN hm hmN Y
    refine ⟨hb.1, hb.2, ?_⟩
    intro c hc
    have hi := AronowAudit.P042.cace_randomization_identity hN hm hmN Y c hc
    refine ⟨AronowAudit.P042.itt_complier_identity (by omega) Y c hc,
      hi.1, hi.2.1, ?_, hi.2.2⟩
    rw [show finiteExpectation (completeAssignments N m)
        (fun s => assignedContactRate m s c) = complierShare c from hi.2.1]
    exact div_pos (by exact_mod_cast hc) (by exact_mod_cast (show 0 < N by omega))
  · intro Ω _ μ _ Z hZ hz Y _hYm hYi hind
    have hi (t : Bool) : IndepFun Z (fun ω => Y ω t) μ := by
      cases t
      · simpa only [Function.comp_def, id_eq] using
          hind.comp measurable_id measurable_fst
      · simpa only [Function.comp_def, id_eq] using
          hind.comp measurable_id measurable_snd
    have harm (t z : Bool) :
        eventMeanW2 μ (fun ω => Y ω t) {ω | Z ω = z} = ∫ ω, Y ω t ∂μ :=
      AronowAudit.P029.Wave1.LateIdentity.n1_proof
        μ Z (fun ω => Y ω t) hZ (hYi t) (hi t) z (hz z)
    refine ⟨harm, ?_⟩
    have ho (z : Bool) :
        eventMeanW2 μ (fun ω => Y ω (Z ω)) {ω | Z ω = z} =
          eventMeanW2 μ (fun ω => Y ω z) {ω | Z ω = z} := by
      unfold eventMeanW2
      congr 1
      apply setIntegral_congr_fun ((measurableSet_singleton z).preimage hZ)
      intro ω hω
      exact congrArg (Y ω) hω
    rw [ho true, ho false, harm true true, harm false false,
      integral_sub (hYi true) (hYi false)]
  · intro N m hN hm hmN A v B b
    simp only [Bridge.finiteExpectation_eq, Bridge.completeAssignments_eq]
    have hne : (AronowAudit.P042.completeAssignments N m).Nonempty :=
      Finset.powersetCard_nonempty.mpr (by simpa using (show m ≤ N by omega))
    have hb (i : Fin N) :
        AronowAudit.P042.finiteExpectation (AronowAudit.P042.completeAssignments N m)
          (fun S => if decide (i ∈ S) = b then 1 else 0) =
            (if b then (m : ℝ) / (N : ℝ) else 1 - (m : ℝ) / (N : ℝ)) := by
      have ht := AronowAudit.P042.complete_inclusion_probability
        (by omega : 0 < N) hm (by omega : m ≤ N) i
      cases b
      · have he (S : Finset (Fin N)) :
            (if decide (i ∈ S) = false then (1 : ℝ) else 0) =
              1 - (if i ∈ S then 1 else 0) := by
          by_cases hi : i ∈ S <;> simp [hi]
        simp_rw [he]
        exact (AronowAudit.P042.finite_expectation_sub _ _ _).trans
          (by rw [AronowAudit.P042.finite_expectation_const _ hne, ht]; rfl)
      · simpa using ht
    have he (i : Fin N) :
        AronowAudit.P042.finiteExpectation (AronowAudit.P042.completeAssignments N m)
          (fun S => if decide (i ∈ S) = b ∧ v i ∈ B then 1 else 0) =
            (if b then (m : ℝ) / (N : ℝ) else 1 - (m : ℝ) / (N : ℝ)) *
              (if v i ∈ B then 1 else 0) := by
      by_cases hv : v i ∈ B
      · simpa [hv] using hb i
      · simp [hv, AronowAudit.P042.finiteExpectation]
    simp_rw [he]
    exact AronowAudit.P042.finite_expectation_mul _ _ _
  · intro N m _hN _hm _hmN Y c S _hS hF
    exact ⟨rfl, div_mul_cancel₀ _ (ne_of_gt hF)⟩

end

end SAP.P042.WH.W2
