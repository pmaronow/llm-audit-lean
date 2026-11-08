import SAP.P028.WH.W1.Donors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SAP.P028.WH.W1
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge
noncomputable section
open Classical

theorem completionFacts : wholeCompletionFacts := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u z d; cases u <;> cases z <;> cases d <;>
      norm_num [wholeCompletion, missingCount]
  · intro u z d v; cases u <;> cases z <;> cases d <;> cases v <;>
      norm_num [wholeCompletedCount, wholeCompletion, wholeQ, recordedCount, missingCount]
  · intro u; cases u <;> refine ⟨?_, ?_, ?_⟩
    all_goals first
      | (intro d; cases d <;> norm_num [wholeMu, wholeCompletedCount, wholeCompletion, recordedCount, missingCount])
      | norm_num [wholeA, wholeB, wholeCompletedCount, wholeCompletion, recordedCount, missingCount]
  · norm_num [wholeA, wholeB, wholeMu, wholeCompletedCount, wholeCompletion, recordedCount, missingCount]
  · norm_num [wholeA, wholeB, wholeMu, wholeCompletedCount, wholeCompletion, recordedCount, missingCount]

theorem sourceTotals : wholeSourceTotals := by
  norm_num [wholeSourceTotals, recordedCount, missingCount, armCount]

theorem mixedRounding : wholeMixedRounding := by
  norm_num [wholeMixedRounding, abs_of_pos, abs_of_neg]

theorem sourceRounding : wholeSourceRounding := by
  refine ⟨mixedRounding, ?_⟩
  norm_num [wholeSourceLower, wholeSourceUpper, abs_of_pos, abs_of_neg]

/-- Exact finite product certificates: expand the seventeen masses and check all
sixty-four latent binary patterns. This is a joint-law description, so it also
states the conditional Bernoulli construction without conditioning on null events. -/
theorem witnessFactorization : ∀ u,
    let M := if u then upperLaw else lowerLaw
    (∀ a : BinaryAtom, fprob M (fun i => M.atom i = a) = wholeConstructedMass u a) ∧
    fprob M (fun i => (M.atom i).d0 = true ∧ (M.atom i).d1 = true) = 16/99 ∧
    fprob M (fun i => (M.atom i).d0 = false ∧ (M.atom i).d1 = false) = 64/101 := by
  set_option maxRecDepth 8192 in
  set_option maxHeartbeats 8000000 in
  intro u
  cases u <;> refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (intro a
       rcases a with ⟨d0,d1,y0,y1,r0,r1⟩
       cases d0 <;> cases d1 <;> cases y0 <;> cases y1 <;> cases r0 <;> cases r1 <;>
         norm_num [fprob, lowerLaw, upperLaw, Fin.sum_univ_succ, wholeConstructedMass,
           wholeBern, wholeQ, wholeMu, wholeA, wholeB, wholeCompletedCount, wholeCompletion,
           recordedCount, missingCount, fd, fy, BinaryAtom.mk.injEq])
    | norm_num [fprob, lowerLaw, upperLaw, Fin.sum_univ_succ]

theorem witnessAtomDistinct : ∀ u : Bool, Function.Injective (if u then upperLaw.atom else lowerLaw.atom) := by
  intro u
  cases u <;> decide

theorem realNonidentification : ∀ d, ¬ ∃ F : (Bool × Bool × Bool × Bool → ℚ) → ℝ,
    ∀ M : BinaryLaw, finiteValid M → F (observedLaw M) = (fcy M d : ℝ) := by
  intro d ⟨F,hF⟩
  have h := existingT1.2.2.2.2.2.1
  rcases h with ⟨hl,hu,he,h00,h01,h10,h11,_⟩
  have hh : (fcy lowerLaw d : ℝ) = (fcy upperLaw d : ℝ) :=
    (hF lowerLaw hl).symm.trans ((congrArg F he).trans (hF upperLaw hu))
  cases d <;> norm_num [h00,h01,h10,h11] at hh


end
end SAP.P028.WH.W1
