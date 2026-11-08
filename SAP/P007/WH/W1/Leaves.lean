import SAP.P007.Defs.WholeW1
import SAP.P007.Bridge
import AronowAudit.P007.P007_Probability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P007.WH.W1

open SAP.P007.Bridge
open AronowAudit.P007

/-- The endpoint countermodel is an existing normalized product law. Its
assumptions, prefix probabilities and expectations follow from the existing
finite-probability results; the remaining refutation is numerical. No new
mathematical leaves are needed. -/
theorem T10_assembly : T10WholeStatement := by
  let A := equalProbabilityLaw 2 1 0 (by norm_num) (by norm_num)
  let L := fromAudit A
  have hmodel := bestCase_attained 2 1 0 (by norm_num) (by norm_num)
  have hb : observationBound L 0 := hmodel.2.1
  have hs (i : Fin 2) : survival L i 1 = 0 := by
    change prefixSurvival
      (equalProbabilityLaw 2 1 0 (by norm_num) (by norm_num)) i 1 = 0
    simpa using equalProbability_prefix 2 1 0 (by norm_num) (by norm_num) i le_rfl
  have hr (i : Fin 2) : expectation L (fun x => deletedIndicator x i) = 1 := by
    calc
      expectation L (fun x => deletedIndicator x i) = 1 - survival L i 1 :=
        expected_removed_row A i
      _ = 1 := by rw [hs i]; norm_num
  have hf : expectation L deletedFraction = 1 := by
    change finiteExpectation
      (equalProbabilityLaw 2 1 0 (by norm_num) (by norm_num)) removedFraction = 1
    simpa [deletedFractionBound] using
      expected_deletion_bound_attained (n := 2) (h := 1) (by norm_num)
        0 (by norm_num) (by norm_num)
  have ha : allDeleted L = 1 := by
    change pAll (equalProbabilityLaw 2 1 0 (by norm_num) (by norm_num)) = 1
    simpa [bestCaseBound] using hmodel.2.2
  have hfrac : fractionBound 0 1 = 1 := by norm_num [fractionBound]
  have hlower : lowerBound 2 0 1 = 1 := by norm_num [lowerBound]
  have heq : lowerBound 2 0 1 = fractionBound 0 1 := hlower.trans hfrac.symm
  refine ⟨⟨L, rfl, hmodel.1, hb, ?_, hf, ha⟩,
    hfrac, hlower, heq, by norm_num, ?_⟩
  · intro i
    exact ⟨zero_bound_first_missing A (by norm_num) hb i, hs i, hr i⟩
  · intro hexclusive
    have hbad := hexclusive 2 1 (by norm_num) (by norm_num) 0
      (by norm_num) (by norm_num) heq
    norm_num at hbad

end SAP.P007.WH.W1
