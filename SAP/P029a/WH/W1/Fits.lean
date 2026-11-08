import SAP.P029a.Defs.WholeW1
import SAP.P029a.Bridge
import AronowAudit.P053.P053_NormalQuantiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029a.WH.W1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

noncomputable section

/-- The standard normal CDF is strictly interior at every finite coefficient. -/
theorem phi_interior (t : ℝ) : wholePhi t ∈ Ioo (0 : ℝ) 1 := by
  have h0 := cdf_nonneg (gaussianReal 0 1) (t-1)
  have h1 := cdf_le_one (gaussianReal 0 1) (t+1)
  have hl := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
    (show t-1 < t by linarith)
  have hu := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
    (show t < t+1 by linarith)
  dsimp [wholePhi]
  exact ⟨by linarith, by linarith⟩

/-- Two normal quantiles give an intercept and a binary-profile slope. -/
theorem binary_saturation : WholeBinaryProbitSaturation := by
  intro q hq
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  obtain ⟨a, ha⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (gaussianReal 0 1) (hq false).1 (hq false).2
  obtain ⟨b, hb⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (gaussianReal 0 1) (hq true).1 (hq true).2
  refine ⟨(a,b-a), ?_⟩
  funext x
  cases x
  · simpa [wholeBinaryProbit, wholePhi, indicatorValue] using ha
  · simpa [wholeBinaryProbit, wholePhi, indicatorValue] using hb

/-- Use a=q1 and b=q0/q1 in the nested Bernoulli model, then saturate both probits. -/
theorem nested_saturation : WholeNestedProbitSaturation := by
  intro q hq
  have hp (x : Bool) := AronowAudit.P029.nested_receipt_parameters
    (q (x,true)) (q (x,false)) (hq x).1 (hq x).2.1 (hq x).2.2
  obtain ⟨α, hα⟩ := binary_saturation (fun x => q (x,true)) (fun x => (hp x).1)
  obtain ⟨β, hβ⟩ := binary_saturation (fun x => q (x,false) / q (x,true))
    (fun x => (hp x).2.1)
  refine ⟨(α,β), ?_⟩
  funext c
  rcases c with ⟨x,z⟩
  dsimp [wholeNestedProbit]
  rw [congrFun hα x, congrFun hβ x]
  cases z
  · exact (hp x).2.2.1
  · exact (hp x).2.2.2.1

/-- Clipping always gives strictly interior receipt probabilities. -/
theorem clipped_interior (q : ℝ) : wholeClipReceipt q ∈ Ioo (0 : ℝ) 1 := by
  have hlow : (1/100000 : ℝ) ≤ wholeClipReceipt q := le_max_left _ _
  have hupp : wholeClipReceipt q ≤ (1-1/100000 : ℝ) :=
    max_le (by norm_num) (min_le_left _ _)
  constructor <;> linarith

/-- Clipping fixes every point of the clipping interval, including its endpoints. -/
theorem clip_eq_self {q : ℝ} (h0 : (1/100000 : ℝ) ≤ q)
    (h1 : q ≤ 1-1/100000) : wholeClipReceipt q = q := by
  unfold wholeClipReceipt
  rw [min_eq_right h1, max_eq_right h0]

/-- Transfer a free-cell unique minimum to any interior model that attains that array. -/
theorem realize_free_fit {I C Θ : Type*} [Fintype I]
    (cell : I → C) (D : I → Bool) (w : I → ℝ) (q : C → ℝ)
    (rate : Θ → C → ℝ) (hf : IsUniqueFreeCellFit cell D w q)
    (hr : ∀ θ c, rate θ c ∈ Ioo (0 : ℝ) 1) (he : ∃ θ, rate θ = q) :
    WholeRealizedMinimum rate q (wholeCellObjective cell D w) := by
  exact ⟨he, fun θ => hf.2 (rate θ) (hr θ)⟩

/-- Parameter-free log-weight shifts preserve each inequality and its equality case. -/
theorem realize_package_fit {I C Θ : Type*} [Fintype I]
    (cell : I → C) (D : I → Bool) (w : I → ℝ) (q : C → ℝ)
    (rate : Θ → C → ℝ) (hf : IsUniqueFreeCellFit cell D (fun _ => 1) q)
    (hr : ∀ θ c, rate θ c ∈ Ioo (0 : ℝ) 1) (he : ∃ θ, rate θ = q)
    (hw : ∀ i, 0 < w i) :
    WholeRealizedMinimum rate q (wholePackageCellObjective cell D w) := by
  have hpos (r : C → ℝ) (h : ∀ c, r c ∈ Ioo (0 : ℝ) 1) (i : I) :
      0 < bernoulliContribution (r (cell i)) (D i) := by
    cases hD : D i
    · simpa [bernoulliContribution, hD] using (h (cell i)).2
    · simpa [bernoulliContribution, hD] using (h (cell i)).1
  have heq (r : C → ℝ) (h : ∀ c, r c ∈ Ioo (0 : ℝ) 1) :
      wholePackageCellObjective cell D w r = wholeCellObjective cell D (fun _ => 1) r -
        ∑ i, Real.log (w i) := by
    have hi := Bridge.proveInsideLogWeightIdentity
      (fun i => bernoulliContribution (r (cell i)) (D i)) w (hpos r h) hw
    simpa [wholePackageCellObjective, wholeCellObjective, insideLogObjective,
      observationWeightedObjective] using hi
  refine ⟨he, fun θ => ?_⟩
  obtain ⟨hle, hiff⟩ := hf.2 (rate θ) (hr θ)
  change wholeCellObjective cell D (fun _ => 1) q ≤
    wholeCellObjective cell D (fun _ => 1) (rate θ) at hle
  change (wholeCellObjective cell D (fun _ => 1) q =
    wholeCellObjective cell D (fun _ => 1) (rate θ) ↔ rate θ = q) at hiff
  rw [heq q hf.1, heq (rate θ) (hr θ)]
  exact ⟨sub_le_sub_right hle _, (sub_left_inj).trans hiff⟩

/-- Unit-weight treated-cell totals are (1,3) successes and (3,1) failures. -/
theorem treated_unweighted_fit :
    IsUniqueFreeCellFit Prod.fst treatedReceipt (fun _ => 1) specifiedUnweightedScores := by
  let S : Bool → ℝ := fun x => if x then 3 else 1
  let F : Bool → ℝ := fun x => if x then 1 else 3
  have hs : ∀ x, successWeightTotal Prod.fst treatedReceipt (fun _ => 1) x = S x := by
    intro x
    cases x <;> simp only [successWeightTotal, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    all_goals norm_num [treatedReceipt, weightWitnessResponse, PotentialResponse.receivedTreatment, S]
  have hf : ∀ x, failureWeightTotal Prod.fst treatedReceipt (fun _ => 1) x = F x := by
    intro x
    cases x <;> simp only [failureWeightTotal, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    all_goals norm_num [treatedReceipt, weightWitnessResponse, PotentialResponse.receivedTreatment, F]
  have heq : (fun x => S x / (S x + F x)) = specifiedUnweightedScores := by
    funext x
    cases x <;> norm_num [S, F, specifiedUnweightedScores]
  have h := Bridge.freeCellFit_of_totals Prod.fst treatedReceipt (fun _ => 1) S F
    (by intro i; norm_num) hs hf (by intro x; cases x <;> norm_num [S])
    (by intro x; cases x <;> norm_num [F])
  simpa only [heq] using h

/-- Unit-weight four-cell totals are the observed counts (1,2,1,3) and their complements. -/
theorem two_sided_unweighted_fit :
    IsUniqueFreeCellFit Prod.fst twoSidedReceipt (fun _ => 1) specifiedInsideLogRates := by
  let S : Bool × Bool → ℝ := fun x => if x.2 then (if x.1 then 3 else 2) else 1
  let F : Bool × Bool → ℝ := fun x => 4 - S x
  have hs : ∀ x, successWeightTotal Prod.fst twoSidedReceipt (fun _ => 1) x = S x := by
    rintro ⟨x,z⟩
    cases x <;> cases z <;> simp only [successWeightTotal, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    all_goals norm_num [twoSidedReceipt, twoSidedSuccessCount, S]
  have hf : ∀ x, failureWeightTotal Prod.fst twoSidedReceipt (fun _ => 1) x = F x := by
    rintro ⟨x,z⟩
    cases x <;> cases z <;> simp only [failureWeightTotal, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    all_goals norm_num [twoSidedReceipt, twoSidedSuccessCount, S, F]
  have heq : (fun x => S x / (S x + F x)) = specifiedInsideLogRates := by
    funext c
    rcases c with ⟨x,z⟩
    cases x <;> cases z <;> norm_num [S, F, specifiedInsideLogRates]
  have h := Bridge.freeCellFit_of_totals Prod.fst twoSidedReceipt (fun _ => 1) S F
    (by intro i; norm_num) hs hf
    (by rintro ⟨x,z⟩; cases x <;> cases z <;> norm_num [S])
    (by rintro ⟨x,z⟩; cases x <;> cases z <;> norm_num [S, F])
  simpa only [heq] using h

/-- Raw realizations of the two fitted arrays are fixed by clipping. -/
theorem clipped_realization (q : Bool × Bool → ℝ)
    (horder : ∀ x, 0 < q (x,false) ∧ q (x,false) < q (x,true) ∧ q (x,true) < 1)
    (hclip : ∀ c, (1/100000 : ℝ) ≤ q c ∧ q c ≤ 1-1/100000) :
    ∃ β, wholeClippedNestedProbit β = q := by
  obtain ⟨β, hβ⟩ := nested_saturation q horder
  refine ⟨β, ?_⟩
  funext c
  dsimp [wholeClippedNestedProbit]
  rw [congrFun hβ c]
  exact clip_eq_self (hclip c).1 (hclip c).2

end
end SAP.P029a.WH.W1
