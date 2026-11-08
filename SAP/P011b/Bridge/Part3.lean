import SAP.P011b.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.Bridge

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

attribute [-simp] Finset.sum_boole

theorem starExtraFacts_correspondence : starExtraFacts ↔
    ((∀ upper : Bool, ∀ k : ℕ,
      type_of% (AronowAudit.P011.Wave1.star_binary upper (k+1))) ∧
    (∀ upper : Bool, ∀ k : ℕ, ∀ A : Graph (4*(k+1)),
      type_of% (AronowAudit.P011.Wave1.star_compatible upper (k+1) A))) := Iff.rfl

/-- The constant witness has all moments; convert its integral formula to
Mathlib covariance by the existing integrable-moment bridge. -/
theorem cwActualCovariance_correspondence : cwActualCovariance=cwTrueCovariance := by
  let : IsProbabilityMeasure constantWitness.law := constantWitness.probability
  unfold cwActualCovariance cwTrueCovariance covOf expectation
  apply AronowAudit.P011.Wave1.fid2_covariance_eq_sub
  all_goals exact MeasureTheory.integrable_dirac enorm_lt_top

/-- Substitute the concrete Dirac witness to identify the partially repaired
moment expression with the numerical expression in the existing certificate. -/
theorem cwBracketOnlyRepair_correspondence :
    cwBracketOnlyRepair = (9/16 - (9/16 + 140-70) : ℝ) := by
  norm_num [cwBracketOnlyRepair, fourthMoment, printedBracket, expectation,
    constantWitness, betaHat, average, weighted, Fin.sum_univ_succ]

theorem sign_scaled_sampleVariance {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) :
    (n : ℝ)*V2star (signModel n) y=sampleVariance (weighted (signModel n) y) := by
  have h := AronowAudit.P011.auxiliary_empty_identity (AronowAudit.P011.signModel n) rfl y
  change V2star (signModel n) y=V2 (emptyGraph n) (weighted (signModel n) y) at h
  rw [h]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp [V2, adjacency, emptyGraph]
  field_simp [hnR]

theorem sign_details : signDetails := by
  intro n hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact AronowAudit.P011.uniform_coordinate_dependency Bool (fun _ => AronowAudit.P011.sign)
      (fun _ => measurable_of_finite _)
  · intro i
    constructor
    · have h := AronowAudit.P011.DataMatrixCompletion.coord_integral i (fun x => x) measurable_id
      norm_num at h
      exact h
    · change AronowAudit.P011.covariance (AronowAudit.P011.signModel n) i i=1
      simp [AronowAudit.P011.DataMatrixCompletion.covariance_formula]
  · have hb : beta (signModel n)=0 := AronowAudit.P011.SignCompletion.beta_zero n
    filter_upwards [AronowAudit.P011.DataMatrixCompletion.ae_signs n] with y hy i
    rw [hb]
    rcases hy i with hi | hi <;> simp [weighted, signModel, hi]
  · intro y hy
    have h := AronowAudit.P011.Wave1.printed_sign_full_pointwise hn y hy
    exact ⟨sign_scaled_sampleVariance hn y, (sign_scaled_sampleVariance hn y).symm.trans h.1⟩

/-- Substitution into the three-vertex definitions; the variable-edge products
and the two zero products are finite rational arithmetic. -/
theorem variables_details : variablesDetails := by
  norm_num [variablesDetails, toUpper, nonzeroRule, fromUpper, centered, average,
    degree, edge12, Fin.sum_univ_succ, Fin.forall_fin_succ, Subtype.forall, Prod.forall]

theorem helper_details : helperDetails := by
  have hb := AronowAudit.P011.helper_counterexamples.2.1
  have hc := AronowAudit.P011.helper_counterexamples.2.2
  rcases hb with ⟨_, _, _, hv1, hv2, hv2p, hr1, hr2, hr2p, _⟩
  rcases hc with ⟨_, hc1, hcr, _⟩
  refine ⟨?_, ?_, ?_⟩
  · norm_num [quadratic, adjacency, emptyGraph, truncatedDegree]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · ext i; fin_cases i <;> norm_num [centered, average, Fin.sum_univ_succ]
    · norm_num [quadratic, adjacency, edge12, centered, average, Fin.sum_univ_succ]
    · norm_num [adjacency, edge12, Fin.sum_univ_succ]
    · norm_num [truncatedDegree, Fin.sum_univ_succ]
    · change AronowAudit.P011.V1R AronowAudit.P011.edge12 _ / AronowAudit.P011.V1 AronowAudit.P011.edge12 _=11/8
      rw [hr1, hv1]; norm_num
    · change AronowAudit.P011.V2R AronowAudit.P011.edge12 _ / AronowAudit.P011.V2 AronowAudit.P011.edge12 _=3/2
      rw [hr2, hv2]; norm_num
    · change AronowAudit.P011.V2primeR _ _ / AronowAudit.P011.V2prime _ _=3/2
      rw [hr2p, hv2p]; norm_num
  · constructor
    · norm_num [quadratic, adjacency, completeGraph, centered, average, Fin.sum_univ_succ]
    · intro C
      change C*AronowAudit.P011.V1 (AronowAudit.P011.completeGraph 3) _ < AronowAudit.P011.V1R (AronowAudit.P011.completeGraph 3) _
      rw [hc1, hcr]; norm_num

end
end SAP.P011b.Bridge
