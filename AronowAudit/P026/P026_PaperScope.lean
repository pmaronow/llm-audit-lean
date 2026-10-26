import AronowAudit.P026.P026_VarianceCompletion

/- Finite probability models for the paper. Randomness is the
allocation vector itself; population size and cluster totals come from the
fixed finite population. -/
namespace AronowAudit.P026.PaperScope
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

structure UnitExperiment (I : Type*) [Fintype I] [DecidableEq I] where
  weight : (I → Bool) → ℝ
  nonnegative : ∀ w, 0 ≤ weight w
  normalized : ∑ w, weight w = 1
  positive : ∀ i, 0 < ∑ w, weight w * (if w i=true then 1 else 0) ∧
    0 < ∑ w, weight w * (if w i=false then 1 else 0)

namespace UnitExperiment
variable {I : Type*} [Fintype I] [DecidableEq I]

def design (E : UnitExperiment I) : Design (I → Bool) I ℝ :=
  ⟨E.weight, fun w => w⟩

theorem probability (E : UnitExperiment I) : probabilityDesign E.design :=
  ⟨E.nonnegative, E.normalized⟩

theorem marginals (E : UnitExperiment I) : positiveMarginals E.design := E.positive

end UnitExperiment

structure ClusterExperiment (U C : Type*) [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] where
  cluster : U → C
  covers : Function.Surjective cluster
  assignment : UnitExperiment C

namespace ClusterExperiment
variable {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

def clusterDesign (E : ClusterExperiment U C) : Design (C → Bool) C ℝ := E.assignment.design
def unitDesign (E : ClusterExperiment U C) : Design (C → Bool) U ℝ :=
  ⟨E.assignment.weight, fun w i => w (E.cluster i)⟩
def totals (E : ClusterExperiment U C) (y : U → ℝ) (c : C) : ℝ :=
  ∑ i ∈ univ.filter (fun i => E.cluster i=c), y i

theorem cluster_probability (E : ClusterExperiment U C) : probabilityDesign E.clusterDesign :=
  E.assignment.probability
theorem cluster_marginals (E : ClusterExperiment U C) : positiveMarginals E.clusterDesign :=
  E.assignment.marginals
theorem unit_probability (E : ClusterExperiment U C) : probabilityDesign E.unitDesign :=
  ⟨E.assignment.nonnegative,E.assignment.normalized⟩
theorem unit_marginals (E : ClusterExperiment U C) : positiveMarginals E.unitDesign :=
  fun i => E.assignment.positive (E.cluster i)

theorem actual_cluster_aggregation (E : ClusterExperiment U C) (y : U → ℝ)
    (a : Bool) (w : C → Bool) :
    htTotal E.unitDesign a y w = htTotal E.clusterDesign a (E.totals y) w := by
  exact cluster_aggregation E.unitDesign E.clusterDesign E.cluster E.covers rfl
    (fun _ _ => rfl) y a w


end ClusterExperiment

/- A fixed covariate matrix, parameter fitting map and prediction map. Fitting
uses the realized allocation and observed responses; no other random argument
is available. This includes predetermined predictions as a special case. -/
structure PredictionRule (I : Type*) [Fintype I] (K Q : ℕ) where
  covariates : I → Fin K → ℝ
  fit : (I → Bool) → (I → ℝ) → (Fin Q → ℝ)
  predict : (Fin K → ℝ) → (Fin Q → ℝ) → ℝ

def PredictionRule.values {I : Type*} [Fintype I] [DecidableEq I] {K Q : ℕ}
    (E : UnitExperiment I) (R : PredictionRule I K Q) (y1 y0 : I → ℝ)
    (w : I → Bool) (i : I) : ℝ :=
  R.predict (R.covariates i) (R.fit w (observed E.design y1 y0 w))

namespace UnitExperiment
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma nonzero_marginal (E : UnitExperiment I) (a : Bool) (i : I) : marginal E.design a i ≠ 0 := by
  cases a
  · exact (E.marginals i).2.ne'
  · exact (E.marginals i).1.ne'
end UnitExperiment

namespace ClusterExperiment
variable {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
end ClusterExperiment

theorem disagreement_identity_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (i j :  C)
    (hij : i ≠ j) :
    disagreement E.clusterDesign i j = joint E.clusterDesign true false i j + joint E.clusterDesign true false j i := by
  exact AronowAudit.P026.disagreement_identity (D := E.clusterDesign) (i := i) (j := j)

theorem disagreement_positive_iff_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (i j :  C)
    (hij : i ≠ j) : 0 < disagreement E.clusterDesign i j ↔
      0 < joint E.clusterDesign true false i j ∨ 0 < joint E.clusterDesign true false j i := by
  exact AronowAudit.P026.disagreement_positive_iff (D := E.clusterDesign) (hD := E.cluster_probability) (i := i) (j := j)

theorem ht_cluster_covariance_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ) : covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) =
      clusterCovarianceExpression E.clusterDesign (E.totals x) (E.totals z) := by
  exact AronowAudit.P026.ht_cluster_covariance (D := E.clusterDesign) (hp := E.cluster_marginals) (x := (E.totals x)) (z := (E.totals z))

theorem printed_variance_bias_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ) :
    ((Fintype.card U) : ℝ)^2 * (expectation E.clusterDesign (printedVariance E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z)) - variance E.clusterDesign (ht E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z))) =
      (∑ i, ((E.totals x) i-(E.totals z) i)^2) + zeroSum E.clusterDesign true true (fun i j => ((E.totals x) i+(E.totals x) j)^2) / 2 +
      zeroSum E.clusterDesign false false (fun i j => ((E.totals z) i+(E.totals z) j)^2) / 2 -
      2 * zeroSum E.clusterDesign true false (fun i j => (E.totals x) i*(E.totals z) j) := by
  exact AronowAudit.P026.printed_variance_bias (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (N := (Fintype.card U)) (hN := Fintype.card_pos) (x := (E.totals x)) (z := (E.totals z))

theorem corrected_covariance_bias_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ) :
    expectation E.clusterDesign (correctedCovariance E.clusterDesign (E.totals x) (E.totals z)) -
      covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) =
      -(∑ i, ((E.totals x) i-(E.totals z) i)^2) / 2 - zeroSum E.clusterDesign true false (fun i j => ((E.totals x) i-(E.totals z) j)^2) / 2 ∧
    expectation E.clusterDesign (correctedCovariance E.clusterDesign (E.totals x) (E.totals z)) ≤
      covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) := by
  exact AronowAudit.P026.corrected_covariance_bias (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (x := (E.totals x)) (z := (E.totals z))

theorem corrected_variance_bias_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ) :
    ((Fintype.card U) : ℝ)^2 * (expectation E.clusterDesign (correctedVariance E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z)) - variance E.clusterDesign (ht E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z))) =
      correctedBiasExpression E.clusterDesign (E.totals x) (E.totals z) ∧
    variance E.clusterDesign (ht E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z)) ≤ expectation E.clusterDesign (correctedVariance E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z)) := by
  exact AronowAudit.P026.corrected_variance_bias (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (N := (Fintype.card U)) (hN := Fintype.card_pos) (x := (E.totals x)) (z := (E.totals z))

theorem corrected_sharp_null_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (c : U → ℝ)
    (hs :  ∀ i j, i ≠ j → 0 < joint E.clusterDesign true true i j ∧ 0 < joint E.clusterDesign false false i j) :
    expectation E.clusterDesign (correctedVariance E.clusterDesign (Fintype.card U) (E.totals c) (E.totals c)) - variance E.clusterDesign (ht E.clusterDesign (Fintype.card U) (E.totals c) (E.totals c)) =
      zeroSum E.clusterDesign true false (fun i j => ((E.totals c) i-(E.totals c) j)^2) / ((Fintype.card U) : ℝ)^2 ∧
    (expectation E.clusterDesign (correctedVariance E.clusterDesign (Fintype.card U) (E.totals c) (E.totals c)) = variance E.clusterDesign (ht E.clusterDesign (Fintype.card U) (E.totals c) (E.totals c)) ↔
      ∀ i j, i ≠ j → joint E.clusterDesign true false i j = 0 → (E.totals c) i = (E.totals c) j) := by
  exact AronowAudit.P026.corrected_sharp_null (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (N := (Fintype.card U)) (hN := Fintype.card_pos) (c := (E.totals c)) (hs := hs)

theorem corrected_variance_decomposition_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ)
    (w :  (C → Bool))
    (hw :  0 < E.clusterDesign.weight w) :
    correctedVariance E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z) w=(armVarianceEstimator E.clusterDesign true (E.totals x) (E.totals z) w+
      armVarianceEstimator E.clusterDesign false (E.totals x) (E.totals z) w-2*correctedCovariance E.clusterDesign (E.totals x) (E.totals z) w)/((Fintype.card U) : ℝ)^2 := by
  exact AronowAudit.P026.corrected_variance_decomposition (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (N := (Fintype.card U)) (hN := Fintype.card_pos) (x := (E.totals x)) (z := (E.totals z)) (w := w) (hw := hw)

theorem corrected_residual_variance_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z r : U → ℝ) :
    ((Fintype.card U) : ℝ)^2 * (expectation E.clusterDesign (correctedVariance E.clusterDesign (Fintype.card U) (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i))-
      variance E.clusterDesign (generalized E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z) (fun _ => (E.totals r)))) =
        correctedBiasExpression E.clusterDesign (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i) ∧
    variance E.clusterDesign (generalized E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z) (fun _ => (E.totals r))) ≤
      expectation E.clusterDesign (correctedVariance E.clusterDesign (Fintype.card U) (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i)) := by
  exact AronowAudit.P026.corrected_residual_variance (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (N := (Fintype.card U)) (hN := Fintype.card_pos) (x := (E.totals x)) (z := (E.totals z)) (r := (E.totals r))

theorem correctedBiasExpression_nonneg_T2 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ) :
    0 ≤ correctedBiasExpression E.clusterDesign (E.totals x) (E.totals z) := by
  exact AronowAudit.P026.correctedBiasExpression_nonneg (D := E.clusterDesign) (x := (E.totals x)) (z := (E.totals z))

theorem support_repair_T3 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (hcross :  crossSupport E.clusterDesign)
    (x z : U → ℝ) :
    expectation E.clusterDesign (printedCovariance E.clusterDesign (E.totals x) (E.totals z)) - covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) =
      -(∑ i, ((E.totals x) i-(E.totals z) i)^2) / 2 ∧
    expectation E.clusterDesign (printedCovariance E.clusterDesign (E.totals x) (E.totals z)) ≤ covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) ∧
    ((Fintype.card U) : ℝ)^2 * (expectation E.clusterDesign (printedVariance E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z)) - variance E.clusterDesign (ht E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z))) =
      (∑ i, ((E.totals x) i-(E.totals z) i)^2) + zeroSum E.clusterDesign true true (fun i j => ((E.totals x) i+(E.totals x) j)^2) / 2 +
        zeroSum E.clusterDesign false false (fun i j => ((E.totals z) i+(E.totals z) j)^2) / 2 ∧
    variance E.clusterDesign (ht E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z)) ≤ expectation E.clusterDesign (printedVariance E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z)) ∧
    ((∀ i, (E.totals x) i = (E.totals z) i) →
      (∀ i j, i ≠ j → 0 < joint E.clusterDesign true true i j ∧ 0 < joint E.clusterDesign false false i j) →
      expectation E.clusterDesign (printedVariance E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z)) = variance E.clusterDesign (ht E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z))) := by
  exact AronowAudit.P026.support_repair (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (hcross := hcross) (N := (Fintype.card U)) (hN := Fintype.card_pos) (x := (E.totals x)) (z := (E.totals z))

theorem support_residual_variance_T3 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (hc :  crossSupport E.clusterDesign)
    (x z r : U → ℝ) :
    variance E.clusterDesign (generalized E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z) (fun _ => (E.totals r))) ≤
      expectation E.clusterDesign (printedVariance E.clusterDesign (Fintype.card U) (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i)) ∧
    ((∀ i, (E.totals x) i=(E.totals z) i) → (∀ i j, i ≠ j → 0 < joint E.clusterDesign true true i j ∧ 0 < joint E.clusterDesign false false i j) →
      expectation E.clusterDesign (printedVariance E.clusterDesign (Fintype.card U) (fun i => (E.totals x) i-(E.totals r) i) (fun i => (E.totals z) i-(E.totals r) i))=
        variance E.clusterDesign (generalized E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z) (fun _ => (E.totals r)))) := by
  exact AronowAudit.P026.support_residual_variance (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (hc := hc) (N := (Fintype.card U)) (hN := Fintype.card_pos) (x := (E.totals x)) (z := (E.totals z)) (r := (E.totals r))

theorem vector_fitting_independence_T5 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    {Θ :  Type*}
    (i :  I)
    (J :  Finset I)
    (y1 y0 :  I → ℝ)
    (G :  (↥J → ℝ) → Θ)
    (P :  Θ → ℝ)
    (h :  independent E.design (fun w => E.design.treatment w i) (fittingAssignments E.design J)) :
    independent E.design (fun w => E.design.treatment w i) (fun w => G (fittingOutcomes E.design J y1 y0 w)) ∧
    independent E.design (fun w => E.design.treatment w i) (fun w => P (G (fittingOutcomes E.design J y1 y0 w))) ∧
    covariance E.design (fun w => indicator E.design true w i)
      (fun w => P (G (fittingOutcomes E.design J y1 y0 w))) = 0 := by
  exact AronowAudit.P026.vector_fitting_independence (Θ := Θ) (D := E.design) (i := i) (J := J) (y1 := y1) (y0 := y0) (G := G) (P := P) (h := h)

theorem outcome_vector_fitting_independence_T5 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    {Θ :  Type*}
    (i :  I)
    (J :  Finset I)
    (y1 y0 :  I → ℝ)
    (G :  (↥J → ℝ) → Θ)
    (P :  Θ → ℝ)
    (h :  independent E.design (fun w => E.design.treatment w i) (fittingOutcomes E.design J y1 y0)) :
    independent E.design (fun w => E.design.treatment w i) (fun w => G (fittingOutcomes E.design J y1 y0 w)) ∧
    independent E.design (fun w => E.design.treatment w i) (fun w => P (G (fittingOutcomes E.design J y1 y0 w))) ∧
    covariance E.design (fun w => indicator E.design true w i)
      (fun w => P (G (fittingOutcomes E.design J y1 y0 w))) = 0 := by
  exact AronowAudit.P026.outcome_vector_fitting_independence (Θ := Θ) (D := E.design) (i := i) (J := J) (y1 := y1) (y0 := y0) (G := G) (P := P) (h := h)

theorem vector_fitting_unbiased_T5 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z :  I → ℝ)
    (J :  I → Finset I)
    (G :  ∀ i, (↥(J i) → ℝ) → ℝ)
    (h :  ∀ i, independent E.design (fun w => E.design.treatment w i) (fittingAssignments E.design (J i))) :
    let f : (I → Bool) → I → ℝ := fun w i => G i (fittingOutcomes E.design (J i) x z w)
    expectation E.design (generalizedTotal E.design true x f)=populationTotal x ∧
    expectation E.design (generalizedTotal E.design false z f)=populationTotal z ∧
    expectation E.design (generalized E.design (Fintype.card I) x z f)=ate (Fintype.card I) x z := by
  exact AronowAudit.P026.vector_fitting_unbiased (D := E.design) (hD := E.probability) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (x := x) (z := z) (J := J) (G := G) (h := h)

theorem additive_fitting_unbiased_T5 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (i :  I)
    (J :  Finset I)
    (x z :  I → ℝ)
    (a :  ℝ)
    (b :  ↥J → ℝ)
    (h :  ∀ j : ↥J, independent E.design (fun w => E.design.treatment w i) (fun w => E.design.treatment w j)) :
    covariance E.design (fun w => indicator E.design true w i)
      (fun w => a+∑ j : ↥J, b j*observed E.design x z w j) =
        ∑ j : ↥J, b j*(x j-z j)*covariance E.design
          (fun w => indicator E.design true w i) (fun w => indicator E.design true w j) ∧
    covariance E.design (fun w => indicator E.design true w i)
      (fun w => a+∑ j : ↥J, b j*observed E.design x z w j)=0 := by
  exact AronowAudit.P026.additive_fitting_unbiased (D := E.design) (hD := E.probability) (i := i) (J := J) (x := x) (z := z) (a := a) (b := b) (h := h)

theorem ht_cluster_covariance_T8 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ) : covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) =
      clusterCovarianceExpression E.clusterDesign (E.totals x) (E.totals z) := by
  exact AronowAudit.P026.ht_cluster_covariance (D := E.clusterDesign) (hp := E.cluster_marginals) (x := (E.totals x)) (z := (E.totals z))

theorem covariance_bound_gap_T8 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ) :
    covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) - covarianceBound E.clusterDesign (E.totals x) (E.totals z) =
      (∑ i, ((E.totals x) i-(E.totals z) i)^2) / 2 := by
  exact AronowAudit.P026.covariance_bound_gap (D := E.clusterDesign) (hp := E.cluster_marginals) (x := (E.totals x)) (z := (E.totals z))

theorem appendixE_corrected_T8 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (hc :  crossSupport E.clusterDesign)
    (x z : U → ℝ) :
    expectation E.clusterDesign (printedCovariance E.clusterDesign (E.totals x) (E.totals z)) = covarianceBound E.clusterDesign (E.totals x) (E.totals z) ∧
    expectation E.clusterDesign (printedCovariance E.clusterDesign (E.totals x) (E.totals z)) ≤ covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) ∧
    (expectation E.clusterDesign (printedCovariance E.clusterDesign (E.totals x) (E.totals z)) = covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) ↔
      ∀ i, (E.totals x) i = (E.totals z) i) := by
  exact AronowAudit.P026.appendixE_corrected (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (hc := hc) (x := (E.totals x)) (z := (E.totals z))

theorem cluster_aggregation_T10 {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] [Nonempty U] (E : ClusterExperiment U C)
    (y : U → ℝ) (a : Bool) (w : C → Bool) :
    htTotal E.unitDesign a y w = htTotal E.clusterDesign a (E.totals y) w :=
  E.actual_cluster_aggregation y a w

theorem ht_arm_variance_T11 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (a :  Bool)
    (y : U → ℝ) :
    variance E.clusterDesign (htTotal E.clusterDesign a (E.totals y)) = armVarianceExpression E.clusterDesign a (E.totals y) := by
  exact AronowAudit.P026.ht_arm_variance (D := E.clusterDesign) (a := a) (y := (E.totals y))

theorem arm_variance_corrected_T11 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (a :  Bool)
    (x z : U → ℝ) :
    let y := if a then (E.totals x) else (E.totals z)
    armVarianceBound E.clusterDesign a y - variance E.clusterDesign (htTotal E.clusterDesign a y) =
      zeroSum E.clusterDesign a a (fun i j => (y i+y j)^2) / 2 ∧
    expectation E.clusterDesign (armVarianceEstimator E.clusterDesign a (E.totals x) (E.totals z)) = armVarianceBound E.clusterDesign a y ∧
    variance E.clusterDesign (htTotal E.clusterDesign a y) ≤ expectation E.clusterDesign (armVarianceEstimator E.clusterDesign a (E.totals x) (E.totals z)) ∧
    ((∀ i j, i ≠ j → 0 < joint E.clusterDesign a a i j) →
      expectation E.clusterDesign (armVarianceEstimator E.clusterDesign a (E.totals x) (E.totals z)) = variance E.clusterDesign (htTotal E.clusterDesign a y)) := by
  exact AronowAudit.P026.arm_variance_corrected (D := E.clusterDesign) (hD := E.cluster_probability) (hp := E.cluster_marginals) (a := a) (x := (E.totals x)) (z := (E.totals z))

theorem unit_sampling_variance_identity_T12 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z :  I → ℝ) :
    variance E.design (ht E.design (Fintype.card I) x z)=
      (armVarianceExpression E.design true x+armVarianceExpression E.design false z-
        2*splitCovarianceExpression E.design x z)/(Fintype.card I : ℝ)^2 := by
  exact AronowAudit.P026.unit_sampling_variance_identity (D := E.design) (hp := E.marginals) (hN := Fintype.card_pos) (x := x) (z := z)

theorem variance_sub_div_T12 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (f g :  (I → Bool) → ℝ)
    (c :  ℝ) :
    variance E.design (fun w => (f w-g w)/c) =
      (variance E.design f+variance E.design g-2*covariance E.design f g)/c^2 := by
  exact AronowAudit.P026.variance_sub_div (D := E.design) (f := f) (g := g) (c := c)

theorem ht_covariance_full_T12 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (a b :  Bool)
    (x z :  I → ℝ) :
    covariance E.design (htTotal E.design a x) (htTotal E.design b z) =
      ∑ i, ∑ j, (joint E.design a b i j - marginal E.design a i * marginal E.design b j) *
        (x i / marginal E.design a i) * (z j / marginal E.design b j) := by
  exact AronowAudit.P026.ht_covariance_full (D := E.design) (a := a) (b := b) (x := x) (z := z)

theorem ht_arm_variance_T12 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (a :  Bool)
    (y :  I → ℝ) :
    variance E.design (htTotal E.design a y) = armVarianceExpression E.design a y := by
  exact AronowAudit.P026.ht_arm_variance (D := E.design) (a := a) (y := y)

theorem ht_covariance_split_T12 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z :  I → ℝ) :
    covariance E.design (htTotal E.design true x) (htTotal E.design false z) = splitCovarianceExpression E.design x z := by
  exact AronowAudit.P026.ht_covariance_split (D := E.design) (hp := E.marginals) (x := x) (z := z)

theorem ht_variance_identity_T12 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z :  I → ℝ) : variance E.design (ht E.design (Fintype.card I) x z) =
      (armVarianceExpression E.design true x + armVarianceExpression E.design false z -
        2*splitCovarianceExpression E.design x z) / ((Fintype.card I) : ℝ)^2 := by
  exact AronowAudit.P026.ht_variance_identity (D := E.design) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (x := x) (z := z)

theorem unit_generalized_bias_T13 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q) :
    expectation E.design (generalized E.design (Fintype.card I) x z (rule.values E x z))-ate (Fintype.card I) x z=
      -(∑ i, covariance E.design (fun w => indicator E.design true w i) (fun w => (rule.values E x z) w i)*
        (1/marginal E.design true i+1/marginal E.design false i))/(Fintype.card I : ℝ) := by
  exact AronowAudit.P026.unit_generalized_bias (D := E.design) (hD := E.probability) (hp := E.marginals) (hN := Fintype.card_pos) (x := x) (z := z) (f := (rule.values E x z))

theorem generalized_total_bias_T13 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (a :  Bool)
    (y1 y0 : I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q) :
    expectation E.design (generalizedTotal E.design a (if a then y1 else y0) (rule.values E y1 y0)) = populationTotal (if a then y1 else y0) -
      ∑ i, covariance E.design (fun w => indicator E.design a w i)
        (fun w => (rule.values E y1 y0) w i / marginal E.design a i) := by
  exact AronowAudit.P026.generalized_total_bias (D := E.design) (a := a) (y := (if a then y1 else y0)) (f := (rule.values E y1 y0)) (hp := (fun i => E.nonzero_marginal a i))

theorem generalized_bias_T13 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q) :
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 (rule.values E y1 y0)) - ate (Fintype.card I) y1 y0 =
      ((∑ i, covariance E.design (fun w => indicator E.design false w i)
        (fun w => (rule.values E y1 y0) w i / marginal E.design false i)) -
       (∑ i, covariance E.design (fun w => indicator E.design true w i)
        (fun w => (rule.values E y1 y0) w i / marginal E.design true i))) / (Fintype.card I) := by
  exact AronowAudit.P026.generalized_bias (D := E.design) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (y1 := y1) (y0 := y0) (f := (rule.values E y1 y0))

theorem generalized_bias_two_arm_T13 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q) : expectation E.design (generalized E.design (Fintype.card I) y1 y0 (rule.values E y1 y0)) - ate (Fintype.card I) y1 y0 =
      -(∑ i, covariance E.design (fun w => indicator E.design true w i) (fun w => (rule.values E y1 y0) w i) *
        (1 / marginal E.design true i + 1 / marginal E.design false i)) / (Fintype.card I) := by
  exact AronowAudit.P026.generalized_bias_two_arm (D := E.design) (hD := E.probability) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (y1 := y1) (y0 := y0) (f := (rule.values E y1 y0))

theorem fixed_prediction_unbiased_T16 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 g :  I → ℝ) :
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 (fun _ => g)) = ate (Fintype.card I) y1 y0 := by
  exact AronowAudit.P026.fixed_prediction_unbiased (D := E.design) (hD := E.probability) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (y1 := y1) (y0 := y0) (g := g)

theorem generalized_residual_T16 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q)
    (w :  (I → Bool)) : generalized E.design (Fintype.card I) y1 y0 (rule.values E y1 y0) w =
      ht E.design (Fintype.card I) (fun i => y1 i - (rule.values E y1 y0) w i) (fun i => y0 i - (rule.values E y1 y0) w i) w := by
  exact AronowAudit.P026.generalized_residual (D := E.design) (N := (Fintype.card I)) (y1 := y1) (y0 := y0) (f := (rule.values E y1 y0)) (w := w)


theorem generalized_unbiased_T16 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q)
    (hf :  ∀ i, covariance E.design (fun w => indicator E.design true w i) (fun w => (rule.values E y1 y0) w i) = 0) :
    expectation E.design (generalizedTotal E.design true y1 (rule.values E y1 y0)) = populationTotal y1 ∧
    expectation E.design (generalizedTotal E.design false y0 (rule.values E y1 y0)) = populationTotal y0 ∧
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 (rule.values E y1 y0)) = ate (Fintype.card I) y1 y0 := by
  exact AronowAudit.P026.generalized_unbiased (D := E.design) (hD := E.probability) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (y1 := y1) (y0 := y0) (f := (rule.values E y1 y0)) (hf := hf)

theorem sharp_null_fit_unbiased_T16 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x :  I → ℝ)
    (G :  (I → ℝ) → (I → ℝ)) :
    expectation E.design (generalized E.design (Fintype.card I) x x (fun w => G (observed E.design x x w)))=ate (Fintype.card I) x x := by
  exact AronowAudit.P026.sharp_null_fit_unbiased (D := E.design) (hD := E.probability) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (x := x) (G := G)

theorem htTotal_unbiased_T20 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (a :  Bool)
    (y :  I → ℝ) :
    expectation E.design (htTotal E.design a y) = populationTotal y := by
  exact AronowAudit.P026.htTotal_unbiased (D := E.design) (a := a) (y := y) (h := (fun i => E.nonzero_marginal a i))

theorem ht_unbiased_T20 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 :  I → ℝ) :
    expectation E.design (htTotal E.design true y1) = populationTotal y1 ∧
    expectation E.design (htTotal E.design false y0) = populationTotal y0 ∧
    expectation E.design (ht E.design (Fintype.card I) y1 y0) = ate (Fintype.card I) y1 y0 := by
  exact AronowAudit.P026.ht_unbiased (D := E.design) (hD := E.probability) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (y1 := y1) (y0 := y0)

theorem unit_generalized_unbiased_T22 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q)
    (hf :  ∀ i, covariance E.design (fun w => indicator E.design true w i) (fun w => (rule.values E x z) w i)=0) :
    expectation E.design (generalizedTotal E.design true x (rule.values E x z))=populationTotal x ∧
    expectation E.design (generalizedTotal E.design false z (rule.values E x z))=populationTotal z ∧
    expectation E.design (generalized E.design (Fintype.card I) x z (rule.values E x z))=ate (Fintype.card I) x z := by
  exact AronowAudit.P026.unit_generalized_unbiased (D := E.design) (hD := E.probability) (hp := E.marginals) (hN := Fintype.card_pos) (x := x) (z := z) (f := (rule.values E x z)) (hf := hf)

theorem generalized_unbiased_T22 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q)
    (hf :  ∀ i, covariance E.design (fun w => indicator E.design true w i) (fun w => (rule.values E y1 y0) w i) = 0) :
    expectation E.design (generalizedTotal E.design true y1 (rule.values E y1 y0)) = populationTotal y1 ∧
    expectation E.design (generalizedTotal E.design false y0 (rule.values E y1 y0)) = populationTotal y0 ∧
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 (rule.values E y1 y0)) = ate (Fintype.card I) y1 y0 := by
  exact AronowAudit.P026.generalized_unbiased (D := E.design) (hD := E.probability) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (y1 := y1) (y0 := y0) (f := (rule.values E y1 y0)) (hf := hf)

theorem generalized_adjustment_T22 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q)
    (w :  (I → Bool)) : generalized E.design (Fintype.card I) y1 y0 (rule.values E y1 y0) w = ht E.design (Fintype.card I) y1 y0 w -
      (htTotal E.design true ((rule.values E y1 y0) w) w - htTotal E.design false ((rule.values E y1 y0) w) w) / (Fintype.card I) := by
  exact AronowAudit.P026.generalized_adjustment (D := E.design) (N := (Fintype.card I)) (y1 := y1) (y0 := y0) (f := (rule.values E y1 y0)) (w := w)

theorem fixed_prediction_unbiased_T22 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 g :  I → ℝ) :
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 (fun _ => g)) = ate (Fintype.card I) y1 y0 := by
  exact AronowAudit.P026.fixed_prediction_unbiased (D := E.design) (hD := E.probability) (hp := E.marginals) (N := (Fintype.card I)) (hN := Fintype.card_pos) (y1 := y1) (y0 := y0) (g := g)

theorem htTotal_affine_T23 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (a :  Bool)
    (x :  I → ℝ)
    (b0 b1 :  ℝ)
    (w :  (I → Bool)) : htTotal E.design a (fun i => b0+b1*x i) w =
      b0*(∑ i, indicator E.design a w i/marginal E.design a i)+b1*htTotal E.design a x w := by
  exact AronowAudit.P026.htTotal_affine (D := E.design) (a := a) (x := x) (b0 := b0) (b1 := b1) (w := w)

theorem ht_affine_T23 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z :  I → ℝ)
    (b0 b1 :  ℝ)
    (w :  (I → Bool)) :
    ht E.design (Fintype.card I) (fun i => b0+b1*x i) (fun i => b0+b1*z i) w =
      b0/((Fintype.card I) : ℝ) * ((∑ i, indicator E.design true w i/marginal E.design true i) -
        (∑ i, indicator E.design false w i/marginal E.design false i)) + b1*ht E.design (Fintype.card I) x z w := by
  exact AronowAudit.P026.ht_affine (D := E.design) (N := (Fintype.card I)) (x := x) (z := z) (b0 := b0) (b1 := b1) (w := w)

theorem ht_affine_invariant_iff_T23 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z :  I → ℝ)
    (b0 b1 :  ℝ)
    (w :  (I → Bool)) :
    ht E.design (Fintype.card I) (fun i => b0+b1*x i) (fun i => b0+b1*z i) w = b1*ht E.design (Fintype.card I) x z w ↔
      b0=0 ∨ (∑ i, indicator E.design true w i/marginal E.design true i) =
        (∑ i, indicator E.design false w i/marginal E.design false i) := by
  exact AronowAudit.P026.ht_affine_invariant_iff (D := E.design) (N := (Fintype.card I)) (hN := Fintype.card_pos) (x := x) (z := z) (b0 := b0) (b1 := b1) (w := w)

theorem generalized_affine_T23 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q)
    (b0 b1 :  ℝ)
    (w :  (I → Bool)) :
    generalized E.design (Fintype.card I) (fun i => b0+b1*x i) (fun i => b0+b1*z i)
      (fun v i => b0+b1*(rule.values E x z) v i) w = b1*generalized E.design (Fintype.card I) x z (rule.values E x z) w := by
  exact AronowAudit.P026.generalized_affine (D := E.design) (N := (Fintype.card I)) (x := x) (z := z) (f := (rule.values E x z)) (b0 := b0) (b1 := b1) (w := w)

theorem unit_generalized_fixed_variance_T24 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (x z r :  I → ℝ) :
    variance E.design (generalized E.design (Fintype.card I) x z (fun _ => r))=
      (armVarianceExpression E.design true (fun i => x i-r i)+
       armVarianceExpression E.design false (fun i => z i-r i)-
       2*splitCovarianceExpression E.design (fun i => x i-r i) (fun i => z i-r i))/(Fintype.card I : ℝ)^2 := by
  exact AronowAudit.P026.unit_generalized_fixed_variance (D := E.design) (hp := E.marginals) (hN := Fintype.card_pos) (x := x) (z := z) (r := r)

theorem generalized_residual_T24 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (E : UnitExperiment I)
    (y1 y0 :  I → ℝ)
    (K Q : ℕ)
    (rule : PredictionRule I K Q)
    (w :  (I → Bool)) : generalized E.design (Fintype.card I) y1 y0 (rule.values E y1 y0) w =
      ht E.design (Fintype.card I) (fun i => y1 i - (rule.values E y1 y0) w i) (fun i => y0 i - (rule.values E y1 y0) w i) w := by
  exact AronowAudit.P026.generalized_residual (D := E.design) (N := (Fintype.card I)) (y1 := y1) (y0 := y0) (f := (rule.values E y1 y0)) (w := w)

theorem generalized_fixed_variance_T24 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z f : U → ℝ) :
    variance E.clusterDesign (generalized E.clusterDesign (Fintype.card U) (E.totals x) (E.totals z) (fun _ => (E.totals f))) =
      (armVarianceExpression E.clusterDesign true (fun i => (E.totals x) i-(E.totals f) i) +
       armVarianceExpression E.clusterDesign false (fun i => (E.totals z) i-(E.totals f) i) -
       2*splitCovarianceExpression E.clusterDesign (fun i => (E.totals x) i-(E.totals f) i) (fun i => (E.totals z) i-(E.totals f) i)) / ((Fintype.card U) : ℝ)^2 := by
  exact AronowAudit.P026.generalized_fixed_variance (D := E.clusterDesign) (hp := E.cluster_marginals) (N := (Fintype.card U)) (hN := Fintype.card_pos) (x := (E.totals x)) (z := (E.totals z)) (f := (E.totals f))

theorem ht_arm_variance_T24 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (a :  Bool)
    (y : U → ℝ) :
    variance E.clusterDesign (htTotal E.clusterDesign a (E.totals y)) = armVarianceExpression E.clusterDesign a (E.totals y) := by
  exact AronowAudit.P026.ht_arm_variance (D := E.clusterDesign) (a := a) (y := (E.totals y))

theorem ht_covariance_full_T24 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (a b :  Bool)
    (x z : U → ℝ) :
    covariance E.clusterDesign (htTotal E.clusterDesign a (E.totals x)) (htTotal E.clusterDesign b (E.totals z)) =
      ∑ i, ∑ j, (joint E.clusterDesign a b i j - marginal E.clusterDesign a i * marginal E.clusterDesign b j) *
        ((E.totals x) i / marginal E.clusterDesign a i) * ((E.totals z) j / marginal E.clusterDesign b j) := by
  exact AronowAudit.P026.ht_covariance_full (D := E.clusterDesign) (a := a) (b := b) (x := (E.totals x)) (z := (E.totals z))

theorem ht_covariance_split_T24 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ) :
    covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) = splitCovarianceExpression E.clusterDesign (E.totals x) (E.totals z) := by
  exact AronowAudit.P026.ht_covariance_split (D := E.clusterDesign) (hp := E.cluster_marginals) (x := (E.totals x)) (z := (E.totals z))

theorem ht_cluster_covariance_T24 {U C : Type*} [Fintype U] [DecidableEq U] [Nonempty U] [Fintype C] [DecidableEq C] [Nonempty C] (E : ClusterExperiment U C)
    (hseparated : ∀ c d, c ≠ d → 0 < disagreement E.clusterDesign c d)
    (x z : U → ℝ) : covariance E.clusterDesign (htTotal E.clusterDesign true (E.totals x)) (htTotal E.clusterDesign false (E.totals z)) =
      clusterCovarianceExpression E.clusterDesign (E.totals x) (E.totals z) := by
  exact AronowAudit.P026.ht_cluster_covariance (D := E.clusterDesign) (hp := E.cluster_marginals) (x := (E.totals x)) (z := (E.totals z))

end
end AronowAudit.P026.PaperScope
