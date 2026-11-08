import SAP.P009a.Defs.WholeW1
import SAP.P009a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SAP.P009a.WH.W1

open Filter MeasureTheory Bridge
open scoped BigOperators Topology Classical

noncomputable section

/-- The already certified sparse-family content, without importing a Challenge. -/
theorem retainedT1 : T1Statement := by
  refine ⟨AronowAudit.P009.Wave1.sparse_coverage_counterexample_proof, ?_⟩
  intro t
  exact (AronowAudit.P009.sparse_moments_finite t).1

/-- The already certified general coverage and Bernoulli application. -/
theorem retainedT2 : T2Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact @AronowAudit.P009.corrected_coverage
  · exact @AronowAudit.P009.relative_underestimate_inclusion
  · intro S k q s α hReg hBER Vhat hVhat hα hCons hScale
    exact AronowAudit.P009.bernoulli_corrected_coverage
      (toProjectSequence S) k q s α hReg hBER Vhat hVhat hα hCons hScale
  · intro n hn E k q s hReg hBER
    exact AronowAudit.P009.BernoulliCompletion.ht_unbiased (toProjectExperiment E) hBER

/-- A full-cube absolute bound and the assignment bounds give all admissible real moment orders. -/
theorem bounded_regularity {n : ℕ} (E : FiniteExperiment n) (k q s : ℝ)
    (hk : 0 < k) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hp : ∀ i, k⁻¹ ≤ armProbability E i true ∧ armProbability E i true ≤ 1-k⁻¹)
    (hy : ∀ i z, |E.outcome i z| ≤ k) : Regularity E k q s := by
  refine ⟨hk, hq, hs, hp, ?_, ?_⟩
  · intro i
    exact AronowAudit.P009.SparseCompletion.mean_le_constant
      (toProjectDistribution E.design) _ _
      (fun z => Real.rpow_le_rpow (abs_nonneg _) (hy i z) (by linarith))
  · intro i b
    exact AronowAudit.P009.SparseCompletion.mean_le_constant
      (toProjectDistribution E.design) _ _
      (fun z => Real.rpow_le_rpow (abs_nonneg _)
        (hy i (Function.update z i b)) (by linarith))

theorem sparse_bounds (t : ℕ) (i : Fin (t+1)) (z : TreatmentVector (t+1)) :
    0 ≤ (sparseSequence.experiment t).outcome i z ∧
      (sparseSequence.experiment t).outcome i z ≤ 1 := by
  change 0 ≤ (if i.val = 0 then treatmentValue (z i) else 0) ∧
    (if i.val = 0 then treatmentValue (z i) else 0) ≤ 1
  by_cases hi : i.val = 0 <;> cases hz : z i <;> norm_num [hi, treatmentValue, hz]

theorem sparse_marginal (t : ℕ) (i : Fin (t+1)) (b : Bool) :
    armProbability (sparseSequence.experiment t) i b = 1/2 :=
  AronowAudit.P009.SparseCompletion.fair_marginal (t+1)
    (fun j z => if j.val = 0 then AronowAudit.P009.bit (z j) else 0) i b

theorem sparse_all_orders (q s : ℝ) (hq : 2 ≤ q) (hs : 1 ≤ s) :
    SequenceRegularity sparseSequence 2 q s := by
  intro t
  apply bounded_regularity _ 2 q s (by norm_num) hq hs
  · intro i
    rw [sparse_marginal t i true]
    norm_num
  · intro i z
    rw [abs_of_nonneg (sparse_bounds t i z).1]
    linarith [(sparse_bounds t i z).2]

theorem sparse_diagonal (t : ℕ) (i j : Fin (t+1)) :
    interferenceIndicator (sparseSequence.experiment t) i j = (if i = j then 1 else 0) ∧
    dependenceIndicator (sparseSequence.experiment t) i j = (if i = j then 1 else 0) := by
  constructor
  · change AronowAudit.P009.I (AronowAudit.P009.sparseStudy.experiment t) i j = _
    unfold AronowAudit.P009.I
    rw [AronowAudit.P009.SparseCompletion.noI_interferes _
      (AronowAudit.P009.SparseCompletion.sparse_NoI_sequence t) i j]
    by_cases hij : i = j <;> simp [hij]
  · exact AronowAudit.P009.SparseCompletion.noI_d _
      (AronowAudit.P009.SparseCompletion.sparse_NoI_sequence t) i j

theorem sparse_normalizations (t : ℕ) :
    sparseNormalizedBias t = 1/sampleSize sparseSequence t ∧
    sparseNormalizedVariance t = 1/sampleSize sparseSequence t := by
  have hv : variance (sparseSequence.experiment t).design
      (htEstimate (sparseSequence.experiment t)) = 1/sampleSize sparseSequence t^2 :=
    (AronowAudit.P009.sparse_moments_finite t).2.1
  have hm : expectation (sparseSequence.experiment t).design
      (bernoulliVarianceEstimate (sparseSequence.experiment t)) = 2/sampleSize sparseSequence t^2 :=
    (AronowAudit.P009.sparse_moments_finite t).2.2
  have hd : averageDependence (sparseSequence.experiment t) = 1 :=
    (AronowAudit.P009.Wave1.sparseCoverage_graph t).1
  have hn : sampleSize sparseSequence t ≠ 0 := by
    change ((t+1 : ℕ) : ℝ) ≠ 0
    positivity
  simp only [sparseNormalizedBias, sparseNormalizedVariance, hv, hm, hd, div_one]
  constructor
  · field_simp
    norm_num
  · field_simp

theorem sparse_inverse_limit :
    Tendsto (fun t => 1/sampleSize sparseSequence t) atTop (nhds 0) :=
  AronowAudit.P009.SparseCompletion.inv_size_zero

theorem sparse_bias_limit : Tendsto sparseNormalizedBias atTop (nhds 0) := by
  have he : sparseNormalizedBias = (fun t => 1/sampleSize sparseSequence t) :=
    funext (fun t => (sparse_normalizations t).1)
  rw [he]
  exact sparse_inverse_limit

theorem sparse_variance_limit : Tendsto sparseNormalizedVariance atTop (nhds 0) := by
  have he : sparseNormalizedVariance = (fun t => 1/sampleSize sparseSequence t) :=
    funext (fun t => (sparse_normalizations t).2)
  rw [he]
  exact sparse_inverse_limit

def signedWitness : FiniteExperiment 2 := fromProjectExperiment AronowAudit.P009.signedExperiment
def countWitness : FiniteExperiment 2 := fromProjectExperiment AronowAudit.P009.countExperiment
def squareWitness : FiniteExperiment 2 := fromProjectExperiment AronowAudit.P009.squareExperiment
def hypergeomWitness : FiniteExperiment 4 := fromProjectExperiment AronowAudit.P009.hypergeomExperiment
def hypergeomSecondWitness : FiniteExperiment 4 :=
  ⟨fromProjectDistribution AronowAudit.P009.completeFourLaw, fun i z => treatmentValue (z i)⟩

theorem signed_base : W1SignedBase signedWitness countWitness squareWitness := by
  refine ⟨(fun _ => rfl), (fun _ _ => rfl), (fun _ => rfl), (fun _ _ => rfl),
    (fun _ => rfl), (fun _ _ => rfl), ?_⟩
  exact AronowAudit.P009.signed_weight_counterexamples

theorem signed_bounds (i : Fin 2) (z : TreatmentVector 2) :
    |signedWitness.outcome i z| ≤ 1 ∧ |countWitness.outcome i z| ≤ 1 ∧
      |squareWitness.outcome i z| ≤ 1 := by
  fin_cases i <;> cases h0 : z 0 <;> cases h1 : z 1 <;>
    norm_num [signedWitness, countWitness, squareWitness, fromProjectExperiment,
      AronowAudit.P009.signedExperiment, AronowAudit.P009.countExperiment,
      AronowAudit.P009.squareExperiment, AronowAudit.P009.bit, treatmentValue, h0, h1]

theorem signed_all_orders (q s : ℝ) (hq : 2 ≤ q) (hs : 1 ≤ s) :
    Regularity signedWitness 4 q s ∧ Regularity countWitness 4 q s ∧
      Regularity squareWitness 4 q s := by
  have hr := AronowAudit.P009.signed_weight_counterexamples
  refine ⟨bounded_regularity _ 4 q s (by norm_num) hq hs hr.1.2.2.2.1 ?_,
    bounded_regularity _ 4 q s (by norm_num) hq hs hr.2.2.1.2.2.2.1 ?_,
    bounded_regularity _ 4 q s (by norm_num) hq hs hr.2.2.2.1.2.2.2.1 ?_⟩
  · intro i z; linarith [(signed_bounds i z).1]
  · intro i z; linarith [(signed_bounds i z).2.1]
  · intro i z; linarith [(signed_bounds i z).2.2]

/-- The erasure formulation avoids a spurious subtraction when the own unit is absent. -/
theorem other_incoming_count {n : ℕ} (E : FiniteExperiment n) (i : Fin n) :
    (Finset.univ.filter (fun j => j ≠ i ∧ Affects E j i)).card = incomingCount E i - 1 := by
  have he : Finset.univ.filter (fun j => j ≠ i ∧ Affects E j i) =
      (Finset.univ.filter (fun j => Affects E j i)).erase i := by
    ext j
    simp
  rw [he, Finset.card_erase_of_mem]
  · rfl
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl rfl

end
end SAP.P009a.WH.W1
