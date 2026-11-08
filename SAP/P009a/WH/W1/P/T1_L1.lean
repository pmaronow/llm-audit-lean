import SAP.P009a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SAP.P009a.WH.W1.P.T1_L1

open SAP.P009a
open SAP.P009a.Bridge
open scoped BigOperators Classical

noncomputable section

def firstIndex (t : ℕ) : Fin (sparseSequence.N t) :=
  ⟨0, by simp [sparseSequence]⟩

lemma firstIndex_eq (t : ℕ) : firstIndex t = (0 : Fin (t+1)) := by
  apply Fin.ext
  rfl

lemma project_experiment (t : ℕ) :
    toProjectExperiment (sparseSequence.experiment t) =
      AronowAudit.P009.sparseStudy.experiment t := by
  rfl

lemma avg_one (t : ℕ) : averageDependence (sparseSequence.experiment t) = 1 := by
  change AronowAudit.P009.dAvg
    (toProjectExperiment (sparseSequence.experiment t)) = 1
  rw [project_experiment]
  exact (AronowAudit.P009.Wave1.sparseCoverage_graph t).1

lemma max_one (t : ℕ) : maximumDependence (sparseSequence.experiment t) = 1 := by
  change AronowAudit.P009.dMax
    (toProjectExperiment (sparseSequence.experiment t)) = 1
  rw [project_experiment]
  exact (AronowAudit.P009.Wave1.sparseCoverage_graph t).2.1

lemma spectral_one (t : ℕ) : spectralRadius (sparseSequence.experiment t) = 1 := by
  change AronowAudit.P009.lambdaMax
    (toProjectExperiment (sparseSequence.experiment t)) = 1
  rw [project_experiment]
  exact (AronowAudit.P009.Wave1.sparseCoverage_graph t).2.2.2

lemma bernoulli_value (t : ℕ) (z : TreatmentVector (t+1)) :
    bernoulliVarianceEstimate (sparseSequence.experiment t) z =
      4 * treatmentValue (z 0) / (sampleSize sparseSequence t)^2 := by
  change AronowAudit.P009.vBER
    (toProjectExperiment (sparseSequence.experiment t)) z =
      4 * AronowAudit.P009.bit (z 0) / (t+1:ℕ)^2
  rw [project_experiment]
  simpa [treatmentValue, AronowAudit.P009.bit, sampleSize, sparseSequence,
    AronowAudit.P009.sparseStudy] using (AronowAudit.P009.sparse_estimators_finite t z).2

lemma variance_value (t : ℕ) :
    variance (sparseSequence.experiment t).design
      (htEstimate (sparseSequence.experiment t)) =
        1 / (sampleSize sparseSequence t)^2 := by
  change AronowAudit.P009.var
    (toProjectExperiment (sparseSequence.experiment t)).design
    (AronowAudit.P009.ht (toProjectExperiment (sparseSequence.experiment t))) =
      1 / (t+1:ℕ)^2
  rw [project_experiment]
  exact AronowAudit.P009.sparse_moments_finite t |>.2.1

lemma msq_value (t : ℕ) :
    meanSquaredEffect (sparseSequence.experiment t) =
      1 / sampleSize sparseSequence t := by
  change AronowAudit.P009.msq
    (toProjectExperiment (sparseSequence.experiment t)) = 1 / (t+1:ℕ)
  rw [project_experiment]
  simpa [sampleSize, sparseSequence, AronowAudit.P009.sparseStudy,
    AronowAudit.P009.size] using
    AronowAudit.P009.Wave1.sparseCoverage_msq t

lemma all_variances_eq (t : ℕ) (a : Fin 4) (z : TreatmentVector (t+1)) :
    wholeVarianceEstimate (sparseSequence.experiment t) a z =
      bernoulliVarianceEstimate (sparseSequence.experiment t) z := by
  fin_cases a <;>
    simp [wholeVarianceEstimate, averageVarianceEstimate, maximumVarianceEstimate,
      spectralVarianceEstimate, avg_one, max_one, spectral_one]

lemma scaled_explicit_first (t : ℕ) (a : Fin 4) (z : TreatmentVector (t+1)) :
    sparseScaledError a t z =
      (4 * treatmentValue (z 0) - 1) / sampleSize sparseSequence t := by
  have hN : sampleSize sparseSequence t = (t+1:ℕ) := rfl
  have hNpos : 0 < sampleSize sparseSequence t := by rw [hN]; positivity
  have hNne : sampleSize sparseSequence t ≠ 0 := ne_of_gt hNpos
  unfold sparseScaledError
  dsimp only
  rw [all_variances_eq, avg_one, bernoulli_value, variance_value]
  field_simp [hNne]

lemma scaled_explicit (t : ℕ) (a : Fin 4) (z : TreatmentVector (t+1)) :
    sparseScaledError a t z =
      (4 * treatmentValue (z 0) - 1) / sampleSize sparseSequence t ∧
    sparseScaledError a t z =
      if z 0 then 3 / sampleSize sparseSequence t else -1 / sampleSize sparseSequence t := by
  have hNne : sampleSize sparseSequence t ≠ 0 := by
    have : sampleSize sparseSequence t = (t+1:ℕ) := rfl
    rw [this]
    positivity
  constructor
  · exact scaled_explicit_first t a z
  · rw [scaled_explicit_first t a z]
    cases z 0 <;> simp [treatmentValue] <;>
      field_simp [hNne] <;> norm_num

lemma coordinate_probability (t : ℕ) (f : Bool → Prop) :
    probability (sparseSequence.experiment t).design (fun z => f (z (firstIndex t))) =
      ((if f true then (1:ℝ) else 0) + (if f false then 1 else 0)) / 2 := by
  change AronowAudit.P009.prob (AronowAudit.P009.fairLaw (t+1))
      (fun z : AronowAudit.P009.Assignment (t+1) => f (z (firstIndex t))) = _
  unfold AronowAudit.P009.prob
  change AronowAudit.P009.mean (AronowAudit.P009.fairLaw (t+1))
    (fun z => if f (z (firstIndex t)) then (1:ℝ) else 0) = _
  rw [firstIndex_eq t]
  exact AronowAudit.P009.fair_first_coordinate t
    (fun b => if f b then (1:ℝ) else 0)

lemma scaled_atom_probability (t : ℕ) (a : Fin 4) (b : Bool) :
    probability (sparseSequence.experiment t).design (fun z =>
      sparseScaledError a t z =
        if b then 3 / sampleSize sparseSequence t else
          -1 / sampleSize sparseSequence t) = 1/2 := by
  have hevent : (fun z : TreatmentVector (sparseSequence.N t) =>
      sparseScaledError a t z =
        if b then 3 / sampleSize sparseSequence t else
          -1 / sampleSize sparseSequence t) = (fun z => z (firstIndex t) = b) := by
    funext z
    apply propext
    rw [(scaled_explicit t a z).2]
    have hn : sampleSize sparseSequence t ≠ 0 := by
      have : sampleSize sparseSequence t = (t+1:ℕ) := rfl
      rw [this]
      positivity
    cases b <;> cases hz : z (firstIndex t)
    all_goals
      have hz0 : z (0 : Fin (t+1)) = z (firstIndex t) := by
        rw [firstIndex_eq t]
      rw [hz0, hz]
      simp [hn] <;> field_simp [hn] <;> norm_num
  calc
    _ = probability (sparseSequence.experiment t).design
        (fun z => z (firstIndex t) = b) :=
          congrArg (probability (sparseSequence.experiment t).design) hevent
    _ = 1/2 := by
      have hp := coordinate_probability t (fun x => x = b)
      cases b <;> simpa using hp

lemma centered_explicit_first (t : ℕ) (z : TreatmentVector (t+1)) :
    sparseCenteredError t z =
      (4 * treatmentValue (z 0) - 2) / sampleSize sparseSequence t := by
  have hN : sampleSize sparseSequence t = (t+1:ℕ) := rfl
  have hNne : sampleSize sparseSequence t ≠ 0 := by rw [hN]; positivity
  unfold sparseCenteredError
  dsimp only
  rw [bernoulli_value, variance_value, msq_value]
  field_simp [hNne]
  <;> ring

lemma centered_explicit (t : ℕ) (z : TreatmentVector (t+1)) :
    sparseCenteredError t z =
      (4 * treatmentValue (z 0) - 2) / sampleSize sparseSequence t ∧
    sparseCenteredError t z =
      if z 0 then 2 / sampleSize sparseSequence t else
        -2 / sampleSize sparseSequence t := by
  have hNne : sampleSize sparseSequence t ≠ 0 := by
    have : sampleSize sparseSequence t = (t+1:ℕ) := rfl
    rw [this]
    positivity
  constructor
  · exact centered_explicit_first t z
  · rw [centered_explicit_first t z]
    cases z 0 <;> simp [treatmentValue] <;>
      field_simp [hNne] <;> norm_num

lemma centered_atom_probability (t : ℕ) (b : Bool) :
    probability (sparseSequence.experiment t).design (fun z =>
      sparseCenteredError t z =
        if b then 2 / sampleSize sparseSequence t else
          -2 / sampleSize sparseSequence t) = 1/2 := by
  have hevent : (fun z : TreatmentVector (sparseSequence.N t) =>
      sparseCenteredError t z =
        if b then 2 / sampleSize sparseSequence t else
          -2 / sampleSize sparseSequence t) = (fun z => z (firstIndex t) = b) := by
    funext z
    apply propext
    rw [(centered_explicit t z).2]
    have hn : sampleSize sparseSequence t ≠ 0 := by
      have : sampleSize sparseSequence t = (t+1:ℕ) := rfl
      rw [this]
      positivity
    cases b <;> cases hz : z (firstIndex t)
    all_goals
      have hz0 : z (0 : Fin (t+1)) = z (firstIndex t) := by
        rw [firstIndex_eq t]
      rw [hz0, hz]
      simp [hn] <;> field_simp [hn] <;> norm_num
  calc
    _ = probability (sparseSequence.experiment t).design
        (fun z => z (firstIndex t) = b) :=
          congrArg (probability (sparseSequence.experiment t).design) hevent
    _ = 1/2 := by
      have hp := coordinate_probability t (fun x => x = b)
      cases b <;> simpa using hp

end
end SAP.P009a.WH.W1.P.T1_L1

open SAP.P009a.WH.W1.P.T1_L1 SAP.P009a.WH.W1 SAP.P009a

theorem SAP.P009a.WH.W1.T1_L1_proof : SAP.P009a.WH.W1.T1_L1 := by
  change W1SparseErrors
  intro t
  dsimp only [W1SparseErrors]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a z
    exact scaled_explicit t a z
  · intro a b
    exact scaled_atom_probability t a b
  · intro ε hε hcut a
    have hn : 0 < sampleSize sparseSequence t := by
      change (0 : ℝ) < (t+1:ℕ)
      positivity
    have hmul : 1 < sampleSize sparseSequence t * ε := by
      have h := (div_lt_iff₀ hε).1 hcut
      nlinarith [h]
    have hinv : 1 / sampleSize sparseSequence t < ε :=
      (div_lt_iff₀ hn).2 (by nlinarith [hmul])
    have hempty : ∀ z : TreatmentVector (t+1),
        ¬ sparseScaledError a t z ≤ -ε := by
      intro z hz
      rw [(scaled_explicit t a z).2] at hz
      by_cases hbit : z 0
      · simp [hbit] at hz
        have hpos : 0 ≤ 3 / sampleSize sparseSequence t :=
          div_nonneg (by norm_num) (le_of_lt hn)
        linarith
      · simp [hbit] at hz
        have hneg : -ε < -(1 / sampleSize sparseSequence t) := neg_lt_neg hinv
        have hz' : -(1 / sampleSize sparseSequence t) ≤ -ε := by
          simpa only [neg_div] using hz
        linarith
    unfold probability expectation
    apply Finset.sum_eq_zero
    intro z hz
    simp [hempty z]
  · intro z
    exact centered_explicit t z
  · intro b
    exact centered_atom_probability t b

