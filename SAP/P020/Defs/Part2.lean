import SAP.P020.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020
open scoped BigOperators
open Filter
noncomputable section

/-- The paper quantity replicateWithin, expressed using finite sums and ordinary real arithmetic. -/
abbrev replicateWithin (P : ClusterPopulation) (h : ℕ) (hh : 0 < h) : ClusterPopulation :=
  { P with
    n := fun j => h * P.n j
    n_pos := fun j => Nat.mul_pos hh (P.n_pos j)
    y0 := fun j => (h : ℝ) * P.y0 j
    y1 := fun j => (h : ℝ) * P.y1 j }

/-- The three-cluster efficiency witness: sizes (1,2,4), control totals (0,1,1). -/
abbrev efficiencyPopulation : ClusterPopulation where
  M := 3
  mt := 1
  mt_pos := by decide
  mt_lt := by decide
  n := ![1, 2, 4]
  n_pos := by intro j; fin_cases j <;> norm_num
  y0 := ![0, 1, 1]
  y1 := ![0, 0, 0]

/-- The three-cluster fitted-slope witness: sizes (1,2,3), treatment totals (0,0,3). -/
abbrev slopePopulation : ClusterPopulation where
  M := 3
  mt := 1
  mt_pos := by decide
  mt_lt := by decide
  n := ![1, 2, 3]
  n_pos := by intro j; fin_cases j <;> norm_num
  y0 := ![0, 0, 0]
  y1 := ![0, 0, 3]

/-- The two-cluster control-subscript witness. -/
abbrev subscriptPopulation : ClusterPopulation where
  M := 2
  mt := 1
  mt_pos := by decide
  mt_lt := by decide
  n := ![1, 2]
  n_pos := by intro j; fin_cases j <;> norm_num
  y0 := ![0, 0]
  y1 := ![1, 2]

/-- The two-cluster expectation-bracket witness. -/
abbrev bracketPopulation : ClusterPopulation :=
  { subscriptPopulation with y0 := ![0, 2], y1 := ![0, 2] }

/-- The paper quantity rajMomentObjective, expressed using finite sums and ordinary real arithmetic. -/
def rajMomentObjective (P : ClusterPopulation) (k : ℝ) : ℝ :=
  (((P.M : ℝ) - controlCount P) / controlCount P) * clusterVariance (rajPotential P false k) +
  (((P.M : ℝ) - P.mt) / P.mt) * clusterVariance (rajPotential P true k) +
  2 * clusterCovariance (rajPotential P false k) (rajPotential P true k)

/-- The paper quantity rajVarianceCurvature, expressed using finite sums and ordinary real arithmetic. -/
def rajVarianceCurvature (P : ClusterPopulation) : ℝ :=
  (P.M : ℝ)^2 / ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1)) *
    ((((P.M : ℝ) - controlCount P) / controlCount P) +
      (((P.M : ℝ) - P.mt) / P.mt) + 2) *
    clusterVariance (fun j => (P.n j : ℝ))

/-- The paper quantity logistic, expressed using finite sums and ordinary real arithmetic. -/
noncomputable def logistic (eta : ℝ) : ℝ := 1 - (1 + Real.exp eta)⁻¹

/-- The paper quantity repairedContrast, expressed using finite sums and ordinary real arithmetic. -/
noncomputable def repairedContrast (n : ℝ) : ℝ := 2 / 5 - 9 / 10000 * n

/-- Convergence in probability along the positive within-cluster replication sequence. -/
def WithinReplicationConsistent (P : ClusterPopulation) : Prop :=
  DesignConsistent
    (fun h => clusterLaw (replicateWithin P (h + 1) (Nat.succ_pos h)))
    (fun h => differenceInMeans (replicateWithin P (h + 1) (Nat.succ_pos h)))
    (fun h => averageTreatmentEffect (replicateWithin P (h + 1) (Nat.succ_pos h)))

end
end SAP.P020
