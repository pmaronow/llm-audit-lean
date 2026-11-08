import Mathlib
import SAP.P053.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P053
open Filter
open scoped BigOperators Topology
noncomputable section

/-- Relabel the repeated four-unit blocks without changing the population. -/
def repeatedEquivW1 (m : ℕ) : Fin (2*m + 2*m) ≃ Fin m × Fin 4 :=
  Fintype.equivOfCardEq (by simp; omega)

/-- The same binary sharp-null potential outcomes as `repeatY`, on the population carrier. -/
def repeatedPopulationW1 (m : ℕ) : Population where
  n1 := 2*m
  n0 := 2*m
  Y1 := fun i => binaryReal (repeatY m (repeatedEquivW1 m i))
  Y0 := fun i => binaryReal (repeatY m (repeatedEquivW1 m i))

def repeatedFamilyW1 (k : ℕ) : Population := repeatedPopulationW1 (k+1)

/-- Exact moments of the positive-block repeated population; all divisors are positive. -/
def RepeatedMomentsW1 (m : ℕ) : Prop :=
  let P := repeatedPopulationW1 m
  SharpNull P ∧
  populationMean P P.Y1 = 1/2 ∧ populationMean P P.Y0 = 1/2 ∧
  populationVariance P P.Y1 = (m : ℝ)/(4*(m : ℝ)-1) ∧
  populationVariance P P.Y0 = (m : ℝ)/(4*(m : ℝ)-1) ∧
  populationVariance P (unitEffects P) = 0 ∧ averageEffect P = 0 ∧
  (∑ i : Fin P.size, ((P.Y1 i)^4 + (P.Y0 i)^4))/(P.size : ℝ) = 1

/-- The uniform complete-design probability of one supported assignment. -/
def uniformMassW1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n1 : ℕ) (z : Finset ι) : ℝ :=
  if z ∈ support n1 then 1/((support (ι := ι) n1).card : ℝ) else 0

/-- P053-T2; Section 4, p. 348 (PDF p. 3).
The specified four-unit and repeated-block examples refute the unrestricted reading
allowing labelled and fixed-covariate statistics. Both statistics have the stated values
and fail to factor through the difference in means. The six four-unit assignments each
have probability 1/6. The same repeated populations have means 1/2, variances m/(4m-1),
zero effect variance and average effect, raw fourth-moment average one, and the full S5
regularity certificate with limits (1/2,1/4,1/4,0,0).
The usual measure-theoretic conditions are assumed and hold automatically here. -/
def T2WholeStatement : Prop :=
  T2Statement ∧
  (∀ z ∈ support (ι := Fin 4) 2, uniformMassW1 2 z = 1/6) ∧
  (∀ m : ℕ, 0 < m → RepeatedMomentsW1 m) ∧
  Regularity repeatedFamilyW1 (1/2) (1/4) (1/4) 0 0

/-- A balanced sharp-null population with just one success, at sizes N=2(k+2). -/
def sparsePopulationW1 (k : ℕ) : Population where
  n1 := k+2
  n0 := k+2
  Y1 := fun i => if i.val = 0 then 1 else 0
  Y0 := fun i => if i.val = 0 then 1 else 0

/-- Exact population moments for the sparse family. -/
def SparseMomentsW1 (k : ℕ) : Prop :=
  let P := sparsePopulationW1 k
  populationVariance P P.Y1 = 1/(2*((k : ℝ)+2)) ∧
  populationVariance P P.Y0 = 1/(2*((k : ℝ)+2)) ∧
  populationVariance P (unitEffects P) = 0 ∧ averageEffect P = 0 ∧
  (∑ i : Fin P.size, ((P.Y1 i)^4 + (P.Y0 i)^4))/(P.size : ℝ) = 1/((k : ℝ)+2)

/-- Inclusive two-sided Fisher randomization p-value, conditional on observed outcomes.
The fresh assignment ranges over every subset of the fixed treatment size. -/
def frtPValueW1 (P : Population) (z : Finset (Fin P.size)) : ℝ :=
  randomizationProbability P
    (fun w => |estimate P z| ≤ |difference P w (observed P z)|)

def waldRejectW1 (P : Population) (α : ℝ) (z : Finset (Fin P.size)) : Prop :=
  normalCritical α < |estimate P z| / Real.sqrt (olsVariance P z)

def frtRejectW1 (P : Population) (α : ℝ) (z : Finset (Fin P.size)) : Prop :=
  frtPValueW1 P z ≤ α

def testDisagreementW1 (P : Population) (α : ℝ) : ℝ :=
  randomizationProbability P (fun z => ¬ (waldRejectW1 P α z ↔ frtRejectW1 P α z))

/-- A consequence of equivalence of the two tests: their rejection probabilities agree
asymptotically along every S5 local sequence. Positivity here merely ensures that the
ordinary Wald statistic is defined at every supported assignment. -/
def localRejectionEquivalenceW1 : Prop :=
  ∀ (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ),
    Regularity E p v1 v0 vt tauInf →
    Tendsto (fun k => averageEffect (E k)) atTop (nhds 0) →
    (∀ k, ∀ z ∈ support (ι := Fin (E k).size) (E k).n1, 0 < olsVariance (E k) z) →
    ∀ α : ℝ, 0 < α → α < 1 → Tendsto
      (fun k => randomizationProbability (E k) (waldRejectW1 (E k) α) -
        randomizationProbability (E k) (frtRejectW1 (E k) α)) atTop (nhds 0)

def sparseAlphaW1 : ℝ := 2*(1-standardNormalCDF (1/2))

/-- P053-T6; Introduction (i), p. 346, and Section 2, pp. 346–347 (PDF pp. 1–2).
The printed claim is false: under the stated S5 reading, local alternatives do not
ensure equivalence of the normal pooled Wald test and the FRT. Balanced sharp-null
populations with one success satisfy S5 with all variance and effect limits zero.
Every supported assignment has absolute difference 1/(k+2), positive Fisher and OLS
variances 1/(k+2)^2, and inclusive two-sided Fisher p-value one. At
alpha=2(1-Phi(1/2)), a level strictly between zero and one with normal critical value
1/2, Wald always rejects and Fisher never rejects. Their disagreement probability and
their rejection-probability difference are one at every size, refuting local equivalence.
The usual measure-theoretic conditions are assumed and hold automatically here. -/
def T6WholeStatement : Prop :=
  Regularity sparsePopulationW1 (1/2) 0 0 0 0 ∧
  (∀ k, SharpNull (sparsePopulationW1 k) ∧ averageEffect (sparsePopulationW1 k) = 0) ∧
  0 < sparseAlphaW1 ∧ sparseAlphaW1 < 1 ∧ normalCritical sparseAlphaW1 = 1/2 ∧
  (∀ k, ∀ z ∈ support (ι := Fin (sparsePopulationW1 k).size) (sparsePopulationW1 k).n1,
    |estimate (sparsePopulationW1 k) z| = 1/((k : ℝ)+2) ∧
    olsVariance (sparsePopulationW1 k) z = 1/((k : ℝ)+2)^2 ∧
    fisherVariance (sparsePopulationW1 k) z = 1/((k : ℝ)+2)^2 ∧
    0 < olsVariance (sparsePopulationW1 k) z ∧
    0 < fisherVariance (sparsePopulationW1 k) z ∧
    frtPValueW1 (sparsePopulationW1 k) z = 1 ∧
    waldRejectW1 (sparsePopulationW1 k) sparseAlphaW1 z ∧
    ¬ frtRejectW1 (sparsePopulationW1 k) sparseAlphaW1 z) ∧
  (∀ k, randomizationProbability (sparsePopulationW1 k)
      (waldRejectW1 (sparsePopulationW1 k) sparseAlphaW1) = 1 ∧
    randomizationProbability (sparsePopulationW1 k)
      (frtRejectW1 (sparsePopulationW1 k) sparseAlphaW1) = 0 ∧
    testDisagreementW1 (sparsePopulationW1 k) sparseAlphaW1 = 1) ∧
  ¬ localRejectionEquivalenceW1

end
end SAP.P053
