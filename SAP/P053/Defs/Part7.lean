import SAP.P053.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Neyman bounds and constant-effect agreement concern variances. The explicit sequence uses
N=10(k+1), two and eight treatment/control units per block, half the control potential
outcomes equal to 1 and half to -1, and doubled treatment outcomes.
-/

namespace SAP.P053
open Filter
open scoped BigOperators Topology
noncomputable section

def NeymanBound (E : ℕ → Population) (p v1 v0 vt _tauInf : ℝ) : Prop :=
    Tendsto (fun k => ((E k).size : ℝ)*randomizationVariance (E k) (estimate (E k)))
      atTop (nhds (neymanLimit p v1 v0-vt)) ∧
    neymanLimit p v1 v0-vt ≤ neymanLimit p v1 v0 ∧
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z) (neymanLimit p v1 v0)
def ConstantLimitAgreement (E : ℕ → Population) (p v1 v0 vt _tauInf : ℝ) : Prop :=
    (∀ k, populationVariance (E k) (E k).Y1 = populationVariance (E k) (E k).Y0 ∧
      populationVariance (E k) (unitEffects (E k)) = 0) ∧
    v1=v0 ∧ vt=0 ∧
    Tendsto (fun k => ((E k).size : ℝ)*randomizationVariance (E k) (estimate (E k)))
      atTop (nhds (neymanLimit p v1 v0)) ∧
    neymanLimit p v1 v0 = olsLimit p v1 v0 ∧
    LittleOInvSize E (fun k z => olsVariance (E k) z-neymanVariance (E k) z)
def HeterogeneousFinite (k : ℕ) : Prop :=
    let P := heterogeneousWitness k
    averageEffect P = 0 ∧
    populationVariance P P.Y0 = (P.size : ℝ)/((P.size : ℝ)-1) ∧
    populationVariance P P.Y1 = 4*(P.size : ℝ)/((P.size : ℝ)-1) ∧
    populationVariance P (unitEffects P) = (P.size : ℝ)/((P.size : ℝ)-1) ∧
    randomizationVariance P (estimate P) = 81/(4*((P.size : ℝ)-1)) ∧
    populationVariance P P.Y1/P.n0+populationVariance P P.Y0/P.n1 = 10/((P.size : ℝ)-1) ∧
    populationVariance P P.Y1/P.n1+populationVariance P P.Y0/P.n0 = 85/(4*((P.size : ℝ)-1)) ∧
    10/((P.size : ℝ)-1) < randomizationVariance P (estimate P)
def HeterogeneousLimit : Prop :=
    Regularity heterogeneousWitness (1/5) 4 1 1 0 ∧
    (∀ k, averageEffect (heterogeneousWitness k) = 0) ∧
    Tendsto (fun k => ((heterogeneousWitness k).size : ℝ)*
      randomizationVariance (heterogeneousWitness k) (estimate (heterogeneousWitness k)))
        atTop (nhds (81/4)) ∧
    InProbability heterogeneousWitness (fun k z =>
      ((heterogeneousWitness k).size : ℝ)*olsVariance (heterogeneousWitness k) z) 10 ∧
    olsLimit (1/5) 4 1 = 10 ∧ neymanLimit (1/5) 4 1 = 85/4 ∧ (10 : ℝ) < 81/4

def T8Statement : Prop :=
  (∀ (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ), Regularity E p v1 v0 vt tauInf →
    NeymanBound E p v1 v0 vt tauInf ∧
    ((∀ k, ConstantEffects (E k)) →
      ConstantLimitAgreement E p v1 v0 vt tauInf ∧
      (∀ k, Real.sqrt (populationVariance (E k) (E k).Y1) =
          Real.sqrt (populationVariance (E k) (E k).Y0) ∧
        Real.sqrt (populationVariance (E k) (unitEffects (E k))) = 0))) ∧
  (∀ k, HeterogeneousFinite k) ∧ HeterogeneousLimit ∧ (81/4 : ℝ) < 85/4

end
end SAP.P053
