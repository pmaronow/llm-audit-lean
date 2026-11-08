import SAP.P053.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The two standard-deviation parameters in T7 are nonnegative; their squares are the S5
variance limits. The local Fisher component retains both probability limits.
-/

namespace SAP.P053
open Filter
open scoped BigOperators Topology
noncomputable section

def WaldComparison (E : ℕ → Population) (p v1 v0 _vt _tauInf : ℝ) : Prop :=
    LittleOInvSize E (fun k z => neymanVariance (E k) z -
      (populationVariance (E k) (E k).Y1/(E k).n1 +
       populationVariance (E k) (E k).Y0/(E k).n0)) ∧
    LittleOInvSize E (fun k z => olsVariance (E k) z-neymanVariance (E k) z -
      ((populationVariance (E k) (E k).Y1/(E k).n0 +
        populationVariance (E k) (E k).Y0/(E k).n1) -
       (populationVariance (E k) (E k).Y1/(E k).n1 +
        populationVariance (E k) (E k).Y0/(E k).n0))) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*olsVariance (E k) z) (olsLimit p v1 v0) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z) (neymanLimit p v1 v0) ∧
    olsLimit p v1 v0-neymanLimit p v1 v0 = ((v1-v0)*(2*p-1))/(p*(1-p)) ∧
    (olsLimit p v1 v0 ≠ neymanLimit p v1 v0 → v1 ≠ v0 ∧ p ≠ 1/2)
def LocalFisherComparison (E : ℕ → Population) (p v1 v0 _vt _tauInf : ℝ) : Prop :=
    LittleOInvSize E (fun k z => fisherVariance (E k) z-neymanVariance (E k) z -
      ((populationVariance (E k) (E k).Y1/(E k).n0 +
        populationVariance (E k) (E k).Y0/(E k).n1) -
       (populationVariance (E k) (E k).Y1/(E k).n1 +
        populationVariance (E k) (E k).Y0/(E k).n0))) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*fisherVariance (E k) z) (olsLimit p v1 v0) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z) (neymanLimit p v1 v0)

def T7Statement : Prop :=
  ∀ (E : ℕ → Population) (p σ1 σ0 vt tauInf : ℝ), 0 ≤ σ1 → 0 ≤ σ0 →
    Regularity E p (σ1^2) (σ0^2) vt tauInf →
      WaldComparison E p (σ1^2) (σ0^2) vt tauInf ∧
      (olsLimit p (σ1^2) (σ0^2) ≠ neymanLimit p (σ1^2) (σ0^2) → σ1 ≠ σ0 ∧ p ≠ 1/2) ∧
      (Tendsto (fun k => averageEffect (E k)) atTop (nhds 0) →
        LocalFisherComparison E p (σ1^2) (σ0^2) vt tauInf)

end
end SAP.P053
