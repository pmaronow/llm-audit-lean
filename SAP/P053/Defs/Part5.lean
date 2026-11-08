import SAP.P053.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
First-order variance comparisons and the restricted Wald-validity claim. PositiveOLS is an
extra hypothesis only for division by the estimated variance or its square root. It does
not become part of S5 and is not asserted to follow from it.
-/

namespace SAP.P053
open Filter
open scoped BigOperators Topology
noncomputable section

def FisherOLSAsymptotics (E : ℕ → Population) (p v1 v0 _vt tauInf : ℝ) : Prop :=
    LittleOInvSize E (fun k z => fisherVariance (E k) z -
      (populationVariance (E k) (E k).Y1/(E k).n0 +
       populationVariance (E k) (E k).Y0/(E k).n1 + (averageEffect (E k))^2/(E k).size)) ∧
    LittleOInvSize E (fun k z => olsVariance (E k) z -
      (populationVariance (E k) (E k).Y1/(E k).n0 +
       populationVariance (E k) (E k).Y0/(E k).n1)) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*
      (fisherVariance (E k) z-olsVariance (E k) z)-(averageEffect (E k))^2) 0 ∧
    InProbability E (fun k z => ((E k).size : ℝ)*fisherVariance (E k) z)
      (olsLimit p v1 v0+tauInf^2) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*olsVariance (E k) z) (olsLimit p v1 v0)

/-- Eventual positivity on every assignment makes ordinary division and studentization defined. -/
def PositiveOLS (E : ℕ → Population) : Prop :=
  ∀ᶠ k in atTop, ∀ z ∈ support (ι := Fin (E k).size) (E k).n1, 0 < olsVariance (E k) z

def T5Statement : Prop :=
  ∀ (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ),
    Regularity E p v1 v0 vt tauInf → FisherOLSAsymptotics E p v1 v0 vt tauInf
def ConstantVarianceApproximation (E : ℕ → Population) (_p _v1 _v0 _vt _tauInf : ℝ) : Prop :=
    LittleOInvSize E (fun k z => olsVariance (E k) z-
      randomizationVariance (E k) (estimate (E k))) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*
      (fisherVariance (E k) z-randomizationVariance (E k) (estimate (E k))) -
      (averageEffect (E k))^2) 0
def SharpWaldValidity (E : ℕ → Population) : Prop :=
    (∀ t : ℝ, Tendsto (fun k => randomizationProbability (E k)
      (fun z => estimate (E k) z/Real.sqrt (olsVariance (E k) z) ≤ t))
        atTop (nhds (standardNormalCDF t))) ∧
    (∀ α : ℝ, 0 < α → α < 1 → Tendsto
      (fun k => randomizationProbability (E k)
        (fun z => normalCritical α < |estimate (E k) z|/Real.sqrt (olsVariance (E k) z)))
      atTop (nhds α))

def T6Statement : Prop :=
  ∀ (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ), Regularity E p v1 v0 vt tauInf →
    ((Tendsto (fun k => averageEffect (E k)) atTop (nhds 0)) →
      LittleOInvSize E (fun k z => fisherVariance (E k) z-olsVariance (E k) z) ∧
      (0 < olsLimit p v1 v0 → PositiveOLS E →
        InProbability E (fun k z => fisherVariance (E k) z/olsVariance (E k) z) 1)) ∧
    ((∀ k, ConstantEffects (E k)) → ConstantVarianceApproximation E p v1 v0 vt tauInf) ∧
    ((∀ k, SharpNull (E k)) → 0 < v0 → PositiveOLS E → SharpWaldValidity E)

end
end SAP.P053
