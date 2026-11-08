import SAP.P053.Defs
import AronowAudit.P053.P053_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P053.Bridge
open SAP.P053
noncomputable section

/-- Preserve the two arm sizes and both potential-outcome vectors. -/
def toPopulation (P : Population) : AronowAudit.P053.Population :=
  ⟨P.n1, P.n0, P.Y1, P.Y0⟩

/-- Every regularity field is transported without adding a statistical premise. -/
theorem toRegularity {E : ℕ → Population} {p v1 v0 vt tauInf : ℝ}
    (h : Regularity E p v1 v0 vt tauInf) :
    AronowAudit.P053.Regularity (fun k => toPopulation (E k)) p v1 v0 vt tauInf :=
  ⟨h.size_diverges, h.arm_sizes, h.p_positive, h.p_less_one, h.allocation,
    h.variance1, h.variance0, h.varianceEffect, h.average_effect, h.fourth_moments⟩

theorem fromRegularity {E : ℕ → Population} {p v1 v0 vt tauInf : ℝ}
    (h : AronowAudit.P053.Regularity (fun k => toPopulation (E k)) p v1 v0 vt tauInf) :
    Regularity E p v1 v0 vt tauInf :=
  ⟨h.size_diverges, h.arm_sizes, h.p_positive, h.p_less_one, h.allocation,
    h.variance1, h.variance0, h.varianceEffect, h.average_effect, h.fourth_moments⟩

theorem support_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    support (ι := ι) k = AronowAudit.P053.support k := rfl

theorem binaryTau_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n1 n0 : ℕ) (y : ι → Bool) (z : Finset ι) :
    binaryTau n1 n0 y z = AronowAudit.P053.binaryTau n1 n0 y z := rfl

theorem orderedSample_eq {N n : ℕ} (y : Fin N → Bool) (s : Finset (Fin N))
    (hs : s.card = n) :
    orderedBinarySample y s hs = AronowAudit.P053.orderedBinarySample y s hs := rfl

theorem probability_eq (P : Population) (event : Finset (Fin P.size) → Prop) :
    randomizationProbability P event =
      AronowAudit.P053.randomizationProbability (toPopulation P) event := rfl

theorem estimate_eq (P : Population) (z : Finset (Fin P.size)) :
    estimate P z = AronowAudit.P053.estimate (toPopulation P) z := rfl

theorem olsVariance_eq (P : Population) (z : Finset (Fin P.size)) :
    olsVariance P z = AronowAudit.P053.olsVariance (toPopulation P) z := rfl

theorem neymanVariance_eq (P : Population) (z : Finset (Fin P.size)) :
    neymanVariance P z = AronowAudit.P053.neymanVariance (toPopulation P) z := rfl

theorem fisherVariance_eq (P : Population) (z : Finset (Fin P.size)) :
    fisherVariance P z = AronowAudit.P053.fisherVariance (toPopulation P) z := rfl

theorem witness_eq (k : ℕ) :
    toPopulation (heterogeneousWitness k) = AronowAudit.P053.heterogeneousWitness k := rfl

end
end SAP.P053.Bridge
