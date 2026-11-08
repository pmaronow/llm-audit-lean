import SAP.P043.Defs
import AronowAudit.P043.P043_Formalization
import AronowAudit.P043.P043_Strata
import AronowAudit.P043.Wave1.Gap.FidP043

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P043.Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
universe u

/-- Preserve the finite probability weights and their certificates. -/
def toAuditPopulation {Ω : Type u} [Fintype Ω]
    (P : Population Ω) : AronowAudit.P043.Population Ω :=
  ⟨P.mass, P.nonneg, P.total⟩

/-- Preserve both potential-outcome functions. -/
def toAuditMediation {Ω : Type u}
    (m : MediationModel Ω) : AronowAudit.P043.MediationModel Ω :=
  ⟨m.knowledge, m.support⟩

/-- Preserve integer potential doses and the exclusion-restricted response. -/
def toAuditIV {Ω : Type u} (m : IVModel Ω) : AronowAudit.P043.IVModel Ω :=
  ⟨m.knowledge, m.response⟩

theorem mean_eq {Ω : Type u} [Fintype Ω] (P : Population Ω) (f : Ω → ℝ) :
    mean P f = AronowAudit.P043.mean (toAuditPopulation P) f := rfl

theorem reducedForm_eq {Ω : Type u} [Fintype Ω]
    (P : Population Ω) (p : ℝ) (m : MediationModel Ω) :
    reducedForm P p m = AronowAudit.P043.reducedForm
      (toAuditPopulation P) p (toAuditMediation m) := rfl

theorem lawReducedForm_eq {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (m : MediationModel Ω) :
    lawReducedForm μ p m = AronowAudit.P043.Wave1.lawReducedForm
      μ p (toAuditMediation m) := rfl

theorem integrablePotentials_iff {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : MediationModel Ω) :
    IntegrableMediationPotentials μ m ↔
      AronowAudit.P043.Wave1.IntegrableMediationPotentials μ (toAuditMediation m) :=
  Iff.rfl

theorem firstStage_eq {Ω : Type u} [Fintype Ω]
    (P : Population Ω) (p : ℝ) (m : IVModel Ω) :
    firstStage P p m = AronowAudit.P043.firstStage
      (toAuditPopulation P) p (toAuditIV m) := rfl

theorem signedUnitClaims_iff {Ω : Type u} (m : IVModel Ω) (J : ℕ) (i : Ω) :
    IVSignedUnitClaims m J i ↔
      AronowAudit.P043.IVSignedUnitClaims (toAuditIV m) J i := Iff.rfl

theorem mediationWitnesses_statement_eq : T1Statement =
    (AronowAudit.P043.LinearWitnessClaims ∧ AronowAudit.P043.IntegerWitnessClaims ∧
    AronowAudit.P043.reducedForm AronowAudit.P043.linearPopulation (1/2)
      AronowAudit.P043.linearWitness = 0 ∧
    AronowAudit.P043.mediated AronowAudit.P043.linearPopulation
      AronowAudit.P043.linearWitness = 3/50 ∧
    AronowAudit.P043.direct AronowAudit.P043.linearPopulation
      AronowAudit.P043.linearWitness = -3/50 ∧
    AronowAudit.P043.reducedForm AronowAudit.P043.integerPopulation (1/2)
      AronowAudit.P043.integerWitness = 0 ∧
    AronowAudit.P043.mediated AronowAudit.P043.integerPopulation
      AronowAudit.P043.integerWitness = 3/50 ∧
    AronowAudit.P043.direct AronowAudit.P043.integerPopulation
      AronowAudit.P043.integerWitness = -3/50 ∧
    (∀ A t, (∑ i, AronowAudit.P043.jointMass AronowAudit.P043.linearPopulation
        (1/2) t i * AronowAudit.P043.indicator (A i)) =
      AronowAudit.P043.armProb (1/2) t *
        AronowAudit.P043.eventProb AronowAudit.P043.linearPopulation A) ∧
    (∀ A t, (∑ i, AronowAudit.P043.jointMass AronowAudit.P043.integerPopulation
        (1/2) t i * AronowAudit.P043.indicator (A i)) =
      AronowAudit.P043.armProb (1/2) t *
        AronowAudit.P043.eventProb AronowAudit.P043.integerPopulation A)) := rfl

/-- All fixed-witness expressions reduce to the same finite sums. -/
theorem mediationWitnesses : T1Statement := by
  exact AronowAudit.P043.mediation_counterexamples

/-- The adapters preserve every expression in the arbitrary-law aggregate. -/
theorem mediationRepair {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : unitInterval) (hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1)
    (m : MediationModel Ω) (hint : IntegrableMediationPotentials μ m) :
    MediationRepairConclusions μ p m := by
  exact AronowAudit.P043.Wave1.mediation_repair_integrable
    μ p hp (toAuditMediation m) hint

/-- Project the fixed witnesses from the aggregate. A nonzero conditional
effect rules out a zero conditioning probability by the displayed quotient. -/
theorem ivWitnesses : T4Statement := by
  obtain ⟨hup, hunits, hA, hB, hlaw, heA, heB, htable, hrange, hnonid⟩ :=
    AronowAudit.P043.iv_counterexamples
  refine ⟨hup, hunits, hA, hB, hlaw, heA, heB, htable, ?_, ?_, hnonid, ?_, ?_⟩
  · intro i
    exact hrange AronowAudit.P043.modelA i (Or.inl rfl)
  · intro i
    exact hrange AronowAudit.P043.modelB i (Or.inr rfl)
  · intro hzero
    have he : increaserEffect (uniformPopulation (Fin 5)) modelA = 1 := heA
    rw [increaserEffect, eventMean, hzero, div_zero] at he
    exact zero_ne_one he
  · intro hzero
    have he : increaserEffect (uniformPopulation (Fin 5)) modelB = 4/3 := heB
    rw [increaserEffect, eventMean, hzero, div_zero] at he
    norm_num at he

/-- Only the quantified model arguments need a structural adapter;
all numerical and response expressions agree by reduction. -/
theorem ivRepair {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (m : IVModel Ω) (J : ℕ)
    (hb : ∀ i, m.knowledge false i ≤ J ∧ m.knowledge true i ≤ J)
    (hm : ∀ i, m.knowledge false i ≤ m.knowledge true i)
    (hfirst : 0 < mean P (fun i => (m.knowledge true i : ℝ) - m.knowledge false i)) :
    IVRepairConclusions P p m J := by
  obtain ⟨hpop, hcov, hmono, htotal, havg, hsigned, hzero, hvalues, hdown⟩ :=
    AronowAudit.P043.iv_repair (toAuditPopulation P) p hp (toAuditIV m) J hb hm hfirst
  refine ⟨hpop, hcov, hmono, htotal, havg, ?_, hzero, hvalues, ?_⟩
  · intro m' J' i hb'
    exact hsigned (toAuditIV m') J' i hb'
  · intro m' i j hd
    exact hdown (toAuditIV m') i j hd

theorem stratumEffect_eq {n q : ℕ} (s : Fin n → Fin (q + 1))
    (γ : Fin q → ℝ) (i : Fin n) :
    stratumEffect s γ i = AronowAudit.P043.stratumEffect s γ i := rfl

/-- The corrected dummy notation uses identical finite sums and indexing. -/
theorem correctedStrata : T6Statement := by
  exact @AronowAudit.P043.corrected_strata

end
end SAP.P043.Bridge
