import SAP.P006a.Defs
import AronowAudit.P006.P006_CounterfactualMetrics
import AronowAudit.P006.Wave1.Gap.FidP006
import AronowAudit.P006.Wave1.Gap.GP006B1
import AronowAudit.P006.Wave1.Gap.GP006B2b
import AronowAudit.P006.Wave1.Gap.RepairT6T7
import AronowAudit.P006.Wave1.Gap.DecideF
import AronowAudit.P006.Wave1.Gap.Fid2P006

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a.Bridge
noncomputable section

/-- Preserve every field of the independently named sample experiment. -/
def experiment {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : SAP.P006a.Experiment Ω C n) : AronowAudit.P006.Experiment Ω C n where
  hn := E.hn
  PX := E.PX
  μ0 := E.μ0
  μ1 := E.μ1
  law := E.law
  X := E.X
  Y0 := E.Y0
  Y1 := E.Y1
  T := E.T
  μhat := E.μhat

/-- A fieldwise adapter; all scalar, integral, and conditional-moment fields reduce identically. -/
theorem standing {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    {E : SAP.P006a.Experiment Ω C n} (h : SAP.P006a.Standing E) :
    AronowAudit.P006.Standing (experiment E) where
  px_probability := h.px_probability
  means_measurable := h.means_measurable
  means_integrable := h.means_integrable
  law_probability := h.law_probability
  measurable_units := h.measurable_units
  integrable_units := h.integrable_units
  covariate_law := h.covariate_law
  potential_law_fixed := h.potential_law_fixed
  iid_independent := h.iid_independent
  iid_identical := h.iid_identical
  conditional_means := h.conditional_means
  bernoulli := h.bernoulli
  ignorability := h.ignorability

theorem averageDesign {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    {E : SAP.P006a.Experiment Ω C n} (h : SAP.P006a.OutcomeStanding E) :
    AronowAudit.P006.Wave1.T2_OutcomeStanding (experiment E) where
  px_probability := h.px_probability
  means_measurable := h.means_measurable
  means_integrable := h.means_integrable
  law_probability := h.law_probability
  measurable_units := h.measurable_units
  integrable_units := h.integrable_units
  covariate_law := h.covariate_law
  potential_law_fixed := h.potential_law_fixed
  iid_independent := h.iid_independent
  iid_identical := h.iid_identical
  conditional_means := h.conditional_means
  bernoulli := h.bernoulli
  ignorability := h.ignorability

theorem rankingDesign {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    {E : SAP.P006a.Experiment Ω C n} (h : SAP.P006a.OutcomeStanding E) :
    AronowAudit.P006.Wave1.T13_OutcomeStanding (experiment E) where
  px_probability := h.px_probability
  means_measurable := h.means_measurable
  means_integrable := h.means_integrable
  law_probability := h.law_probability
  measurable_units := h.measurable_units
  integrable_units := h.integrable_units
  covariate_law := h.covariate_law
  potential_law_fixed := h.potential_law_fixed
  iid_independent := h.iid_independent
  iid_identical := h.iid_identical
  conditional_means := h.conditional_means
  bernoulli := h.bernoulli
  ignorability := h.ignorability

theorem policyDesign {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    {E : SAP.P006a.Experiment Ω C n} {π : C → ℝ} (h : SAP.P006a.PolicyDesign E π) :
    AronowAudit.P006.Wave1.RepairT6T7_Design (experiment E) π where
  px_probability := h.px_probability
  means_measurable := h.means_measurable
  means_integrable := h.means_integrable
  law_probability := h.law_probability
  measurable_units := h.measurable_units
  integrable_units := h.integrable_units
  covariate_law := h.covariate_law
  conditional_means := h.conditional_means
  bernoulli := h.bernoulli
  ignorability := h.ignorability

/-- The two average rewards coincide in the fixed zero-baseline witness. -/
theorem zeroBaseline {C : Type*} {n : ℕ} (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) :
    wATT (fun _ => 0) X T Y = wATO T Y :=
  AronowAudit.P006.wATT_zero X T Y

theorem averageWitness (π : BinaryPolicy) : rewardE001ATT π = rewardE001 π := by
  simp only [rewardE001ATT, rewardE001, twoATO, zeroBaseline]

/-- Singleton ATT is the same realized reward as TT, before taking the finite sum. -/
theorem singletonATT (y : Bool → ℝ) (est : Bool → Bool → ℝ) (π : BinaryPolicy) :
    oneATT y est π = oneTT y est π := by
  unfold oneATT oneTT
  simp only [show ∀ x t, wATT (est x) ![x] ![t] ![y x] =
      wTT (est x) ![x] ![t] ![y x] from
    fun x t => AronowAudit.P006.wATT_one_eq_TT (est x) x t (y x)]

/-- Transport the exported realized-outcome invariance to the shared reward definition. -/
theorem observedATO {n : ℕ} (T : Fin n → Bool) (Y0 Y1 : Fin n → ℝ) :
    wATO T (fun i => if T i then Y1 i else Y0 i) = wATO T Y1 :=
  (AronowAudit.P006.realized_rewards_SUTVA (fun _ : Unit => 0) (fun _ => 1)
    (fun _ => ()) T Y0 Y1).1

theorem witnessReward_eq : witnessReward = rewardE001 := by
  funext π
  simp only [witnessReward, rewardE001, twoATO, observedATO]

theorem witnessWelfare_eq : witnessWelfare = binaryWelfare (1/2) effectE001 := by
  funext π
  change binaryObservedWelfare (1/2) (fun _ => 0) effectE001 π = _
  have h : binaryObservedWelfare (1/2) (fun _ => 0) effectE001 π =
      binaryWelfare (1/2) (fun x => effectE001 x - 0) π :=
    AronowAudit.P006.binaryWelfare_SUTVA (1/2) (fun _ => 0) effectE001 π
  simpa only [sub_zero] using h

end
end SAP.P006a.Bridge
