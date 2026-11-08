import SAP.P006b.Defs
import AronowAudit.P006.P006_CounterfactualMetrics

import SAP.P006b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.Bridge

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology


/-- Structural adapter: all experiment data and the positive population-size certificate are retained. -/
def toProject {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : SAP.P006b.Experiment Ω C n) : AronowAudit.P006.Experiment Ω C n where
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

/-- Reverse structural adapter, used to transport the two universal refutations. -/
def fromProject {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : AronowAudit.P006.Experiment Ω C n) : SAP.P006b.Experiment Ω C n where
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

/-- The standing assumptions have the same fields, including finite means and treatment independence. -/
theorem standing_toProject {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    {E : SAP.P006b.Experiment Ω C n} (h : SAP.P006b.Standing E) :
    AronowAudit.P006.Standing (toProject E) where
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

theorem standing_fromProject {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    {E : AronowAudit.P006.Experiment Ω C n} (h : AronowAudit.P006.Standing E) :
    SAP.P006b.Standing (fromProject E) where
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

theorem experiment_roundtrip {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : AronowAudit.P006.Experiment Ω C n) :
    toProject (fromProject E) = E := rfl

theorem welfare_eq {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : SAP.P006b.Experiment Ω C n) :
    E.V = (toProject E).V := rfl

theorem expectedATO_eq {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : SAP.P006b.Experiment Ω C n) :
    E.expectedATO = (toProject E).expectedATO := rfl

theorem expectedATT_eq {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : SAP.P006b.Experiment Ω C n) :
    E.expectedATT = (toProject E).expectedATT := rfl

theorem expectedTT_eq {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : SAP.P006b.Experiment Ω C n) :
    E.expectedTT = (toProject E).expectedTT := rfl

def fitToProject {d : ℕ} (β : SAP.P006b.LogisticFit d) : AronowAudit.P006.LogisticFit d where
  β0 := β.β0
  β1 := β.β1
  β2 := β.β2
  β3 := β.β3

theorem predictor_eq {d : ℕ} (β : SAP.P006b.LogisticFit d) (x : Fin d → ℝ) (t : Bool) :
    SAP.P006b.linearPredictor β x t = AronowAudit.P006.linearPredictor (fitToProject β) x t := rfl

end SAP.P006b.Bridge
