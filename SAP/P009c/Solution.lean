import SAP.P009c.Defs
import SAP.P009c.Bridge
import AronowAudit.P009.P009_TransportCompletion
import AronowAudit.P009.P009_BernoulliCompletion
import AronowAudit.P009.P009_PairedCompletion
import AronowAudit.P009.Wave1.Gap.DecideP009
import AronowAudit.P009.Wave1.Gap.GP0091B1b
import AronowAudit.P009.Wave1.Gap.GP0091B2b
import AronowAudit.P009.Wave1.Gap.GLP0091B10
import AronowAudit.P009.Wave1.Gap.GP0092B1
import AronowAudit.P009.Wave1.Gap.GP0092B2
import AronowAudit.P009.Wave1.Gap.GLP0092B3
import AronowAudit.P009.Wave1.Gap.GLP0092B4
import SAP.P009c.WH.W1.Proofs.T40
import SAP.P009c.WH.W1.Proofs.T41
import SAP.P009c.WH.W1.Proofs.T43
import SAP.P009c.WH.W1.Proofs.T45
import SAP.P009c.WH.W1.Proofs.T46

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

theorem T35 : T35Statement := by
  intro n hn E
  exact AronowAudit.P009.estimand_identities hn (Bridge.toExperiment E)

theorem T36 : T36Statement := by
  intro n hn E
  exact AronowAudit.P009.interference_count_bounds hn (Bridge.toExperiment E)

theorem T37 : T37Statement := by
  intro n hn E Q K hK
  exact AronowAudit.P009.external_validity_total_variation hn
    (Bridge.toExperiment E) (Bridge.toLaw Q) K hK

theorem T38 : T38Statement := by
  intro n hn E K r hK hr z z'
  exact AronowAudit.P009.assignment_ATE_lipschitz hn (Bridge.toExperiment E) K r hK hr z z'

theorem T39 : T39Statement := by
  intro n hn E Q K r hK hr
  have h := AronowAudit.P009.external_validity_wasserstein hn
    (Bridge.toExperiment E) (Bridge.toLaw Q) K r hK hr
  change |eate E - eate {E with design := Q}| ≤
    2 * K * Real.rpow (n : ℝ) (-1 / r) * conjugateC E r *
      AronowAudit.P009.wasserstein r (Bridge.toLaw E.design) (Bridge.toLaw Q) at h
  rw [Bridge.wasserstein_toLaw] at h
  exact h

theorem T40 : SAP.P009c.T40WholeStatement := SAP.P009c.WH.W1.T40_whole

theorem T41 : SAP.P009c.T41WholeStatement := SAP.P009c.WH.W1.T41_whole

theorem T42 : T42Statement := by
  intro S k q s hReg hCR hRestricted hC1
  exact AronowAudit.P009.Wave1.complete_consistency_proof (Bridge.toStudy S) k q s
    hReg hCR hRestricted hC1

theorem T43 : SAP.P009c.T43WholeStatement := SAP.P009c.WH.W1.T43_whole

theorem T44 : T44Statement := by
  intro S ρ k q s hReg hPair hRestricted hE hR
  exact AronowAudit.P009.paired_consistency (Bridge.toStudy S)
    (fun t => Bridge.toPairing (ρ t)) k q s hReg hPair hRestricted hE hR

theorem T45 : SAP.P009c.T45WholeStatement := SAP.P009c.WH.W1.T45_whole

theorem T46 : SAP.P009c.T46WholeStatement := SAP.P009c.WH.W1.T46_whole

theorem T47 : T47Statement := by
  intro S k q s hReg hQ hBER
  refine ⟨AronowAudit.P009.Wave1.variance_bias_limit_proof (Bridge.toStudy S)
    k q s hReg hQ hBER, ?_⟩
  intro t
  unfold msq
  positivity

theorem T48 : T48Statement := by
  intro S k q s hReg hQ hBER hRestricted hSD
  exact AronowAudit.P009.Wave1.average_inflation_conservative_proof (Bridge.toStudy S)
    k q s hReg hQ hBER hRestricted hSD

theorem T49 : T49Statement := by
  intro S k q s hReg hQ hBER hAlt
  exact AronowAudit.P009.Wave1.maximum_inflation_conservative_proof (Bridge.toStudy S)
    k q s hReg hQ hBER hAlt

theorem T50 : T50Statement := by
  constructor
  · intro S k q s hReg hQ hBER hAlt
    exact AronowAudit.P009.Wave1.spectral_inflation_conservative_proof (Bridge.toStudy S)
      k q s hReg hQ hBER hAlt
  · exact Bridge.spectral_bounds

theorem T51 : T51Statement := by
  constructor
  · intro S k α x hk hA hBER hα hx
    exact AronowAudit.P009.Wave1.chebyshev_asymptotic_sharpness_proof (Bridge.toStudy S)
      k α x hk hA hBER hα hx
  · intro α hα
    exact AronowAudit.P009.chebyshev_three_point_sharp α hα

end
end SAP.P009c
