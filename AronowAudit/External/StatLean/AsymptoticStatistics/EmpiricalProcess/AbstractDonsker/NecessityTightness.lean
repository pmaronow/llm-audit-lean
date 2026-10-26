/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
Local scope: this is a dependency-only module. It contains none of the three necessity theorems
listed in the upstream Main results section.
-/

import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.PBridgeTight
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.Outer
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterTightness

/-!
# Theorem 18.14 necessity (⟹): asymptotic tightness ⟹ equicontinuity

The tightness side of the necessity direction of van der Vaart, *Asymptotic
Statistics* Theorem 18.14 (book p.261), via the outer-Prohorov asymptotic
tightness machinery (vdV §18.3 Theorem 18.12; van der Vaart–Wellner §1.5.7).

Weak convergence of the empirical process `𝔾ₙ` in `ℓ∞(F)` (the outer sense
`⇝ₒ`) to the tight `P`-Brownian-bridge law `G_P` forces, by the easy-Prohorov
direction, asymptotic tightness of `𝔾ₙ`. The uniform `distL2`-continuity of
the Brownian-bridge paths, together with closed-set outer portmanteau, gives the
oscillation-modulus control in outer probability that defines
`IsAsymptoticallyEquicontinuous`.

## Main results (all proved; vdV p.261 / 18.12)

* `outerMeasure_modulusComplement_le` — weak convergence of `𝔾ₙ` to the
  uniformly `distL2`-continuous Brownian bridge ⟹ close-pair oscillations above
  any threshold `ε` have limiting outer probability at most any prescribed `η`.
* `empiricalProcess_asymptoticallyTight` — the `⇝ₒ`-to-`G_P` hypothesis ⟹
  asymptotic tightness of `𝔾ₙ` (easy-Prohorov + `pBridge_tight`).
* `equicont_of_weakConvergesOuter_gp` — the `⇝ₒ`-to-`G_P` hypothesis ⟹
  `IsAsymptoticallyEquicontinuous F P`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Theorem
18.14 (book p.261), Theorem 18.12 (book p.260), §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology AsymptoticStatistics BoundedContinuousFunction
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

section Necessity

variable {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
variable {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
  (hF_meas : ∀ f ∈ F, Measurable f)
  (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)


end Necessity

end AsymptoticStatistics.EmpiricalProcess
