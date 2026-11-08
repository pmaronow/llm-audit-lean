import Mathlib
import SAP.P018b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ENNReal

/-- P018-T27; p. 567 (PDF p. 4), Proposition 1, equation (3);
pp. 573–574 (PDF pp. 10–11), Appendix B.
For iid units and a fixed bounded symmetric measurable dyad regression kernel
with an intercept and nonsingular population Gram matrix Q, the sandwich
estimator (3), formed using fitted residuals, satisfies N Vhat_N - V_N ->p 0.
Here beta = Q^(-1) E[XY], epsilon = Y - X' beta, and
V_N = (N/D^2) Q^(-1) Var(sum_d X_d epsilon_d) Q^(-1), with unconditional variance.
The usual measure-theoretic conditions are assumed. Population rank suffices;
the estimator uses the existing totalized inverse convention on singular samples.
The additional printed fitted-residual and moment conditions may be imposed,
but are unnecessary for this conclusion. -/
def T27WholeStatement_W3 : Prop :=
  ∀ {U : Type} [MeasurableSpace U] {k : ℕ} (K : Kernel U k),
    Standing K →
    inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • sampleVariance members (design K ω) (response K ω) - trueTarget K N)

end SAP.P018b
