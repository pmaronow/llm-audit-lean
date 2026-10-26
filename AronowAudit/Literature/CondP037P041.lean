import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.Basic
import AronowAudit.P037.P037_Bootstrap
import AronowAudit.P045.P045_Spillover

/-!
Gamma-Dirichlet literature statement and a conditional Bayesian-bootstrap
identity. `DevroyeGammaDirichlet` is an explicit hypothesis of the identity;
no literature result is asserted as a theorem here.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal

namespace AronowAudit.Literature
universe u

/-- The open simplex in its ordinary free coordinates, independent of any
application. Devroye (1986), XI.4.1, p. 593. -/
def dirichletSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i < 1}

/-- Append the dependent coordinate to free simplex coordinates. -/
noncomputable def simplexCompletion (k : ℕ) (p : Fin k → ℝ) : Fin (k+1) → ℝ :=
  fun i => if hi : i.val < k then p ⟨i.val, hi⟩ else 1 - ∑ j, p j

/-- The usual Dirichlet density relative to k-dimensional coordinate
Lebesgue measure. The last coordinate is 1-sum(p), not an additional
integration variable. Devroye (1986), XI.4.1, p. 593; for the explicit normalizer,
see also DasGupta, Graduate Probability, Theorem 1.68 and Definition 1.59,
manuscript p. 139 (author-hosted gradprob.pdf). -/
noncomputable def dirichletFreeDensity (k : ℕ) (a : Fin (k+1) → ℝ)
    (p : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.Gamma (∑ i, a i) / ∏ i, Real.Gamma (a i)) *
    (∏ i : Fin k, Real.rpow (p i) (a i.castSucc - 1)) *
    Real.rpow (1 - ∑ i, p i) (a (Fin.last k) - 1))

/-- Dirichlet law on free coordinates. Restriction removes the Lebesgue-null
boundary; powers at boundary points therefore impose no extra convention. -/
noncomputable def dirichletFreeLaw (k : ℕ) (a : Fin (k+1) → ℝ) :
    Measure (Fin k → ℝ) :=
  (volume.restrict (dirichletSimplex k)).withDensity (dirichletFreeDensity k a)

/-- Luc Devroye, Non-Uniform Random Variate Generation, Springer-Verlag,
1986, Chapter XI, Theorem 4.1, p. 594, with the Dirichlet definition on
p. 593. Both directions are included. Gamma parameters are arbitrary
positive real shapes, with rate ONE as in the source. All probability spaces,
measurable random variables and positive dimensions are quantified here.
The forward conclusion is the free-coordinate Dirichlet law and independence
from the total. The converse reconstructs independent gammas. No forward
claim about the total's law is added to the printed theorem.

Source: https://numerical.recipes/devroye/Devroye_files/chapter_eleven.pdf
printed pp. 593-594, PDF pp. 40-41. -/
def DevroyeGammaDirichlet : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ (k : ℕ), 0 < k → ∀ (a : Fin (k+1) → ℝ), (∀ i, 0 < a i) →
    (∀ (Y : Fin (k+1) → Ω → ℝ),
      (∀ i, Measurable (Y i)) →
      ProbabilityTheory.iIndepFun Y μ →
      (∀ i, Measure.map (Y i) μ = ProbabilityTheory.gammaMeasure (a i) 1) →
      let T : Ω → ℝ := fun ω => ∑ i, Y i ω
      let X : Ω → (Fin k → ℝ) := fun ω i => Y i.castSucc ω / T ω
      Measure.map X μ = dirichletFreeLaw k a ∧
        ProbabilityTheory.IndepFun X T μ) ∧
    (∀ (T : Ω → ℝ) (X : Ω → (Fin k → ℝ)),
      Measurable T → Measurable X →
      Measure.map T μ = ProbabilityTheory.gammaMeasure (∑ i, a i) 1 →
      Measure.map X μ = dirichletFreeLaw k a →
      ProbabilityTheory.IndepFun X T μ →
      let Y : Fin (k+1) → Ω → ℝ :=
        fun i ω => T ω * simplexCompletion k (X ω) i
      ProbabilityTheory.iIndepFun Y μ ∧
        ∀ i, Measure.map (Y i) μ = ProbabilityTheory.gammaMeasure (a i) 1)

namespace HH


end HH


end AronowAudit.Literature

namespace AronowAudit.P037

/-- P037-T5(b) conditional on an independent published general theorem.
The application uses universe 0. -/
def exponentials_give_bayesian_bootstrap_conditional_statement : Prop :=
  AronowAudit.Literature.DevroyeGammaDirichlet.{0} →
    ∀ (n : ℕ), normalizedExponentialLaw n = bayesianBootstrapLaw (n+1)

end AronowAudit.P037

namespace AronowAudit.P045


end AronowAudit.P045

