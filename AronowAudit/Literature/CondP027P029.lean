import AronowAudit.P029.P029_Audit
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import AronowAudit.External.Causalean.Stat.CLT.ChiSquaredProjection
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT

/-!
Conditional assessment for cond-P027P029. No target is proved in this file.
The sole proposed literature input is general ordered-binomial likelihood
optimization. Existing probability inputs are checked below, not postulated.
-/

namespace AronowAudit.Literature

/-- The likelihood kernel for arbitrary independent binomial counts. The
parameter-independent binomial coefficients are omitted, as in van Eeden (1956),
equation (1.5). Natural powers retain the endpoint convention 0^0 = 1. -/
noncomputable def orderedBinomialKernel {k : ℕ} (n a : Fin k → ℕ)
    (x : Fin k → ℝ) : ℝ :=
  ∏ i, x i ^ a i * (1 - x i) ^ (n i - a i)

/-- An order restriction and the closed probability cube. -/
def orderedBinomialDomain {k : ℕ} (R : Fin k → Fin k → Prop)
    (x : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∀ i j, R i j → x i ≤ x j

/-- The irredundant restrictions R₁,...,Rₛ in van Eeden (1956), (1.9):
a comparable pair with no intermediate comparable index. -/
def orderedBinomialCover {k : ℕ} (R : Fin k → Fin k → Prop)
    (i j : Fin k) : Prop :=
  R i j ∧ ¬ ∃ h, R i h ∧ R h j

/-- A feasible unique global maximizer, with equality characterized explicitly. -/
def orderedBinomialMax {k : ℕ} (n a : Fin k → ℕ)
    (R : Fin k → Fin k → Prop) (p : Fin k → ℝ) : Prop :=
  orderedBinomialDomain R p ∧
    ∀ x, orderedBinomialDomain R x →
      orderedBinomialKernel n a x ≤ orderedBinomialKernel n a p ∧
        (orderedBinomialKernel n a x = orderedBinomialKernel n a p ↔ x = p)

/-- Constance van Eeden, "Maximum likelihood estimation of ordered
probabilities", Proceedings of the Koninklijke Nederlandse Akademie van
Wetenschappen, Series A 59 = Indagationes Mathematicae 18 (1956), 444–455:
Theorem I, p. 445, together with its unrestricted base case (2.2), pp. 445–446.
Primary scan: https://ir.cwi.nl/pub/8218/8218D.pdf .

Every finite numbered partial order, positive trial count and admissible success
count is quantified here. The first clause is (2.2). The second is the unique
maximum assertion of Theorem I. The third is both alternatives of (2.1), for
every irredundant restriction and every relaxed maximizer. R is the transitive
numbered order; its covers are exactly the restrictions (1.9).

The source maximizes the binomial log likelihood on the CLOSED cube. We use its
product likelihood, preserving boundary cases, rather than Lean's totalized
real logarithm. A feasible constant vector 1/2 has strictly positive likelihood;
thus maximizers have positive likelihood and taking log preserves their order.
This change of objective has no effect on the maximum or its uniqueness.
-/
def VanEedenOrderedBinomialMLE : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (n a : Fin k → ℕ),
    (∀ i, 0 < n i) → (∀ i, a i ≤ n i) →
    orderedBinomialMax n a (fun _ _ => False) (fun i => (a i : ℝ) / n i) ∧
    ∀ (R : Fin k → Fin k → Prop),
      (∀ i j, R i j → i < j) →
      (∀ i j h, R i j → R j h → R i h) →
      (∃ p, orderedBinomialMax n a (orderedBinomialCover R) p) ∧
      ∀ (i j : Fin k), orderedBinomialCover R i j →
        ∀ p p',
          orderedBinomialMax n a (orderedBinomialCover R) p →
          orderedBinomialMax n a
            (fun h l => orderedBinomialCover R h l ∧ ¬ (h = i ∧ l = j)) p' →
          (p' i ≤ p' j → p = p') ∧ (p' j < p' i → p i = p j)

end AronowAudit.Literature

namespace AronowAudit.P029

/-- Held complete proposition, conditional only on a general published
ordered-binomial likelihood theorem. No use of the held theorem constant. -/
def saturated_ml_characterization_conditional_statement : Prop :=
  AronowAudit.Literature.VanEedenOrderedBinomialMLE →
  ∀ (n1 n0 k1 k0 : ℕ)
    (hn1 : 0 < n1) (hn0 : 0 < n0) (hk1 : k1 ≤ n1) (hk0 : k0 ≤ n0),
    saturatedFit n1 n0 k1 k0 ∈ receiptTriangle ∧
    (∀ v ∈ receiptTriangle,
      saturatedLikelihood n1 n0 k1 k0 v.1 v.2 ≤
        saturatedLikelihood n1 n0 k1 k0 (saturatedFit n1 n0 k1 k0).1
          (saturatedFit n1 n0 k1 k0).2 ∧
      (saturatedLikelihood n1 n0 k1 k0 v.1 v.2 =
        saturatedLikelihood n1 n0 k1 k0 (saturatedFit n1 n0 k1 k0).1
          (saturatedFit n1 n0 k1 k0).2 ↔ v = saturatedFit n1 n0 k1 k0)) ∧
    (saturatedFit n1 n0 k1 k0).1 - (saturatedFit n1 n0 k1 k0).2 =
      positiveScore ((k1 : ℝ)/n1) ((k0 : ℝ)/n0)

end AronowAudit.P029

-- Inspect the closed literature proposition and the complete conditional type.
#print AronowAudit.Literature.VanEedenOrderedBinomialMLE
#check @AronowAudit.Literature.VanEedenOrderedBinomialMLE
#print AronowAudit.P029.saturated_ml_characterization_conditional_statement
#check @AronowAudit.P029.saturated_ml_characterization_conditional_statement

#print axioms AronowAudit.Literature.VanEedenOrderedBinomialMLE
#print axioms AronowAudit.P029.saturated_ml_characterization_conditional_statement

-- Existing general results are evidence for no_gain, never additional hypotheses.
#check Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero
#check ProbabilityTheory.strong_law_ae_real
#check ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_inner
#check Causalean.Stat.stdGaussian_map_normSq_orthogonalProjection
#check StatLean.HypothesisTesting.tendsto_perm_cdf_blockSum
#print axioms Causalean.Stat.stdGaussian_map_normSq_orthogonalProjection
#print axioms StatLean.HypothesisTesting.tendsto_perm_cdf_blockSum
