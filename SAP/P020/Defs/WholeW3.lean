import Mathlib
import SAP.P020.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020

open scoped BigOperators

noncomputable section

/-- The selected arm's mean of a fixed cluster feature, centered at its
whole-population cluster mean. The positive arm counts are carried by `P`. -/
def centeredArmMeanW3 (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ)
    (s : Finset (Fin P.M)) : ℝ :=
  armSum P a v s / (if a then P.mt else controlCount P) - clusterMean v

/-- P020-T13; p. 54 (PDF p. 16), equations (20)-(22) and the following display;
pp. 58-59 (PDF pp. 20-21), Section 5.4.
Under complete random allocation of fixed positive numbers of clusters to both
arms, the Des Raj estimators with any fixed common size coefficient, and with
any finite collection of fixed covariates and coefficients, unbiasedly estimate
both potential-outcome totals and their difference divided by the population
size. Equation (22) averages the selected cluster or arm mean: the fixed
coefficient factors out of expectation, the centered arm mean has expectation
zero, and so does its fixed multiple. The combined size and covariate arm-mean
adjustment also has expectation zero. Both adjusted arm-total estimators have
the same expectations as HT. Covariate totals and all coefficients are fixed
before analysis; zero covariates and zero size or covariate variance are allowed.
The usual measure-theoretic conditions are assumed; here all expectations are
finite design sums. -/
def T13WholeStatement_W3 : Prop :=
  T13Statement ∧
  (∀ (P : ClusterPopulation) (a : Bool) (k : ℝ),
    expectation (clusterLaw P)
        (fun s => k * (armMeanSize P a s - (populationSize P : ℝ) / P.M)) =
      k * expectation (clusterLaw P)
        (fun s => armMeanSize P a s - (populationSize P : ℝ) / P.M) ∧
    expectation (clusterLaw P)
        (fun s => armMeanSize P a s - (populationSize P : ℝ) / P.M) = 0 ∧
    expectation (clusterLaw P)
        (fun s => k * (armMeanSize P a s - (populationSize P : ℝ) / P.M)) = 0) ∧
  (∀ (P : ClusterPopulation) {A : ℕ} (X : Fin A → Fin P.M → ℝ)
      (ks : ℝ) (ka : Fin A → ℝ) (a : Bool),
    expectation (clusterLaw P) (fun s =>
      ks * centeredArmMeanW3 P a (fun j => (P.n j : ℝ)) s +
        ∑ cov, ka cov * centeredArmMeanW3 P a (X cov) s) = 0) ∧
  (∀ (P : ClusterPopulation) (a : Bool) (k : ℝ),
    expectation (clusterLaw P) (rajTotal P a k) =
      expectation (clusterLaw P) (htTotal P a)) ∧
  (∀ (P : ClusterPopulation) {A : ℕ} (X : Fin A → Fin P.M → ℝ)
      (ks : ℝ) (ka : Fin A → ℝ) (a : Bool),
    expectation (clusterLaw P) (rajCovariateTotal P X ks ka a) =
      expectation (clusterLaw P) (htTotal P a))

end

end SAP.P020
