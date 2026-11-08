import Mathlib
import SAP.P040.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P040

open scoped BigOperators

noncomputable section

/-- The CDF of the actual standard normal probability measure. -/
def T1NormalCDF (t : ℝ) : ℝ :=
  ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t

/-- The standard normal .975 quantile. Its defining set is proved nonempty and
bounded below in `T1NormalQuantileSpecification`, so the infimum has its intended meaning. -/
def T1NormalQuantile : ℝ := sInf {t : ℝ | (39 / 40 : ℝ) ≤ T1NormalCDF t}

/-- Uniform finite-sample coverage of a deterministic count-based set rule. -/
def T1UniformIntervalCoverage (level : ℝ) (I : DetectionCount → Set ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0 : ℝ) 1, level ≤ intervalCoverage p I

/-- Uniform finite-sample coverage of a deterministic count-based lower bound. -/
def T1UniformLowerCoverage (level : ℝ) (ell : DetectionCount → ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0 : ℝ) 1, level ≤ countProbability p (fun k => ell k ≤ p)

/-- Equivalent displayed fractions and terminating decimals in T1 A1--A3.
The other exact probabilities, inequalities and endpoint arithmetic are retained
in `T1Statement`. All decimals here are exact real rational constants. -/
def T1DisplayedIdentities : Prop :=
  binomialMass (4 / 5) 14 = 15 * (4 / 5 : ℝ) ^ 14 * (1 / 5) ∧
  binomialMass (4 / 5) 14 = (3 * (4 : ℝ) ^ 14) / 5 ^ 14 ∧
  binomialMass (4 / 5) 14 = (0.13194139533312 : ℝ) ∧
  1 - binomialMass (4 / 5) 14 = (5298209257 : ℝ) / 6103515625 ∧
  (5298209257 : ℝ) / 6103515625 = 0.86805860466688 ∧
  (24866193408 : ℝ) / 30517578125 = 0.814815425593344 ∧
  (25417304461 : ℝ) / 30517578125 = 0.832874232578048 ∧
  (5100273664 : ℝ) / 30517578125 = (19 * (4 : ℝ) ^ 14) / 5 ^ 15 ∧
  (5100273664 : ℝ) / 30517578125 = 0.167125767421952

/-- T1 A4: the actual normal quantile exists, is unique, and lies in the
robustness range. The tighter enclosure also certifies the endpoint prefixes
given in the canonical definitions. Existence is a conclusion, not a premise. -/
def T1NormalQuantileSpecification : Prop :=
  {t : ℝ | (39 / 40 : ℝ) ≤ T1NormalCDF t}.Nonempty ∧
  BddBelow {t : ℝ | (39 / 40 : ℝ) ≤ T1NormalCDF t} ∧
  T1NormalCDF T1NormalQuantile = (39 / 40 : ℝ) ∧
  (∀ t : ℝ, T1NormalCDF t = (39 / 40 : ℝ) → t = T1NormalQuantile) ∧
  T1NormalQuantile ∈ Set.Icc (19599 / 10000 : ℝ) (19601 / 10000) ∧
  (195996398454005 / 10 ^ 14 : ℝ) < T1NormalQuantile ∧
  T1NormalQuantile < (195996398454006 / 10 ^ 14 : ℝ)

/-- The reconstruction also reproduces the printed interval with the actual
normal quantile; the six-decimal prefixes are enclosed, not treated as rounded values. -/
def T1ExactQuantileEndpoints : Prop :=
  (807099 / 1000000 : ℝ) < detectionProportion 14 - waldRadius T1NormalQuantile 14 ∧
  detectionProportion 14 - waldRadius T1NormalQuantile 14 < (807100 / 1000000 : ℝ) ∧
  (1059567 / 1000000 : ℝ) < detectionProportion 14 + waldRadius T1NormalQuantile 14 ∧
  detectionProportion 14 + waldRadius T1NormalQuantile 14 < (1059568 / 1000000 : ℝ) ∧
  roundsTwo (detectionProportion 14 - waldRadius T1NormalQuantile 14) (81 / 100) ∧
  roundsTwo (detectionProportion 14 + waldRadius T1NormalQuantile 14) (106 / 100) ∧
  (1 : ℝ) < detectionProportion 14 + waldRadius T1NormalQuantile 14 ∧
  (4 / 5 : ℝ) ∉ waldInterval T1NormalQuantile 14

/-- The finite sum, tail-complement identity, and failure of both uniform lower
confidence levels, for a multiplier in the range quantified in the whole statement. -/
def T1WaldConsequences (z : ℝ) : Prop :=
  intervalCoverage (4 / 5) (waldInterval z) =
    ∑ k ∈ Finset.Icc (9 : DetectionCount) 13, binomialMass (4 / 5) k ∧
  countProbability (4 / 5) (fun k => detectionProportion k - waldRadius z k ≤ 4 / 5) =
    1 - upperDetectionTail (4 / 5) 14 ∧
  upperDetectionTail (4 / 5) 14 = (5100273664 : ℝ) / 30517578125 ∧
  (∀ k : DetectionCount,
    ((4 / 5 : ℝ) < detectionProportion k - waldRadius z k ↔ 14 ≤ k.val)) ∧
  ¬ T1UniformLowerCoverage (19 / 20) (fun k => detectionProportion k - waldRadius z k) ∧
  ¬ T1UniformLowerCoverage (39 / 40) (fun k => detectionProportion k - waldRadius z k)

/-- T1 A2 and its consequence: an arbitrary set rule excluding .80 at count 14,
or an arbitrary lower bound above .80 there, cannot have either stated uniform
coverage guarantee. No shape or monotonicity assumption is imposed. -/
def T1MethodFreeConsequences : Prop :=
  (∀ I : DetectionCount → Set ℝ, (4 / 5 : ℝ) ∉ I 14 →
    ¬ T1UniformIntervalCoverage (19 / 20) I ∧
    ¬ T1UniformIntervalCoverage (39 / 40) I) ∧
  (∀ ell : DetectionCount → ℝ, (4 / 5 : ℝ) < ell 14 →
    ¬ T1UniformLowerCoverage (19 / 20) ell ∧
    ¬ T1UniformLowerCoverage (39 / 40) ell)

/-- P040-T1; p. 3, right column, manipulation check (PDF p. 3).
Under the independent common-probability binomial model for fifteen detections,
the mass of count 14 at p = .80 is .13194139533312. Every deterministic count-based
set excluding .80 there, and every lower bound above .80 there, has coverage at
most .86805860466688, so cannot guarantee .95 or .975 uniformly. The printed
interval and every lower endpoint rounding to .81 exclude .80. The Wald rule
with multiplier 1.96 reproduces the printed endpoints, with the stated rational
arithmetic and brackets. For every multiplier in [1.9599,1.9601], membership,
two-sided coverage .814815425593344, lower coverage .832874232578048 and lower
failure probability .167125767421952 have the stated exact values. The actual
standard normal .975 quantile exists uniquely in that range and also reproduces
the printed endpoints, with prefixes .807099 and 1.059567. This is the canonical
finite-sample calibration counterexample under the added binomial model. -/
def T1WholeStatement : Prop :=
  T1Statement ∧
  T1DisplayedIdentities ∧
  (∀ l : ℝ, roundsTwo l (81 / 100) →
    (161 / 200 : ℝ) ≤ l ∧
    ∀ J : Set ℝ, J ⊆ Set.Ici l → (4 / 5 : ℝ) ∉ J) ∧
  (∀ z : ℝ, ∀ k : DetectionCount,
    waldRadius z k ^ 2 = z ^ 2 *
      (detectionProportion k * (1 - detectionProportion k) / 15)) ∧
  T1NormalQuantileSpecification ∧
  T1ExactQuantileEndpoints ∧
  (∀ z : ℝ, (19599 / 10000 : ℝ) ≤ z → z ≤ (19601 / 10000 : ℝ) →
    T1WaldConsequences z) ∧
  T1MethodFreeConsequences

end

end SAP.P040
