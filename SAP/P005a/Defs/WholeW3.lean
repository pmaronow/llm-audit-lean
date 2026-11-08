import Mathlib
import SAP.P005a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a

noncomputable section
open Finset
open scoped BigOperators Matrix

/-- T12's six-unit population: a=(-3,-2,-1,0,1,5), x=sqrt(3/20)a,
y(1)=0 and y(0)=a². Unlike weightPopulation, the nonzero outcome is control. -/
def T12Population : Population 6 1 :=
  scalarPopulation weightA (fun _ => 0) weightY weightScale

/-- The control nuisance product whose expectation the printed display estimates. -/
def T12ControlNuisance (S : Finset (Fin 6)) : ℝ :=
  dot (xMean T12Population (control S))
    (armNu1 T12Population (control S) T12Population.yC +
      armNu2 T12Population (control S) T12Population.yC +
      armNu3 T12Population (control S) T12Population.yC)

/-- The display printed on p. 1518, with the treated-arm inverse. -/
def T12PrintedEstimator (S : Finset (Fin 6)) : ℝ :=
  (2 : ℝ) / ((6 - 2 : ℝ) * 4) *
      sampleCov (control S) (leverage T12Population) T12Population.yC +
    dot (xMean T12Population (control S))
      (((armL T12Population S)⁻¹ - 1) *ᵥ
        armN T12Population (control S) T12Population.yC)

/-- The same display with the control-arm inverse, as required by nu₂C. -/
def T12CorrectedEstimator (S : Finset (Fin 6)) : ℝ :=
  (2 : ℝ) / ((6 - 2 : ℝ) * 4) *
      sampleCov (control S) (leverage T12Population) T12Population.yC +
    dot (xMean T12Population (control S))
      (((armL T12Population (control S))⁻¹ - 1) *ᵥ
        armN T12Population (control S) T12Population.yC)

/-- P005-T12; Appendix B.4, display introduced by “Similarly”, p. 1518 (PDF p. 17).
The printed claim is false: for the six-unit population with a=(-3,-2,-1,0,1,5),
x=sqrt(3/20)a, y(1)=0 and y(0)=a², all 15 assignments have positive treated and
control Gram matrices. The population is standardized, has bounded second
moments and allocation 1/3, and has h_i=(3/20)a_i² and mean leverage one.
The control slope decomposes into its population slope and the three nu terms;
the mean control covariate and its population-slope product have expectation
zero. The nuisance-product and fitted-slope-product expectations both equal
31085815448171/17062566567774 (approximately 1.822). The printed estimator has
expectation 12010469/846720 (approximately 14.18), so is biased; replacing the
treated inverse by the control inverse gives exactly the nuisance expectation.
The arm sizes, variance scaling, coefficient 1/8 and all rational-coordinate
identities hold assignment by assignment. -/
def T12WholeStatement : Prop :=
  let P := T12Population
  ((design 6 2).card = 15 ∧
    Function.Injective weightX ∧
    popMean (fun i => weightA i ^ 2) = (40 / 6 : ℝ) ∧
    standardized P ∧
    popMean weightX = 0 ∧
    popMean (fun i => weightX i ^ 2) = (3 / 20 : ℝ) * (40 / 6 : ℝ) ∧
    popMean (fun i => weightX i ^ 2) = 1 ∧
    popMean (fun i => P.yT i ^ 2) = 0 ∧
    popMean (fun i => P.yC i ^ 2) ≤ 121 ∧
    (1 / 4 : ℝ) < pT 6 2 ∧ pT 6 2 < (3 / 4 : ℝ)) ∧
  (interactedRegular P 2 ∧
    ∀ S ∈ design 6 2,
      S.card = 2 ∧ (control S).card = 4 ∧
      armL P S 0 0 = (3 / 20 : ℝ) * sampleCov S weightA weightA ∧
      armL P (control S) 0 0 =
        (3 / 20 : ℝ) * sampleCov (control S) weightA weightA ∧
      0 < armL P S 0 0 ∧ 0 < armL P (control S) 0 0 ∧
      armBetaHat P (control S) P.yC =
        populationSlope P P.yC + armNu1 P (control S) P.yC +
          armNu2 P (control S) P.yC + armNu3 P (control S) P.yC) ∧
  ((∀ i, leverage P i = weightX i ^ 2 ∧
      leverage P i = (3 / 20 : ℝ) * weightA i ^ 2) ∧
    popMean (leverage P) = 1) ∧
  (expectation 2 (fun S => xMean P (control S) 0) = 0 ∧
    expectation 2 (fun S =>
      dot (xMean P (control S)) (populationSlope P P.yC)) = 0 ∧
    expectation 2 T12ControlNuisance =
      expectation 2 (fun S =>
        dot (xMean P (control S)) (armBetaHat P (control S) P.yC)) ∧
    expectation 2 (fun S =>
      dot (xMean P (control S)) (armBetaHat P (control S) P.yC)) =
        (31085815448171 / 17062566567774 : ℝ) ∧
    expectation 2 T12ControlNuisance =
      (31085815448171 / 17062566567774 : ℝ)) ∧
  (expectation 2 T12PrintedEstimator = (12010469 / 846720 : ℝ) ∧
    expectation 2 T12CorrectedEstimator =
      (31085815448171 / 17062566567774 : ℝ) ∧
    expectation 2 T12PrintedEstimator ≠ expectation 2 T12ControlNuisance ∧
    expectation 2 T12CorrectedEstimator = expectation 2 T12ControlNuisance ∧
    |(31085815448171 / 17062566567774 : ℝ) - 1.822| < 0.0005 ∧
    |(12010469 / 846720 : ℝ) - 14.18| < 0.005) ∧
  ((2 : ℝ) / ((6 - 2 : ℝ) * 4) = 1 / 8 ∧
    ∀ S ∈ design 6 2,
      dot (xMean P (control S)) (armBetaHat P (control S) P.yC) =
        mean (control S) weightA * sampleCov (control S) weightA weightY /
          sampleCov (control S) weightA weightA ∧
      dot (xMean P (control S)) (armN P (control S) P.yC) =
        (3 / 20 : ℝ) * mean (control S) weightA *
          sampleCov (control S) weightA weightY ∧
      dot (xMean P (control S))
          ((armL P S)⁻¹ *ᵥ armN P (control S) P.yC) =
        mean (control S) weightA * sampleCov (control S) weightA weightY /
          sampleCov S weightA weightA ∧
      sampleCov (control S) (leverage P) P.yC =
        (3 / 20 : ℝ) *
          (mean (control S) (fun i => weightA i ^ 2 * weightY i) -
            mean (control S) (fun i => weightA i ^ 2) * mean (control S) weightY))

end
end SAP.P005a
