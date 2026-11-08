import SAP.P011b.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

def T18Core : Prop :=
  beta constantWitness = 7/2 ∧
  cwTrueCovariance = 0 ∧
  cwPrintedFirst = 9/4 ∧
  cwPrintedLast = 93009/16 ∧
  (9/16 - (9/16 + 140-70) : ℝ) = -70 ∧
  (fourthMoment (expectation constantWitness) (fun y => 2*y 0) (fun y => 3*y 1)
    (fun y => 4*y 2) (fun y => 5*y 3) (betaHat constantWitness) -
    pairMoment (expectation constantWitness) (fun y => y 0) (fun y => y 1) (betaHat constantWitness) 2 3 *
    pairMoment (expectation constantWitness) (fun y => y 2) (fun y => y 3) (betaHat constantWitness) 4 5) = 0 ∧
  cwTrueCovariance ≠ cwPrintedFirst ∧ cwTrueCovariance ≠ cwPrintedLast ∧
  cwTrueCovariance ≠ -70

def T18Statement : Prop :=
  T18Core ∧ cwActualCovariance = cwTrueCovariance ∧
  cwBracketOnlyRepair = -70 ∧ cwActualCovariance ≠ cwBracketOnlyRepair

def T19Statement (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hs : ∀ k, Homoskedastic (F.model k))
    (hpos : ∀ k, 0 < meanVariance (F.model k)) : Prop :=
  (∀ k y, (F.size k : ℝ)*V2star (F.model k) y-scaledTrue F k =
    (1+(∑ i, ∑ j, adjacency (F.model k).G i j*rho (F.model k) i j)/(F.size k : ℝ))*
      (sampleVariance (weighted (F.model k) y)-meanVariance (F.model k))) ∧
  InProbability F (fun k y => varianceRemainder (F.model k) y) (fun _ => 0) ∧
  (Tendsto (fun k => meanSpread (F.model k)) atTop (𝓝 0) →
    InProbability F (fun k y => (F.size k : ℝ)*V2star (F.model k) y) (scaledTrue F))

def signCertificate : Prop :=
  Scaling signFamily 1 1 1 2 ∧ Valid signFamily ∧
  (∀ n : ℕ, 0 < n →
    Homoskedastic (signModel n) ∧ beta (signModel n) = 0 ∧
    (n : ℝ)*var (signModel n) (betaHat (signModel n)) = 1 ∧
    expectation (signModel n) (fun y => (betaHat (signModel n) y)^2) = 1/(n : ℝ) ∧
    (∀ y : Fin n → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      (n : ℝ)*V2star (signModel n) y = 1 - (betaHat (signModel n) y)^2 ∧
      |(n : ℝ)*V2star (signModel n) y -
        (n : ℝ)*var (signModel n) (betaHat (signModel n))| =
          (betaHat (signModel n) y)^2)) ∧
  (∀ ε : ℝ, 0 < ε →
    (∀ n : ℕ, 0 < n →
      1 - 1/((n : ℝ)*ε) ≤
        signInsideProbability n ε) ∧
    Tendsto (fun k => signInsideProbability (k+1) ε)
      atTop (𝓝 1)) ∧
  signInsideProbability 2 (1/2) = 1/2 ∧
  signInsideProbability 4 (1/2) = 7/8 ∧
  signInsideProbability 16 (1/2) = 32631/32768 ∧
  ¬ (∀ ε : ℝ, 0 < ε →
    Tendsto (fun k => signInsideProbability (k+1) ε)
      atTop (𝓝 0))

/-- The printed universal limit-zero assertion, with its strict inside event. -/
def printedSignAssertion : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ),
    Scaling F c1 c2 c3 c4 → Valid F →
    (∀ k, Homoskedastic (F.model k)) →
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => probability (F.model k)
        {y | |(F.size k : ℝ)*V2star (F.model k) y -
          (F.size k : ℝ)*var (F.model k) (betaHat (F.model k))| < ε})
        atTop (𝓝 0)

def signDetails : Prop := ∀ n : ℕ, 0 < n →
  Dependency (signModel n) ∧
  (∀ i, expectation (signModel n) (fun y => y i)=0 ∧
    covariance (signModel n) i i=1) ∧
  (∀ᵐ y ∂(signModel n).law, ∀ i,
    |weighted (signModel n) y i-beta (signModel n)|=1) ∧
  (∀ y : Fin n → ℝ, (∀ i, y i=1 ∨ y i= -1) →
    (n : ℝ)*V2star (signModel n) y=sampleVariance (weighted (signModel n) y) ∧
    sampleVariance (weighted (signModel n) y)=1-(betaHat (signModel n) y)^2)

def T20Statement : Prop := signCertificate ∧ ¬ printedSignAssertion ∧ signDetails

end
end SAP.P011b
