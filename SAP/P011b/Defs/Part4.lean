import SAP.P011b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-! Corrected and printed moment expressions. These are integral
expressions; T17 supplies their separate moment domains explicitly. -/

def covOf {n : ℕ} (m : Model n) (f g : (Fin n → ℝ) → ℝ) : ℝ :=
  expectation m (fun y => f y*g y)-expectation m f*expectation m g

def pairMoment {Ω : Type} (E : (Ω → ℝ) → ℝ) (yi yj B : Ω → ℝ) (ti tj : ℝ) : ℝ :=
  ti*tj*E (fun y => yi y*yj y)-ti*E (fun y => yi y*B y)-
    tj*E (fun y => yj y*B y)+E (fun y => B y^2)

def fourthMoment {Ω : Type} (E : (Ω → ℝ) → ℝ) (Xi Xj Xk Xl B : Ω → ℝ) : ℝ :=
  E (fun y => Xi y*Xj y*Xk y*Xl y) -
  E (fun y => B y*(Xi y*Xj y*Xk y+Xi y*Xj y*Xl y+Xi y*Xk y*Xl y+Xj y*Xk y*Xl y)) +
  E (fun y => B y^2*(Xi y*Xj y+Xi y*Xk y+Xi y*Xl y+Xj y*Xk y+Xj y*Xl y+Xk y*Xl y)) -
  E (fun y => B y^3*(Xi y+Xj y+Xk y+Xl y)) + E (fun y => B y^4)

def printedBracket {Ω : Type} (E : (Ω → ℝ) → ℝ) (yi yj yk yl B : Ω → ℝ)
    (ti tj tk tl : ℝ) : ℝ :=
  E (fun y => yi y*yj y)*E (fun y => yk y*yl y) -
  ti*tj*tk*E (fun y => yi y*yj y)*E (fun y => yk y*B y) -
  ti*tj*tl*E (fun y => yi y*yj y)*E (fun y => yl y*B y) +
  ti*tj*E (fun y => yi y*yj y)*E (fun y => B y^2) -
  tk*tl*E (fun y => yi y*B y)*E (fun y => yk y*yl y) +
  ti*tl*E (fun y => yi y*B y)*E (fun y => yl y*B y) +
  ti*tk*E (fun y => yi y*B y)*E (fun y => yk y*B y) -
  ti*E (fun y => yi y*B y)*E (fun y => B y^2) -
  tj*tk*tl*E (fun y => yj y*B y)*E (fun y => yk y*yl y) +
  tj*tl*E (fun y => yj y*B y)*E (fun y => yl y*B y) +
  tj*tk*E (fun y => yj y*B y)*E (fun y => yk y*B y) -
  tj*E (fun y => yj y*B y)*E (fun y => B y^2) +
  tk*tl*E (fun y => B y^2)*E (fun y => yk y*yl y) -
  tk*E (fun y => B y^2)*E (fun y => yk y*B y) -
  tl*E (fun y => B y^2)*E (fun y => yl y*B y) +
  E (fun y => B y^2)*E (fun y => B y^2)

def constantWitness : Model 4 where
  law := Measure.dirac (fun _ => (1 : ℝ))
  probability := by infer_instance
  theta := ![2,3,4,5]
  G := emptyGraph 4
  R := emptyGraph 4
  d := fun _ => 0

def cwTrueCovariance : ℝ :=
  covOf constantWitness
      (fun y => (2*y 0-betaHat constantWitness y)*(3*y 1-betaHat constantWitness y))
      (fun y => (4*y 2-betaHat constantWitness y)*(5*y 3-betaHat constantWitness y))

def cwActualCovariance : ℝ :=
  ProbabilityTheory.covariance
    (fun y => (2*y 0-betaHat constantWitness y)*(3*y 1-betaHat constantWitness y))
    (fun y => (4*y 2-betaHat constantWitness y)*(5*y 3-betaHat constantWitness y))
    constantWitness.law

def cwPrintedFirst : ℝ :=
  (expectation constantWitness (fun y => (2*y 0-betaHat constantWitness y)*
      (y 1-betaHat constantWitness y)*(4*y 2-betaHat constantWitness y)*(5*y 3-betaHat constantWitness y)) -
      expectation constantWitness (fun y => (2*y 0-betaHat constantWitness y)*(3*y 1-betaHat constantWitness y))*
      expectation constantWitness (fun y => (4*y 2-betaHat constantWitness y)*(5*y 3-betaHat constantWitness y)))

def cwPrintedLast : ℝ :=
  (fourthMoment (expectation constantWitness) (fun y => 2*y 0) (fun y => 3*y 1)
      (fun y => 4*y 2) (fun y => 5*y 3) (betaHat constantWitness) -
      120*printedBracket (expectation constantWitness) (fun y => y 0) (fun y => y 1)
        (fun y => y 2) (fun y => y 3) (betaHat constantWitness) 2 3 4 5)

/-- Move only the opening bracket in (3.3). The leading pair-moment product
now has coefficient 2*3*4*5 instead of 1, and the remaining terms retain
their printed coefficients, including the missing weight in the fifth term. -/
def cwBracketOnlyRepair : ℝ :=
  let E := expectation constantWitness
  let B := betaHat constantWitness
  fourthMoment E (fun y => 2*y 0) (fun y => 3*y 1)
    (fun y => 4*y 2) (fun y => 5*y 3) B -
    (printedBracket E (fun y => y 0) (fun y => y 1)
      (fun y => y 2) (fun y => y 3) B 2 3 4 5 +
      ((2*3*4*5 : ℝ)-1) * E (fun y => y 0*y 1) * E (fun y => y 2*y 3))

def rho {n : ℕ} (m : Model n) (i j : Fin n) : ℝ :=
  if meanVariance m = 0 then 0 else covariance m i j/meanVariance m

def V2star {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  sampleVariance (weighted m y)/n * (1+(∑ i, ∑ j, adjacency m.G i j*rho m i j)/n)

def rawFourthMoment
    {Ω : Type} (E : (Ω → ℝ) → ℝ) (Y : Fin 4 → Ω → ℝ)
    (B : Ω → ℝ) (θ : Fin 4 → ℝ) : ℝ :=
  θ 0*θ 1*θ 2*θ 3 * E (fun y => Y 0 y*Y 1 y*Y 2 y*Y 3 y) -
  θ 0*θ 1*θ 2 * E (fun y => Y 0 y*Y 1 y*Y 2 y*B y) -
  θ 0*θ 1*θ 3 * E (fun y => Y 0 y*Y 1 y*Y 3 y*B y) -
  θ 0*θ 2*θ 3 * E (fun y => Y 0 y*Y 2 y*Y 3 y*B y) -
  θ 1*θ 2*θ 3 * E (fun y => Y 1 y*Y 2 y*Y 3 y*B y) +
  θ 0*θ 1 * E (fun y => Y 0 y*Y 1 y*(B y)^2) +
  θ 0*θ 2 * E (fun y => Y 0 y*Y 2 y*(B y)^2) +
  θ 0*θ 3 * E (fun y => Y 0 y*Y 3 y*(B y)^2) +
  θ 1*θ 2 * E (fun y => Y 1 y*Y 2 y*(B y)^2) +
  θ 1*θ 3 * E (fun y => Y 1 y*Y 3 y*(B y)^2) +
  θ 2*θ 3 * E (fun y => Y 2 y*Y 3 y*(B y)^2) -
  θ 0 * E (fun y => Y 0 y*(B y)^3) -
  θ 1 * E (fun y => Y 1 y*(B y)^3) -
  θ 2 * E (fun y => Y 2 y*(B y)^3) -
  θ 3 * E (fun y => Y 3 y*(B y)^3) + E (fun y => (B y)^4)

noncomputable def signInsideProbability (n : ℕ) (ε : ℝ) : ℝ :=
  probability (signModel n)
    {y | |(n : ℝ)*V2star (signModel n) y -
      (n : ℝ)*var (signModel n) (betaHat (signModel n))| < ε}

end
end SAP.P011b
