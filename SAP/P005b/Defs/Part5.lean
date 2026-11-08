import SAP.P005b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005b

noncomputable section
open scoped BigOperators Matrix
open Finset Filter

def T19Statement : Prop :=
      ¬ (∀ {n m : ℕ}, 4 ≤ n → 0 < m → m < n →
      ∀ (t : Arm) (a b : Fin n → ℝ),
      expectation m (fun S => sampleCov (armSet t S) a b) =
        ((armSize n m t : ℝ)-1)*n/((armSize n m t : ℝ)*(n-1))*popCov a b ∧
      variance m (fun S => sampleCov (armSet t S) a b) ≤
        covarianceBound (armSize n m t) a b)

def T24Statement : Prop :=
  ∀ {n d m : ℕ} (P : Population n d)
    (hn : 2 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : interactedRegular P m),
    (∀ S ∈ design n m,
      armBetaHat P S P.yT = populationSlope P P.yT + armNu1 P S P.yT + armNu2 P S P.yT + armNu3 P S P.yT ∧
      armBetaHat P (control S) P.yC = populationSlope P P.yC + armNu1 P (control S) P.yC +
        armNu2 P (control S) P.yC + armNu3 P (control S) P.yC) ∧
    expectation m (fun S => interactedATE P S - ate P) =
      expectation m (fun S => dot (xMean P (control S))
        (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT + armNu2 P S P.yT + armNu3 P S P.yT)) ∧
    expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
      ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu1 P S P.yT)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC -
        ((n : ℝ)-m)/((n-1 : ℝ)*m)*leverageCov P P.yT

def T20Statement : Prop :=
  T24Statement ∧
  (    ¬ (∀ {n d m : ℕ} (P : Population n d),
      3 ≤ n → 0 < m → m < n → standardized P → interactedRegular P m →
      expectation m (fun S => dot (xMean P (control S)) (armNu3 P (control S) P.yC)) -
        expectation m (fun S => dot (xMean P S) (armNu3 P S P.yT)) =
          NCCC n m * leverageCov P P.yC - NTTT n m * leverageCov P P.yT)) ∧
  (    ¬ ∀ (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)), standingAssumptions d m P →
      (∀ᶠ n in atTop, interactedRegular (P n) (m n)) →
      Tendsto (fun n => kappa (P n) * Real.log (d n)) atTop (nhds 0) →
      stochasticO m (fun n S => interactedATE (P n) S - ate (P n) - armLeading (P n) S)
        (fun n => Real.sqrt (kappa (P n) * (d n) / n)))

end
end SAP.P005b
