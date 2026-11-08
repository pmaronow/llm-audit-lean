import SAP.P005a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005a

noncomputable section
open Finset Filter
open scoped BigOperators Matrix Topology

/-- The packaged content of P005-T5; scope is recorded in its Challenge docstring. -/
def T5Statement : Prop :=
  standardized signPopulation ∧ interactedRegular signPopulation 2 ∧
    popMean (fun i => signPopulation.yT i^2) ≤ 28 ∧
    popMean (fun i => signPopulation.yC i^2) ≤ 28 ∧
    (1/4 : ℝ) < pT 6 2 ∧ pT 6 2 < (3/4 : ℝ) ∧
    (design 6 2).card = 15 ∧
    leverageCov signPopulation signPopulation.yT = (434/625 : ℝ) ∧
    leverageCov signPopulation signPopulation.yC = (868/625 : ℝ) ∧
    expectation 2 (fun S => dot (xMean signPopulation (control S))
      (armNu3 signPopulation (control S) signPopulation.yC)) -
      expectation 2 (fun S => dot (xMean signPopulation S)
        (armNu3 signPopulation S signPopulation.yT)) = (217/2500 : ℝ) ∧
    NCCC 6 2 * leverageCov signPopulation signPopulation.yC -
      NTTT 6 2 * leverageCov signPopulation signPopulation.yT = -(217/2500 : ℝ) ∧
    expectation 2 (fun S => dot (xMean signPopulation (control S))
      (armNu3 signPopulation (control S) signPopulation.yC)) -
      expectation 2 (fun S => dot (xMean signPopulation S)
        (armNu3 signPopulation S signPopulation.yT)) ≠
      NCCC 6 2 * leverageCov signPopulation signPopulation.yC -
        NTTT 6 2 * leverageCov signPopulation signPopulation.yT

/-- The packaged content of P005-T6; scope is recorded in its Challenge docstring. -/
def T6Statement : Prop :=
  ∀ {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0),
    expectation m (fun S => dot (xMean P S) (xMean P S) * mean S (centered P.yT)) =
      NTTT n m * leverageCov P P.yT ∧
    expectation m (fun S => dot (xMean P (control S)) (xMean P (control S)) *
      mean (control S) (centered P.yC)) = NCCC n m * leverageCov P P.yC ∧
    expectation m (fun S => dot (xMean P S) (armNu3 P S P.yT)) =
      -NTTT n m * leverageCov P P.yT ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu3 P (control S) P.yC)) =
      -NCCC n m * leverageCov P P.yC ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu3 P (control S) P.yC)) -
      expectation m (fun S => dot (xMean P S) (armNu3 P S P.yT)) =
        -NCCC n m * leverageCov P P.yC + NTTT n m * leverageCov P P.yT

/-- The packaged content of P005-T7; scope is recorded in its Challenge docstring. -/
def T7Statement : Prop :=
  (standingAssumptions (fun _ => 1) (fun n => n/2) spikePopulation ∧
    (∀ n, 6 ≤ n → standardized (spikePopulation n) ∧
      popMean (fun i => (spikePopulation n).yT i^2) ≤ 1 ∧
      popMean (fun i => (spikePopulation n).yC i^2) ≤ 1 ∧
      (∀ k, popMean (fun i => (spikePopulation n).x i k^2) = 1) ∧
      (1/4 : ℝ) < pT n (n/2) ∧ pT n (n/2) < (3/4 : ℝ)) ∧
    (∀ n, 6 ≤ n → interactedRegular (spikePopulation n) (n/2)) ∧
    Tendsto (fun n => kappa (spikePopulation n)) atTop (nhds 1) ∧
    Tendsto (fun n => kappa (spikePopulation n) * Real.log (1 : ℝ)) atTop (nhds 0) ∧
    (∀ n, 6 ≤ n → ate (spikePopulation n) = 0) ∧
    (∀ n, 6 ≤ n → Even n → ∀ S ∈ design n (n/2),
      (n : ℝ)-6 ≤ |interactedATE (spikePopulation n) S - ate (spikePopulation n) -
        armLeading (spikePopulation n) S|) ∧
    ¬stochasticO (fun n => n/2)
      (fun n S => interactedATE (spikePopulation n) S - ate (spikePopulation n) - armLeading (spikePopulation n) S)
      (fun n => Real.sqrt (kappa (spikePopulation n)/n))) ∧
  (∀ n : ℕ, 6 ≤ n → 0 < spikeQ n) ∧
  (∀ n : ℕ, 6 ≤ n → kappa (spikePopulation n) * Real.log (1 : ℝ) = 0)

/-- The packaged content of P005-T9; scope is recorded in its Challenge docstring. -/
def T9Statement : Prop :=
  (∀ (d : ℕ) (hd : 1 ≤ d),
    Real.log (max d 2 : ℕ) ≤ Real.log (2*d : ℕ) ∧
    Real.log (2*d : ℕ) ≤ 2 * Real.log (max d 2 : ℕ)) ∧
  (∀ (d : ℕ → ℕ) (κ : ℕ → ℝ)
    (hd : ∀ᶠ n in atTop, 1 ≤ d n) (hκ : ∀ᶠ n in atTop, 0 ≤ κ n),
    (Tendsto (fun n => κ n * Real.log (2*d n : ℕ)) atTop (nhds 0) ↔
      Tendsto (fun n => κ n * Real.log (max (d n) 2 : ℕ)) atTop (nhds 0)) ∧
    (Tendsto (fun n => κ n * Real.log (2*d n : ℕ)) atTop (nhds 0) →
      Tendsto κ atTop (nhds 0) ∧
      Tendsto (fun n => κ n * Real.log (d n)) atTop (nhds 0)) ∧
    ((∀ᶠ n in atTop, 2 ≤ d n) →
      (Tendsto (fun n => κ n * Real.log (d n)) atTop (nhds 0) ↔
        Tendsto (fun n => κ n * Real.log (2*d n : ℕ)) atTop (nhds 0))))

/-- The packaged content of P005-T10; scope is recorded in its Challenge docstring. -/
def T10Statement : Prop :=
  standardized weightPopulation ∧ interactedRegular weightPopulation 2 ∧
    popMean (fun i => weightY i^2) ≤ 121 ∧
    (1/4 : ℝ) < pT 6 2 ∧ pT 6 2 < (3/4 : ℝ) ∧
    expectation 2 (fun S => mean S weightY - dot (xMean weightPopulation S) (armN weightPopulation S weightY) +
      (1/8 : ℝ)*sampleCov S (leverage weightPopulation) weightY) = (4913/1200 : ℝ) ∧
    expectation 2 (fun S => mean S weightY - dot (xMean weightPopulation S) (armN weightPopulation S weightY) +
      (1/2 : ℝ)*sampleCov S (leverage weightPopulation) weightY) = (20/3 : ℝ) ∧
    popMean weightY = (20/3 : ℝ) ∧
    expectation 2 (fun S => mean S weightY - dot (xMean weightPopulation S) (armN weightPopulation S weightY) +
      (1/8 : ℝ)*sampleCov S (leverage weightPopulation) weightY) ≠ popMean weightY

end
end SAP.P005a
