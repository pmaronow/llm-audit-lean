import SAP.P037a.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037a

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

def exposureOverlapWitnesses : Prop :=
  ExposureData.Feasible ⟨1,0,0,0⟩ ∧
      printedCase ⟨1,0,0,0⟩ .school ∧
      printedCase ⟨1,0,0,0⟩ .nonreferent ∧
      ExposureCase.school ≠ ExposureCase.nonreferent ∧
      ExposureData.Feasible ⟨1,1,0,0⟩ ∧
      printedCase ⟨1,1,0,0⟩ .nonreferent ∧
      printedCase ⟨1,1,0,0⟩ .direct ∧
      ExposureCase.nonreferent ≠ ExposureCase.direct

def exposureNotFunction : Prop :=
  ¬ ∃ f : ExposureData → ExposureCase,
        ∀ x, x.Feasible → ∀ e, printedCase x e → f x=e

def exposureOverlaps : Prop :=
  ∀ (x : ExposureData)
      (hx : x.Feasible),
    (printedCase x .school → printedCase x .nonreferent) ∧
      (x.school = 1 → x.seed = 1 → x.referentPeers = 0 →
        printedCase x .nonreferent ∧ printedCase x .direct)

def exposurePartition : Prop :=
  ∀ (x : ExposureData) (hx : x.Feasible),
    ∃! e : ExposureCase, correctedCase x e

def T7Statement : Prop := exposureOverlapWitnesses ∧ exposureNotFunction ∧ exposureOverlaps

def T8Statement : Prop := exposurePartition ∧
  correctedCase ⟨1,0,0,0⟩ .school ∧ correctedCase ⟨1,1,0,0⟩ .direct

def frequencyExample : Prop :=
  frequency 2 (![0,1] : Fin 2 → ℕ) 1 = 1/2 ∧
      (if ((1:ℝ)+1)/2 = 1 then (1:ℝ) else 0) = 1 ∧
      (if ((0:ℝ)+1)/2 = 1 then (1:ℝ) else 0) = 0

def frequencyLastDraw : Prop :=
  ∀ (J : ℕ) (hJ : 0 < J) (v target : ℝ),
    (if (∑ _ : Fin J, v)/(J:ℝ)=target then (1:ℝ) else 0) =
        (if v=target then (1:ℝ) else 0)

def FrequencyFacts : Prop :=
  ∀ {Ω : Type} [Fintype Ω] (d : Design Ω) (E : Ω → Prop) [DecidablePred E],
  let X := fun w => if E w then (1:ℝ) else 0
  let pi := mean d X
  variance d X = pi*(1-pi) ∧
  (∀ J : ℕ, 0 < J →
    let draws := independentDesign (fun _ : Fin J => d)
    mean draws (fun w => (∑ j, X (w j))/J) = pi ∧
    variance draws (fun w => (∑ j, X (w j))/J) = pi*(1-pi)/J ∧
    variance draws (fun w => (∑ j, X (w j))/J) ≤ 1/(4*J) ∧
    ∀ eps : ℝ, 0 < eps →
      probability draws (fun w => eps < |(∑ j, X (w j))/J-pi|) ≤ 1/(4*J*eps^2)) ∧
  (∀ eps : ℝ, 0 < eps → Tendsto (fun J =>
    probability (independentDesign (fun _ : Fin (J+1) => d))
      (fun w => eps < |(∑ j, X (w j))/(J+1)-pi|)) atTop (nhds 0))

def T9Statement : Prop := FrequencyFacts ∧ frequencyLastDraw ∧ frequencyExample

def blockConstraints : Prop :=
  (∀ w i, treatment w i = 0 ∨ treatment w i = 1) ∧
      (∀ w, ∑ i, treatment w i = 2)

def withinBlockDependence : Prop :=
  (∀ i, mean blockDesign (fun w => treatment w i) = 1/2) ∧
      (∀ i j, i ≠ j →
        mean blockDesign (fun w => treatment w i*treatment w j) = 1/6 ∧
        covariance blockDesign (fun w => treatment w i)
          (fun w => treatment w j) = -1/12 ∧
        covariance blockDesign (fun w => 1-treatment w i)
          (fun w => 1-treatment w j) = -1/12 ∧
        mean blockDesign (fun w => treatment w i*treatment w j) ≠
          mean blockDesign (fun w => treatment w i) *
          mean blockDesign (fun w => treatment w j))

def fixedCountDependence : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
      (d : Design Ω) (T : Fin 4 → Ω → ℝ)
      (hbinary : ∀ i w, T i w=0 ∨ T i w=1)
      (hcount : ∀ w, ∑ i, T i w=2)
      (hmarginal : ∀ i, mean d (T i)=1/2),
    variance d (fun w => ∑ i, T i w)=0 ∧
      (∑ i, variance d (T i))=1 ∧
      (∑ i, ∑ j, if i=j then (0:ℝ) else covariance d (T i) (T j)) = -1 ∧
      (∃ i j, i≠j ∧ covariance d (T i) (T j) < 0)

def betweenBlockIndependence : Prop :=
  (∀ u v, doubleBlockDesign.weight (u,v) =
        blockDesign.weight u * blockDesign.weight v) ∧
      (∀ i j, covariance doubleBlockDesign
        (fun w => treatment w.1 i) (fun w => treatment w.2 j) = 0)

def T10Statement : Prop := blockConstraints ∧ withinBlockDependence ∧
  fixedCountDependence ∧ betweenBlockIndependence ∧
  Fintype.card (Fin 6 × Fin 6) = 36 ∧
  (∀ u v, doubleBlockDesign.weight (u,v) = 1/36)

end SAP.P037a
