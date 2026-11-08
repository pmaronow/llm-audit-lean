import SAP.P005a.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005a

noncomputable section
open Finset Filter
open scoped BigOperators Matrix Topology

/-- The packaged content of P005-T11; scope is recorded in its Challenge docstring. -/
def T11Statement : Prop :=
  (∀ {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (y : Fin n → ℝ) (c : ℝ)
    (hn : 3 ≤ n) (hS : S.Nonempty) (hinv : (armL P S).det ≠ 0),
    mean S y - dot (xMean P S) (armBetaHat P S y) -
      (-dot (xMean P S) (armNu2 P S y) - c * sampleCov S (leverage P) y) =
      mean S y - dot (xMean P S) (armN P S y) + c * sampleCov S (leverage P) y ∧
    mean S y - dot (xMean P S) (armN P S y) + c * sampleCov S (leverage P) y =
      mean S y - dot (xMean P S) (populationSlope P y) -
        dot (xMean P S) (armN P S y - populationSlope P y) + c * sampleCov S (leverage P) y) ∧
  (∀ {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hmn : m < n) (hx : xMean P univ = 0) (c : ℝ),
    expectation m (fun S => mean S P.yT - dot (xMean P S) (armN P S P.yT) +
      c*sampleCov S (leverage P) P.yT) =
        popMean P.yT + (-((n : ℝ)-m)/((m : ℝ)*(n-1)) + NTTT n m +
          c*((m : ℝ)-1)*n/((m : ℝ)*(n-1))) * leverageCov P P.yT ∧
    (-((n : ℝ)-m)/((m : ℝ)*(n-1)) + NTTT n m +
       c*((m : ℝ)-1)*n/((m : ℝ)*(n-1)) = 0 ↔
      c = ((n : ℝ)-m)/((n-2 : ℝ)*m)) ∧
    expectation m (fun S => armDebiased P S P.yT) = popMean P.yT ∧
    expectation m (fun S => mean S P.yT-dot (xMean P S) (armN P S P.yT) +
      (m : ℝ)/((n-2 : ℝ)*(n-m))*sampleCov S (leverage P) P.yT) =
      popMean P.yT + ((m : ℝ)^2-((n : ℝ)-m)^2)/((n-2 : ℝ)*m*(n-m)) *
        (((m : ℝ)-1)*n/((m : ℝ)*(n-1))) * leverageCov P P.yT) ∧
  (∀ {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n)
    (hm : 0 < m) (hmn : m < n) (hc : 2 ≤ n-m) (hx : xMean P univ = 0) (c : ℝ),
    expectation m (fun S => mean (control S) P.yC -
      dot (xMean P (control S)) (armN P (control S) P.yC) +
      c*sampleCov (control S) (leverage P) P.yC) =
        popMean P.yC + (-(m : ℝ)/(((n : ℝ)-m)*(n-1)) + NCCC n m +
          c*((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1))) * leverageCov P P.yC ∧
    (-(m : ℝ)/(((n : ℝ)-m)*(n-1)) + NCCC n m +
       c*((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1)) = 0 ↔
      c = (m : ℝ)/((n-2 : ℝ)*(n-m))) ∧
    expectation m (fun S => armDebiased P (control S) P.yC) = popMean P.yC) ∧
  (∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P) (t : Arm),
    stochasticO m (fun n S =>
      let A := armSet t S
      let y := if t = .treated then (P n).yT else (P n).yC
      armDebiased (P n) A y - (mean A y - dot (xMean (P n) A) (populationSlope (P n) y)))
      (fun n => Real.sqrt (kappa (P n)/n)))

/-- The packaged content of P005-T12; scope is recorded in its Challenge docstring. -/
def T12Statement : Prop :=
  popMean weightX = 0 ∧ popMean (fun i => weightX i^2) = 1 ∧
    (∀ S ∈ design 6 2, 0 < sampleCov S weightX weightX ∧
      0 < sampleCov (control S) weightX weightX) ∧
    popMean (fun i => weightY i^2) ≤ 121 ∧
    (1/4 : ℝ) < pT 6 2 ∧ pT 6 2 < (3/4 : ℝ) ∧
    expectation 2 (fun S => mean (control S) weightX * scalarSlope (control S) weightX weightY) =
      (31085815448171/17062566567774 : ℝ) ∧
    expectation 2 (fun S => (1/8 : ℝ)*sampleCov (control S) (fun i => weightX i^2) weightY +
      mean (control S) weightX * ((sampleCov S weightX weightX)⁻¹ - 1) * sampleCov (control S) weightX weightY) =
      (12010469/846720 : ℝ) ∧
    expectation 2 (fun S => (1/8 : ℝ)*sampleCov (control S) (fun i => weightX i^2) weightY +
      mean (control S) weightX * ((sampleCov (control S) weightX weightX)⁻¹ - 1) *
        sampleCov (control S) weightX weightY) = (31085815448171/17062566567774 : ℝ) ∧
    expectation 2 (fun S => mean (control S) weightX * scalarSlope (control S) weightX weightY) ≠
      expectation 2 (fun S => (1/8 : ℝ)*sampleCov (control S) (fun i => weightX i^2) weightY +
        mean (control S) weightX * ((sampleCov S weightX weightX)⁻¹ - 1) * sampleCov (control S) weightX weightY)

/-- The packaged content of P005-T13; scope is recorded in its Challenge docstring. -/
def T13Statement : Prop :=
  ∀ {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : ∀ S ∈ design n m, (armL P (control S)).det ≠ 0),
    expectation m (fun S =>
      (m : ℝ)/((n-2 : ℝ)*(n-m)) * sampleCov (control S) (leverage P) P.yC +
        dot (xMean P (control S)) (armNu2 P (control S) P.yC)) =
    expectation m (fun S => dot (xMean P (control S))
      (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) ∧
    expectation m (fun S => dot (xMean P (control S))
      (armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC)) =
    expectation m (fun S => dot (xMean P (control S)) (armBetaHat P (control S) P.yC)) ∧
    (∀ S ∈ design n m, dot (xMean P (control S)) (armNu2 P (control S) P.yC) =
      dot (xMean P (control S)) (((armL P (control S))⁻¹-1) *ᵥ armN P (control S) P.yC)) ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu1 P (control S) P.yC)) =
      (m : ℝ)/((n-1 : ℝ)*(n-m))*leverageCov P P.yC ∧
    expectation m (fun S => dot (xMean P (control S)) (armNu3 P (control S) P.yC)) =
      -NCCC n m*leverageCov P P.yC ∧
    expectation m (fun S => sampleCov (control S) (leverage P) P.yC) =
      ((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1))*leverageCov P P.yC ∧
    (m : ℝ)/((n-1 : ℝ)*(n-m))-NCCC n m =
      (m : ℝ)*n*((n : ℝ)-m-1)/((n-1 : ℝ)*(n-2)*(n-m)^2) ∧
    (m : ℝ)*n*((n : ℝ)-m-1)/((n-1 : ℝ)*(n-2)*(n-m)^2) =
      (m : ℝ)/((n-2 : ℝ)*(n-m))*(((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1)))

/-- The packaged content of P005-T14; scope is recorded in its Challenge docstring. -/
def T14Statement : Prop :=
  (∀ {n d : ℕ} (P : Population n d) (m : ℕ)
    (S : Finset (Fin n)) (v : Fin d → ℝ) (hn : 3 ≤ n) (hm : 0 < m)
    (hmn : m < n) (hS : S ∈ design n m) (hinv : (Lhat P m S).det ≠ 0),
    debiasedATE P m S =
      mean S P.yT - mean (control S) P.yC -
        dot (xMean P S - xMean P (control S)) (Nhat P m S) +
        sampleCov S (leverage P) P.yT / (n - 2 : ℝ) -
        sampleCov (control S) (leverage P) P.yC / (n - 2 : ℝ) ∧
    debiasedATE P m S =
      mean S (fun i => P.yT i - dot (P.x i) v) -
        mean (control S) (fun i => P.yC i - dot (P.x i) v) -
        dot (xMean P S - xMean P (control S)) (Nhat P m S - v) +
        sampleCov S (leverage P) P.yT / (n - 2 : ℝ) -
        sampleCov (control S) (leverage P) P.yC / (n - 2 : ℝ) ∧
    debiasedATE P m S =
      (mean S P.yT - mean (control S) P.yC -
        dot (xMean P S - xMean P (control S)) ((Lhat P m S)⁻¹ *ᵥ Nhat P m S)) -
      dot (xMean P (control S) - xMean P S) (((Lhat P m S)⁻¹ - 1) *ᵥ Nhat P m S) +
      sampleCov S (leverage P) P.yT / (n - 2 : ℝ) -
      sampleCov (control S) (leverage P) P.yC / (n - 2 : ℝ) ∧
    -dot (xMean P S - xMean P (control S)) ((Lhat P m S)⁻¹ *ᵥ Nhat P m S) -
      dot (xMean P (control S) - xMean P S) (((Lhat P m S)⁻¹ - 1) *ᵥ Nhat P m S) =
      -dot (xMean P S - xMean P (control S)) (Nhat P m S) ∧
    mean S P.yT - mean (control S) P.yC -
        dot (xMean P S - xMean P (control S)) (Nhat P m S) =
      mean S (fun i => P.yT i - dot (P.x i) v) -
        mean (control S) (fun i => P.yC i - dot (P.x i) v) -
        dot (xMean P S - xMean P (control S)) (Nhat P m S - v)) ∧
  (∀ {n d m : ℕ} (P : Population n d)
    (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hx : xMean P univ = 0)
    (S : Finset (Fin n)) (hS : S ∈ design n m),
    xMean P (control S)-xMean P S = (1/pT n m) • xMean P (control S) ∧
    xMean P (control S)-xMean P S = (-(1/pC n m)) • xMean P S) ∧
  (∀ {n d m : ℕ} (P : Population n d) (hn : 3 ≤ n) (hm : 0 < m)
    (hmn : m < n) (hP : standardized P) (hinv : noninteractedRegular P m),
    expectation m (adjustedATE P m) - ate P =
      expectation m (fun S => dot (xMean P (control S) - xMean P S)
        (nu1 P m S + nu2 P m S + nu3 P m S))) ∧
  (∀ (n d m : ℕ) (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n),
    ∃ F : Finset (Fin n) → (Fin n → Fin d → ℝ) → (Fin n → ℝ) → ℝ,
      ∀ P : Population n d, standardized P → ∀ S ∈ design n m,
      (Lhat P m S).det ≠ 0 →
      dot (xMean P (control S)-xMean P S) (nu2 P m S) = F S P.x (observedOutcome P S))

end
end SAP.P005a
