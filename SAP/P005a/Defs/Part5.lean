import SAP.P005a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005a

noncomputable section
open Finset Filter
open scoped BigOperators Matrix Topology

/-- The packaged content of P005-T1; scope is recorded in its Challenge docstring. -/
def T1Statement : Prop :=
  4 ≤ (6 : ℕ) ∧ 1 ≤ (4 : ℕ) ∧ (4 : ℕ) < 6 ∧
    (design 6 4).card = 15 ∧
    popMean witnessA = -(3/2 : ℝ) ∧ popMean witnessB = (5/6 : ℝ) ∧
    popCov witnessA witnessB = -(23/12 : ℝ) ∧
    expectation 4 (fun S => sampleCov S witnessA witnessB) = -(69/40 : ℝ) ∧
    variance 4 (fun S => sampleCov S witnessA witnessB) = (16607/4800 : ℝ) ∧
    covarianceBound 4 witnessA witnessB = (3829/1440 : ℝ) ∧
    covarianceBound 4 witnessA witnessB < variance 4 (fun S => sampleCov S witnessA witnessB)

/-- The packaged content of P005-T2; scope is recorded in its Challenge docstring. -/
def T2Statement : Prop :=
  ∀ {n m : ℕ} (hn : 4 ≤ n) (hm : 0 < m) (hmn : m < n)
    (t : Arm) (a b : Fin n → ℝ),
    expectation m (fun S => sampleCov (armSet t S) a b) =
      (((armSize n m t : ℕ) : ℝ) - 1) * n /
        ((armSize n m t : ℝ) * (n - 1)) * popCov a b ∧
    variance m (fun S => sampleCov (armSet t S) a b) ≤
      covarianceBound (armSize n m t) (centered a) (centered b)

/-- The packaged content of P005-T3; scope is recorded in its Challenge docstring. -/
def T3Statement : Prop :=
  standardized leveragePopulation ∧ interactedRegular leveragePopulation 8 ∧
    noninteractedRegular leveragePopulation 8 ∧
    popMean (fun i => leverageY i^2) ≤ 1 ∧
    popMean (fun i => leveragePopulation.yC i^2) = 0 ∧
    (1/4 : ℝ) < pT 16 8 ∧ pT 16 8 < (3/4 : ℝ) ∧
    (design 16 8).card = 12870 ∧
    kappa leveragePopulation = (32/71 : ℝ) ∧
    (∀ i, leverage leveragePopulation i * leverageY i = (8/71 : ℝ)) ∧
    variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) =
      (1678565511/8259174400 : ℝ) ∧
    covarianceBound 8 (leverage leveragePopulation) leverageY = (117645319/619438080 : ℝ) ∧
    covarianceBound 8 (leverage leveragePopulation) leverageY <
      variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) ∧
    (2*((16 : ℝ)-8)/(8*(16-1))*popMean (fun i => (leverage leveragePopulation i)^2*leverageY i^2) +
      2*((16 : ℝ)-8)*16/((8 : ℝ)^3*(16-1))*popMean (fun i => leverageY i^2)*
        popMean (fun i => (leverage leveragePopulation i)^2)) = (334349/1744896 : ℝ) ∧
    (334349/1744896 : ℝ) < variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY)

/-- The packaged content of P005-T4; scope is recorded in its Challenge docstring. -/
def T4Statement : Prop :=
  (∀ {n d m : ℕ} (P : Population n d)
    (hn : 4 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (t : Arm) (K : ℝ)
    (hK : popMean (fun i => (if t = .treated then P.yT i else P.yC i)^2) ≤ K),
    let y := if t = .treated then P.yT else P.yC
    let u := fun i => leverage P i - (d : ℝ)
    let v := centered y
    popMean (leverage P) = d ∧
    (∀ i, 0 ≤ leverage P i ∧ leverage P i ≤ n * kappa P ∧ |u i| ≤ n * kappa P) ∧
    (d : ℝ) ≤ n * kappa P ∧
    popMean (fun i => u i^2) = popMean (fun i => leverage P i^2) - (d : ℝ)^2 ∧
    popMean (fun i => u i^2) ≤ n * kappa P * d ∧
    popMean (fun i => v i^2) = popMean (fun i => y i^2) - popMean y^2 ∧
    popMean (fun i => v i^2) ≤ K ∧
    popMean (fun i => (u i * v i - popMean (fun j => u j*v j))^2) ≤
      popMean (fun i => u i^2 * v i^2) ∧
    popMean (fun i => u i^2 * v i^2) ≤ (n : ℝ)^2 * kappa P^2 * K ∧
    variance m (fun S => sampleCov (armSet t S) (leverage P) y) ≤
      covarianceBound (armSize n m t) u v ∧
    covarianceBound (armSize n m t) u v ≤
      2 * ((n : ℝ)-armSize n m t) / ((armSize n m t : ℝ)*(n-1)) * (n : ℝ)^2 * kappa P^2 * K +
      2 * ((n : ℝ)-armSize n m t) * n / ((armSize n m t : ℝ)^3*(n-1)) * n * kappa P * d * K) ∧
  (∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P) (t : Arm),
    Asymptotics.IsBigO atTop
      (fun n => variance (m n) (fun S => sampleCov (armSet t S) (leverage (P n))
        (if t = .treated then (P n).yT else (P n).yC)))
      (fun n => (n : ℝ)*kappa (P n)^2 + kappa (P n)*(d n)/n) ∧
    Asymptotics.IsBigO atTop
      (fun n => variance (m n) (fun S => sampleCov (armSet t S) (leverage (P n))
        (if t = .treated then (P n).yT else (P n).yC) / n))
      (fun n => kappa (P n)^2/n + kappa (P n)*(d n)/(n : ℝ)^3))

end
end SAP.P005a
