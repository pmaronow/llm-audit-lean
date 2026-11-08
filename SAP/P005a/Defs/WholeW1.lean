import Mathlib
import SAP.P005a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a

noncomputable section
open Finset Filter
open scoped BigOperators Matrix Topology

/-- The two allocation coefficients in the variance bound; subtraction is in ℝ. -/
def W1A (n s : ℕ) : ℝ := 2 * ((n : ℝ) - s) / ((s : ℝ) * (n - 1))

def W1B (n s : ℕ) : ℝ := 2 * ((n : ℝ) - s) * n / ((s : ℝ)^3 * (n - 1))

/-- The product of the two unnormalized sample sums. -/
def W1Z {n : ℕ} (u v : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, u i) * (∑ i ∈ S, v i)

def W1Alpha (n s : ℕ) : ℝ := (s : ℝ) * (n - s : ℝ) / ((n : ℝ) * (n - 1))

def W1Ell (n s : ℕ) : ℝ :=
  (s : ℝ) * (s - 1 : ℝ) * (n - s : ℝ) * (n - s - 1 : ℝ) /
    ((n : ℝ) * (n - 1) * (n - 2) * (n - 3))

/-- Exact moments and bound for the product of centered sums, for the selected arm. -/
def W1ProductFacts {n : ℕ} (m : ℕ) (t : Arm) (u v : Fin n → ℝ) : Prop :=
  let s := armSize n m t
  let A := ∑ i, u i^2
  let B := ∑ i, v i^2
  let G := ∑ i, u i * v i
  let H := ∑ i, u i^2 * v i^2
  let α := W1Alpha n s
  let ℓ := W1Ell n s
  expectation m (fun S => W1Z u v (armSet t S)) = α * G ∧
  variance m (fun S => W1Z u v (armSet t S)) =
    (α - 6*ℓ)*H + ℓ*A*B + (2*ℓ - α^2)*G^2 ∧
  variance m (fun S => W1Z u v (armSet t S)) ≤ α*A*B ∧
  variance m (fun S => mean (armSet t S) u * mean (armSet t S) v) =
    variance m (fun S => W1Z u v (armSet t S)) / (s : ℝ)^4 ∧
  variance m (fun S => mean (armSet t S) u * mean (armSet t S) v) ≤
    ((n : ℝ)-s)*n / ((s : ℝ)^3*(n-1)) *
      popMean (fun i => u i^2) * popMean (fun i => v i^2)

/-- P005-T1; Appendix A.2, Lemma A.1, pp. 1510–1511 (PDF pp. 9–10).
The six-unit counterexample has all the stated means, coefficients, moments,
expectation, variance, bound and positive gap. Covariance and its variance are
unchanged by constant shifts; the printed bound changes under centering, and
its centered value bounds the variance. -/
def T1WholeStatement : Prop :=
  T1Statement ∧
  popMean (fun i => witnessA i * witnessB i) = -(19/6 : ℝ) ∧
  expectation 4 (fun S => sampleCov S witnessA witnessB) =
    (((4 : ℝ)-1)*6/(4*(6-1))) * popCov witnessA witnessB ∧
  W1A 6 4 = (1/5 : ℝ) ∧ W1B 6 4 = (3/40 : ℝ) ∧
  popMean (fun i => (witnessA i*witnessB i -
    popMean (fun j => witnessA j*witnessB j))^2) = (113/36 : ℝ) ∧
  popMean (fun i => witnessA i^2) = (13/2 : ℝ) ∧
  popMean (fun i => witnessB i^2) = (25/6 : ℝ) ∧
  W1A 6 4 * popMean (fun i => (witnessA i*witnessB i -
    popMean (fun j => witnessA j*witnessB j))^2) = (113/180 : ℝ) ∧
  W1B 6 4 * popMean (fun i => witnessA i^2) *
    popMean (fun i => witnessB i^2) = (65/32 : ℝ) ∧
  covarianceBound 4 witnessA witnessB = (113/180 : ℝ) + 65/32 ∧
  variance 4 (fun S => sampleCov S witnessA witnessB) -
    covarianceBound 4 witnessA witnessB = (11531/14400 : ℝ) ∧
  (0 : ℝ) < 11531/14400 ∧
  (∀ (S : Finset (Fin 6)), S.Nonempty → ∀ c e : ℝ,
    sampleCov S (fun i => witnessA i+c) (fun i => witnessB i+e) =
      sampleCov S witnessA witnessB) ∧
  (∀ c e : ℝ, variance 4 (fun S =>
      sampleCov S (fun i => witnessA i+c) (fun i => witnessB i+e)) =
    variance 4 (fun S => sampleCov S witnessA witnessB)) ∧
  (∀ S ∈ design 6 4, sampleCov S (centered witnessA) (centered witnessB) =
    sampleCov S witnessA witnessB) ∧
  covarianceBound 4 (centered witnessA) (centered witnessB) = (835/128 : ℝ) ∧
  variance 4 (fun S => sampleCov S witnessA witnessB) ≤
    covarianceBound 4 (centered witnessA) (centered witnessB) ∧
  covarianceBound 4 (centered witnessA) (centered witnessB) ≠
    covarianceBound 4 witnessA witnessB

/-- P005-T2; Appendix A.2, Lemma A.1, p. 1511 (PDF p. 10).
For either nonempty arm, the printed expectation and the variance bound with
both vectors centered hold. Covariance is location invariant, the centered
sample-product mean has the simple-random-sampling variance, the product of
centered sums has the stated exact expectation and variance and their bound,
and the generic variance-difference inequality gives the repaired bound.
The printed bound is recovered when both population means are zero. -/
def T2WholeStatement : Prop :=
  T2Statement ∧
  (∀ {n : ℕ} (S : Finset (Fin n)), S.Nonempty → ∀ (a b : Fin n → ℝ) (c e : ℝ),
    sampleCov S (fun i => a i-c) (fun i => b i-e) = sampleCov S a b) ∧
  (∀ {n m : ℕ}, 4 ≤ n → 0 < m → m < n → ∀ (t : Arm) (a b : Fin n → ℝ),
    let u := centered a
    let v := centered b
    (∑ i, u i) = 0 ∧ (∑ i, v i) = 0 ∧
    popMean (fun i => u i*v i) = popCov a b ∧
    (∀ S ∈ design n m, sampleCov (armSet t S) a b = sampleCov (armSet t S) u v) ∧
    variance m (fun S => mean (armSet t S) (fun i => u i*v i)) =
      ((n : ℝ)-armSize n m t) / ((armSize n m t : ℝ)*(n-1)) *
        popMean (fun i => (u i*v i-popMean (fun j => u j*v j))^2) ∧
    W1ProductFacts m t u v ∧
    (popMean a = 0 → popMean b = 0 →
      variance m (fun S => sampleCov (armSet t S) a b) ≤ covarianceBound (armSize n m t) a b)) ∧
  (∀ {n m : ℕ}, 4 ≤ n → 0 < m → m < n → ∀ U V : Finset (Fin n) → ℝ,
    variance m (fun S => U S-V S) ≤ 2*variance m U + 2*variance m V)

/-- Number of the two high-leverage labels in the treated arm of the witness. -/
def W1HighCount (S : Finset (Fin 16)) : ℕ := (S ∩ {0, 1}).card

def W1ThirdBound : ℝ :=
  W1A 16 8 * (16 : ℝ)^2 * kappa leveragePopulation^2 * popMean (fun i => leverageY i^2) +
  W1B 16 8 * popMean (fun i => leverageY i^2) * popMean (leverage leveragePopulation) *
    16 * kappa leveragePopulation

/-- P005-T3; Appendix B.2, item 2, p. 1517 (PDF p. 16).
The standardized regular sixteen-unit counterexample satisfies all stated
moment and allocation conditions. Its leverage vector, mean and constant
leverage-product, three-category probabilities and covariance values, exact
variance, both failed bounds and positive gaps, and the valid third-expression
and centered-bound comparisons have the stated numerical values. -/
def T3WholeStatement : Prop :=
  T3Statement ∧
  popMean (fun i => leverageY i^2) = (28673/32768 : ℝ) ∧ pT 16 8 = (1/2 : ℝ) ∧
  (∀ i : Fin 16, (univ.filter (fun j => leveragePopulation.x j 0 = leveragePopulation.x i 0)).card ≤ 7) ∧
  (∀ S ∈ design 16 8,
    0 < sampleCov S (fun i => leveragePopulation.x i 0) (fun i => leveragePopulation.x i 0) ∧
    0 < sampleCov (control S) (fun i => leveragePopulation.x i 0) (fun i => leveragePopulation.x i 0)) ∧
  leverage leveragePopulation = (fun i => if i.val < 2 then (512/71 : ℝ) else 8/71) ∧
  popMean (leverage leveragePopulation) = 1 ∧
  popMean (fun i => (leverage leveragePopulation i*leverageY i -
    popMean (fun j => leverage leveragePopulation j*leverageY j))^2) = 0 ∧
  probability 8 (fun S => W1HighCount S = 0) = (7/30 : ℝ) ∧
  probability 8 (fun S => W1HighCount S = 1) = (8/15 : ℝ) ∧
  probability 8 (fun S => W1HighCount S = 2) = (7/30 : ℝ) ∧
  (∀ S ∈ design 16 8, W1HighCount S ≤ 2 ∧
    sampleCov S (leverage leveragePopulation) leverageY =
      if W1HighCount S = 0 then 0 else if W1HighCount S = 1 then -(27783/36352 : ℝ)
      else -(11907/9088 : ℝ)) ∧
  variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) -
    covarianceBound 8 (leverage leveragePopulation) leverageY = (329883773/24777523200 : ℝ) ∧
  (0 : ℝ) < 329883773/24777523200 ∧
  variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) -
    (W1A 16 8 * popMean (fun i => leverage leveragePopulation i^2*leverageY i^2) +
      W1B 16 8 * popMean (fun i => leverageY i^2) *
        popMean (fun i => leverage leveragePopulation i^2)) = (287940733/24777523200 : ℝ) ∧
  (0 : ℝ) < 287940733/24777523200 ∧
  W1ThirdBound = (60758087/9678720 : ℝ) ∧
  variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) ≤ W1ThirdBound ∧
  covarianceBound 8 (fun i => leverage leveragePopulation i-1) (centered leverageY) =
    (5550293259/13214679040 : ℝ) ∧
  variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) ≤
    covarianceBound 8 (fun i => leverage leveragePopulation i-1) (centered leverageY)

/-- The deterministic final right-hand side of the repaired leverage chain. -/
def W1LeverageRHS {n d : ℕ} (P : Population n d) (s : ℕ) (K : ℝ) : ℝ :=
  W1A n s * (n : ℝ)^2 * kappa P^2 * K + W1B n s * n * kappa P * d * K

/-- Assumptions 1–3 on the admissible indices n ≥ 2, without positivity of d.
The values at n=0,1 cannot describe a two-nonempty-arm experiment and are ignored.
One common bound and two common allocation constants apply at every admissible
index; only standardization is eventual. -/
def W1SequenceAssumptions (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n))
    (K lo hi : ℝ) : Prop :=
  0 ≤ K ∧ 0 < lo ∧ lo < hi ∧ hi < 1 ∧
  (∀ n, 2 ≤ n → d n ≤ n ∧ 0 < m n ∧ m n < n ∧
    popMean (fun i => (P n).yT i^2) ≤ K ∧ popMean (fun i => (P n).yC i^2) ≤ K ∧
    (∀ k, popMean (fun i => (P n).x i k^2) ≤ K) ∧
    lo < pT n (m n) ∧ pT n (m n) < hi) ∧
  (∀ᶠ n in atTop, standardized (P n))

/-- P005-T4; Appendix B.2, item 2, p. 1517 (PDF p. 16).
For either arm the centered leverage and outcome moments give every inequality
in the repaired finite variance chain, including the intermediate raw leverage
second moment. The two allocation coefficients obey the stated bounds.
Under Assumptions 1–3 the numerical right-hand side and the actual variance
are O(nκ²+κd/n), and the variance after division by n is
O(κ²/n+κd/n³). Dimension zero is allowed, including along a sequence. -/
def T4WholeStatement : Prop :=
  (∀ {n d m : ℕ} (P : Population n d), 4 ≤ n → 0 < m → m < n → standardized P →
    ∀ (t : Arm) (K : ℝ),
    popMean (fun i => (if t = .treated then P.yT i else P.yC i)^2) ≤ K →
    let y := if t = .treated then P.yT else P.yC
    let u := fun i => leverage P i-(d : ℝ)
    let v := centered y
    popMean (leverage P) = d ∧
    (∀ i, 0 ≤ leverage P i ∧ leverage P i ≤ n*kappa P ∧ |u i| ≤ n*kappa P) ∧
    (d : ℝ) ≤ n*kappa P ∧
    popMean (fun i => u i^2) = popMean (fun i => leverage P i^2)-(d : ℝ)^2 ∧
    popMean (fun i => u i^2) ≤ popMean (fun i => leverage P i^2) ∧
    popMean (fun i => leverage P i^2) ≤ n*kappa P*d ∧
    popMean (fun i => v i^2) = popMean (fun i => y i^2)-popMean y^2 ∧
    popMean (fun i => v i^2) ≤ K ∧
    popMean (fun i => (u i*v i-popMean (fun j => u j*v j))^2) ≤ popMean (fun i => u i^2*v i^2) ∧
    popMean (fun i => u i^2*v i^2) ≤ (n : ℝ)^2*kappa P^2*K ∧
    variance m (fun S => sampleCov (armSet t S) (leverage P) y) ≤ covarianceBound (armSize n m t) u v ∧
    covarianceBound (armSize n m t) u v ≤ W1LeverageRHS P (armSize n m t) K) ∧
  (∀ {n m : ℕ}, 4 ≤ n → 0 < m → m < n → ∀ (t : Arm) (p : ℝ),
    0 < p → p < (armSize n m t : ℝ)/n →
    W1A n (armSize n m t) ≤ 2/(p*(n-1)) ∧
    W1B n (armSize n m t) ≤ 2/(p^3*n*(n-1))) ∧
  (∀ (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)) (K lo hi : ℝ),
    W1SequenceAssumptions d m P K lo hi → ∀ t : Arm,
    let V := fun n => variance (m n) (fun S => sampleCov (armSet t S) (leverage (P n))
      (if t = .treated then (P n).yT else (P n).yC))
    let R := fun n => W1LeverageRHS (P n) (armSize n (m n) t) K
    let r := fun (n : ℕ) => (n : ℝ)*kappa (P n)^2+kappa (P n)*(d n)/n
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, 0 ≤ R n ∧ R n ≤ C*r n ∧ 0 ≤ V n ∧ V n ≤ R n) ∧
    Asymptotics.IsBigO atTop R r ∧ Asymptotics.IsBigO atTop V r ∧
    (∀ n, 2 ≤ n → variance (m n) (fun S => sampleCov (armSet t S) (leverage (P n))
      (if t = .treated then (P n).yT else (P n).yC)/n) = V n/(n : ℝ)^2) ∧
    Asymptotics.IsBigO atTop
      (fun n => variance (m n) (fun S => sampleCov (armSet t S) (leverage (P n))
        (if t = .treated then (P n).yT else (P n).yC)/n))
      (fun n => kappa (P n)^2/n+kappa (P n)*(d n)/(n : ℝ)^3))

/-- A standardized four-unit population witnessing failure of the printed control sum. -/
def W1WrongSumPopulation : Population 4 1 where
  x := fun i _ => (![-1, -1, 1, 1] : Fin 4 → ℝ) i
  yT := fun _ => 0
  yC := fun _ => 1

/-- Full concrete witness, with ordinary inverses defined on every assignment. -/
def W1WrongSumFacts : Prop :=
  standardized W1WrongSumPopulation ∧ noninteractedRegular W1WrongSumPopulation 1 ∧
  N W1WrongSumPopulation 1 = 0 ∧ ({0} : Finset (Fin 4)) ∈ design 4 1 ∧
  popMean (fun i => W1WrongSumPopulation.yT i^2) ≤ 1 ∧
  popMean (fun i => W1WrongSumPopulation.yC i^2) ≤ 1 ∧
  (∀ k, popMean (fun i => W1WrongSumPopulation.x i k^2) ≤ 1) ∧
  (1/5 : ℝ) < pT 4 1 ∧ pT 4 1 < (4/5 : ℝ) ∧
  (∑ i ∈ ({0} : Finset (Fin 4)), (W1WrongSumPopulation.yC i -
    dot (W1WrongSumPopulation.x i) (N W1WrongSumPopulation 1))) / (4-1 : ℝ) = (1/3 : ℝ) ∧
  mean (control ({0} : Finset (Fin 4))) W1WrongSumPopulation.yC -
    dot (xMean W1WrongSumPopulation (control {0})) (N W1WrongSumPopulation 1) = 1

/-- P005-T14; Appendix B.2, pp. 1515–1516 (PDF pp. 14–15), and Remark 2,
p. 1507 (PDF p. 6). The corrected debiased expansion, inverse cancellation,
arbitrary-vector residual identities, centered arm-mean identities and actual
bias decomposition hold. A standardized everywhere regular four-unit example
shows that the printed treated-set control sum can differ from the control
residual mean. One function of the assignment, covariates and observed outcomes,
chosen before the potential outcomes, gives the inverse bias component. -/
def T14WholeStatement : Prop :=
  T14Statement ∧ W1WrongSumFacts ∧
  (∑ i ∈ ({0} : Finset (Fin 4)), (W1WrongSumPopulation.yC i -
    dot (W1WrongSumPopulation.x i) (N W1WrongSumPopulation 1))) / (4-1 : ℝ) ≠
    mean (control ({0} : Finset (Fin 4))) W1WrongSumPopulation.yC -
      dot (xMean W1WrongSumPopulation (control {0})) (N W1WrongSumPopulation 1) ∧
  (∀ (n d m : ℕ), 3 ≤ n → 0 < m → m < n →
    ∃ F : Finset (Fin n) → (Fin n → Fin d → ℝ) → (Fin n → ℝ) → ℝ,
      ∀ (P : Population n d) (S : Finset (Fin n)), S ∈ design n m → (Lhat P m S).det ≠ 0 →
        dot (xMean P (control S)-xMean P S) (nu2 P m S) = F S P.x (observedOutcome P S))

end
end SAP.P005a
