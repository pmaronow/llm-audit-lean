import Mathlib
import SAP.P002a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

/-- The fixed balanced-sign response; the first half have sign -1. -/
def W2sign (m : ℕ) (i : Fin (2*m)) : ℝ := (signModel m).y i false

/-- Number of positive responses in the reassigned treatment group. -/
def W2K (m : ℕ) (T : Finset (Fin (2*m))) : ℕ :=
  (T.filter fun i => m ≤ i.val).card

/-- Reassigned treatment-arm mean, expressed using its positive-response count. -/
def W2q (m : ℕ) (T : Finset (Fin (2*m))) : ℝ :=
  (2*(W2K m T : ℝ)-(m : ℝ))/(m : ℝ)

/-- Actual standard-deviation/variance ratio, not a substituted variance formula. -/
def W2U (m : ℕ) (T : Finset (Fin (2*m))) : ℝ :=
  Real.sqrt (rawSigma2 (signModel m) (W2sign m) T) /
    designVariance (signModel m) (rawTau (signModel m) (W2sign m))

/-- Actual ratio of variances in the balanced-sign family. -/
def W2R (m : ℕ) (T : Finset (Fin (2*m))) : ℝ :=
  rawSigma2 (signModel m) (W2sign m) T /
    designVariance (signModel m) (rawTau (signModel m) (W2sign m))

def W2T14Finite : Prop :=
  ∀ m, 2 ≤ m →
    (∀ O ∈ assignments (signModel m), observedW (signModel m) 0 O = W2sign m) ∧
    expectation (signModel m) (fun T => W2q m T ^ 2) = 1/((2*m : ℕ) - (1 : ℝ)) ∧
    0 < designVariance (signModel m) (rawTau (signModel m) (W2sign m)) ∧
    (∀ T ∈ assignments (signModel m),
      armMean (W2sign m) T true = W2q m T ∧
      rawSigma2 (signModel m) (W2sign m) T = (1-W2q m T^2)/(4*(2*m : ℕ)) ∧
      W2U m T = 2*((2*m : ℕ)-(1 : ℝ))/Real.sqrt (2*m : ℕ)*Real.sqrt (1-W2q m T^2) ∧
      W2R m T = ((2*m : ℕ)-(1 : ℝ))*(1-W2q m T^2)/(2*m : ℕ) ∧
      (W2q m T^2 = 1 → W2U m T = 0) ∧
      (W2q m T^2 ≠ 1 →
        8*((2*m : ℕ)-(2 : ℝ))/(2*m : ℕ)^2 ≤ 1-W2q m T^2 ∧ 3 ≤ W2U m T) ∧
      0 ≤ W2R m T ∧ W2R m T ≤ 1) ∧
    expectation (signModel m) (fun T => 1-W2R m T) = 2/(2*m : ℕ)

def W2T14Hypergeom : Prop :=
  ∀ m, 2 ≤ m → ∀ l : ℕ,
    probability (signModel m) (fun T => W2K m T = l) =
      if l ≤ m then
        ((Nat.choose m l * Nat.choose m (m-l) : ℕ) : ℝ)/(Nat.choose (2*m) m : ℝ)
      else 0

def W2T14Limits : Prop :=
  ∀ (ms : ℕ → ℕ), StrictMono ms → (∀ j, 2 ≤ ms j) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun j => probability (signModel (ms j))
      (fun T => |W2U (ms j) T/Real.sqrt (2*ms j : ℕ)-2| ≥ ε)) atTop (nhds 0)) ∧
    (∀ M : ℝ, Tendsto (fun j => probability (signModel (ms j))
      (fun T => M < W2U (ms j) T)) atTop (nhds 1)) ∧
    (∀ κ : ℝ, 0 < κ → Tendsto (fun j => probability (signModel (ms j))
      (fun T => |W2R (ms j) T-1| ≥ κ)) atTop (nhds 0))

/-- P002-T14; Supplement p. 30 (Supplement PDF p. 10).
The printed claim is false: the admissible balanced-sign family has the stated
hypergeometric law, moments, exact variance and ratio formulas, and zero-or-at-least-three
support. The printed error probability is one for every original assignment; its ratio
divided by the square root of sample size tends to two in probability and diverges.
The variance ratio lies in [0,1], has mean deficit 2/n and has the stated vanishing tails. -/
def T14WholeStatement : Prop :=
  T14Statement ∧ W2T14Hypergeom ∧ W2T14Finite ∧ W2T14Limits

/-- Explicit evaluations omitted from the twelve-unit counterexample. -/
def W2T1Details : Prop :=
  let P := negativeDeltaModel 1
  (∀ i, P.pop.d i false = false ∧ P.pop.d i true = true) ∧
  (∀ a, w P.pop a 0 = fun i => P.pop.y i false) ∧
  (∀ a, mean (w P.pop a 0) = 0 ∧ fourthNorm (w P.pop a 0) = 1) ∧
  groupCov (compliers P.pop) (w P.pop true 0) (w P.pop false 0) = 12/11 ∧
  (∀ a, groupVar (compliers P.pop) (w P.pop a 0) = 12/11) ∧
  (1 : ℝ) ≤ 2*Real.sqrt (12/11) ∧
  (∑ i, P.x i 0) = 0 ∧ (∑ i, P.pop.y i false) = 0 ∧
  (∑ i, P.x i 0*P.pop.y i false) = 0 ∧ (∑ i, P.x i 0^2) = 12 ∧
  mean (fun i => P.x i 0^4) = 1 ∧ leastRayleigh P.x = 1 ∧
  (∀ a, residual P a 0 = fun i => P.pop.y i false) ∧
  popCov (residual P true 0) (residual P false 0) = 12/11 ∧
  (∀ a, popVar (residual P a 0) = 12/11 ∧ fourthNorm (residual P a 0) = 1) ∧
  Sdiff2 P.pop 0 = 0 ∧ popVar (fun i => residual P true 0 i-residual P false 0 i) = 0 ∧
  (1-(-1/2 : ℝ))*(controlSize P.pop/(12*2)*S2 P.pop 0 true +
    2/(12*controlSize P.pop)*S2 P.pop 0 false) = 65/4752 ∧
  (1-(-1/2 : ℝ))*(controlSize P.pop/(12*2)*popVar (residual P true 0) +
    2/(12*controlSize P.pop)*popVar (residual P false 0)) = 39/55 ∧
  (∀ S ∈ assignments P.pop,
    probability P.pop (fun T => T = S) = 1/66 ∧
    oracleTau P 0 S = (1/2)*∑ i ∈ S, P.pop.y i false -
      (1/10)*∑ i ∈ Sᶜ, P.pop.y i false)

/-- P002-T1; Supplement pp. 23-24 (PDF pp. 3-4) and pp. 34-35 (PDF pp. 14-15).
The printed claim is false: the twelve-unit population satisfies both parameter spaces,
with all the stated moments, OLS coefficients, contrast variances, assignment probabilities
and oracle formula. Its variance bounds have right sides 65/4752 and 39/55, exceeding
the actual variances 5/396 and 36/55. The repeated-block family preserves both failures
with factor 13/12; the displayed negative-delta arithmetic step fails. -/
def T1WholeStatement : Prop := T1Statement ∧ W2T1Details

/-- Weighted coefficients in the corrected square bounds. -/
def W2b1 {n : ℕ} (P : Population n) (δ : ℝ) : ℝ :=
  1+max δ 0*controlSize P/(P.n1 : ℝ)
def W2b0 {n : ℕ} (P : Population n) (δ : ℝ) : ℝ :=
  1+max δ 0*(P.n1 : ℝ)/controlSize P

def W2T2GroupChain : Prop :=
  ∀ {n : ℕ} (P : Population n) (δ r A : ℝ),
    δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A → Theta P δ r A →
    2 ≤ (compliers P).card →
    let C := compliers P
    let V1 := groupVar C (w P true (late P))
    let V0 := groupVar C (w P false (late P))
    let C10 := groupCov C (w P true (late P)) (w P false (late P))
    let Q := (∑ i ∈ C, (v P true (late P) i-v P false (late P) i)^2)/((C.card : ℝ)-1)
    Q = V1+V0-2*C10 ∧
    Q ≤ V1+V0+2*max δ 0*Real.sqrt V1*Real.sqrt V0 ∧
    V1+V0+2*max δ 0*Real.sqrt V1*Real.sqrt V0 ≤ W2b1 P δ*V1+W2b0 P δ*V0 ∧
    W2b1 P δ*V1+W2b0 P δ*V0 ≤
      (W2b1 P δ*(∑ i ∈ C, v P true (late P) i^2)+
       W2b0 P δ*(∑ i ∈ C, v P false (late P) i^2))/((C.card : ℝ)-1)

def W2T2Scaled : Prop :=
  ∀ {n : ℕ} (P : Population n) (δ r A : ℝ),
    δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A → Theta P δ r A →
    Sdiff2 P (late P) ≤ (fraction P)^2*(1-fraction P)^2/((n : ℝ)-1)*
      (W2b1 P δ*(∑ i, v P true (late P) i^2)+W2b0 P δ*(∑ i, v P false (late P) i^2))

def W2T2Residual : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (δ e A B r : ℝ),
    0 < k → δ < 1 → 0 < e → 0 < A → 0 < B → (0 < r ∧ r ≤ 1/2) →
    Xi P δ e A B r →
    (∑ i, (residual P true (late P.pop) i-residual P false (late P.pop) i)^2) ≤
      W2b1 P.pop δ*(∑ i, residual P true (late P.pop) i^2)+
      W2b0 P.pop δ*(∑ i, residual P false (late P.pop) i^2)

def W2T2Inclusions : Prop :=
  (∀ {n : ℕ} (P : Population n) (δ r A : ℝ), δ < 0 → Theta P δ r A → Theta P 0 r A) ∧
  (∀ {n k : ℕ} (P : CovPopulation n k) (δ e A B r : ℝ),
    δ < 0 → Xi P δ e A B r → Xi P 0 e A B r)

def W2T2Printed : Prop :=
  (∀ {n : ℕ} (P : Population n) (δ r A : ℝ),
    0 ≤ δ → δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A → Theta P δ r A →
    (1-δ)*(controlSize P/((n : ℝ)*(P.n1 : ℝ))*S2 P (late P) true+
      (P.n1 : ℝ)/((n : ℝ)*controlSize P)*S2 P (late P) false) ≤ designVariance P (tau P (late P))) ∧
  (∀ {n k : ℕ} (P : CovPopulation n k) (δ e A B r : ℝ),
    0 < k → 0 ≤ δ → δ < 1 → 0 < e → 0 < A → 0 < B → (0 < r ∧ r ≤ 1/2) → Xi P δ e A B r →
    (1-δ)*(controlSize P.pop/((n : ℝ)*(P.pop.n1 : ℝ))*popVar (residual P true (late P.pop))+
      (P.pop.n1 : ℝ)/((n : ℝ)*controlSize P.pop)*popVar (residual P false (late P.pop))) ≤
      designVariance P.pop (oracleTau P (late P.pop)))

/-- P002-T2; Supplement pp. 23-24 (PDF pp. 3-4) and pp. 34-35 (PDF pp. 14-15).
Replacing delta by max(delta,0) gives the two corrected variance lower bounds for every
admissible model, hence at every subsequence term. The entire corrected complier chain
(C.3)-(C.6), full-population bound (C.8), and residual-square bound preceding (E.10) hold.
Negative-delta classes are contained in the corresponding zero-delta classes; nonnegative
delta recovers the printed bounds. Singleton compliers and zero variances are included. -/
def T2WholeStatement : Prop :=
  T2Statement ∧ W2T2GroupChain ∧ W2T2Scaled ∧ W2T2Residual ∧ W2T2Inclusions ∧ W2T2Printed

/-- The observed and reassigned zero-statistic identities in the raw degenerate class. -/
def W2T4RawZeros : Prop :=
  ∀ {n : ℕ} (P : Population n), Theta P 0 (1/4) (1/2) →
    ∀ α : ℝ, (0 < α ∧ α < 1) → ∃ c : ℝ,
      (∀ a i, w P a (late P) i = c) ∧
      ∀ O ∈ assignments P,
        observedW P (late P) O = (fun _ => c) ∧ tau P (late P) O = 0 ∧
        rawSigma2 P (observedW P (late P) O) O = 0 ∧ rawAR P (observedW P (late P) O) O = 0 ∧
        (∀ T ∈ assignments P, rawTau P (observedW P (late P) O) T = 0 ∧
          rawSigma2 P (observedW P (late P) O) T = 0 ∧ rawAR P (observedW P (late P) O) T = 0) ∧
        quantile P (rawAR P (observedW P (late P) O)) α = 0 ∧ accepted P (late P) α O

/-- A fit rule can be completed arbitrarily on singular arm designs. -/
def W2FitRule {n k : ℕ} (_P : CovPopulation n k) :=
  (Fin n → ℝ) → Finset (Fin n) → Bool → Option (Fin k) → ℝ

def W2FullRank {n k : ℕ} (P : CovPopulation n k) (S : Finset (Fin n)) : Prop :=
  (gram P.x S).det ≠ 0 ∧ (gram P.x Sᶜ).det ≠ 0

def W2Completion {n k : ℕ} (P : CovPopulation n k) (F : W2FitRule P) : Prop :=
  ∀ q S a, (gram P.x (if a then S else Sᶜ)).det ≠ 0 → F q S a = fitted P q S a

def W2CompletedAR {n k : ℕ} (P : CovPopulation n k) (F : W2FitRule P)
    (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ≥0∞ :=
  absStudent (adjustedWith P q S (F q S true) (F q S false))
    (rss P.x S q (F q S true)/(P.pop.n1 : ℝ)^2+
     rss P.x Sᶜ q (F q S false)/(controlSize P.pop)^2)

def W2CompletedCoverage {n k : ℕ} (P : CovPopulation n k) (F : W2FitRule P) (β α : ℝ) : ℝ :=
  probability P.pop fun O =>
    W2CompletedAR P F (observedW P.pop β O) O ≤
      quantile P.pop (W2CompletedAR P F (observedW P.pop β O)) α

def W2T4Fits : Prop :=
  ∀ {n : ℕ} (P : CovPopulation n 1), Xi P 0 (1/4) 4 (1/2) (1/4) →
    (∀ a i, residual P a (late P.pop) i = 0) ∧
    psi P true (late P.pop) none = psi P false (late P.pop) none ∧
    (∀ O ∈ assignments P.pop, W2FullRank P O →
      (∀ a, fitted P (observedW P.pop (late P.pop) O) O a = psi P a (late P.pop)) ∧
      (∀ i, observedW P.pop (late P.pop) O i -
        dotProduct (augmented P.x i) (fitted P (observedW P.pop (late P.pop) O) O (decide (i ∈ O))) = 0) ∧
      adjustedTau P (observedW P.pop (late P.pop) O) O = 0 ∧
      adjustedSigma2 P (observedW P.pop (late P.pop) O) O = 0 ∧
      adjustedAR P (observedW P.pop (late P.pop) O) O = 0) ∧
    (∀ (F : W2FitRule P), W2Completion P F → ∀ α : ℝ,
      max 0 (1-1548/((n : ℝ)-1)) ≤ W2CompletedCoverage P F (late P.pop) α)

/-- Rank-loss bounds apply even to singleton arms, where their upper bounds exceed one. -/
def W2T4Ranks : Prop :=
  ∀ {n : ℕ} (P : CovPopulation n 1), Xi P 0 (1/4) 4 (1/2) (1/4) →
    probability P.pop (fun S => (gram P.x S).det = 0) ≤
      258*controlSize P.pop/((P.pop.n1 : ℝ)*((n : ℝ)-1)) ∧
    probability P.pop (fun S => (gram P.x Sᶜ).det = 0) ≤
      258*(P.pop.n1 : ℝ)/(controlSize P.pop*((n : ℝ)-1)) ∧
    258*controlSize P.pop/((P.pop.n1 : ℝ)*((n : ℝ)-1)) ≤ 774/((n : ℝ)-1) ∧
    258*(P.pop.n1 : ℝ)/(controlSize P.pop*((n : ℝ)-1)) ≤ 774/((n : ℝ)-1) ∧
    probability P.pop (fun S => ¬ W2FullRank P S) ≤ 1548/((n : ℝ)-1)

def W2T4Grid : Prop :=
  ∀ n, 2 ≤ n → (∑ i : Fin n, gridX i 0) = 0 ∧
    mean (fun i : Fin n => gridX i 0^2) = ((n : ℝ)^2-1)/(3*(n : ℝ)^2) ∧
    1/4 ≤ mean (fun i : Fin n => gridX i 0^2) ∧ mean (fun i : Fin n => gridX i 0^4) < 1

/-- Six-unit heterogeneous-effect illustration, with indices shifted from [6] to Fin 6. -/
def W2Six : CovPopulation 6 1 where
  pop := {y := fun i a => if a then 7/3+2*gridX i 0 else gridX i 0,
          d := fun _ a => a, n1 := 3}
  x := gridX

def W2T4Six : Prop :=
  Xi W2Six 0 (1/4) 4 (1/2) (1/4) ∧ late W2Six.pop = 7/3 ∧
    (∃ i j, W2Six.pop.y i true-W2Six.pop.y i false ≠
      W2Six.pop.y j true-W2Six.pop.y j false) ∧
    (assignments W2Six.pop).card = 20 ∧
    (∀ O ∈ assignments W2Six.pop,
      adjustedAR W2Six (observedW W2Six.pop (7/3) O) O = 0 ∧
      ∀ α : ℝ, (0 < α ∧ α < 1) → adjustedAccepted W2Six (7/3) α O) ∧
    (((assignments W2Six.pop).product (assignments W2Six.pop)).filter fun OT =>
      adjustedAR W2Six (observedW W2Six.pop (7/3) OT.1) OT.2 ≠ 0).card = 312

/-- Finite bounds on the adjusted class infimum, including its upper endpoint. -/
def W2T4InfBounds : Prop :=
  ∀ α : ℝ, (0 < α ∧ α < 1) → ∀ n : ℕ, 2 ≤ n →
    ENNReal.ofReal (max 0 (1-1548/((n : ℝ)-1))) ≤
      infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α ∧
    infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α ≤ 1

/-- P002-T4; main p. 8 (Theorem 1 and Remark 3), main p. 11 (Theorem 2),
Supplement p. 31 (PDF p. 11), and Assumptions 3(ii), 5(ii).
The printed claim is false: the half-moment bound forces collapse. The stated nonempty
raw class has all observed and reassigned statistics and quantiles zero, and coverage one.
The adjusted class has zero population residuals, exact full-rank fits, the individual
258 and 774 rank-loss bounds and the 1548 coverage bound for every singular-fit completion.
The grid moments give every beta fiber; both worst-case coverages tend to one. The
six-unit heterogeneous example has 20 accepting assignments and 312 nonzero reassigned
squared statistics among its 400 assignment pairs. -/
def T4WholeStatement : Prop :=
  T4Statement ∧ W2T4RawZeros ∧ W2T4Fits ∧ W2T4Ranks ∧ W2T4Grid ∧ W2T4Six ∧ W2T4InfBounds

/-- The unrestricted lower bound uses ENNReal infima over nonempty sizes.
A bounded set of such sizes has bottom size filter and liminf equal to top. -/
def W2T5Raw : Prop :=
  ∀ δ r A α : ℝ, δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A → (0 < α ∧ α < 1) →
    ENNReal.ofReal (1-α) ≤ Filter.liminf (fun n => infCoverageTheta n δ r A α)
      (atTop ⊓ Filter.principal (thetaSizes δ r A))

def W2T5Adjusted : Prop :=
  ∀ (k : ℕ) (δ e A B r α : ℝ), 0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (0 < α ∧ α < 1) →
    ENNReal.ofReal (1-α) ≤ Filter.liminf (fun n => infCoverageXi n k δ e A B r α)
      (atTop ⊓ Filter.principal (xiSizes k δ e A B r))

/-- A suitable sequence in the same fixed raw parameter class. -/
def W2RawWitness (δ r A α : ℝ) : Prop :=
  ∃ (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j)), StrictMono sizes ∧
    (∀ j, Theta (P j) δ r A) ∧
    (∀ j, ∃ β : ℝ, ∀ i, (P j).y i true = (P j).y i false+β) ∧
    (∀ j, 0 < popVar (fun i => (P j).y i false)) ∧
    Tendsto (fun j => ENNReal.ofReal (coverage (P j) (late (P j)) α))
      atTop (nhds (ENNReal.ofReal (1-α)))

/-- Adjusted nondegeneracy is positivity of the population OLS residual variance. -/
def W2AdjustedWitness (k : ℕ) (δ e A B r α : ℝ) : Prop :=
  ∃ (sizes : ℕ → ℕ) (P : ∀ j, CovPopulation (sizes j) k), StrictMono sizes ∧
    (∀ j, Xi (P j) δ e A B r) ∧
    (∀ j, ∃ β : ℝ, ∀ i, (P j).pop.y i true = (P j).pop.y i false+β) ∧
    (∀ j, 0 < popVar (residual (P j) false (late (P j).pop))) ∧
    Tendsto (fun j => ENNReal.ofReal (adjustedCoverage (P j) (late (P j).pop) α))
      atTop (nhds (ENNReal.ofReal (1-α)))

def W2T5NecessaryRaw : Prop :=
  ∀ δ r A α : ℝ, δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A → (0 < α ∧ α < 1) →
    Filter.liminf (fun n => infCoverageTheta n δ r A α)
      (atTop ⊓ Filter.principal (thetaSizes δ r A)) = ENNReal.ofReal (1-α) →
    W2RawWitness δ r A α

def W2T5NecessaryAdjusted : Prop :=
  ∀ (k : ℕ) (δ e A B r α : ℝ), 0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (0 < α ∧ α < 1) →
    Filter.liminf (fun n => infCoverageXi n k δ e A B r α)
      (atTop ⊓ Filter.principal (xiSizes k δ e A B r)) = ENNReal.ofReal (1-α) →
    W2AdjustedWitness k δ e A B r α

/-- Balanced nondegenerate baseline, with just one complier to allow every delta < 1. -/
def W2RawSharpModel (j : ℕ) : Population (2*(j+1)) where
  y := fun i _ => if i.val < j+1 then -1 else 1
  d := fun i a => if i.val = 0 then a else false
  n1 := j+1

/-- Repeat the (k+1)-dimensional sign cube. The last coordinate is the response. -/
def W2CubeSize (k j : ℕ) : ℕ := 2^(k+1)*(j+1)
/-- Label units by a sign pattern and a repetition index. -/
def W2CubeEquiv (k j : ℕ) :
    Fin (W2CubeSize k j) ≃ ((Fin (k+1) → Bool) × Fin (j+1)) :=
  (finCongr (by simp [W2CubeSize])).trans (Fintype.equivFin _).symm

def W2CubeSign (k j : ℕ) (s : Fin (k+1)) (i : Fin (W2CubeSize k j)) : ℝ :=
  if (W2CubeEquiv k j i).1 s then 1 else -1

def W2CubeModel (k : ℕ) (e : ℝ) (j : ℕ) : CovPopulation (W2CubeSize k j) k where
  pop := {y := fun i _ => W2CubeSign k j (Fin.last k) i,
          d := fun _ a => a, n1 := W2CubeSize k j/2}
  x := fun i s => Real.sqrt e*W2CubeSign k j s.castSucc i

/-- Absolute standard normal CDF, used only at positive arguments. -/
def W2AbsNormalCDF (t : ℝ) : ℝ :=
  2*ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t-1

/-- P002-T5; main pp. 8, 11; Supplement Sections C and E, pp. 23-42 (PDF pp. 3-22).
Both corrected uniform liminf lower bounds hold along nonempty sizes, including degenerate
models, without a cofinality hypothesis. Nominal worst-case liminf in a fixed class
requires a nondegenerate constant-additive-effect sequence in that very class whose
coverage tends to nominal. Raw nondegeneracy is baseline variance; adjusted nondegeneracy
is population OLS residual variance. Admissible nondegenerate raw constant-effect
sequences give nominal coverage and worst-case liminf. The specified degenerate raw
and adjusted classes instead have worst-case coverage tending to one. -/
def T5WholeStatement : Prop :=
  W2T5Raw ∧ W2T5Adjusted ∧ T5Sharpness ∧ W2T5NecessaryRaw ∧ W2T5NecessaryAdjusted ∧
    T4Unadjusted ∧ T4Adjusted

end
end SAP.P002a
