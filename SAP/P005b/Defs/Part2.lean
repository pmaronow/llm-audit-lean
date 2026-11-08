import SAP.P005b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005b

noncomputable section
open scoped BigOperators Matrix
open Finset Filter

/-! The printed regression formulas and randomization orders. Sequence results
use positive dimension from size three, matching the exported theorems. -/

def adjustedATE {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  mean S P.yT - mean (control S) P.yC - dot (xMean P S - xMean P (control S)) (betaHat P m S)

def interactedATE {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : ℝ :=
  mean S P.yT - mean (control S) P.yC -
    (dot (xMean P S) (armBetaHat P S P.yT) -
      dot (xMean P (control S)) (armBetaHat P (control S) P.yC))

def armNu1 {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) (y : Fin n → ℝ) :
    Fin d → ℝ := fun k => mean S (fun i => centered y i * P.x i k) -
      popMean (fun i => centered y i * P.x i k)

def armNu2 {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) (y : Fin n → ℝ) :
    Fin d → ℝ := ((armL P S)⁻¹ - 1) *ᵥ armN P S y

def armNu3 {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) (y : Fin n → ℝ) :
    Fin d → ℝ := fun k => -(xMean P S k * mean S (centered y))

def nu1 {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  pT n m • armNu1 P S P.yT + pC n m • armNu1 P (control S) P.yC

def nu2 {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  ((Lhat P m S)⁻¹ - 1) *ᵥ Nhat P m S

def nu3 {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : Fin d → ℝ :=
  pT n m • armNu3 P S P.yT + pC n m • armNu3 P (control S) P.yC

def biasEstimate {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  (sampleCov (control S) (leverage P) P.yC - sampleCov S (leverage P) P.yT) / (n - 2 : ℝ) +
  dot (xMean P (control S) - xMean P S) (nu2 P m S)

def debiasedATE {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  adjustedATE P m S - biasEstimate P m S

def interactedBiasEstimate {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  (m : ℝ) / ((n - 2 : ℝ) * (n - m)) * sampleCov (control S) (leverage P) P.yC +
    dot (xMean P (control S)) (armNu2 P (control S) P.yC) -
  ((n : ℝ) - m) / ((n - 2 : ℝ) * m) * sampleCov S (leverage P) P.yT -
    dot (xMean P S) (armNu2 P S P.yT)

def interactedDebiasedATE {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  interactedATE P S - interactedBiasEstimate P m S

def leverageCov {n d : ℕ} (P : Population n d) (y : Fin n → ℝ) : ℝ := popCov (leverage P) y

def NTTT (n m : ℕ) : ℝ :=
  ((n : ℝ) - m) * (n - 2 * m : ℝ) / ((n - 1 : ℝ) * (n - 2 : ℝ) * (m : ℝ)^2)

def NCCC (n m : ℕ) : ℝ := NTTT n (n - m)

def NTTC (n m : ℕ) : ℝ := -(n - 2 * m : ℝ) / ((n - 1 : ℝ) * (n - 2 : ℝ) * m)

def armResidual {n d : ℕ} (P : Population n d) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  centered y i - dot (P.x i) (populationSlope P y)

def commonResidual {n d : ℕ} (P : Population n d) (m : ℕ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  centered y i - dot (P.x i) (N P m)

def commonLeading {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  mean S (commonResidual P m P.yT) - mean (control S) (commonResidual P m P.yC)

def armLeading {n d : ℕ} (P : Population n d) (S : Finset (Fin n)) : ℝ :=
  mean S (armResidual P P.yT) - mean (control S) (armResidual P P.yC)

def stochasticO (m : ℕ → ℕ) (R : (n : ℕ) → Finset (Fin n) → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∃ n₀ : ℕ,
    ∀ n ≥ n₀, probability (m n) (fun S => |R n S| > M * r n) < ε

def stochasticLittleO (m : ℕ → ℕ) (R : (n : ℕ) → Finset (Fin n) → ℝ)
    (r : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto (fun n => probability (m n) (fun S => |R n S| > δ * r n)) atTop (nhds 0)

def standingAssumptions (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)) : Prop :=
  (∀ n, 3 ≤ n → 1 ≤ d n ∧ d n ≤ n ∧ 0 < m n ∧ m n < n) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ n, 3 ≤ n →
    popMean (fun i => (P n).yT i^2) ≤ K ∧
    popMean (fun i => (P n).yC i^2) ≤ K ∧
    ∀ k, popMean (fun i => (P n).x i k^2) ≤ K) ∧
  (∀ᶠ n in atTop, standardized (P n)) ∧
  (∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ hi < 1 ∧
    ∀ n, 3 ≤ n → lo < pT n (m n) ∧ pT n (m n) < hi)

def armDebiased {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) : ℝ :=
  mean S y - dot (xMean P S) (armN P S y) +
    ((n : ℝ)-S.card) / ((n-2 : ℝ)*S.card) * sampleCov S (leverage P) y

def indicator {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ S then 1 else 0

def repeatedPair {n : ℕ} (S : Finset (Fin n)) (a b c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ univ.erase i, indicator S i * indicator S j * a i * b i * c j

def distinctTriple {n : ℕ} (S : Finset (Fin n)) (a b c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
    indicator S i * indicator S j * indicator S k * a i * b j * c k

def observedResidual {n : ℕ} (S : Finset (Fin n)) (eT eC : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i ∈ S then eT i else eC i

def residualStarTerm {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (eT eC : Fin n → ℝ) : ℝ :=
  dot (xMean P S-xMean P (control S)) (populationSlope P (observedResidual S eT eC))

end
end SAP.P005b
