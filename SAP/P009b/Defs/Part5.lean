import Mathlib
import SAP.P009b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def T18ZeroStatement : Prop :=
  ∀ {n : ℕ} (E : Experiment n) (m : ℕ) (_hCR : Complete E m)
    (i : Fin n) (_hc : incoming E i ≤ min m (n-m)),
    incoming E i - 1 = 0 → prob E.design (fun z => treatedIncoming E i z = 0) = 1

def T18Statement : Prop := T18CoreStatement ∧ T18ZeroStatement

def T19DetailsStatement : Prop :=
  let E := fairExperiment 6 sixOutcome
  Function.Involutive sixPartner ∧
  (∀ j, (Interferes E j 0 ↔ j = 0 ∨ j = 2 ∨ j = 4) ∧
    (Interferes E j 1 ↔ j = 1 ∨ j = 3 ∨ j = 5)) ∧
  (∀ i j, j ≠ 0 → j ≠ 1 → (Interferes E i j ↔ i = j)) ∧
  (∀ ℓ, (1-d E 0 1)*I E ℓ 0*I E (sixPairing.partner ℓ) 1 =
    if ℓ = 0 ∨ ℓ = 2 ∨ ℓ = 4 then 1 else 0)

def T19Statement : Prop := T19CoreStatement ∧ T19DetailsStatement

def T20Statement : Prop := T20CoreStatement

def T21DetailsStatement : Prop :=
  ∀ (x ε : Fin 6 → ℝ) (_hSupport : UniformBaselineSupport6 x ε),
    let c := fun i => x i + ε i
    let E := fairExperiment 6 (oneSourceOutcome 4 c)
    (6:ℝ)*dAvg E = 18 ∧
    msq E/dAvg E-B1 E-B2 E = -(1 + 2 * c 0) / 3 ∧
    ((4:ℝ)*3/(6+4*3)) = 2/3

def T21Statement : Prop := T21CoreStatement ∧ T21DetailsStatement

def T22CorrectionStatement : Prop :=
  ∀ (n b : ℕ) (_hn : 0 < n) (_hb : 1 ≤ b ∧ b ≤ n),
    ((n:ℝ)-((b:ℝ)-1)^2)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) -
      ((n:ℝ)-((b:ℝ)-1)-(b:ℝ)*((b:ℝ)-1))/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) =
      2*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1))

def T22Statement : Prop := T22FiniteStatement ∧ T22CorrectionStatement ∧ T22LimitStatement

def T23Statement : Prop := T23CoreStatement

def T24MagnitudeStatement : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (_heven : Even n)
    (E : Experiment n) (b : Fin n → ℝ) (_hy : E.outcome = fullOutcome b)
    (_hDesign : Complete E (n/2) ∨ ∃ ρ : Pairing n, Paired E ρ),
    |mean E.design (ht E)-eate E| = 1 ∧ |mean E.design (hajek E)-eate E| = 1

def T24Statement : Prop := T24CoreStatement ∧ T24MagnitudeStatement

def T25SignLossStatement : Prop :=
  empiricalBias 1 (fun _ => 0) = -1 ∧ empiricalBias 1 (fun _ => 2) = 1 ∧
  reportedBias 1 (fun _ => 0) = reportedBias 1 (fun _ => 2)

def T25Statement : Prop := T25CaptionStatement ∧ T25PopulationStatement ∧ T25SignLossStatement

def T26Statement : Prop := T26CoreStatement

def T27Statement : Prop := T27AtomsStatement ∧ T27ApproximationStatement.{u} ∧ T27MinimizerStatement

def T28MeanStatement : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] (P : Law Ω) (F : Ω → ℝ),
    (∀ ω, F ω = -1 ∨ F ω = 0 ∨ F ω = 1) →
    mean P F = prob P (fun ω => F ω = 1)-prob P (fun ω => F ω = -1)

def T28SequenceStatement : Prop :=
  ∀ (Ω : ℕ → Type*) [∀ t, Fintype (Ω t)]
    (P : (t : ℕ) → Law (Ω t)) (F : (t : ℕ) → Ω t → ℝ)
    (_hF : ∀ t ω, F t ω = -1 ∨ F t ω = 0 ∨ F t ω = 1)
    (_hMean : Tendsto (fun t => mean (P t) (F t)) atTop (nhds 0))
    (x : ℝ) (_hx : x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1),
    0 < threePointDistance x ∧
    (∀ᶠ t in atTop, |mean (P t) (F t)| < threePointDistance x ∧
      prob (P t) (fun ω => F t ω-mean (P t) (F t) ≤ x) =
        prob (P t) (fun ω => F t ω ≤ x) ∧
      ¬ threePointDistance x < mean (P t) (F t))

def T28Statement : Prop :=
  T28MeanStatement.{u} ∧ T28FiniteStatement.{u} ∧ T28EventualStatement ∧ T28SequenceStatement.{u}

def T29Statement : Prop := T29CoreStatement

def T30Statement : Prop := T30CoreStatement

def T31Statement : Prop := T31FiniteStatement ∧ T31LimitStatement.{u}

def T32FlipStatement : Prop :=
  ∀ {n : ℕ} (G : Finset (Fin n)) (i : Fin n) (_hi : i ∈ G)
    (z : Assignment n) (_hz : z i = false),
    balance G (Function.update z i true)-balance G z = 2

def T32Statement : Prop :=
  T32UpdateStatement ∧ T32FlipStatement ∧ T32CrossingsStatement ∧ T32PairedStatement

def T33Statement : Prop := T33CoreStatement

def T34SumStatement : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (ρ : Pairing n)
    (_hPair : Paired E ρ) (k q s : ℝ) (_hReg : Regular E k q s) (i : Fin n),
    |cmean E.design (fun z => z i = true) (potential E i true)-
      mean E.design (potential E i true)| +
    |cmean E.design (fun z => z i = false) (potential E i false)-
      mean E.design (potential E i false)| ≤ 2*k

def T34Statement : Prop := T34CoreStatement ∧ T34SumStatement

end
end SAP.P009b
