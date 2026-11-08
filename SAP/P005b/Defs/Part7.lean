import SAP.P005b.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005b

noncomputable section
open scoped BigOperators Matrix
open Finset Filter

def T25Statement : Prop :=
  ∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P)
    (hinv : ∀ᶠ n in atTop, noninteractedRegular (P n) (m n))
    (hd : Tendsto (fun n => (d n : ℝ)/n) atTop (nhds 0)),
    stochasticO m (fun n S => adjustedATE (P n) (m n) S - ate (P n) - commonLeading (P n) (m n) S)
      (fun n => Real.sqrt (kappa (P n)*(d n)/n))

def T26Statement : Prop :=
  ∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P)
    (hinv : ∀ᶠ n in atTop, noninteractedRegular (P n) (m n))
    (hκ : Tendsto (fun n => kappa (P n)) atTop (nhds 0)),
    stochasticLittleO m
      (fun n S => debiasedATE (P n) (m n) S - ate (P n) - commonLeading (P n) (m n) S)
      (fun n => Real.sqrt (1/(n : ℝ)))

def T27Statement : Prop :=
  ∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P)
    (hinv : ∀ᶠ n in atTop, interactedRegular (P n) (m n))
    (hκ : Tendsto (fun n => kappa (P n)) atTop (nhds 0)),
    stochasticLittleO m
      (fun n S => interactedDebiasedATE (P n) (m n) S - ate (P n) - armLeading (P n) S)
      (fun n => Real.sqrt (1/(n : ℝ)))

end
end SAP.P005b
