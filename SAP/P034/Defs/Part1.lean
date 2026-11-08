import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P034

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- “Y=Y(T), R=R(T)” (validator P034-E017, derivation.md §2).
`T` is the treatment, `Y t` the potential outcome, `R t` the potential
completion indicator, and `X` a finite vector of pretreatment covariates.
The paper's “survey completion rates” (article p. 6) concern `R`. -/
structure SurveyModel (Ω K : Type*) (k : ℕ) where
  T : Ω → Bool
  Y : Bool → Ω → K
  R : Bool → Ω → Bool
  X : Ω → Fin k → K

/-- “Y=Y(T)” (validator §2): the outcome under the realized assignment. -/
def realizedOutcome {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) (ω : Ω) : K :=
  M.Y (M.T ω) ω

/-- “R=R(T)” (validator §2): an outcome is observed iff this indicator is true. -/
def realizedCompletion {Ω K : Type*} {k : ℕ} (M : SurveyModel Ω K k) (ω : Ω) : Bool :=
  M.R (M.T ω) ω

/-- The numerical 0/1 coding used for treatment and binary outcomes in the
constructed witness (validator §§2-3). -/
def bitQ (b : Bool) : ℚ := if b then 1 else 0

/-- The finite probability of an event is the sum of its point masses.
This implements the validator's “probability of each of the 32 configurations”
(§3). All weights here are exact rationals. -/
def finiteProb {Ω : Type*} [Fintype Ω] (w : Ω → ℚ)
    (E : Ω → Prop) [DecidablePred E] : ℚ := ∑ ω, if E ω then w ω else 0

/-- “E[Y(1)-Y(0)]” (validator §2), evaluated as a weighted finite sum. -/
def finiteMean {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (f : Ω → ℚ) : ℚ :=
  ∑ ω, w ω * f ω

/-- Ordinary event conditioning: the joint probability divided by the
conditioning event's probability (validator §§3-6). Positivity is checked
separately for every conditioning event used in the witness. -/
def finiteCondProb {Ω : Type*} [Fintype Ω] (w : Ω → ℚ)
    (E F : Ω → Prop) [DecidablePred E] [DecidablePred F] : ℚ :=
  finiteProb w (fun ω => E ω ∧ F ω) / finiteProb w F

/-- “E[Y | T=t,R=1]” and “E[ZZ' | R=1]” (validator §§3-4), with event
conditioning implemented by the normalized weighted finite sum. -/
def finiteCondMean {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (f : Ω → ℚ)
    (E : Ω → Prop) [DecidablePred E] : ℚ :=
  (∑ ω, if E ω then w ω * f ω else 0) / finiteProb w E

/-- Independence for finite-valued variables is the factorization of every
joint cell probability (validator §2: “T is independent of ...”). -/
def finiteIndependent {Ω A B : Type*} [Fintype Ω] [DecidableEq A] [DecidableEq B]
    (w : Ω → ℚ) (f : Ω → A) (g : Ω → B) : Prop :=
  ∀ a b, finiteProb w (fun ω => f ω = a ∧ g ω = b) =
    finiteProb w (fun ω => f ω = a) * finiteProb w (fun ω => g ω = b)

/-- Independence within an event of positive probability (validator §3:
“conditional on (T,X)”), again as factorization of every finite joint cell. -/
def finiteConditionalIndependent {Ω A B : Type*} [Fintype Ω]
    [DecidableEq A] [DecidableEq B] (w : Ω → ℚ) (f : Ω → A) (g : Ω → B)
    (E : Ω → Prop) [DecidablePred E] : Prop :=
  ∀ a b, finiteCondProb w (fun ω => f ω = a ∧ g ω = b) E =
    finiteCondProb w (fun ω => f ω = a) E * finiteCondProb w (fun ω => g ω = b) E

/-- `Ω={0,1}^5`, with coordinates `(u,r₀,r₁,x,t)` (validator §3;
fixed target T1). Booleans represent binary values without extra support hypotheses. -/
abbrev WorldA := Fin 5 → Bool

/-- `p₀(0)=37/50, p₀(1)=13/50, p₁(0)=13/50, p₁(1)=37/50`
(validator §5's first numerical specification). -/
def completionChance (t u : Bool) : ℚ := if t = u then 37/50 else 13/50

/-- `p^r (1-p)^(1-r)` for a binary indicator (validator §3's point-mass formula). -/
def bernoulliMass (p : ℚ) (r : Bool) : ℚ := if r then p else 1-p

/-- `P(u,r₀,r₁,x,t)=1/8 p₀(u)^r₀(1-p₀(u))^(1-r₀)
p₁(u)^r₁(1-p₁(u))^(1-r₁)` (validator §3). -/
def worldAWeight (ω : WorldA) : ℚ :=
  (1/8) * bernoulliMass (completionChance false (ω 0)) (ω 1) *
    bernoulliMass (completionChance true (ω 0)) (ω 2)

/-- “Y(0)=Y(1)=U” and the potential completions/covariate/assignment
(validator §3); the single binary covariate is also encoded as a rational. -/
def worldAModel : SurveyModel WorldA ℚ 1 where
  T ω := ω 4
  Y _ ω := bitQ (ω 0)
  R t ω := if t then ω 2 else ω 1
  X ω _ := bitQ (ω 3)

/-- `(Y(0),Y(1),R(0),R(1),X)` in its binary coding (validator §2).
Both potential outcomes use the same `u`. -/
def worldABundle (ω : WorldA) : Bool × Bool × Bool × Bool × Bool :=
  (ω 0, ω 0, ω 1, ω 2, ω 3)

/-- The target “τ=E[Y(1)-Y(0)]” (validator §2), for the constructed world A. -/
def worldAEffect : ℚ := finiteMean worldAWeight
  (fun ω => worldAModel.Y true ω - worldAModel.Y false ω)

/-- “E[Y | T=t,R=1]” (validator §3), the complete-case arm mean. -/
def worldAArmMean (t : Bool) : ℚ := finiteCondMean worldAWeight
  (realizedOutcome worldAModel)
  (fun ω => worldAModel.T ω = t ∧ realizedCompletion worldAModel ω = true)

/-- The conditioning stratum `(T=t,X=x,Y=y)` in T1(v), validator §3. -/
def worldAStratum (t x y : Bool) (ω : WorldA) : Prop :=
  worldAModel.T ω = t ∧ worldAModel.X ω 0 = bitQ x ∧
    realizedOutcome worldAModel ω = bitQ y

instance (t x y : Bool) : DecidablePred (worldAStratum t x y) :=
  fun ω => by unfold worldAStratum; infer_instance

end SAP.P034
