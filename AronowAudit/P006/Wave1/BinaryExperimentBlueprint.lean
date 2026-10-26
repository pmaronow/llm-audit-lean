import AronowAudit.P006.P006_CounterfactualMetrics

/-!
# Binary-covariate product experiment for P006-T26 and P006-T27

One unit has state `(x, t) ∈ Bool × Bool` with mass
`(1/2)·coinMass (π x) t`: a fair covariate and Bernoulli `π x` treatment.
The `n` units are i.i.d. (`Measure.pi`), with `X_i = (ω i).1`,
`T_i = (ω i).2`, `Y0 = 0`, `Y1_i = y1 (ω i).1`, `μ0 = 0` and `μ1 = y1`.
The random baseline `μhat` is an arbitrary parameter. At non-admissible
policies the same formula uses masses clipped at `0` (`Real.toNNReal`);
`Standing` makes no claim there. For n=1 the sample space is
`Fin 1 → Bool × Bool`, with the same law as a single `Bool × Bool` state.

`Sk` denotes a mathematical proposition; `Nk` is either `Sk` itself or an
implication from other stated propositions to `Sk`. These propositions imply
`Standing` for the experiment.
-/

set_option autoImplicit false

namespace AronowAudit.P006.Wave1.BinaryExperiment

open AronowAudit.P006 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! ## The witness experiment -/

/-- One-unit atom mass `(1/2)·coinMass (π x) t`, clipped at `0` (only relevant for
non-admissible `π`). -/
def unitMass (π : Bool → ℝ) (a : Bool × Bool) : ℝ≥0 :=
  Real.toNNReal ((1 / 2) * coinMass (π a.1) a.2)

/-- One-unit law of `(X, T)` under policy `π`. -/
def unitLaw (π : Bool → ℝ) : Measure (Bool × Bool) :=
  ∑ a : Bool × Bool, unitMass π a • Measure.dirac a

/-- The unit law is finite at every policy (so `Measure.pi` lemmas apply). -/
instance unitLaw_isFiniteMeasure (π : Bool → ℝ) : IsFiniteMeasure (unitLaw π) := by
  unfold unitLaw; infer_instance

/-- The fair covariate law `P_X`. -/
def fairLaw : Measure Bool := ∑ b : Bool, (1 / 2 : ℝ≥0) • Measure.dirac b

/-- The `n`-unit product experiment with deterministic potential outcomes `Y0 = 0`,
`Y1 = y1(X)` and random baseline `μhat`. -/
def binExp (n : ℕ) (hn : 0 < n) (y1 : Bool → ℝ)
    (μhat : (Bool → ℝ) → (Fin n → Bool × Bool) → Bool → ℝ) :
    Experiment (Fin n → Bool × Bool) Bool n where
  hn := hn
  PX := fairLaw
  μ0 := fun _ => 0
  μ1 := y1
  law π := Measure.pi (fun _ : Fin n => unitLaw π)
  X i ω := (ω i).1
  Y0 _ _ := 0
  Y1 i ω := y1 (ω i).1
  T _ i ω := (ω i).2
  μhat := μhat

/-! ## Mathematical statements -/

/-- **Statement S1.** For admissible `π`, the four atom masses
(1/2)coinMass(π x,t) define a probability law with fair X marginal.
The nonnegative Bernoulli masses sum to one; summing the Dirac masses
identifies the atoms and covariate marginal. -/
def S1 : Prop :=
  ∀ π : Bool → ℝ, Admissible π →
    IsProbabilityMeasure (unitLaw π) ∧
    (∀ a : Bool × Bool, unitLaw π {a} = ENNReal.ofReal ((1 / 2) * coinMass (π a.1) a.2)) ∧
    (unitLaw π).map Prod.fst = fairLaw

/-- **Statement S2.** On the finite product space, every integral equals
the explicit weighted sum. All functions are integrable on this finite
discrete space, and the product singleton masses follow from S1. -/
def S2 : Prop :=
  ∀ (n : ℕ) (π : Bool → ℝ), Admissible π → ∀ f : (Fin n → Bool × Bool) → ℝ,
    ∫ ω, f ω ∂(Measure.pi fun _ : Fin n => unitLaw π) =
      ∑ ω : Fin n → Bool × Bool, (∏ i, (1 / 2) * coinMass (π (ω i).1) (ω i).2) * f ω

/-- **Statement S3.** Given X_i=x, treatment T_i is Bernoulli π(x).
This gives the conditional expectation of any function of unit i's state
given `σ(X_i)`. The candidate is a function of `X_i`; every `σ(X_i)`-measurable
set is a preimage under `X_i`. The coordinate projection reduces the
set-integral identity to the unit law in S1. -/
def S3 : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (y1 : Bool → ℝ) (μhat : (Bool → ℝ) → (Fin n → Bool × Bool) → Bool → ℝ)
    (π : Bool → ℝ), Admissible π → ∀ (i : Fin n) (g : Bool × Bool → ℝ),
    ((binExp n hn y1 μhat).law π)[fun ω => g (ω i) | (binExp n hn y1 μhat).covariateSigma i]
      =ᵐ[(binExp n hn y1 μhat).law π]
      fun ω => ∑ t : Bool, coinMass (π (ω i).1) t * g ((ω i).1, t)

/-- **Statement S4.** The ten non-conditional fields of `Standing`.
Functions on the finite discrete spaces are measurable and integrable;
the units are independent and identically distributed under the product law.
The full (X_i,Y0_i,Y1_i) law is identical across policies because the triple
is a function of X_i, whose law is fair by S1. -/
def S4 : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (y1 : Bool → ℝ) (μhat : (Bool → ℝ) → (Fin n → Bool × Bool) → Bool → ℝ),
    let E := binExp n hn y1 μhat
    IsProbabilityMeasure E.PX ∧
    (Measurable E.μ0 ∧ Measurable E.μ1) ∧
    (Integrable E.μ0 E.PX ∧ Integrable E.μ1 E.PX) ∧
    (∀ π, Admissible π → IsProbabilityMeasure (E.law π)) ∧
    (∀ π, Admissible π → ∀ i,
      Measurable (E.X i) ∧ Measurable (E.Y0 i) ∧ Measurable (E.Y1 i) ∧ Measurable (E.T π i)) ∧
    (∀ π, Admissible π → ∀ i,
      Integrable (E.Y0 i) (E.law π) ∧ Integrable (E.Y1 i) (E.law π) ∧
      Integrable (fun ω => E.μhat π ω (E.X i ω)) (E.law π)) ∧
    (∀ π, Admissible π → ∀ i, IdentDistrib (E.X i) (fun x : Bool => x) (E.law π) E.PX) ∧
    (∀ π π', Admissible π → Admissible π' → ∀ i,
      IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω))
        (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω)) (E.law π) (E.law π')) ∧
    (∀ π, Admissible π →
      iIndepFun (fun i ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω)) (E.law π)) ∧
    (∀ π, Admissible π → ∀ i j,
      IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω))
        (fun ω => (E.X j ω, E.Y0 j ω, E.Y1 j ω, E.T π j ω)) (E.law π) (E.law π))

/-- **Statement S5.** The three conditional fields of `Standing`:
the two conditional means, the Bernoulli conditional moment and the
all-Borel-set ignorability equality. These include π(x)=0 and π(x)=1.
For a Borel set B, the conditional treatment-weighted indicator is
π(x)1{(0,μ1(x))∈B}. Each identity follows from S3 with an explicit function
of the unit's state and the Bernoulli mass identity. -/
def S5 : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (y1 : Bool → ℝ) (μhat : (Bool → ℝ) → (Fin n → Bool × Bool) → Bool → ℝ),
    let E := binExp n hn y1 μhat
    (∀ π, Admissible π → ∀ i,
      (E.law π)[E.Y0 i | E.covariateSigma i] =ᵐ[E.law π] (fun ω => E.μ0 (E.X i ω)) ∧
      (E.law π)[E.Y1 i | E.covariateSigma i] =ᵐ[E.law π] (fun ω => E.μ1 (E.X i ω))) ∧
    (∀ π, Admissible π → ∀ i,
      (E.law π)[(fun ω => bit (E.T π i ω)) | E.covariateSigma i] =ᵐ[E.law π]
        (fun ω => π (E.X i ω))) ∧
    (∀ π, Admissible π → ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
      (E.law π)[(fun ω => bit (E.T π i ω) *
        B.indicator (fun _ => (1 : ℝ)) (E.Y0 i ω, E.Y1 i ω)) | E.covariateSigma i]
        =ᵐ[E.law π] (fun ω => π (E.X i ω) *
          (E.law π)[(fun η => B.indicator (fun _ => (1 : ℝ))
            (E.Y0 i η, E.Y1 i η)) | E.covariateSigma i] ω))

/-! ## Implications between statements -/

def N1 : Prop := S1
def N2 : Prop := S1 → S2
def N3 : Prop := S1 → S3
def N4 : Prop := S1 → S4
def N5 : Prop := S1 → S3 → S5

/-! ## Assembly of `Standing` -/

/-- **Assembly.** The stated implications imply `Standing` for every
experiment `binExp n hn y1 μhat`. -/
theorem standing_of (h1 : N1) (h3 : N3) (h4 : N4) (h5 : N5) (n : ℕ) (hn : 0 < n)
    (y1 : Bool → ℝ) (μhat : (Bool → ℝ) → (Fin n → Bool × Bool) → Bool → ℝ) :
    Standing (binExp n hn y1 μhat) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h4 h1 n hn y1 μhat
  obtain ⟨c1, c2, c3⟩ := h5 h1 (h3 h1) n hn y1 μhat
  exact
    { px_probability := a1
      means_measurable := a2
      means_integrable := a3
      law_probability := a4
      measurable_units := a5
      integrable_units := a6
      covariate_law := a7
      potential_law_fixed := a8
      iid_independent := a9
      iid_identical := a10
      conditional_means := c1
      bernoulli := c2
      ignorability := c3 }

end

end AronowAudit.P006.Wave1.BinaryExperiment
