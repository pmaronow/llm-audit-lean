import AronowAudit.P006.P006_CounterfactualMetrics

/-!
# Blueprint (shared nodes): the binary-covariate product experiment for P006-T26 and P006-T27

Wave 1, group P005-P006-P017-P023-P046-P047. This module has no `Target` of its own: it
defines the explicit finite witness experiment used by both refutations
(`AverageBestResponseBlueprint`, n = 2; `TTAlignmentBlueprint`, n = 1) and the shared nodes
that certify the frozen `Standing` predicate for it.

Construction (mapper §§4–5, "binary_policy_unit_law", accepted by both referees): one unit has
state `(x, t) ∈ Bool × Bool` with mass `(1/2)·coinMass (π x) t` (fair covariate, treatment
Bernoulli `π x`); `n` units are i.i.d. (`Measure.pi`). `X_i = (ω i).1`, `T_i = (ω i).2`,
`Y0 = 0`, `Y1_i = y1 (ω i).1`, `μ0 = 0`, `μ1 = y1`, and the random baseline `μhat` is an
arbitrary parameter. At non-admissible policies the same formula is used with masses clipped at
`0` (`Real.toNNReal`); `Standing` makes no claim there. The mapper's T27 witness used
`Ω = Bool × Bool`; here `Ω = Fin 1 → Bool × Bool` (same law), so one construction serves both.

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P006/Wave1/BinaryExperiment/Nk.lean`.
`Sk` is the statement of node k; `Nk` is `Sk` with, as hypotheses, the statements it may use.
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

/-! ## Node statements -/

/-- **Statement S1** (mapper "binary_policy_unit_law": "the four atom masses (1/2)coinMass(π x)t
define a probability law with fair X marginal"): for admissible `π` the unit law is a
probability measure with the stated atoms and fair covariate marginal. Use
`coin_is_probability`, `Measure.coe_finset_sum`, `Measure.dirac_apply`, `Fintype.sum_prod_type`,
`Real.toNNReal` of a nonnegative number, and `Measure.map_apply` / `Measure.ext` on `Bool`. -/
def S1 : Prop :=
  ∀ π : Bool → ℝ, Admissible π →
    IsProbabilityMeasure (unitLaw π) ∧
    (∀ a : Bool × Bool, unitLaw π {a} = ENNReal.ofReal ((1 / 2) * coinMass (π a.1) a.2)) ∧
    (unitLaw π).map Prod.fst = fairLaw

/-- **Statement S2** (mapper §4 step 2, "expand the integral under νπ⊗νπ over x0,x1,t0,t1"):
on the finite product space every integral is the explicit weighted sum. Use `integral_fintype`
(all functions on a finite discrete space are integrable), `Measure.pi_pi` on singletons
(`Set.univ_pi_singleton`) and S1. -/
def S2 : Prop :=
  ∀ (n : ℕ) (π : Bool → ℝ), Admissible π → ∀ f : (Fin n → Bool × Bool) → ℝ,
    ∫ ω, f ω ∂(Measure.pi fun _ : Fin n => unitLaw π) =
      ∑ ω : Fin n → Bool × Bool, (∏ i, (1 / 2) * coinMass (π (ω i).1) (ω i).2) * f ω

/-- **Statement S3** (mapper §4 step 1, "Given X_i=x ... T_i is Bernoulli π(x)"): conditional
expectation given `σ(X_i)` of any function of unit `i`'s state. Use
`ae_eq_condExp_of_forall_setIntegral_eq` (the candidate is a function of `X_i`; every
`σ(X_i)`-measurable set is `X_i ⁻¹' B`), `measurePreserving_eval` / `Measure.pi_map_eval`
to reduce to the unit law, and S1. -/
def S3 : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (y1 : Bool → ℝ) (μhat : (Bool → ℝ) → (Fin n → Bool × Bool) → Bool → ℝ)
    (π : Bool → ℝ), Admissible π → ∀ (i : Fin n) (g : Bool × Bool → ℝ),
    ((binExp n hn y1 μhat).law π)[fun ω => g (ω i) | (binExp n hn y1 μhat).covariateSigma i]
      =ᵐ[(binExp n hn y1 μhat).law π]
      fun ω => ∑ t : Bool, coinMass (π (ω i).1) t * g ((ω i).1, t)

/-- **Statement S4** (mapper §4 step 1, "All functions on these finite discrete spaces are
measurable ... The units are independent and identically distributed by its definition ...
the full (X_i,Y0_i,Y1_i) law is identical across policies"): the ten non-conditional fields of
`Standing`. Measurability is `measurable_of_finite`/`measurable_of_countable` on the discrete
product; integrability is `Integrable.of_finite`; independence is `iIndepFun_pi` (with the
`IsProbabilityMeasure` instance from S1); identical distribution and the fixed potential law
follow from `Measure.pi_map_eval` and S1 (the triple is a function of `X_i` whose law is fair).
-/
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

/-- **Statement S5** (mapper §4 step 1, "Consequently the two conditional means, the Bernoulli
conditional moment and the all-Borel-set ignorability equality in Standing hold, including when
π(x)=0 or 1. Explicitly, for a Borel B the conditional left side is π(x)1{(0,μ1(x))∈B}"): the
three conditional fields of `Standing`. Each is S3 with an explicit `g` (`g = 0`,
`g (x,t) = y1 x`, `g (x,t) = bit t`, `g (x,t) = bit t · 1_B(0, y1 x)`, `g (x,t) = 1_B(0,y1 x)`)
followed by pointwise arithmetic (`coin_is_probability`). -/
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

/-! ## Nodes (`Nk` = statements it may use → `Sk`) -/

/-- Node N1 = S1. -/
def N1 : Prop := S1
/-- Node N2: may use S1. -/
def N2 : Prop := S1 → S2
/-- Node N3: may use S1. -/
def N3 : Prop := S1 → S3
/-- Node N4: may use S1. -/
def N4 : Prop := S1 → S4
/-- Node N5: may use S1, S3. -/
def N5 : Prop := S1 → S3 → S5

/-! ## Assembly of `Standing` -/

/-- **Shared assembly.** The nodes certify the frozen `Standing` predicate for every witness
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

/-- Sanity checks on the construction. -/
example (n : ℕ) (hn : 0 < n) (y1 : Bool → ℝ) (μhat : (Bool → ℝ) → (Fin n → Bool × Bool) → Bool → ℝ)
    (π : Bool → ℝ) (i : Fin n) (ω : Fin n → Bool × Bool) :
    (binExp n hn y1 μhat).observed π ω i = if (ω i).2 then y1 (ω i).1 else 0 := rfl
example (n : ℕ) (hn : 0 < n) (y1 : Bool → ℝ) (μhat : (Bool → ℝ) → (Fin n → Bool × Bool) → Bool → ℝ) :
    (binExp n hn y1 μhat).τ = fun x => y1 x - 0 := rfl
example (π : Bool → ℝ) : IsFiniteMeasure (unitLaw π) := inferInstance

end

end AronowAudit.P006.Wave1.BinaryExperiment
