import AronowAudit.P006.P006_CounterfactualMetrics

/-!
# Blueprint: P006-T13, corrected Theorem 2 on a bare measurable covariate domain

Wave 1, group P005-P006-P017-P023-P046-P047. Resolution `repair_and_prove` (mapper §3, accepted
by both referees with no fixes).

The frozen draft `AronowAudit.P006.T13_corrected_ranking` (line 1037) imposes a Borel topology
on `C`, a common support equality and a common sample space `Ω` for all agents. The repaired
`Target` (the mapper's `corrected_ranking_measurable`, unchanged) drops the topology and the
support equality and lets every agent have its own sample space `Ω k`; it keeps the corrected
domination `P0 ≪ P_X^(k)`, the unit-level normalised RN weight `referenceWeight`, common `μ0`,
reference integrability of `τ_k`, treated-evaluation unbiasedness and integrability of every
actual weighted reward summand, and states all five corrected clauses (i)–(v). The theorem is
universe polymorphic (`C : Type u`, `Ω k : Type v`).

Proof route (decision of the blueprint architect, no change of mathematics): the mapper's
truncation `min(g,b)` plus dominated convergence is unnecessary, because Mathlib's pull-out
`condExp_mul_of_stronglyMeasurable_left` needs only integrability of the product `g(X_i)·Z_i`
(supplied by `hreward`) and of `Z_i` (from `Standing`), with no boundedness of `g`.

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P006/Wave1/CorrectedRanking/Nk.lean`.
`Sk` is the statement of node k; `Nk` is `Sk` with, as hypotheses, the statements it may use.
Do not cite the admitted `T13_corrected_ranking`, `T6_corrected_TT` or `T7_...`.

Nonvacuity (referee 1): `K = 2`, `nk ≡ 1`, `C = Bool`, `Ω k = Bool × Bool` with fair `X` and
Bernoulli `π(X)` treatment, `P_X = P0` fair, `Y0 = μhat = μ0 = 0`, constant `Y1 = μ1 = 1/4`
resp. `3/4`; all hypotheses hold and the weight is `1`.
-/

set_option autoImplicit false

universe u v

namespace AronowAudit.P006.Wave1.CorrectedRanking

open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

/-! ## Target -/

/-- **Target (P006-T13, repaired).** Corrected Theorem 2 (PDF pp. 6, 20) on an arbitrary common
measurable covariate domain with agent-specific sample spaces (mapper's
`corrected_ranking_measurable`). -/
def Target : Prop :=
  ∀ {K : ℕ} {C : Type u} [MeasurableSpace C] {Ω : Fin K → Type v}
    [∀ k, MeasurableSpace (Ω k)]
    (nk : Fin K → ℕ) (E : (k : Fin K) → Experiment (Ω k) C (nk k))
    (P0 : Measure C) (_hP0 : IsProbabilityMeasure P0)
    (_hS : ∀ k, Standing (E k))
    (_hmu0 : ∀ j k, (E j).μ0 = (E k).μ0)
    (_hac : ∀ k, P0 ≪ (E k).PX)
    (_hτ : ∀ k, Integrable (E k).τ P0)
    (_hU : ∀ k, TreatedUnbiased (E k) (E k).μ0 {π | Admissible π})
    (_hreward : ∀ k π, Admissible π → ∀ i,
      Integrable (fun ω => ((E k).observed π ω i -
        (E k).μhat π ω ((E k).X i ω)) * bit ((E k).T π i ω) *
        referenceWeight (nk k) P0 (E k).PX ((E k).X i ω)) ((E k).law π)),
    (∀ k π, Admissible π →
      (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX) π =
        (nk k : ℝ)*(∫ x, (E k).τ x*π x*
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) ∧
      (nk k : ℝ)*(∫ x, (E k).τ x*π x*
          referenceWeight (nk k) P0 (E k).PX x ∂(E k).PX) =
        (∫ x, (E k).τ x*π x ∂P0)) ∧
    (∀ k, IsBest {π | Admissible π}
      ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (positiveRule (E k).τ) ∧
      bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, positivePart ((E k).τ x) ∂P0)) ∧
    UniformRankPreservation (fun _ => {π | Admissible π})
      (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
      (fun k => (E k).τ) ∧
    ((∀ k x, 0 ≤ (E k).τ x) →
      (∀ k, bestValue {π | Admissible π}
        ((E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX)) =
        (∫ x, (E k).τ x ∂P0)) ∧
      RelativeRankPreservation P0 (fun _ => {π | Admissible π})
        (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
        (fun k => (E k).τ))

/-! ## Node statements (per agent, except S3 and S6 which are generic) -/

/-- **Statement S1** (mapper §3 step 1, "The Standing ignorability equality applies to indicators
of every Borel subset of the potential-outcome pair ... Hence Eμ[T Y1|X]=π(X) μ1(X)"): lifting
the all-indicator ignorability field to the integrable test `Y1`. Suggested route (avoids simple
functions): for a `σ(X_i)`-set `A`, the two finite measures `B ↦ ∫_A T·1_B(Y0,Y1)` and
`B ↦ ∫_A π(X)·1_B(Y0,Y1)` on `ℝ × ℝ` agree on every measurable `B` (ignorability plus the
defining property of `condExp` with the bounded `σ(X_i)`-multiplier `1_A·π(X_i)`), hence are
equal (`Measure.ext`); integrate the coordinate `y1` against both (`integral_map`,
`integral_withDensity_eq_integral_toReal_smul`), then use `Standing.conditional_means` and
`ae_eq_condExp_of_forall_setIntegral_eq`. -/
def S1 : Prop :=
  ∀ {Ω : Type v} {C : Type u} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n), Standing E → ∀ π, Admissible π → ∀ i,
      (E.law π)[fun ω => bit (E.T π i ω) * E.Y1 i ω | E.covariateSigma i]
        =ᵐ[E.law π] fun ω => π (E.X i ω) * E.μ1 (E.X i ω)

/-- **Statement S2** (mapper §3 step 1, "Combining these facts yields, for Z_i=T_i(observed_i-
μhat(X_i)), Eμ[Z_i|X_i]=τ(X_i)π(X_i)"): uses S1, consistency (`T·observed = T·Y1` pointwise),
`TreatedUnbiased`, `Standing.bernoulli`, and the pull-out
`condExp_mul_of_stronglyMeasurable_left` for `μ0(X_i)·bit T_i` (integrable since
`|bit T| ≤ 1` and `μ0(X_i)` is integrable by `covariate_law`). -/
def S2 : Prop :=
  ∀ {Ω : Type v} {C : Type u} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n), Standing E → TreatedUnbiased E E.μ0 {π | Admissible π} →
    ∀ π, Admissible π → ∀ i,
      (E.law π)[fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) |
          E.covariateSigma i]
        =ᵐ[E.law π] fun ω => E.τ (E.X i ω) * π (E.X i ω)

/-- **Statement S3** (mapper §3 step 3, "Since n>0 and g=ρ/n, the Bochner RN formula for the
integrable Q-function τπ gives n∫ τπ g dP=∫ τπρ dP=∫ τπ dQ"): generic normalised
change of measure. Use `MeasureTheory.integrable_toReal_rnDeriv_mul_iff` and
`MeasureTheory.integral_toReal_rnDeriv_mul`. -/
def S3 : Prop :=
  ∀ {C : Type u} [MeasurableSpace C] (Q P : Measure C) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure P], Q ≪ P → ∀ n : ℕ, 0 < n → ∀ f : C → ℝ, Integrable f Q →
      Integrable (fun x => f x * referenceWeight n Q P x) P ∧
      (n : ℝ) * ∫ x, f x * referenceWeight n Q P x ∂P = ∫ x, f x ∂Q

/-- **Statement S4** (mapper §3 steps 2–3, "Eμ[g(X_i) Z_i]=∫ g(x)τ(x)π(x) dP(x) ... The actual
score is the finite sum of these n integrable weighted summands ... E[w_k]=n∫ τπ g dP"): the
first conjunct of `Target` for one agent. Uses S2 (with `integral_condExp` and the pull-out of
the `σ(X_i)`-measurable weight `referenceWeight n P0 E.PX (X_i)`; no boundedness needed),
`integral_finset_sum` (each summand integrable by `hreward`), `Standing.covariate_law`
(`IdentDistrib.integral_eq` after composing with the measurable `g·τ·π`), and S3 with
`f = τ·π` (`|τ π| ≤ |τ|`). -/
def S4 : Prop :=
  ∀ {Ω : Type v} {C : Type u} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (P0 : Measure C) [IsProbabilityMeasure P0],
    Standing E → P0 ≪ E.PX → Integrable E.τ P0 → TreatedUnbiased E E.μ0 {π | Admissible π} →
    (∀ π, Admissible π → ∀ i,
      Integrable (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) *
        referenceWeight n P0 E.PX (E.X i ω)) (E.law π)) →
    ∀ π, Admissible π →
      E.expectedWeightedTT (referenceWeight n P0 E.PX) π =
        (n : ℝ) * (∫ x, E.τ x * π x * referenceWeight n P0 E.PX x ∂E.PX) ∧
      (n : ℝ) * (∫ x, E.τ x * π x * referenceWeight n P0 E.PX x ∂E.PX) = ∫ x, E.τ x * π x ∂P0

/-- **Statement S5** (mapper §3 step 4, "π*(x)=1{τ(x)>0} is an admissible policy. For every
0≤π≤1, pointwise τ(x)π(x)≤max(τ(x),0)=τ(x)π*(x) ... its sSup equals that value"): the
second conjunct of `Target` for one agent. Uses S4, `pointwise_policy_gain_le`,
`integral_mono`, `bestValue_eq`; note `τ x * positiveRule τ x = positivePart (τ x)` by definition. -/
def S5 : Prop :=
  ∀ {Ω : Type v} {C : Type u} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (P0 : Measure C) [IsProbabilityMeasure P0],
    Standing E → P0 ≪ E.PX → Integrable E.τ P0 → TreatedUnbiased E E.μ0 {π | Admissible π} →
    (∀ π, Admissible π → ∀ i,
      Integrable (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) *
        referenceWeight n P0 E.PX (E.X i ω)) (E.law π)) →
    IsBest {π | Admissible π} (E.expectedWeightedTT (referenceWeight n P0 E.PX))
        (positiveRule E.τ) ∧
      bestValue {π | Admissible π} (E.expectedWeightedTT (referenceWeight n P0 E.PX)) =
        ∫ x, positivePart (E.τ x) ∂P0

/-- **Statement S6** (mapper §3 step 5, "If τj(x)≥τk(x) for all x, max(τj(x),0)≥max(τk(x),0).
Integrate against the same Q ... If all effects are nonnegative, positivePart(τk)=τk"): generic
ranking consequences of the best-value formula. Use `T14_corrected_rank_inequality`
(integrability of `positivePart ∘ τ` from `positivePart_eq_max` and `Integrable.pos_part`-type
lemmas). -/
def S6 : Prop :=
  ∀ {K : ℕ} {C : Type u} [MeasurableSpace C] (P0 : Measure C)
    (score : Fin K → (C → ℝ) → ℝ) (τ : Fin K → C → ℝ),
    (∀ k, Integrable (τ k) P0) →
    (∀ k, bestValue {π : C → ℝ | Admissible π} (score k) = ∫ x, positivePart (τ k x) ∂P0) →
    UniformRankPreservation (fun _ => {π : C → ℝ | Admissible π}) score τ ∧
    ((∀ k x, 0 ≤ τ k x) →
      (∀ k, bestValue {π : C → ℝ | Admissible π} (score k) = ∫ x, τ k x ∂P0) ∧
      RelativeRankPreservation P0 (fun _ => {π : C → ℝ | Admissible π}) score τ)

/-! ## Nodes (`Nk` = statements it may use → `Sk`) -/

/-- Node N1 = S1. -/
def N1 : Prop := S1.{u, v}
/-- Node N2: may use S1. -/
def N2 : Prop := S1.{u, v} → S2.{u, v}
/-- Node N3 = S3. -/
def N3 : Prop := S3.{u}
/-- Node N4: may use S2, S3. -/
def N4 : Prop := S2.{u, v} → S3.{u} → S4.{u, v}
/-- Node N5: may use S4. -/
def N5 : Prop := S4.{u, v} → S5.{u, v}
/-- Node N6 = S6. -/
def N6 : Prop := S6.{u}

/-! ## Assembly -/

/-- **Assembly.** The nodes prove the repaired theorem. -/
theorem assemble (h1 : N1.{u, v}) (h2 : N2.{u, v}) (h3 : N3.{u}) (h4 : N4.{u, v})
    (h5 : N5.{u, v}) (h6 : N6.{u}) : Target.{u, v} := by
  intro K C _ Ω _ nk E P0 hP0 hS _ hac hτ hU hreward
  have s4 : S4.{u, v} := h4 (h2 h1) h3
  have s5 : S5.{u, v} := h5 s4
  have hbest := fun k => s5 (E k) P0 (hS k) (hac k) (hτ k) (hU k) (hreward k)
  refine ⟨fun k π hπ => s4 (E k) P0 (hS k) (hac k) (hτ k) (hU k) (hreward k) π hπ,
    hbest, ?_⟩
  exact h6 P0 (fun k => (E k).expectedWeightedTT (referenceWeight (nk k) P0 (E k).PX))
    (fun k => (E k).τ) hτ (fun k => (hbest k).2)

/-- Specialisation check: the repaired statement implies the frozen draft's conclusion for a
common `Ω` (the frozen draft's extra topology and support premises are simply not needed).
Only the type of the frozen draft is read. -/
example (h : Target.{0, 0}) : type_of% @AronowAudit.P006.T13_corrected_ranking.{0, 0} := by
  intro K Ω C _ _ _ _ nk E P0 hP0 hS _ hmu0 hac hτ hU hreward
  exact h (Ω := fun _ => Ω) nk E P0 hP0 hS hmu0 hac hτ hU hreward

end

end AronowAudit.P006.Wave1.CorrectedRanking
