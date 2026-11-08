import AronowAudit.P047.P047_Identification
import Mathlib.MeasureTheory.Function.Floor

/-!
# Blueprint: P047-T3, unknown-propensity impossibility with randomized procedures

Wave 1, group P005-P006-P017-P023-P046-P047. Resolution `repair_and_prove` (mapper §9, accepted
by both referees with no fixes).

The frozen draft `AronowAudit.P047.unknown_propensity_impossibility` (line 870) covers only
deterministic procedures and finite ordered interval endpoints. The repaired `Target` (mapper's
`unknown_propensity_impossibility_randomized`) quantifies an arbitrary auxiliary seed `(R, Q)`
independent of the sample (procedures are measurable functions of observed sample and seed) and
measurable `EReal` endpoints (finite, unbounded or empty intervals); the class `UnknownModel`,
`observedSample`, `ate`, the constants and the single fixed `baselineLaw` are unchanged. The
`let`-bound risk/coverage functions of the mapper's statement are the named definitions
`randRisk`, `randStrictRisk`, `randCoverage`, `widthProb` below (`Target` is checked against the
literal `let` form by `Iff.rfl`). The width event is written with `((1/6 : ℝ) : EReal)`.

Construction (mapper §9): for `M + 1` equal cells of `(0,1]` (`cellLabel`) and a type vector
`σ : Fin (M+1) → Bool`, family laws `familyMeasure M family σ` are generated from three
independent uniforms `(W, V_A, V_Y)`: `A = 1{V_A ≤ e_σ(W)}`, `Y0 = 0`, `Y1 = 1{V_Y ≤ m_σ(W)}`
with `e = cellPropensity`, `m = cellMean`. Averaging over the fair type prior, the observed
`n`-sample laws of both families agree with the baseline on the no-collision event, so every
observed-data-and-seed event probability differs by at most `n(n-1)/(2(M+1))`.

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P047/Wave1/Impossibility/Nk.lean`.
`Sk` is the statement of node k; `Nk` is `Sk` with, as hypotheses, the statements it may use.
Do not use the admitted `unknown_propensity_impossibility`. Proved and usable:
`familyEffect_prior_concentration`, `familyEffect_eq_cell_average`, `familyEffect_bounds`,
`single_cell_observable_agreement`, `cell_overlap`, `cell_mean_bounds`,
`event_difference_of_agreement_on_good`, `uniform_labels_pair_collision`,
`iid_uniform_labels_collision`, `collision_union_bound`, `two_point_estimator_algebra`,
`two_point_interval_algebra`, `measurable_observed`, `measurable_potential`, `measurable_arm`,
`baseline_covariate_law`, `baseline_ate`, `measurable_baseline_map`, `highIndicator_mean`.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-! ## Risk, coverage and width with an auxiliary seed -/

/-- Worst-case `≥ η` error probability of a randomized estimator over `UnknownModel`
(zero inserted for the empty-class convention, as in `unknownRisk`). -/
def randRisk {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) : ℝ :=
  sSup (insert (0 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
    r = ((sampleLaw L.measure).prod Q).real
      {z | η ≤ |E n (observedSample n z.1, z.2) - ate L|}})

/-- Worst-case strict (`> η`) error probability. -/
def randStrictRisk {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) : ℝ :=
  sSup (insert (0 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
    r = ((sampleLaw L.measure).prod Q).real
      {z | η < |E n (observedSample n z.1, z.2) - ate L|}})

/-- Worst-case coverage of a randomized `EReal`-endpoint interval (one inserted, as in
`honestCoverage`). -/
def randCoverage {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) (n : ℕ) : ℝ :=
  sInf (insert (1 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
    r = ((sampleLaw L.measure).prod Q).real
      {z | lo n (observedSample n z.1, z.2) ≤ (ate L : EReal) ∧
        (ate L : EReal) ≤ hi n (observedSample n z.1, z.2)}})

/-- Probability under the fixed baseline (with the seed) that the width exceeds `1/6`,
written `lo + 1/6 < hi` in `EReal`. -/
def widthProb {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) (n : ℕ) : ℝ :=
  ((sampleLaw baselineLaw).prod Q).real
    {z | lo n (observedSample n z.1, z.2) + ((1 / 6 : ℝ) : EReal) < hi n (observedSample n z.1, z.2)}

/-! ## Target -/

/-- **Target (P047-T3, repaired).** Second bullet, pp. 85–86, with an arbitrary independent seed
and measurable extended-real endpoints (mapper's `unknown_propensity_impossibility_randomized`). -/
def Target : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q],
    (∀ E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ, (∀ n, Measurable (E n)) →
      (∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) ≤ randRisk Q E n (1 / 12)) ∧
      (∃ η : ℝ, 0 < η ∧ 0 < Filter.limsup (fun n => randStrictRisk Q E n η) atTop)) ∧
    (∀ lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal,
      (∀ n, Measurable (lo n)) → (∀ n, Measurable (hi n)) →
      ∀ α : ℝ, 0 < α → α < 1 / 2 →
        1 - α ≤ Filter.liminf (randCoverage Q lo hi) atTop →
        (1 - 2 * α ≤ Filter.liminf (widthProb Q lo hi) atTop) ∧ 0 < 1 - 2 * α)

/-- The mapper's literal statement with `let`-bound functions (endpoint constant written
`((1/6 : ℝ) : EReal)`). -/
def MapperStatement : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q],
    (∀ E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ,
      (∀ n, Measurable (E n)) →
      let risk := fun (n : ℕ) (η : ℝ) =>
        sSup (insert (0 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
          r = ((sampleLaw L.measure).prod Q).real
            {z | η ≤ |E n (observedSample n z.1, z.2) - ate L|}})
      let strictRisk := fun (n : ℕ) (η : ℝ) =>
        sSup (insert (0 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
          r = ((sampleLaw L.measure).prod Q).real
            {z | η < |E n (observedSample n z.1, z.2) - ate L|}})
      (∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) ≤ risk n (1 / 12)) ∧
      (∃ η : ℝ, 0 < η ∧
        0 < Filter.limsup (fun n => strictRisk n η) atTop)) ∧
    (∀ lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal,
      (∀ n, Measurable (lo n)) → (∀ n, Measurable (hi n)) →
      let coverage := fun n =>
        sInf (insert (1 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
          r = ((sampleLaw L.measure).prod Q).real
            {z | lo n (observedSample n z.1, z.2) ≤ (ate L : EReal) ∧
              (ate L : EReal) ≤ hi n (observedSample n z.1, z.2)}})
      ∀ α : ℝ, 0 < α → α < 1 / 2 →
        1 - α ≤ Filter.liminf coverage atTop →
        (1 - 2 * α ≤ Filter.liminf
          (fun n => ((sampleLaw baselineLaw).prod Q).real
            {z | lo n (observedSample n z.1, z.2) + ((1 / 6 : ℝ) : EReal) <
              hi n (observedSample n z.1, z.2)}) atTop) ∧
        0 < 1 - 2 * α)

/-- Fidelity check: `Target` is the mapper's statement, up to naming the `let`s. -/
example : Target.{u} ↔ MapperStatement.{u} := Iff.rfl

/-! ## The two-family construction -/

/-- Cell of `w` among the `M + 1` cells `(j/(M+1), (j+1)/(M+1)]` of `(0,1]` (any value outside
`(0,1]`, a null set, is sent to a cell by the same formula). -/
def cellLabel (M : ℕ) (w : ℝ) : Fin (M + 1) :=
  ⟨min M (⌈w * (M + 1)⌉₊ - 1), by omega⟩

/-- Cell propensity `e_σ(w) ∈ {1/4, 3/4}`. -/
def cellProp (M : ℕ) (σ : Fin (M + 1) → Bool) (w : ℝ) : ℝ := cellPropensity (σ (cellLabel M w))

/-- Cell outcome mean `m_σ(w)` of family `family` (`true` = A, `false` = B). -/
def cellMeanFn (M : ℕ) (family : Bool) (σ : Fin (M + 1) → Bool) (w : ℝ) : ℝ :=
  cellMean family (σ (cellLabel M w))

/-- The generator from three independent uniforms `(W, V_A, V_Y)`:
`(W, 1{V_A ≤ e(W)}, (0, 1{V_Y ≤ m(W)}))`. -/
def gen (e m : ℝ → ℝ) (z : ℝ × ℝ × ℝ) : UnitData :=
  (z.1, decide (z.2.1 ≤ e z.1), ((0 : ℝ), if z.2.2 ≤ m z.1 then (1 : ℝ) else 0))

/-- The generated unit law. -/
def genMeasure (e m : ℝ → ℝ) : Measure UnitData :=
  (uniform01.prod (uniform01.prod uniform01)).map (gen e m)

instance genMeasure_isProbabilityMeasure (e m : ℝ → ℝ) : IsProbabilityMeasure (genMeasure e m) := by
  unfold genMeasure; infer_instance

/-- The family law with type vector `σ`. -/
def familyMeasure (M : ℕ) (family : Bool) (σ : Fin (M + 1) → Bool) : Measure UnitData :=
  genMeasure (cellProp M σ) (cellMeanFn M family σ)

instance familyMeasure_isProbabilityMeasure (M : ℕ) (family : Bool) (σ : Fin (M + 1) → Bool) :
    IsProbabilityMeasure (familyMeasure M family σ) := by
  unfold familyMeasure; infer_instance

theorem measurable_cellLabel (M : ℕ) : Measurable (cellLabel M) :=
  (measurable_of_countable (fun k : ℕ => (⟨min M (k - 1), by omega⟩ : Fin (M + 1)))).comp
    (measurable_id.mul_const _).nat_ceil

theorem measurable_cellProp (M : ℕ) (σ : Fin (M + 1) → Bool) : Measurable (cellProp M σ) :=
  (measurable_of_countable (fun j : Fin (M + 1) => cellPropensity (σ j))).comp
    (measurable_cellLabel M)

theorem measurable_cellMeanFn (M : ℕ) (family : Bool) (σ : Fin (M + 1) → Bool) :
    Measurable (cellMeanFn M family σ) :=
  (measurable_of_countable (fun j : Fin (M + 1) => cellMean family (σ j))).comp
    (measurable_cellLabel M)

/-- The `σ(W)`-version of the joint-ignorability field of `UnknownModel`, stated for a bare
measure and propensity (`JointIgnorable L` is this for `L.measure`, `L.propensity`). -/
def JointIgnorableM (μ : Measure UnitData) (e : ℝ → ℝ) : Prop :=
  ∀ (a : Bool) (f : ℝ × ℝ → ℝ), Measurable f →
    Integrable (fun u => f (potential false u, potential true u)) μ →
    μ[fun u => arm a u * f (potential false u, potential true u) | covariateSigma] =ᵐ[μ]
      fun u => armPropensity e a u * (μ[fun v => f (potential false v, potential true v) |
        covariateSigma]) u

example (L : CausalLaw) : JointIgnorable L ↔ JointIgnorableM L.measure L.propensity := Iff.rfl

/-- The bundled family laws: every type vector of each family gives a member of `UnknownModel`
with the stated ATE. (Proved below from nodes N1–N5.) -/
def FamilyLaws : Prop :=
  ∀ (M : ℕ) (family : Bool) (σ : Fin (M + 1) → Bool), ∃ L : CausalLaw,
    L.measure = familyMeasure M family σ ∧ UnknownModel L ∧ ate L = familyEffect family (M + 1) σ

/-! ## Observed records -/

/-- The observed unit `(W, A, Y)`; `observedSample n s i = obsUnit (s i)`. -/
def obsUnit (u : UnitData) : ObservedUnit := (covariate u, u.2.1, observed u)

/-- The three observable records at covariate `w`: `k = 0` is `(A,Y) = (1,1)`, `k = 1` is
`(1,0)`, `k = 2` is `(0,0)`. -/
def record (w : ℝ) (k : Fin 3) : ObservedUnit :=
  (w, decide (k ≠ 2), if k = 0 then (1 : ℝ) else 0)

/-- Record probabilities given `W = w` for the generator: `(e m, e(1-m), 1-e)`. -/
def genQ (e m : ℝ → ℝ) (w : ℝ) (k : Fin 3) : ℝ :=
  if k = 0 then e w * m w else if k = 1 then e w * (1 - m w) else 1 - e w

/-- The common mixed record probabilities `(1/4, 1/4, 1/2)` (also those of the baseline). -/
def baseObs (k : Fin 3) : ℝ := if k = 2 then 1 / 2 else 1 / 4

example (M : ℕ) (family : Bool) (σ : Fin (M + 1) → Bool) :
    genQ (cellProp M σ) (cellMeanFn M family σ) =
      fun w k => cellObservable family (σ (cellLabel M w)) k := rfl

example (n : ℕ) (s : ℕ → UnitData) (i : Fin n) : observedSample n s i = obsUnit (s i) := rfl

/-! ## Node statements -/

/-- **Statement S1** (mapper §9 step 3 and node `uniform_cell_label`, "Partition (0,1] into the M
intervals I_j ... each of uniform probability 1/M"): each cell has `uniform01`-mass
`1/(M+1)`. Identify `{w ∈ (0,1] | cellLabel M w = j}` with `Ioc (j/(M+1)) ((j+1)/(M+1))`
(`Nat.ceil_eq_iff`), then `Real.volume_Ioc`. -/
def S1 : Prop :=
  ∀ (M : ℕ) (j : Fin (M + 1)), uniform01 {w | cellLabel M w = j} = ENNReal.ofReal (1 / (M + 1 : ℝ))

/-- **Statement S2** (mapper §9 step 1, "for any f on the potential-outcome pair the conditional
expectation is (1-mσ(W))f(0,0)+mσ(W)f(0,1), and the arm-weighted version is this expression
multiplied by eσ(W) or 1-eσ(W). These finite conditional formulas follow by Fubini for every
bounded test of W"): conditional expectation given `W` of any measurable function of
`(A, Y0, Y1)` under the generated law. Use `ae_eq_condExp_of_forall_setIntegral_eq`
(`covariateSigma`-sets are `covariate ⁻¹' B`), `integral_map`, `integral_prod`, and
`P(V ≤ p) = p` under `uniform01` for `p ∈ [0,1]`; `g ∘ (·).2` is integrable because it is a.e.
one of four values. -/
def S2 : Prop :=
  ∀ (e m : ℝ → ℝ), Measurable e → Measurable m → (∀ w, 0 ≤ e w ∧ e w ≤ 1) →
    (∀ w, 0 ≤ m w ∧ m w ≤ 1) → ∀ g : Bool × ℝ × ℝ → ℝ, Measurable g →
      (genMeasure e m)[fun u => g u.2 | covariateSigma] =ᵐ[genMeasure e m] fun u =>
        e u.1 * m u.1 * g (true, 0, 1) + e u.1 * (1 - m u.1) * g (true, 0, 0) +
          (1 - e u.1) * m u.1 * g (false, 0, 1) + (1 - e u.1) * (1 - m u.1) * g (false, 0, 0)

/-- **Statement S3** (mapper §9 step 1, "Thus they establish both Ignorable for CausalLaw and
JointIgnorable for UnknownModel, not merely mean ignorability"): both ignorability fields for
the generated law, from S2 (apply S2 to `g = 1{b = a}·f(...)` and to `g = f(...)`, then
`filter_upwards` and `ring`). -/
def S3 : Prop :=
  ∀ (e m : ℝ → ℝ), Measurable e → Measurable m → (∀ w, 0 ≤ e w ∧ e w ≤ 1) →
    (∀ w, 0 ≤ m w ∧ m w ≤ 1) → Ignorable (genMeasure e m) e ∧ JointIgnorableM (genMeasure e m) e

/-- **Statement S4** (mapper §9 step 1, "W has the exact uniform01 law. Outcomes are binary and
eσ∈[1/4,3/4] everywhere"): the remaining `UnknownModel` facts and the ATE as the
`uniform01`-integral of `m`. Use `Measure.map_map`, `Measure.map_fst_prod`, `ae_map_iff`,
`integral_map`, `integral_prod` (inner `∫ 1{v ≤ m w} dv = m w`). -/
def S4 : Prop :=
  ∀ (e m : ℝ → ℝ), Measurable e → Measurable m → (∀ w, 1 / 4 ≤ e w ∧ e w ≤ 3 / 4) →
    (∀ w, 0 ≤ m w ∧ m w ≤ 1) →
    (genMeasure e m).map covariate = uniform01 ∧
    (∀ a, ∀ᵐ u ∂(genMeasure e m), potential a u = 0 ∨ potential a u = 1) ∧
    (∀ᵐ u ∂(genMeasure e m), (1 / 4 : ℝ) ≤ e (covariate u) ∧ e (covariate u) ≤ 3 / 4) ∧
    (∫ u, potential true u - potential false u ∂(genMeasure e m)) = ∫ w, m w ∂uniform01

/-- **Statement S5** (mapper §9 step 2, "integrating over the equal-length cells gives
θ_A(σ)=1-(2/3)U_M, θ_B(σ)=(2/3)U_M"): the family ATE. Split `uniform01` over the cells (S1,
`MeasureTheory.integral_fintype`-style decomposition via `integral_finset_biUnion` or the
pushforward `uniform01.map (cellLabel M)`), then `familyEffect_eq_cell_average`. -/
def S5 : Prop :=
  ∀ (M : ℕ) (family : Bool) (σ : Fin (M + 1) → Bool),
    (∫ w, cellMeanFn M family σ w ∂uniform01) = familyEffect family (M + 1) σ

/-- **Statement S6** (mapper §9 step 3, iid structure): the observed `n`-sample of an i.i.d.
sample has the product law of the one-unit observed law. Use
`Measure.infinitePi_map_restrict` (first `n` coordinates), `Measure.map_map`,
`Measure.pi_map_pi` and the measurability of `obsUnit` (`measurable_observed`). -/
def S6 : Prop :=
  ∀ (μ : Measure UnitData) [IsProbabilityMeasure μ] (n : ℕ),
    (sampleLaw μ).map (observedSample n) = Measure.pi (fun _ : Fin n => μ.map obsUnit)

/-- **Statement S7** (mapper §9 step 3, "Conditional on the complete vector w, the observable
(A_i,Y_i) probabilities in a cell are (e m, e(1-m), 1-e)"): the product of "uniform `W`, then
record `k` with probability `q(W,k)`" laws has the `n`-fold record formula. Suggested route:
identify `ν` with `((uniform01.prod Measure.count).withDensity (q · ·)).map record` by
`Measure.ext_of_generateFrom`-free `Measure.ext` (both finite, equal on measurable sets), push
`Measure.pi` through the map and the density (`Measure.pi_map_pi`, `Measure.pi` of
`withDensity`), then Fubini over the finite factor `Fin n → Fin 3`. -/
def S7 : Prop :=
  ∀ (ν : Measure ObservedUnit) [IsProbabilityMeasure ν] (q : ℝ → Fin 3 → ℝ),
    (∀ k, Measurable fun w => q w k) → (∀ w k, 0 ≤ q w k) →
    (∀ B : Set ObservedUnit, MeasurableSet B →
      ν.real B = ∫ w, ∑ k, q w k * B.indicator (fun _ => (1 : ℝ)) (record w k) ∂uniform01) →
    ∀ (n : ℕ) (E : Set (Fin n → ObservedUnit)), MeasurableSet E →
      (Measure.pi fun _ : Fin n => ν).real E =
        ∫ w, ∑ k : Fin n → Fin 3, (∏ i, q (w i) (k i)) *
          E.indicator (fun _ => (1 : ℝ)) (fun i => record (w i) (k i))
          ∂(Measure.pi fun _ : Fin n => uniform01)

/-- **Statement S8** (mapper §9 step 3, one unit of a family): the one-unit observed law of the
generated law is "uniform `W`, then record `k` with probability `genQ e m W k`". Use
`Measure.map_map`, `integral_map`, `integral_prod` (two inner uniform integrals). -/
def S8 : Prop :=
  ∀ (e m : ℝ → ℝ), Measurable e → Measurable m → (∀ w, 0 ≤ e w ∧ e w ≤ 1) →
    (∀ w, 0 ≤ m w ∧ m w ≤ 1) → ∀ B : Set ObservedUnit, MeasurableSet B →
      ((genMeasure e m).map obsUnit).real B =
        ∫ w, ∑ k, genQ e m w k * B.indicator (fun _ => (1 : ℝ)) (record w k) ∂uniform01

/-- **Statement S9** (mapper §9 step 3, "These are exactly S's conditional observable
probabilities, independent of w"): the baseline's one-unit observed law is "uniform `W`, then
record `k` with probability `baseObs k`". Unfold `baselineLaw`, use `integral_map`
(`measurable_baseline_map`), `integral_prod` and `fairBool` (`bernoulliMeasure`) integrals. -/
def S9 : Prop :=
  ∀ B : Set ObservedUnit, MeasurableSet B →
    (baselineLaw.map obsUnit).real B =
      ∫ w, ∑ k, baseObs k * B.indicator (fun _ => (1 : ℝ)) (record w k) ∂uniform01

/-- **Statement S10** (mapper §9 step 3, "On G the n cell labels are different, so the n used
prior coordinates are independent; averaging the PRODUCT of their observable probabilities is
therefore the product of these common means"): finite prior averaging on distinct cells. Use
`Finset.prod_univ_sum`/`Fintype.prod_sum`-type factorisation over `σ` (the coordinates
`σ (c i)` are distinct) and `single_cell_observable_agreement`. -/
def S10 : Prop :=
  ∀ (M : ℕ) (family : Bool) (n : ℕ) (c : Fin n → Fin (M + 1)), Function.Injective c →
    ∀ k : Fin n → Fin 3,
      ∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) * ∏ i, cellObservable family (σ (c i)) (k i) =
        ∏ i, baseObs (k i)

/-- **Statement S11** (mapper §9 step 3, "A particular pair has equal labels with probability
M*(1/M)²=1/M. Union over the n(n-1)/2 pairs gives Pr(Gᶜ)≤d"): the collision bound for i.i.d.
uniform covariates. Use S1, `iIndepFun_pi`, `uniform_labels_pair_collision` /
`collision_union_bound` (or a direct union bound over pairs). -/
def S11 : Prop :=
  ∀ (M n : ℕ),
    (Measure.pi fun _ : Fin n => uniform01).real
        {w | ¬ Function.Injective (fun i => cellLabel M (w i))} ≤
      (n : ℝ) * (n - 1) / (2 * (M + 1))

/-- **Statement S12** (mapper §9 step 3, "It follows that B_A, B_B and S^n have the same
conditional probability ... |B_F(E)-S^n(E)|≤d"): the seedless transfer between each family
mixture and the baseline, for every measurable observed-sample event. From S6–S9 both sides
are `∫ w, Σ_k (·) 1_E` over `(0,1]^n`; on the no-collision set the integrands agree (S10); both
integrands lie in `[0,1]`; bound the difference by S11. -/
def S12 : Prop :=
  ∀ (M : ℕ) (family : Bool) (n : ℕ) (E : Set (Fin n → ObservedUnit)), MeasurableSet E →
    |∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) *
        (sampleLaw (familyMeasure M family σ)).real {s | observedSample n s ∈ E} -
      (sampleLaw baselineLaw).real {s | observedSample n s ∈ E}| ≤
      (n : ℝ) * (n - 1) / (2 * (M + 1))

/-- **Statement S13** (mapper §9 step 3, "Adding the independent seed preserves all equalities
and bounds: condition on the seed and integrate the corresponding event sections"): the
transfer with an arbitrary independent seed. Use `Measure.prod_apply` (sections
`{o | (o, r) ∈ E}` are measurable), `Measure.map_apply` for `observedSample n`, linearity of the
`Q`-integral of the finite mixture, and S12 inside the integral. -/
def S13 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (M : ℕ) (family : Bool) (n : ℕ) (E : Set ((Fin n → ObservedUnit) × R)), MeasurableSet E →
    |∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) *
        ((sampleLaw (familyMeasure M family σ)).prod Q).real
          {z | (observedSample n z.1, z.2) ∈ E} -
      ((sampleLaw baselineLaw).prod Q).real {z | (observedSample n z.1, z.2) ∈ E}| ≤
      (n : ℝ) * (n - 1) / (2 * (M + 1))

/-- **Statement S14** (mapper §9 step 2, "Chebyshev gives, in each family,
Pr_prior(|θ_F-center_F|≥1/12)≤16/M"): the prior concentration as a finite sum. From
`familyEffect_prior_concentration` at `M + 1` and `typePrior (M+1) {σ} = (1/2)^(M+1)`
(`Measure.pi_pi`, `fairBool` singleton masses). -/
def S14 : Prop :=
  ∀ (family : Bool) (M : ℕ),
    ∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) *
        (if (1 / 12 : ℝ) ≤ |familyEffect family (M + 1) σ - familyCenter family| then 1 else 0) ≤
      16 / (M + 1)

/-- **Statement S15** (mapper §9 step 4, "Under A, on the good-type event and the complementary
error event, estimate>1/2. Hence B_A(E)≥1-r-16/M. Under B, ... B_B(E)≤r+16/M ... Therefore
r≥1/2-16/M-n(n-1)/(4M)"; constant here from `|B_F - S| ≤ d` for each family): the finite-`M`
minimax bound. Test event `{(o, ρ) | 1/2 ≤ E n (o, ρ)}`; each family law is in `UnknownModel`
(`FamilyLaws`), so its error probability is `≤ randRisk` (`le_csSup`, bounded by `1`);
combine S13 (twice, through the baseline) and S14; `two_point_estimator_algebra`-style
arithmetic. -/
def S15 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ), (∀ n, Measurable (E n)) →
    ∀ n : ℕ, 1 ≤ n → ∀ M : ℕ,
      (1 / 2 : ℝ) - 16 / (M + 1) - (n : ℝ) * (n - 1) / (2 * (M + 1)) ≤ randRisk Q E n (1 / 12)

/-- **Statement S16** (mapper §9 step 4, "Let M grow, or use the Archimedean property to
contradict any r<1/2"): generic limit step. -/
def S16 : Prop :=
  ∀ (r C : ℝ), (∀ M : ℕ, (1 / 2 : ℝ) - C / (M + 1) ≤ r) → (1 / 2 : ℝ) ≤ r

/-- **Statement S17** (mapper §9 step 4, "the strict risk at η=1/24 is at least 1/2 for every
n≥1. Its limsup is therefore at least 1/2>0"): `randRisk (1/12) ≤ randStrictRisk (1/24)`
(event inclusion, `csSup_le`/`le_csSup`, both bounded by `1`), then
`Filter.le_limsup_of_frequently_le` with boundedness. -/
def S17 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ), (∀ n, Measurable (E n)) →
    (∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) ≤ randRisk Q E n (1 / 12)) →
    ∃ η : ℝ, 0 < η ∧ 0 < Filter.limsup (fun n => randStrictRisk Q E n η) atTop

/-- **Statement S18** (mapper §9 step 5, "Good-type coverage implies D_F, so B_F(D_F)≥c_n-16/M.
The two transfers in step 3 give (S^n⊗Q)(D_A), (S^n⊗Q)(D_B) ≥ c_n-16/M-d. The intersection
probability is at least 2c_n-1-32/M-2d ... lo+1/6<hi in EReal"): the finite-`M` width bound.
Bands: under family A with good type, coverage forces `7/12 < hi`; under B, `lo < 5/12`;
both together force `lo + 1/6 < hi` in `EReal` (`EReal.add_lt_add`-type reasoning, including
`lo = ⊥`); `two_point_interval_algebra`-style arithmetic. -/
def S18 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal),
    (∀ n, Measurable (lo n)) → (∀ n, Measurable (hi n)) →
    ∀ (n M : ℕ),
      2 * randCoverage Q lo hi n - 1 - 32 / (M + 1) - (n : ℝ) * (n - 1) / (M + 1) ≤
        widthProb Q lo hi n

/-- **Statement S19** (mapper §9 step 5, "q_n≥2c_n-1 exactly. If liminf c_n≥1-α, then for every
ε>0, eventually c_n≥1-α-ε ... Hence liminf q_n≥1-2α"): generic limit step for bounded
sequences (`Filter.le_liminf_of_le`, `Filter.liminf_le_liminf`, boundedness from `[0,1]`). -/
def S19 : Prop :=
  ∀ (c q : ℕ → ℝ), (∀ n, 0 ≤ c n ∧ c n ≤ 1) → (∀ n, 0 ≤ q n ∧ q n ≤ 1) →
    (∀ n M : ℕ, 2 * c n - 1 - 32 / (M + 1) - (n : ℝ) * (n - 1) / (M + 1) ≤ q n) →
    ∀ α : ℝ, 0 < α → α < 1 / 2 → 1 - α ≤ Filter.liminf c atTop →
      (1 - 2 * α ≤ Filter.liminf q atTop) ∧ 0 < 1 - 2 * α

/-- **Statement S20** (mapper §9 step 5, "Its inserted one does not affect a nonempty infimum,
and 0≤c_n≤1"): coverage and width probabilities lie in `[0,1]`. -/
def S20 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) (n : ℕ),
    (0 ≤ randCoverage Q lo hi n ∧ randCoverage Q lo hi n ≤ 1) ∧
    (0 ≤ widthProb Q lo hi n ∧ widthProb Q lo hi n ≤ 1)

/-! ## Nodes (`Nk` = statements it may use → `Sk`) -/

/-- Node N1 = S1. -/
def N1 : Prop := S1
/-- Node N2 = S2. -/
def N2 : Prop := S2
/-- Node N3: may use S2. -/
def N3 : Prop := S2 → S3
/-- Node N4 = S4. -/
def N4 : Prop := S4
/-- Node N5: may use S1. -/
def N5 : Prop := S1 → S5
/-- Node N6 = S6. -/
def N6 : Prop := S6
/-- Node N7 = S7. -/
def N7 : Prop := S7
/-- Node N8 = S8. -/
def N8 : Prop := S8
/-- Node N9 = S9. -/
def N9 : Prop := S9
/-- Node N10 = S10. -/
def N10 : Prop := S10
/-- Node N11: may use S1. -/
def N11 : Prop := S1 → S11
/-- Node N12: may use S6, S7, S8, S9, S10, S11. -/
def N12 : Prop := S6 → S7 → S8 → S9 → S10 → S11 → S12
/-- Node N13: may use S12. -/
def N13 : Prop := S12 → S13.{u}
/-- Node N14 = S14. -/
def N14 : Prop := S14
/-- Node N15: may use `FamilyLaws`, S13, S14. -/
def N15 : Prop := FamilyLaws → S13.{u} → S14 → S15.{u}
/-- Node N16 = S16 (generic). -/
def N16 : Prop := S16
/-- Node N17 = S17. -/
def N17 : Prop := S17.{u}
/-- Node N18: may use `FamilyLaws`, S13, S14. -/
def N18 : Prop := FamilyLaws → S13.{u} → S14 → S18.{u}
/-- Node N19 = S19 (generic). -/
def N19 : Prop := S19
/-- Node N20 = S20. -/
def N20 : Prop := S20.{u}

/-! ## Assembly -/

/-- The family laws from nodes 2–5 (node 5 uses S1) (bundling into `CausalLaw`). -/
theorem familyLaws_of (s3 : S3) (s4 : S4) (s5 : S5) : FamilyLaws := by
  intro M family σ
  have he := measurable_cellProp M σ
  have hm := measurable_cellMeanFn M family σ
  have hb : ∀ w, 1 / 4 ≤ cellProp M σ w ∧ cellProp M σ w ≤ 3 / 4 := fun w =>
    cell_overlap (σ (cellLabel M w))
  have hb' : ∀ w, 0 ≤ cellProp M σ w ∧ cellProp M σ w ≤ 1 := fun w =>
    ⟨by linarith [(hb w).1], by linarith [(hb w).2]⟩
  have hmb : ∀ w, 0 ≤ cellMeanFn M family σ w ∧ cellMeanFn M family σ w ≤ 1 := fun w =>
    cell_mean_bounds family (σ (cellLabel M w))
  obtain ⟨hI, hJ⟩ := s3 _ _ he hm hb' hmb
  obtain ⟨hcov, hbin, hov, hate⟩ := s4 _ _ he hm hb hmb
  refine ⟨⟨familyMeasure M family σ, inferInstance, cellProp M σ, he, hI⟩, rfl,
    ⟨hcov, hJ, hbin, hov⟩, ?_⟩
  change (∫ u, potential true u - potential false u ∂(familyMeasure M family σ)) = _
  rw [show familyMeasure M family σ = genMeasure (cellProp M σ) (cellMeanFn M family σ) from rfl,
    hate, s5 M family σ]

/-- **Assembly.** The nodes prove the repaired theorem. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11) (h12 : N12) (h13 : N13.{u}) (h14 : N14)
    (h15 : N15.{u}) (h16 : N16) (h17 : N17.{u}) (h18 : N18.{u}) (h19 : N19) (h20 : N20.{u}) :
    Target.{u} := by
  have hF : FamilyLaws := familyLaws_of (h3 h2) h4 (h5 h1)
  have s13 : S13.{u} := h13 (h12 h6 h7 h8 h9 h10 (h11 h1))
  have s15 : S15.{u} := h15 hF s13 h14
  have s18 : S18.{u} := h18 hF s13 h14
  intro R _ Q _
  constructor
  · intro E hE
    have hrisk : ∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) ≤ randRisk Q E n (1 / 12) := by
      intro n hn
      refine h16 _ (16 + (n : ℝ) * (n - 1) / 2) (fun M => ?_)
      have hM := s15 Q E hE n hn M
      have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
      have heq : (16 + (n : ℝ) * (n - 1) / 2) / ((M : ℝ) + 1) =
          16 / ((M : ℝ) + 1) + (n : ℝ) * (n - 1) / (2 * ((M : ℝ) + 1)) := by
        field_simp
      linarith
    exact ⟨hrisk, h17 Q E hE hrisk⟩
  · intro lo hi hlo hhi α hα hα2 hcov
    exact h19 (randCoverage Q lo hi) (widthProb Q lo hi) (fun n => (h20 Q lo hi n).1)
      (fun n => (h20 Q lo hi n).2) (fun n M => s18 Q lo hi hlo hhi n M) α hα hα2 hcov

/-- Sanity check: `FamilyLaws` is consistent with the existing finite construction, i.e. the
family ATE is the existing `familyEffect` at `M + 1` cells, whose prior centres are `2/3`, `1/3`. -/
example : familyCenter true = 2 / 3 ∧ familyCenter false = 1 / 3 := ⟨rfl, rfl⟩

end

end AronowAudit.P047.Wave1.Impossibility
