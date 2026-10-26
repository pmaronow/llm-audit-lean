import AronowAudit.P047.P047_Identification
import Mathlib.MeasureTheory.Function.Floor

/-!
# P047-T3: unknown-propensity impossibility with randomized procedures

`Target` quantifies an arbitrary auxiliary seed `(R, Q)` independent of the
sample. Procedures are measurable functions of the observed sample and seed.
Interval endpoints are measurable `EReal` functions, allowing finite,
unbounded or empty intervals. The definitions `randRisk`, `randStrictRisk`,
`randCoverage` and `widthProb` express the risk, coverage and width
probabilities over `UnknownModel`, with the fixed `baselineLaw`.
The width event is `lo + ((1/6 : ℝ) : EReal) < hi`.

For `M + 1` equal cells of `(0,1]` and a type vector
`σ : Fin (M+1) → Bool`, the family laws `familyMeasure M family σ` are
generated from three independent uniforms `(W, V_A, V_Y)`:
`A = 1{V_A ≤ e_σ(W)}`, `Y0 = 0`, `Y1 = 1{V_Y ≤ m_σ(W)}`,
with `e = cellPropensity`, `m = cellMean`. Averaging over the fair type prior,
the observed n-sample laws of both families agree with the baseline on the
no-collision event. Each observed-data-and-seed event probability therefore
differs by at most `n(n-1)/(2(M+1))`.

`Sk` denotes statement k; `Nk` expresses the implication from its hypotheses
to `Sk`.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-! ## Risk, coverage and width with an auxiliary seed -/

/-- Worst-case `≥ η` error probability of a randomized estimator over `UnknownModel`,
with zero inserted for the empty-class convention. -/
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

/-- Worst-case coverage of a randomized `EReal`-endpoint interval,
with one inserted for the empty-class convention. -/
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

/-- Target P047-T3: second bullet, pp. 85–86, with an arbitrary independent
seed and measurable extended-real endpoints. -/
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

/-- Every type vector of each family gives a member of `UnknownModel`
with the stated ATE. -/
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

/-! ## Mathematical statements -/

/-- S1: each cell has `uniform01`-mass `1/(M+1)`.
On `(0,1]`, the fibre of `cellLabel M` at j is
`Ioc (j/(M+1)) ((j+1)/(M+1))`, whose length is `1/(M+1)`. -/
def S1 : Prop :=
  ∀ (M : ℕ) (j : Fin (M + 1)), uniform01 {w | cellLabel M w = j} = ENNReal.ofReal (1 / (M + 1 : ℝ))

/-- S2: conditional expectation given W of any measurable function of
(A,Y0,Y1) under the generated law. Fubini gives the finite conditional
table from P(V≤p)=p for uniform V and p∈[0,1]. The test function is
integrable because the three binary coordinates take only four possible
combinations under the generator. -/
def S2 : Prop :=
  ∀ (e m : ℝ → ℝ), Measurable e → Measurable m → (∀ w, 0 ≤ e w ∧ e w ≤ 1) →
    (∀ w, 0 ≤ m w ∧ m w ≤ 1) → ∀ g : Bool × ℝ × ℝ → ℝ, Measurable g →
      (genMeasure e m)[fun u => g u.2 | covariateSigma] =ᵐ[genMeasure e m] fun u =>
        e u.1 * m u.1 * g (true, 0, 1) + e u.1 * (1 - m u.1) * g (true, 0, 0) +
          (1 - e u.1) * m u.1 * g (false, 0, 1) + (1 - e u.1) * (1 - m u.1) * g (false, 0, 0)

/-- S3: armwise and joint ignorability for the generated law follow
from S2, applied to an arm-weighted outcome test and to the outcome test. -/
def S3 : Prop :=
  ∀ (e m : ℝ → ℝ), Measurable e → Measurable m → (∀ w, 0 ≤ e w ∧ e w ≤ 1) →
    (∀ w, 0 ≤ m w ∧ m w ≤ 1) → Ignorable (genMeasure e m) e ∧ JointIgnorableM (genMeasure e m) e

/-- S4: W has the uniform law, outcomes are binary, and the ATE is the
`uniform01` integral of m. The inner uniform integral of 1{v≤m(w)} is m(w). -/
def S4 : Prop :=
  ∀ (e m : ℝ → ℝ), Measurable e → Measurable m → (∀ w, 1 / 4 ≤ e w ∧ e w ≤ 3 / 4) →
    (∀ w, 0 ≤ m w ∧ m w ≤ 1) →
    (genMeasure e m).map covariate = uniform01 ∧
    (∀ a, ∀ᵐ u ∂(genMeasure e m), potential a u = 0 ∨ potential a u = 1) ∧
    (∀ᵐ u ∂(genMeasure e m), (1 / 4 : ℝ) ≤ e (covariate u) ∧ e (covariate u) ≤ 3 / 4) ∧
    (∫ u, potential true u - potential false u ∂(genMeasure e m)) = ∫ w, m w ∂uniform01

/-- S5: integrating over the equal-length cells gives the family ATEs
θ_A(σ)=1-(2/3)U and θ_B(σ)=(2/3)U. S1 identifies the finite pushforward
of the cell label, and `familyEffect_eq_cell_average` gives these expressions. -/
def S5 : Prop :=
  ∀ (M : ℕ) (family : Bool) (σ : Fin (M + 1) → Bool),
    (∫ w, cellMeanFn M family σ w ∂uniform01) = familyEffect family (M + 1) σ

/-- S6: the observed n-sample from an i.i.d. sample has the product law
of the one-unit observed law, by restriction to the first n coordinates
and pushforward through the measurable observation map. -/
def S6 : Prop :=
  ∀ (μ : Measure UnitData) [IsProbabilityMeasure μ] (n : ℕ),
    (sampleLaw μ).map (observedSample n) = Measure.pi (fun _ : Fin n => μ.map obsUnit)

/-- S7: a product of laws obtained by drawing uniform W and then record k
with probability q(W,k) has the n-fold record formula. The joint law is
a density with respect to uniform measure times counting measure,
pushed through `record`; finite summation and Fubini give the event formula. -/
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

/-- S8: the generated one-unit observed law is uniform W followed by
record k with probability `genQ e m W k`. The two inner uniform integrals
give these record probabilities. -/
def S8 : Prop :=
  ∀ (e m : ℝ → ℝ), Measurable e → Measurable m → (∀ w, 0 ≤ e w ∧ e w ≤ 1) →
    (∀ w, 0 ≤ m w ∧ m w ≤ 1) → ∀ B : Set ObservedUnit, MeasurableSet B →
      ((genMeasure e m).map obsUnit).real B =
        ∫ w, ∑ k, genQ e m w k * B.indicator (fun _ => (1 : ℝ)) (record w k) ∂uniform01

/-- S9: the baseline one-unit observed law is uniform W followed by
record k with probability `baseObs k`, independent of W. -/
def S9 : Prop :=
  ∀ B : Set ObservedUnit, MeasurableSet B →
    (baselineLaw.map obsUnit).real B =
      ∫ w, ∑ k, baseObs k * B.indicator (fun _ => (1 : ℝ)) (record w k) ∂uniform01

/-- S10: finite prior averaging on distinct cells. The selected type
coordinates are independent, so the average of the product of observable
probabilities equals the product of their common means. -/
def S10 : Prop :=
  ∀ (M : ℕ) (family : Bool) (n : ℕ) (c : Fin n → Fin (M + 1)), Function.Injective c →
    ∀ k : Fin n → Fin 3,
      ∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) * ∏ i, cellObservable family (σ (c i)) (k i) =
        ∏ i, baseObs (k i)

/-- S11: the collision bound for i.i.d. uniform covariates. Each pair
has equal cell labels with probability 1/(M+1); the union bound over
n(n-1)/2 pairs gives n(n-1)/(2(M+1)). -/
def S11 : Prop :=
  ∀ (M n : ℕ),
    (Measure.pi fun _ : Fin n => uniform01).real
        {w | ¬ Function.Injective (fun i => cellLabel M (w i))} ≤
      (n : ℝ) * (n - 1) / (2 * (M + 1))

/-- S12: transfer between each family mixture and the baseline for every
measurable observed-sample event. Both probabilities have the integral
record formula from S6–S9. On the no-collision set the integrands agree
by S10; both lie in [0,1], so S11 bounds the difference. -/
def S12 : Prop :=
  ∀ (M : ℕ) (family : Bool) (n : ℕ) (E : Set (Fin n → ObservedUnit)), MeasurableSet E →
    |∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) *
        (sampleLaw (familyMeasure M family σ)).real {s | observedSample n s ∈ E} -
      (sampleLaw baselineLaw).real {s | observedSample n s ∈ E}| ≤
      (n : ℝ) * (n - 1) / (2 * (M + 1))

/-- S13: adding an arbitrary independent seed preserves the event
probability bound. Conditioning on the seed, applying S12 to each
measurable event section, and integrating gives the result. -/
def S13 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (M : ℕ) (family : Bool) (n : ℕ) (E : Set ((Fin n → ObservedUnit) × R)), MeasurableSet E →
    |∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) *
        ((sampleLaw (familyMeasure M family σ)).prod Q).real
          {z | (observedSample n z.1, z.2) ∈ E} -
      ((sampleLaw baselineLaw).prod Q).real {z | (observedSample n z.1, z.2) ∈ E}| ≤
      (n : ℝ) * (n - 1) / (2 * (M + 1))

/-- S14: prior concentration as a finite sum. For each family,
P(|θ_F-center_F|≥1/12)≤16/(M+1). Each point mass of the fair product
prior is (1/2)^(M+1). -/
def S14 : Prop :=
  ∀ (family : Bool) (M : ℕ),
    ∑ σ : Fin (M + 1) → Bool, (1 / 2 : ℝ) ^ (M + 1) *
        (if (1 / 12 : ℝ) ≤ |familyEffect family (M + 1) σ - familyCenter family| then 1 else 0) ≤
      16 / (M + 1)

/-- S15: the finite-M minimax bound. The test event is
{(o,ρ) | 1/2 ≤ E n (o,ρ)}. Each family law belongs to `UnknownModel`,
so its error probability is bounded by `randRisk`. Combining the two
transfers through the baseline in S13 with the concentration bound S14
gives risk ≥ 1/2-16/(M+1)-n(n-1)/(2(M+1)). -/
def S15 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ), (∀ n, Measurable (E n)) →
    ∀ n : ℕ, 1 ≤ n → ∀ M : ℕ,
      (1 / 2 : ℝ) - 16 / (M + 1) - (n : ℝ) * (n - 1) / (2 * (M + 1)) ≤ randRisk Q E n (1 / 12)

/-- S16: letting M grow removes an error of the form C/(M+1),
by the Archimedean property. -/
def S16 : Prop :=
  ∀ (r C : ℝ), (∀ M : ℕ, (1 / 2 : ℝ) - C / (M + 1) ≤ r) → (1 / 2 : ℝ) ≤ r

/-- S17: event inclusion gives `randRisk (1/12) ≤ randStrictRisk (1/24)`.
The strict risk is therefore at least 1/2 for every n≥1, so its limsup
is at least 1/2>0. -/
def S17 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ), (∀ n, Measurable (E n)) →
    (∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) ≤ randRisk Q E n (1 / 12)) →
    ∃ η : ℝ, 0 < η ∧ 0 < Filter.limsup (fun n => randStrictRisk Q E n η) atTop

/-- S18: the finite-M width bound. Under family A with a good type,
coverage forces 7/12 < hi; under family B it forces lo < 5/12.
Together these imply lo+1/6<hi in EReal, including infinite endpoints.
The two transfers and prior concentration give the probability bound
2c_n-1-32/(M+1)-n(n-1)/(M+1). -/
def S18 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal),
    (∀ n, Measurable (lo n)) → (∀ n, Measurable (hi n)) →
    ∀ (n M : ℕ),
      2 * randCoverage Q lo hi n - 1 - 32 / (M + 1) - (n : ℝ) * (n - 1) / (M + 1) ≤
        widthProb Q lo hi n

/-- S19: letting M grow yields q_n≥2c_n-1. If liminf c_n≥1-α,
then liminf q_n≥1-2α, for bounded sequences. -/
def S19 : Prop :=
  ∀ (c q : ℕ → ℝ), (∀ n, 0 ≤ c n ∧ c n ≤ 1) → (∀ n, 0 ≤ q n ∧ q n ≤ 1) →
    (∀ n M : ℕ, 2 * c n - 1 - 32 / (M + 1) - (n : ℝ) * (n - 1) / (M + 1) ≤ q n) →
    ∀ α : ℝ, 0 < α → α < 1 / 2 → 1 - α ≤ Filter.liminf c atTop →
      (1 - 2 * α ≤ Filter.liminf q atTop) ∧ 0 < 1 - 2 * α

/-- S20: coverage and width probabilities lie in [0,1]. The inserted
one does not affect the coverage infimum for a nonempty model. -/
def S20 : Prop :=
  ∀ {R : Type u} [MeasurableSpace R] (Q : Measure R) [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) (n : ℕ),
    (0 ≤ randCoverage Q lo hi n ∧ randCoverage Q lo hi n ≤ 1) ∧
    (0 ≤ widthProb Q lo hi n ∧ widthProb Q lo hi n ≤ 1)

/-! ## Implications (`Nk` = hypotheses → `Sk`) -/

/-- Alias for `S1`. -/
def N1 : Prop := S1
/-- Alias for `S2`. -/
def N2 : Prop := S2
/-- N3: S2 implies S3. -/
def N3 : Prop := S2 → S3
/-- Alias for `S4`. -/
def N4 : Prop := S4
/-- N5: S1 implies S5. -/
def N5 : Prop := S1 → S5
/-- Alias for `S6`. -/
def N6 : Prop := S6
/-- Alias for `S7`. -/
def N7 : Prop := S7
/-- Alias for `S8`. -/
def N8 : Prop := S8
/-- Alias for `S9`. -/
def N9 : Prop := S9
/-- Alias for `S10`. -/
def N10 : Prop := S10
/-- N11: S1 implies S11. -/
def N11 : Prop := S1 → S11
/-- N12: S6–S11 imply S12. -/
def N12 : Prop := S6 → S7 → S8 → S9 → S10 → S11 → S12
/-- N13: S12 implies S13. -/
def N13 : Prop := S12 → S13.{u}
/-- Alias for `S14`. -/
def N14 : Prop := S14
/-- N15: `FamilyLaws`, S13 and S14 imply S15. -/
def N15 : Prop := FamilyLaws → S13.{u} → S14 → S15.{u}
/-- Alias for `S16`. -/
def N16 : Prop := S16
/-- Alias for `S17`. -/
def N17 : Prop := S17.{u}
/-- N18: `FamilyLaws`, S13 and S14 imply S18. -/
def N18 : Prop := FamilyLaws → S13.{u} → S14 → S18.{u}
/-- Alias for `S19`. -/
def N19 : Prop := S19
/-- Alias for `S20`. -/
def N20 : Prop := S20.{u}

/-! ## The family laws and impossibility theorem -/

/-- Statements S3–S5 imply `FamilyLaws`. -/
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

/-- The twenty statements imply the impossibility theorem. -/
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

end

end AronowAudit.P047.Wave1.Impossibility
