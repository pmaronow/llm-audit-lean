import SAP.P001b.Defs.WholeW1
import SAP.P001b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b.WH.W1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Classical Topology

noncomputable section

universe u v

local instance : MeasurableSpace DyadicIndex := ⊤
local instance : MeasurableSpace (ℕ × Bool) := ⊤

/-- Uniform conditional positivity gives the same null sets for each conditional
covariate law and the marginal law. Use the CEF set-integral identity and the binary
indicator identity to express treated and control covariate masses as the integrals
of p(X) and 1-p(X). Their uniform positive lower bounds show that either integral
vanishes exactly when the marginal mass does. Normalize by the positive arm masses.
This is the continuous/general-space forward theorem under the usual version convention. -/
def T20_L1V2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ),
    Measurable X → Measurable D → (∀ ω, D ω = 0 ∨ D ω = 1) →
    0 < probability μ {ω | D ω = 0} → 0 < probability μ {ω | D ω = 1} →
    ∀ p : E → ℝ, W1CEF μ X D p →
      (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1 - ε) →
      (W1ArmLaw μ X D 1 ≪ μ.map X) ∧ (μ.map X ≪ W1ArmLaw μ X D 1) ∧
      (W1ArmLaw μ X D 0 ≪ μ.map X) ∧ (μ.map X ≪ W1ArmLaw μ X D 0)

/-- A positive-probability zero/one propensity region is absent in one arm and present
in the other. Use the same CEF set-integral identity, now with p = 0 or p = 1 on the
region. The binary partition makes the other arm mass equal to the marginal region
mass. There is deliberately no uniform positivity premise in this leaf. -/
def T20_L2V2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ),
    Measurable X → Measurable D → (∀ ω, D ω = 0 ∨ D ω = 1) →
    ∀ p : E → ℝ, W1CEF μ X D p →
      ∀ A : Set E, MeasurableSet A → 0 < probability μ (X ⁻¹' A) →
        ((∀ᵐ ω ∂μ.restrict (X ⁻¹' A), p (X ω) = 0) →
          probability μ {ω | X ω ∈ A ∧ D ω = 1} = 0 ∧
          0 < probability μ {ω | X ω ∈ A ∧ D ω = 0}) ∧
        ((∀ᵐ ω ∂μ.restrict (X ⁻¹' A), p (X ω) = 1) →
          probability μ {ω | X ω ∈ A ∧ D ω = 0} = 0 ∧
          0 < probability μ {ω | X ω ∈ A ∧ D ω = 1})

/-- Realize the geometric t,c sequences as the specified joint probability law on
N × Bool. Sum weighted Dirac measures on the powerset sigma-algebra. Reuse the
proved summability and half-mass totals for t and c; split the sum over Bool.
Evaluate the singleton covariate/arm cells and the two arm events. No nonconverse
argument belongs here: that argument is already proved by the project donor. -/
def T20_L3V2 : Prop :=
  IsProbabilityMeasure W1GeometricLaw ∧
  (∀ k, W1JointMass W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) 1 k = W1OverlapT k ∧
    W1JointMass W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) 0 k = W1OverlapC k) ∧
  probability W1GeometricLaw {z | W1BinaryValue z.2 = 0} = 1 / 2 ∧
  probability W1GeometricLaw {z | W1BinaryValue z.2 = 1} = 1 / 2

/-- Construct the actual discrete conditional expectation functions. For each
positive-mass cell the conditional mean is its set integral divided by its mass;
null cells may be assigned zero, or one half for the propensity. Countable cell
partitions prove the CEF set-integral identity and arm-restricted integrability.
First prove this finite-measure cell-mean fact generically, then apply it to D and
the two observed-outcome arm restrictions. Binary D makes D integrable and turns
its cell integral into the joint treated-cell probability. Null-cell alterations
are a.e. invisible. All outcome integrability assumptions are the standing existence
conditions; population integrability of the arm CEFs is proved in the next leaf. -/
def T22_L1V2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E), Measurable X →
    ∀ Y0 Y1 D : Ω → ℝ, Measurable Y0 → Measurable Y1 → Measurable D →
      Integrable Y0 μ → Integrable Y1 μ → (∀ ω, D ω = 0 ∨ D ω = 1) →
      W1CEF μ X D (W1CellPropensity μ X D) ∧
      W1CEF (μ.restrict {ω | D ω = 0}) X
        (fun ω => Y1 ω * D ω + Y0 ω * (1 - D ω)) (W1ArmMean μ X Y0 Y1 D 0) ∧
      W1CEF (μ.restrict {ω | D ω = 1}) X
        (fun ω => Y1 ω * D ω + Y0 ω * (1 - D ω)) (W1ArmMean μ X Y0 Y1 D 1)

/-- Uniform positivity lifts the actual observed-arm cell means to integrable
functions on the full population. For each positive covariate cell, its arm mass
is at least epsilon times the marginal mass. The absolute numerator is bounded by
the cell integral of |Y_d|, since observed Y equals Y_d in arm d. Sum these bounds
over the countable disjoint cells. This proves the required weighted absolute
summability, hence integrability of m_d(X). Handle zero-mass cells with the explicit
zero default. Conditional independence is not needed for this integrability step. -/
def T22_L2V2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E), Measurable X →
    ∀ Y0 Y1 D : Ω → ℝ, Measurable Y0 → Measurable Y1 → Measurable D →
      Integrable Y0 μ → Integrable Y1 μ → (∀ ω, D ω = 0 ∨ D ω = 1) →
      (∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < probability μ {ω | X ω = x} →
        ε < W1CellPropensity μ X D x ∧ W1CellPropensity μ X D x < 1 - ε) →
      Integrable (W1ArmMean μ X Y0 Y1 D 0 ∘ X) μ ∧
      Integrable (W1ArmMean μ X Y0 Y1 D 1 ∘ X) μ

/-- Probability-law bridge for an arbitrary countable-range real random variable
whose noninteger point masses vanish. Decompose its countable range into point
fibers; the noninteger fibers have union measure zero. Reindex the remaining fibers
by the integers, apply countable additivity and convert the finite ENNReal sums to
real sums. The event identity includes arbitrary sets B: their inverse images are
measurable because the range is countable. Do not impose pointwise integer values. -/
def T26_L1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → (Set.range X).Countable →
    (∀ x : ℝ, (¬ ∃ k : ℤ, (k : ℝ) = x) → probability μ {ω | X ω = x} = 0) →
    let q : ℤ → ℝ := fun k => probability μ {ω | X ω = (k : ℝ)}
    Summable q ∧ (∑' k, q k) = 1 ∧
    ∀ B : Set ℝ, probability μ {ω | X ω ∈ B} =
      ∑' k : ℤ, if (k : ℝ) ∈ B then q k else 0

/-- Uniqueness of an odd numerator over a power of two. Clear the positive real
denominators in an equality of locations. If the exponents differ, cancellation
makes an odd natural number divisible by two; if they agree, cancel to get equal
numerators and use Sigma/Fin extensionality. -/
def T27_L1 : Prop := Function.Injective dyadicLocation

/-- Exact dyadic range, rather than just density of the displayed locations.
The forward inclusion follows directly from the formula and k < 2^m. For a dyadic
a/2^n in (0,1), a is positive. Factor a into a power of two times an odd natural
number, cancel that power, and use x < 1 to obtain the required m and k < 2^m.
The excluded endpoints ensure that the remaining denominator exponent is positive. -/
def T27_L2 : Prop := Set.range dyadicLocation = W1DyadicRationals


theorem realize_weights :
    ∀ w : DyadicIndex → ℝ, (∀ i, 0 ≤ w i) → Summable w → (∑' i, w i) = 1 →
      let μ : Measure DyadicIndex :=
        Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac i)
      IsProbabilityMeasure μ ∧ ∀ A : Set DyadicIndex,
        probability μ A = ∑' i, if i ∈ A then w i else 0 := by
  intro w hn hs ht
  let μ : Measure DyadicIndex :=
    Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac i)
  have heval (A : Set DyadicIndex) :
      μ A = ∑' i, ENNReal.ofReal (if i ∈ A then w i else 0) := by
    rw [show μ = Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac i) from rfl,
      Measure.sum_apply _ (by trivial)]
    apply tsum_congr
    intro i
    by_cases hi : i ∈ A <;> simp [Measure.smul_apply, hi]
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [heval]
    simp only [Set.mem_univ, ite_true]
    rw [← ENNReal.ofReal_tsum_of_nonneg hn hs, ht]
    norm_num
  refine ⟨hprob, ?_⟩
  intro A
  change (μ A).toReal = _
  rw [heval, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro i
  apply ENNReal.toReal_ofReal
  split_ifs
  · exact hn i
  · exact le_rfl


theorem T37_assembly : T37WholeStatement := by
  constructor
  · intro ν _ f hf
    obtain ⟨hfinite, hversions⟩ :=
      AronowAudit.P001.Wave1.marginal_pdf_ae_correction_all_versions ν f hf
    refine ⟨hfinite, ?_⟩
    intro g hpos heq
    have hg := hversions g hpos heq
    exact ⟨hg, (AronowAudit.P001.pdf_version_change (ν.map Prod.snd) g g hg hg.1 hpos
      Filter.EventuallyEq.rfl).2⟩
  · intro f hnonneg x hint hpos
    refine ⟨hint.div_const _, (fun y => div_nonneg (hnonneg (x, y)) hpos.le), ?_⟩
    rw [integral_div, div_self hpos.ne']

theorem T26_assembly (h1 : T26_L1.{u}) : T26WholeStatement.{u} := by
  constructor
  · intro Ω _ μ _ X hX hcount hZ
    obtain ⟨hs, ht, hevents⟩ := h1 μ X hX hcount hZ
    let q : ℤ → ℝ := fun k => probability μ {ω | X ω = (k : ℝ)}
    have hn : ∀ k, 0 ≤ q k := fun _ => ENNReal.toReal_nonneg
    obtain ⟨hfour, hmissing, hiff⟩ :=
      AronowAudit.P001.integer_lower_tail_correction q hn hs ht
    have hlt : probability μ {ω | X ω < 4} = integerCDF q 3 := by
      exact (hevents {x : ℝ | x < 4}).trans hfour
    have hzero : probability μ {ω | X ω ≤ 0} = integerCDF q 0 :=
      hevents (Set.Iic 0)
    exact ⟨hs, ht, hlt, by rw [hlt, hzero]; exact hmissing,
      by rw [hlt, hzero]; exact hiff⟩
  · refine ⟨(fun _ => by norm_num [dieMass]), ?_, ?_, ?_, ?_, by norm_num⟩
    · norm_num [dieMass, Fin.sum_univ_succ]
    · intro x
      by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;> by_cases h3 : x = 3 <;>
        by_cases h4 : x = 4 <;> by_cases h5 : x = 5 <;> by_cases h6 : x = 6 <;>
        norm_num [finiteProbability, dieMass, dieValue, Fin.sum_univ_succ,
          h1, h2, h3, h4, h5, h6, eq_comm]
    · have hi : Finset.Icc (1 : ℤ) 3 = {1, 2, 3} := by decide
      rw [hi]
      norm_num [finiteProbability, dieMass, dieValue, Fin.sum_univ_succ]
    · norm_num [finiteProbability, dieMass, dieValue, Fin.sum_univ_succ]

theorem T27_assembly (h1 : T27_L1) (h2 : T27_L2) :
    T27WholeStatement := by
  obtain ⟨hs, ht, hstrict, hcont, hflat⟩ :=
    AronowAudit.P001.Wave1.dense_discrete_cdf_counterexample_proof
  change Summable dyadicWeight at hs
  change (∑' i, dyadicWeight i) = 1 at ht
  change ∀ a b : ℝ, 0 < a → a < b → b < 1 →
    dyadicDistributionFunction a < dyadicDistributionFunction b at hstrict
  have hpos : ∀ i, 0 < dyadicWeight i := AronowAudit.P001.Wave1.T27_mass_pos
  have hlevel : ∀ m : ℕ, (∑ k : Fin (2 ^ m), dyadicWeight ⟨m, k⟩) =
      (1 / 2 : ℝ) ^ (m + 1) := by
    intro m
    have h := AronowAudit.P001.Wave1.T27_level_mass m
    change (∑' k : Fin (2 ^ m), dyadicWeight ⟨m, k⟩) = (1 / 2 : ℝ) ^ (m + 1) at h
    simpa only [tsum_fintype] using h
  obtain ⟨hprob, hsets⟩ := realize_weights dyadicWeight (fun i => (hpos i).le) hs ht
  change IsProbabilityMeasure W1DyadicLaw at hprob
  change ∀ A : Set DyadicIndex, probability W1DyadicLaw A =
    ∑' i, if i ∈ A then dyadicWeight i else 0 at hsets
  letI : IsProbabilityMeasure W1DyadicLaw := hprob
  have hsingle (i : DyadicIndex) : probability W1DyadicLaw {i} = dyadicWeight i := by
    rw [hsets]
    simp
  refine ⟨hlevel, tsum_congr hlevel, AronowAudit.P001.Wave1.T27_geometric.tsum_eq,
    hs, ht, hpos, (fun s => s.to_countable.measurableSet), hprob,
    measurable_of_countable _, h1, h2, Set.countable_range _, ?_, ?_, hstrict, ?_, ?_,
    hcont, hflat⟩
  · intro i
    have hpre : {j | dyadicLocation j = dyadicLocation i} = ({i} : Set DyadicIndex) := by
      ext j
      exact h1.eq_iff
    have hmass : W1DyadicLaw {i} = ENNReal.ofReal (dyadicWeight i) := by
      rw [← hsingle i, probability, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ⟨hmass, by rw [hpre]; exact hsingle i, by rw [hpre, hsingle]; exact hpos i⟩
  · intro x
    exact hsets {i | dyadicLocation i ≤ x}
  · intro a b ha hab hb
    rintro ⟨c, hc⟩
    have hx := hc (a + (b - a) / 3) (by constructor <;> linarith)
    have hy := hc (a + 2 * (b - a) / 3) (by constructor <;> linarith)
    have hlt := hstrict (a + (b - a) / 3) (a + 2 * (b - a) / 3)
      (by linarith) (by linarith) (by linarith)
    rw [hx, hy] at hlt
    exact lt_irrefl _ hlt
  · have he : {i | dyadicLocation i = (1 / 3 : ℝ)} = (∅ : Set DyadicIndex) := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact AronowAudit.P001.Wave1.T27_third_not_atom i
    rw [he, measure_empty]

end
end SAP.P001b.WH.W1
