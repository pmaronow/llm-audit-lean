import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Order.DenselyOrdered

/-!
P061: On the Foundations of the Design-Based Approach.
The assignment type is the feasible intervention set, not just the support.
Zero-weight feasible assignments are retained. All probability statements use the
normalized, nonnegative atom weights below. Unordered real sums are used; existence
of signed expectations is separately asserted by `Integrable`. No totalized tsum
is used as evidence that a mean exists.
-/

namespace AronowAudit.P061

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

set_option autoImplicit false

/-- Section 3, p. 3: "Pr[A] = ∑_{ω∈A} p(ω)" with "p : Ω → [0,1]".
`Ω` labels feasible assignments; the normalization also implies each atom is at most 1.
The support need not be finite or the whole feasible set. -/
structure Design (Ω : Type) where
  p : Ω → ℝ
  nonneg : ∀ z, 0 ≤ p z
  summable : Summable p
  total : (∑' z, p z) = 1

/-- Section 3.2, p. 4, Eq. (1): "The raw potential outcome y_i(z) ... is what
we observe if we perform intervention z and measure unit i's outcome."
`Fin N` indexes the paper's N fixed population units. -/
abbrev OutcomeSchedule (Ω : Type) (N : ℕ) := Fin N → Ω → ℝ

/-- Section 3.3, p. 4: "our exposure mapping ... is a function g_i : Z → R";
Eq. (2): "D = (g_1(Z), ... , g_N(Z))". -/
abbrev ExposureMapping (Ω : Type) (N : ℕ) := Fin N → Ω → ℝ

/-- Positive-probability assignment support. -/
def Support {Ω : Type} (D : Design Ω) (z : Ω) : Prop := 0 < D.p z

/-- Section 3, p. 3: probability of any event is the sum of its atom weights.
Classical decidability supplies indicators for arbitrary subsets. -/
noncomputable def probability {Ω : Type} (D : Design Ω) (A : Ω → Prop) : ℝ :=
  ∑' z, if A z then D.p z else 0

/-- Expectations over the design distribution; usable as a signed mean
only together with `Integrable D f`. -/
noncomputable def expectation {Ω : Type} (D : Design Ω) (f : Ω → ℝ) : ℝ :=
  ∑' z, D.p z * f z

/-- Finite ordinary expectation: absolute summability of the weighted outcomes.
P061-T8's first-moment correction. -/
def Integrable {Ω : Type} (D : Design Ω) (f : Ω → ℝ) : Prop :=
  Summable (fun z => D.p z * |f z|)

/-- Eq. (4), p. 6: "π_i(d) = Pr[D_i = d]". -/
noncomputable def pi {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (i : Fin N) (d : ℝ) : ℝ :=
  probability D (fun z => g i z = d)

/-- Condition 4.1, p. 6: "there exists a c such that 0 < c ≤ π_i(d) ...". -/
def IndividualPositivity {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (d : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ pi D g i d

/-- P061-T8's targeted moment condition: ∑_{g_i(z)=d} |y_i(z)| Pr[Z=z] < ∞.
Zero-probability feasible assignments contribute zero. -/
def TargetedMoment {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) : Prop :=
  ∀ i, Integrable D (fun z => if g i z = d then y i z else 0)

/-- Eq. (5), p. 6: "ȳ_i(d) = [∑_{g_i(z)=d} y_i(z) Pr[Z=z]] / π_i(d)".
The paper defines this only at positive π; the correction also requires the
targeted moment. Real division and tsum are total in Lean, so existence is an
explicit proposition, not an inference from this function's codomain. -/
noncomputable def epo {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (i : Fin N) (d : ℝ) : ℝ :=
  expectation D (fun z => if g i z = d then y i z else 0) / pi D g i d

/-- Conditional mean on a positive-probability exposure event, Eq. (5), p. 6.
This uses the conditional atom weights p(z)/π_i(d) directly. -/
noncomputable def conditionalMean {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (i : Fin N) (d : ℝ) : ℝ :=
  ∑' z, if g i z = d then (D.p z / pi D g i d) * y i z else 0

/-- Eq. (6), p. 7: "ȳ(d) = (1/N) ∑_i ȳ_i(d)". -/
noncomputable def aepo {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, epo D g y i d

/-- Eq. (7), p. 7: "τ_i(d,d') = ȳ_i(d) − ȳ_i(d')". -/
noncomputable def eed {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (i : Fin N) (d d' : ℝ) : ℝ :=
  epo D g y i d - epo D g y i d'

/-- Eq. (8), p. 7: "τ(d,d') = ȳ(d) − ȳ(d')". -/
noncomputable def aeed {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) : ℝ :=
  aepo D g y d - aepo D g y d'

/-- Supplement Eq. (1), p. 1: "ŷ̄(d) = (1/N) ∑_i Y_i 1{D_i=d}/π_i(d)". -/
noncomputable def ht {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (z : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (if g i z = d then y i z else 0) / pi D g i d

/-- Supplement p. 4, before Eq. (9): "τ̂(d,d') = ŷ̄(d) − ŷ̄(d')". -/
noncomputable def htContrast {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) (z : Ω) : ℝ :=
  ht D g y d z - ht D g y d' z

/-- Condition 5.1, p. 8: equal own exposure implies equal raw outcomes on
Supp(Z). The EPO equality printed afterward is a consequence proved below. -/
def NURVA {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) : Prop :=
  ∀ i z z', Support D z → Support D z' → g i z = g i z' → y i z = y i z'

/-- Condition 5.2, p. 8: the same stability restriction over all feasible Z.
Its printed EPO equality is read only where the EPO is defined. -/
def SUTVA {Ω : Type} {N : ℕ} (g : ExposureMapping Ω N)
    (y : OutcomeSchedule Ω N) : Prop :=
  ∀ i z z', g i z = g i z' → y i z = y i z'

/-- Supplement pp. 3–4: "π_ij(d,d') = Pr[D_i=d,D_j=d']";
the same-exposure π_ij(d) is this function at d'=d. Ordered diagonal pairs
are included, exactly as in Eqs. (5)–(9). -/
noncomputable def jointPi {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (i j : Fin N) (d d' : ℝ) : ℝ :=
  probability D (fun z => g i z = d ∧ g j z = d')

/-- Design variance, supplement Eqs. (5), (9), pp. 3–4:
E[(X−EX)^2], interpreted only when the corresponding moments exist. -/
noncomputable def variance {Ω : Type} (D : Design Ω) (X : Ω → ℝ) : ℝ :=
  expectation D (fun z => (X z - expectation D X)^2)

/-- Design covariance, supplement Eq. (9), p. 4. -/
noncomputable def covariance {Ω : Type} (D : Design Ω) (X Y : Ω → ℝ) : ℝ :=
  expectation D (fun z => (X z - expectation D X) * (Y z - expectation D Y))

section Linear
variable {Ω : Type} {N : ℕ} (D : Design Ω)

/-- Summability of every event's atom weights; the Section 3 probability setup. -/
theorem event_summable (A : Ω → Prop) :
    Summable (fun z => if A z then D.p z else 0) := by
  classical
  refine Summable.of_nonneg_of_le (fun z => ?_) (fun z => ?_) D.summable
  · split_ifs <;> simp [D.nonneg]
  · split_ifs <;> simp [D.nonneg]

/-- All event probabilities are nonnegative (Section 3, p. 3). -/
theorem probability_nonneg (A : Ω → Prop) : 0 ≤ probability D A := by
  classical
  apply tsum_nonneg
  intro z; split_ifs <;> simp [D.nonneg]

/-- All event probabilities are at most one (Section 3, p. 3). -/
theorem probability_le_one (A : Ω → Prop) : probability D A ≤ 1 := by
  classical
  rw [← D.total]
  exact Summable.tsum_le_tsum (fun z => by split_ifs <;> simp [D.nonneg])
    (event_summable D A) D.summable

/-- Absolute integrability entails summability of signed weighted outcomes;
the existence step in P061-T8(i). -/
theorem integrable_summable {f : Ω → ℝ} (h : Integrable D f) :
    Summable (fun z => D.p z * f z) := by
  apply Summable.of_abs
  simpa only [Integrable, abs_mul, abs_of_nonneg (D.nonneg _)] using h

/-- Signed summability and absolute integrability agree for these real
unordered sums; P061-T8's existence convention. -/
theorem integrable_of_summable {f : Ω → ℝ}
    (h : Summable (fun z => D.p z * f z)) : Integrable D f := by
  simpa only [Integrable, abs_mul, abs_of_nonneg (D.nonneg _)] using h.abs

/-- Integrability is preserved by finite differences, used in T8(iii). -/
theorem integrable_sub {f h : Ω → ℝ} (hf : Integrable D f) (hh : Integrable D h) :
    Integrable D (fun z => f z - h z) := by
  simpa only [Integrable, ← mul_sub, abs_mul, abs_of_nonneg (D.nonneg _)] using
    ((integrable_summable D hf).sub (integrable_summable D hh)).abs

/-- Linearity of design expectation for finite differences of integrable
variables; supplement Eq. (3), p. 2. -/
theorem expectation_sub {f h : Ω → ℝ} (hf : Integrable D f) (hh : Integrable D h) :
    expectation D (fun z => f z - h z) = expectation D f - expectation D h := by
  simp only [expectation, mul_sub]
  exact Summable.tsum_sub (integrable_summable D hf) (integrable_summable D hh)

/-- Scaling the totalized weighted-sum expression. Implementation algebra
supporting supplement Eq. (3), p. 2; it asserts no signed-moment existence. -/
theorem expectation_mul_algebra (a : ℝ) (f : Ω → ℝ) :
    expectation D (fun z => a * f z) = a * expectation D f := by
  unfold expectation
  calc
    (∑' z, D.p z * (a * f z)) = ∑' z, a * (D.p z * f z) :=
      tsum_congr (fun z => by ring)
    _ = a * ∑' z, D.p z * f z := tsum_mul_left

/-- Division in the totalized weighted-sum expression. Implementation algebra
supporting supplement Eq. (3), p. 2, without an expectation-existence claim. -/
theorem expectation_div_algebra (f : Ω → ℝ) (a : ℝ) :
    expectation D (fun z => f z / a) = expectation D f / a := by
  simp only [expectation, ← mul_div_assoc]
  exact tsum_div_const

/-- T8: scaling a genuine signed design expectation; the targeted first-moment
correction supplies the integrability hypothesis. -/
theorem expectation_mul (a : ℝ) (f : Ω → ℝ) (_hf : Integrable D f) :
    expectation D (fun z => a * f z) = a * expectation D f :=
  expectation_mul_algebra D a f

/-- T8: division of an integrable design variable by a nonzero deterministic
scalar, as used in the positive-probability conditional mean. -/
theorem expectation_div (f : Ω → ℝ) (a : ℝ) (_hf : Integrable D f) (_ha : a ≠ 0) :
    expectation D (fun z => f z / a) = expectation D f / a :=
  expectation_div_algebra D f a

/-- Eq. (5), p. 6, expanded using conditional atom probabilities.
Its statistical interpretation requires the positivity and moment hypotheses
retained here; the algebra itself does not require the denominator to be nonzero. -/
theorem epo_conditional (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (i : Fin N) (d : ℝ) (_hpos : 0 < pi D g i d)
    (_hm : Integrable D (fun z => if g i z = d then y i z else 0)) :
    epo D g y i d = conditionalMean D g y i d := by
  classical
  unfold epo conditionalMean expectation
  rw [← tsum_div_const]
  apply tsum_congr
  intro z
  by_cases h : g i z = d
  · simp only [h, ite_true]; ring
  · simp only [h, ite_false, mul_zero, zero_div]

/-- Eq. (8), p. 7: the AEED is the average of unit EEDs, with the
same population, design and mapping in every term. -/
theorem aeed_average_eed_algebra (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (d d' : ℝ) : aeed D g y d d' = (N : ℝ)⁻¹ * ∑ i, eed D g y i d d' := by
  simp only [aeed, aepo, eed, Finset.sum_sub_distrib, mul_sub]

/-- T6(ii), Eq. (8), p. 7: on the stipulated common finite domain and
positive target cells, AEED equals the average of the unit EEDs. -/
theorem aeed_average_eed [Fintype Ω] (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (d d' : ℝ) (_hN : 0 < N)
    (_hp : ∀ i, 0 < pi D g i d ∧ 0 < pi D g i d') :
    aeed D g y d d' = (N : ℝ)⁻¹ * ∑ i, eed D g y i d d' :=
  aeed_average_eed_algebra D g y d d'

/-- A finite assignment set automatically supplies the correction's targeted
absolute first moment, P061-T8(iv). -/
theorem finite_type_targeted_moment [Fintype Ω] (g : ExposureMapping Ω N)
    (y : OutcomeSchedule Ω N) (d : ℝ) : TargetedMoment D g y d := by
  intro i
  exact Summable.of_finite

/-- Supplement Eq. (3), p. 2, with the corrected first-moment condition:
the HT AEPO estimator is integrable and unbiased, without NURVA (T8(iii)). -/
theorem ht_unbiased (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ)
    (hm : TargetedMoment D g y d) : expectation D (ht D g y d) = aepo D g y d := by
  classical
  unfold ht aepo
  rw [expectation_mul_algebra]
  congr 1
  unfold expectation epo
  simp_rw [Finset.mul_sum, ← mul_div_assoc]
  rw [Summable.tsum_finsetSum]
  · simp_rw [tsum_div_const]
    rfl
  · intro i hi
    exact (integrable_summable D (hm i)).div_const _

/-- Supplement Eq. (3) and the following take-away, p. 2: HT contrasts
are unbiased for AEED when the two targeted moments exist (T8(iii)). -/
theorem ht_contrast_unbiased (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (d d' : ℝ) (hm : TargetedMoment D g y d) (hm' : TargetedMoment D g y d')
    (hht : Integrable D (ht D g y d)) (hht' : Integrable D (ht D g y d')) :
    expectation D (htContrast D g y d d') = aeed D g y d d' := by
  unfold htContrast aeed
  rw [expectation_sub D hht hht', ht_unbiased D g y d hm,
    ht_unbiased D g y d' hm']


/-- Corrected T6(i)–(ii): on a finite feasible assignment type with positive
target probabilities, EPO equals the conditional expected exposure outcome,
and AEED equals the average of the conditional exposure contrasts. -/
theorem corrected_attribution [Fintype Ω] (g : ExposureMapping Ω N)
    (y : OutcomeSchedule Ω N) (a b : ℝ) (_hN : 0 < N)
    (ha : ∀ i, 0 < pi D g i a) (hb : ∀ i, 0 < pi D g i b) :
    (∀ i e, e = a ∨ e = b → epo D g y i e = conditionalMean D g y i e) ∧
    aeed D g y a b = (N : ℝ)⁻¹ *
      ∑ i, (conditionalMean D g y i a - conditionalMean D g y i b) := by
  constructor
  · intro i e he
    rcases he with he | he
    · subst e; exact epo_conditional D g y i a (ha i) (Summable.of_finite)
    · subst e; exact epo_conditional D g y i b (hb i) (Summable.of_finite)
  · rw [aeed_average_eed_algebra]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [eed, epo_conditional D g y i a (ha i) (Summable.of_finite),
      epo_conditional D g y i b (hb i) (Summable.of_finite)]

/-- Supplement Eq. (2), p. 1: equal exposure probabilities n/N reduce
the HT estimator to the exposed-outcome sum divided by the fixed number n,
without outcome stability. This is the exposed-units sample mean when
exactly n units have exposure d. -/
theorem ht_sample_mean (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (d : ℝ) (n : ℕ) (hN : 0 < N) (hn : 0 < n)
    (hp : ∀ i, pi D g i d = (n : ℝ) / N) (z : Ω) :
    ht D g y d z = (n : ℝ)⁻¹ * ∑ i, if g i z = d then y i z else 0 := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold ht
  simp_rw [hp]
  rw [← Finset.sum_div]
  field_simp

/-- T13(ii): global SUTVA entails design-support NURVA (Condition 5.2
implies Condition 5.1, p. 8). -/
theorem sutva_implies_nurva (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (h : SUTVA g y) : NURVA D g y := by
  intro i z z' hz hz' he
  exact h i z z' he

/-! Additional first-moment and stability results. -/

/-- Integrability under deterministic scaling, needed for T8(iii). -/
theorem integrable_mul {f : Ω → ℝ} (hf : Integrable D f) (a : ℝ) :
    Integrable D (fun z => a * f z) := by
  apply integrable_of_summable D
  exact ((integrable_summable D hf).mul_left a).congr (fun z => by ring)

/-- Integrability under deterministic division, needed for T8(iii). -/
theorem integrable_div {f : Ω → ℝ} (hf : Integrable D f) (a : ℝ) :
    Integrable D (fun z => f z / a) := by
  apply integrable_of_summable D
  exact ((integrable_summable D hf).div_const a).congr (fun z => by ring)

/-- Integrability of a finite sum of integrable design variables (T8(iii)). -/
theorem integrable_sum (f : Fin N → Ω → ℝ) (hf : ∀ i, Integrable D (f i)) :
    Integrable D (fun z => ∑ i, f i z) := by
  apply integrable_of_summable D
  simp_rw [Finset.mul_sum]
  exact summable_sum (fun i hi => integrable_summable D (hf i))

/-- Linearity for a finite sum of integrable design variables (supplement
Eq. (3), p. 2). -/
theorem expectation_sum (f : Fin N → Ω → ℝ) (hf : ∀ i, Integrable D (f i)) :
    expectation D (fun z => ∑ i, f i z) = ∑ i, expectation D (f i) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i hi => integrable_summable D (hf i))

/-- The targeted moment makes the HT estimator integrable, T8(iii). -/
theorem ht_integrable (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ)
    (hm : TargetedMoment D g y d) : Integrable D (ht D g y d) := by
  exact integrable_mul D (integrable_sum D _
    (fun i => integrable_div D (hm i) _)) _

/-- P061-T8(i)–(iii), corrected well-definedness and first-moment unbiasedness:
positive target exposures and targeted absolute first moments supply genuine
signed EPOs, an integrable HT estimator, and unbiased AEPO and AEED estimates.
No stability assumption is made. Parts (iv) are `finite_targeted_moment` and
`nurva_targeted_moment`; finite-type and global-NURVA specializations are also retained. -/
theorem corrected_first_moment (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (d : ℝ) (_hN : 0 < N) (hp : ∀ i, 0 < pi D g i d)
    (hm : TargetedMoment D g y d) :
    (∀ i, Summable (fun z => D.p z * (if g i z = d then y i z else 0)) ∧
      epo D g y i d = conditionalMean D g y i d ∧
      Integrable D (fun z => (if g i z = d then y i z else 0) / pi D g i d) ∧
      expectation D (fun z => |(if g i z = d then y i z else 0) / pi D g i d|) =
        expectation D (fun z => |if g i z = d then y i z else 0|) / pi D g i d ∧
      expectation D (fun z => (if g i z = d then y i z else 0) / pi D g i d) =
        epo D g y i d) ∧
    Integrable D (ht D g y d) ∧ expectation D (ht D g y d) = aepo D g y d ∧
    (∀ d' : ℝ, (∀ i, 0 < pi D g i d') → TargetedMoment D g y d' →
      Integrable D (htContrast D g y d d') ∧
      expectation D (htContrast D g y d d') = aeed D g y d d' ∧
      aeed D g y d d' = (N : ℝ)⁻¹ * ∑ i, eed D g y i d d') := by
  refine ⟨?_, ht_integrable D g y d hm, ht_unbiased D g y d hm, ?_⟩
  · intro i
    refine ⟨integrable_summable D (hm i), epo_conditional D g y i d (hp i) (hm i),
      integrable_div D (hm i) _, ?_, expectation_div_algebra D _ _⟩
    simp_rw [abs_div, abs_of_pos (hp i)]
    exact expectation_div_algebra D _ _
  · intro d' hp' hm'
    exact ⟨integrable_sub D (ht_integrable D g y d hm) (ht_integrable D g y d' hm'),
      ht_contrast_unbiased D g y d d' hm hm'
        (ht_integrable D g y d hm) (ht_integrable D g y d' hm'),
      aeed_average_eed_algebra D g y d d'⟩

/-- A stable on-support exposure cell has an integrable, constant EPO.
This proves the sentence following Condition 5.1 on p. 8 and T8(iv). -/
theorem constant_cell (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (i : Fin N) (d a : ℝ) (hp : 0 < pi D g i d)
    (hc : ∀ z, Support D z → g i z = d → y i z = a) :
    Integrable D (fun z => if g i z = d then y i z else 0) ∧
    epo D g y i d = a ∧
    expectation D (fun z => |if g i z = d then y i z else 0|) = |a| * pi D g i d := by
  have heq : ∀ z, D.p z * (if g i z = d then y i z else 0) =
      a * (if g i z = d then D.p z else 0) := by
    intro z
    by_cases hz : Support D z
    · by_cases hg : g i z = d
      · simp [hg, hc z hz hg, mul_comm]
      · simp [hg]
    · have hzero : D.p z = 0 := le_antisymm (le_of_not_gt hz) (D.nonneg z)
      simp [hzero]
  have hs : Summable (fun z => D.p z * (if g i z = d then y i z else 0)) :=
    ((event_summable D _).mul_left a).congr (fun z => (heq z).symm)
  refine ⟨integrable_of_summable D hs, ?_, ?_⟩
  · unfold epo expectation pi probability
    simp_rw [heq]
    rw [tsum_mul_left]
    exact mul_div_cancel_right₀ a hp.ne'
  · unfold expectation pi probability
    calc
      (∑' z, D.p z * |if g i z = d then y i z else 0|) =
          ∑' z, |a| * (if g i z = d then D.p z else 0) := by
        apply tsum_congr
        intro z
        have hh := congr_arg abs (heq z)
        simpa only [abs_mul, abs_of_nonneg (D.nonneg z),
          abs_of_nonneg (show 0 ≤ (if g i z = d then D.p z else 0) from
            by split_ifs <;> simp [D.nonneg])] using hh
      _ = |a| * ∑' z, if g i z = d then D.p z else 0 := tsum_mul_left

/-- A positive exposure cell contains a supported assignment; Section 4.1,
Eq. (4), and the representative used in T13(i). -/
theorem positive_cell_has_assignment (g : ExposureMapping Ω N) (i : Fin N) (d : ℝ)
    (hp : 0 < pi D g i d) : ∃ z, Support D z ∧ g i z = d := by
  by_contra h
  have hz : ∀ z, (if g i z = d then D.p z else 0) = 0 := by
    intro z
    by_cases he : g i z = d
    · have hn : ¬Support D z := fun hs => h ⟨z, hs, he⟩
      simp [he, le_antisymm (le_of_not_gt hn) (D.nonneg z)]
    · simp [he]
  have : pi D g i d = 0 := by simp only [pi, probability, hz, tsum_zero]
  linarith

/-- T8(iv): NURVA supplies the targeted absolute moment even on infinite
support. The constant-cell formula is included in `constant_cell`. -/
theorem global_nurva_targeted_moment (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (d : ℝ) (hp : ∀ i, 0 < pi D g i d) (hn : NURVA D g y) :
    TargetedMoment D g y d := by
  intro i
  obtain ⟨z, hz, hg⟩ := positive_cell_has_assignment D g i d (hp i)
  exact (constant_cell D g y i d (y i z) (hp i) (fun w hw he =>
    hn i w z hw hz (he.trans hg.symm))).1

/-- T8(iv): only stability within the targeted exposure cell is needed
for its absolute first moment; stability at other exposures is unrestricted. -/
theorem nurva_targeted_moment (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (d : ℝ) (hp : ∀ i, 0 < pi D g i d)
    (hn : ∀ i z z', Support D z → Support D z' →
      g i z = d → g i z' = d → y i z = y i z') :
    TargetedMoment D g y d := by
  intro i
  obtain ⟨z, hz, hg⟩ := positive_cell_has_assignment D g i d (hp i)
  exact (constant_cell D g y i d (y i z) (hp i)
    (fun w hw he => hn i w z hw hz he hg)).1

/-- T12, general: when raw outcomes factor through an exposure-level schedule
on every feasible intervention, EPOs and the AEED equal that schedule's
potential-outcome contrasts under every positive design (SUTVA, p. 8). -/
theorem sutva_design_free (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (h : Fin N → ℝ → ℝ) (hc : ∀ i z, y i z = h i (g i z))
    (d d' : ℝ) (_hN : 0 < N) (hp : ∀ i, 0 < pi D g i d)
    (hp' : ∀ i, 0 < pi D g i d') :
    (∀ i, epo D g y i d = h i d ∧ eed D g y i d d' = h i d - h i d') ∧
    aeed D g y d d' = (N : ℝ)⁻¹ * ∑ i, (h i d - h i d') := by
  have hd (i : Fin N) : epo D g y i d = h i d :=
    (constant_cell D g y i d (h i d) (hp i)
      (fun z hz he => by rw [hc, he])).2.1
  have hd' (i : Fin N) : epo D g y i d' = h i d' :=
    (constant_cell D g y i d' (h i d') (hp' i)
      (fun z hz he => by rw [hc, he])).2.1
  constructor
  · intro i; simp only [eed, hd, hd', and_self]
  · simp only [aeed_average_eed_algebra, eed, hd, hd']

/-- T13(i): under NURVA, the EPO is the raw outcome at every supported
assignment in its exposure cell; Eq. (7) subtracts the two such values. -/
theorem nurva_epo (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (hn : NURVA D g y) (i : Fin N) (d : ℝ) (hp : 0 < pi D g i d)
    (z : Ω) (hz : Support D z) (hg : g i z = d) : epo D g y i d = y i z :=
  (constant_cell D g y i d (y i z) hp
    (fun w hw he => hn i w z hw hz (he.trans hg.symm))).2.1

/-- Common on-support value of an exposure cell, extended by zero for
unrevealable exposure labels: the SUTVA extension in T13(iii), p. 8. -/
noncomputable def stableValue (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (i : Fin N) (e : ℝ) : ℝ :=
  if h : ∃ z, Support D z ∧ g i z = e then y i (Classical.choose h) else 0

/-- Observed-data event probabilities for (Z,Y), Section 3.2, p. 4, and
the observational equivalence sentence on p. 8. -/
noncomputable def observedProbability (y : OutcomeSchedule Ω N)
    (A : Ω × (Fin N → ℝ) → Prop) : ℝ :=
  probability D (fun z => A (z, fun i => y i z))

/-- Observed-data laws depend only on the raw outcomes on the design support,
T13(iii), p. 8. -/
theorem observed_law_support (y y' : OutcomeSchedule Ω N)
    (hc : ∀ i z, Support D z → y i z = y' i z)
    (A : Ω × (Fin N → ℝ) → Prop) :
    observedProbability D y A = observedProbability D y' A := by
  unfold observedProbability probability
  apply tsum_congr
  intro z
  by_cases hz : Support D z
  · have he : (fun i => y i z) = (fun i => y' i z) := funext (fun i => hc i z hz)
    dsimp only
    simp only [he]
  · have hzero : D.p z = 0 := le_antisymm (le_of_not_gt hz) (D.nonneg z)
    simp [hzero]

/-- T13(iii): every NURVA raw schedule has a globally SUTVA schedule with
exactly the same observed-data law under this design (p. 8).
The other direction follows from `sutva_implies_nurva`. -/
theorem nurva_sutva_observational_equivalence (g : ExposureMapping Ω N)
    (y : OutcomeSchedule Ω N) (hn : NURVA D g y) :
    ∃ y' : OutcomeSchedule Ω N, SUTVA g y' ∧
      (∀ i z, Support D z → y i z = y' i z) ∧
      (∀ A, observedProbability D y A = observedProbability D y' A) := by
  let y' : OutcomeSchedule Ω N := fun i z => stableValue D g y i (g i z)
  have ha : ∀ i z, Support D z → y i z = y' i z := by
    intro i z hz
    have he : ∃ w, Support D w ∧ g i w = g i z := ⟨z, hz, rfl⟩
    dsimp [y', stableValue]
    rw [dite_eq_left he]
    exact hn i z (Classical.choose he) hz (Classical.choose_spec he).1
      (Classical.choose_spec he).2.symm
  refine ⟨y', ?_, ha, fun A => observed_law_support D y y' ha A⟩
  intro i z z' he
  dsimp [y']
  rw [he]

end Linear

/-! Explicit finite designs and the domain counterexample. -/

/-- Uniform finite randomization, used in the paper's finite examples and
in the T1 and T2 constructions. -/
noncomputable def uniformDesign (Ω : Type) [Fintype Ω] [Nonempty Ω] : Design Ω where
  p := fun _ => (Fintype.card Ω : ℝ)⁻¹
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  summable := Summable.of_finite
  total := by
    rw [tsum_fintype]
    simp [Fintype.card_ne_zero]

/-- Independent coordinate randomization: the probability of an assignment
is the product of its coordinate probabilities. T1 uses uniform ternary
coordinates; T4 uses independently randomized correlated binary pairs. -/
noncomputable def productDesign {A : Type} [Fintype A] (N : ℕ)
    (q : Fin N → Design A) : Design (Fin N → A) where
  p := fun z => ∏ i, (q i).p (z i)
  nonneg := fun z => Finset.prod_nonneg (fun i hi => (q i).nonneg _)
  summable := Summable.of_finite
  total := by
    rw [tsum_fintype, ← Fintype.prod_sum]
    have hi (i : Fin N) : ∑ a, (q i).p a = 1 := by
      rw [← tsum_fintype (L := .unconditional A)]; exact (q i).total
    simp only [hi, Finset.prod_const_one]

/-- The expectation of a constant one under any normalized design is one. -/
theorem expectation_one {Ω : Type} (D : Design Ω) :
    expectation D (fun _ => 1) = 1 := by
  simpa only [expectation, mul_one] using D.total

/-- Product designs factor expectations of products of coordinate functions.
This is an exact finite lemma for T1 and T4, not an independence assumption. -/
theorem product_expectation {A : Type} [Fintype A] (N : ℕ)
    (q : Fin N → Design A) (f : Fin N → A → ℝ) :
    expectation (productDesign N q) (fun z => ∏ i, f i (z i)) =
      ∏ i, expectation (q i) (f i) := by
  simp only [expectation, productDesign, tsum_fintype, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (q i).p a * f i a)).symm

/-- One-coordinate expectations under a product design use its marginal law;
an exact lemma for T1, T2(e), and T4. -/
theorem coordinate_expectation {A : Type} [Fintype A] (N : ℕ)
    (q : Fin N → Design A) (i : Fin N) (f : A → ℝ) :
    expectation (productDesign N q) (fun z => f (z i)) = expectation (q i) f := by
  have hh := product_expectation N q (fun j a => if j = i then f a else 1)
  have hff (j : Fin N) : expectation (q j) (fun a => if j = i then f a else 1) =
      if j = i then expectation (q j) f else 1 := by
    by_cases hj : j = i
    · simp only [hj, ite_true]
    · simp only [hj, ite_false, expectation_one]
  simpa only [hff, Finset.prod_ite_eq', Finset.mem_univ, ite_true] using hh

/-- Binary assignment space for the paper's two-person household examples,
Section 5.2, pp. 8–10, Tables 1–3. -/
abbrev BinaryPair := Fin 2 × Fin 2

/-- The individualistic mapping, g_i(z)=z_i, p. 5, for the two-person examples. -/
def pairAssignment (i : Fin 2) (z : BinaryPair) : ℝ :=
  if i = 0 then (z.1.val : ℝ) else (z.2.val : ℝ)

/-- The voting schedule, p. 8: "Person one votes iff Person two is treated,
and Person two votes iff Person one is treated." -/
def votingOutcome (i : Fin 2) (z : BinaryPair) : ℝ :=
  if i = 0 then (z.2.val : ℝ) else (z.1.val : ℝ)

/-- Table 1(a), pp. 8–9: a fair coin treats exactly one of the two people. -/
noncomputable def oppositeDesign : Design BinaryPair where
  p := fun z => if z.1 = z.2 then 0 else 1/2
  nonneg := fun z => by split_ifs <;> norm_num
  summable := Summable.of_finite
  total := by norm_num [tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Table 2(a) and Table 3(a), pp. 9–10: a fair coin treats both or neither. -/
noncomputable def sameDesign : Design BinaryPair where
  p := fun z => if z.1 = z.2 then 1/2 else 0
  nonneg := fun z => by split_ifs <;> norm_num
  summable := Summable.of_finite
  total := by norm_num [tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Equation (3), p. 5, specialized to a two-vertex adjacency edge:
g_1=z_1+2z_2 and g_2=z_2+2z_1, T2(a). -/
def networkExposure (i : Fin 2) (z : BinaryPair) : ℝ :=
  pairAssignment i z + 2 * votingOutcome i z

/-- Full exposure vector in the network example, Eq. (2), p. 4. -/
def networkVector (z : BinaryPair) : ℝ × ℝ :=
  (networkExposure 0 z, networkExposure 1 z)

/-- Membership in the network exposure image, T2(c): a hybrid
exposure argument has a value only on this image. -/
def InNetworkImage (r : ℝ × ℝ) : Prop := ∃ z : BinaryPair, networkVector z = r

/-- Membership in the raw assignment domain {0,1}^2 of Eq. (1), p. 4,
used for the literal raw-coordinate reading in T2(d). -/
def InBinaryDomain (r : ℝ × ℝ) : Prop :=
  (r.1 = 0 ∨ r.1 = 1) ∧ (r.2 = 0 ∨ r.2 = 1)

/-- T2(a): the exposure image consists of exactly four vectors, using the paper's Eq. (3). -/
theorem network_image (r : ℝ × ℝ) :
    InNetworkImage r ↔ r = (0,0) ∨ r = (2,1) ∨ r = (1,2) ∨ r = (3,3) := by
  constructor
  · rintro ⟨⟨x,y⟩, h⟩
    fin_cases x <;> fin_cases y <;>
      norm_num [networkVector, networkExposure, pairAssignment, votingOutcome] at h <;>
      aesop
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨(0,0), by norm_num [networkVector, networkExposure, pairAssignment, votingOutcome]⟩
    · exact ⟨(0,1), by norm_num [networkVector, networkExposure, pairAssignment, votingOutcome]⟩
    · exact ⟨(1,0), by norm_num [networkVector, networkExposure, pairAssignment, votingOutcome]⟩
    · exact ⟨(1,1), by norm_num [networkVector, networkExposure, pairAssignment, votingOutcome]⟩

/-- T2(a)–(d): positivity and SUTVA hold and AEED is one, but the two
printed hybrid exposure arguments are never both in the exposure image.
Read as raw assignment arguments, their joint domain probability is one half
for each unit. This certifies domain membership, not a totalized expression
pretending to evaluate an undefined raw outcome. -/
theorem network_domain_counterexample :
    (∀ i : Fin 2, ∀ e : Fin 4,
      pi (uniformDesign BinaryPair) networkExposure i (e.val : ℝ) = 1/4) ∧
    (∀ i : Fin 2, epo (uniformDesign BinaryPair) networkExposure pairAssignment i 1 = 1 ∧
      epo (uniformDesign BinaryPair) networkExposure pairAssignment i 0 = 0) ∧
    aeed (uniformDesign BinaryPair) networkExposure pairAssignment 1 0 = 1 ∧
    SUTVA networkExposure pairAssignment ∧
    (∀ z : BinaryPair,
      ¬(InNetworkImage (1,networkExposure 1 z) ∧
        InNetworkImage (0,networkExposure 1 z)) ∧
      ¬(InNetworkImage (networkExposure 0 z,1) ∧
        InNetworkImage (networkExposure 0 z,0))) ∧
    probability (uniformDesign BinaryPair) (fun z =>
      InBinaryDomain (1,networkExposure 1 z) ∧
      InBinaryDomain (0,networkExposure 1 z)) = 1/2 ∧
    probability (uniformDesign BinaryPair) (fun z =>
      InBinaryDomain (networkExposure 0 z,1) ∧
      InBinaryDomain (networkExposure 0 z,0)) = 1/2 := by
  have hpi : ∀ i : Fin 2, ∀ e : Fin 4,
      pi (uniformDesign BinaryPair) networkExposure i (e.val : ℝ) = 1/4 := by
    intro i e
    fin_cases i <;> fin_cases e <;>
      norm_num [pi, probability, uniformDesign, networkExposure, pairAssignment,
        votingOutcome, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
  refine ⟨hpi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      norm_num [epo, expectation, pi, probability, uniformDesign, networkExposure,
        pairAssignment, votingOutcome, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [aeed, aepo, epo, expectation, pi, probability, uniformDesign, networkExposure,
      pairAssignment, votingOutcome, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
  · intro i ⟨x,y⟩ ⟨x',y'⟩ h
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
      norm_num [networkExposure, pairAssignment, votingOutcome] at *
  · rintro ⟨x,y⟩
    fin_cases x <;> fin_cases y <;>
      norm_num [network_image, networkExposure, pairAssignment, votingOutcome]
  · norm_num [probability, uniformDesign, InBinaryDomain, networkExposure,
      pairAssignment, votingOutcome, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [probability, uniformDesign, InBinaryDomain, networkExposure,
      pairAssignment, votingOutcome, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- T14, Tables 1 and 2, pp. 8–10: the voting rule gives AEEDs −1, 1 and
0 under the three printed designs; on the original support NURVA holds, while
global SUTVA fails. Every table's raw outcomes are those of `votingOutcome`. -/
theorem household_tables :
    aepo oppositeDesign pairAssignment votingOutcome 1 = 0 ∧
    aepo oppositeDesign pairAssignment votingOutcome 0 = 1 ∧
    aeed oppositeDesign pairAssignment votingOutcome 1 0 = -1 ∧
    NURVA oppositeDesign pairAssignment votingOutcome ∧
    ¬SUTVA pairAssignment votingOutcome ∧
    aeed sameDesign pairAssignment votingOutcome 1 0 = 1 ∧
    aeed (uniformDesign BinaryPair) pairAssignment votingOutcome 1 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try norm_num [aepo, aeed, epo, expectation, pi, probability, oppositeDesign,
    sameDesign, uniformDesign, pairAssignment, votingOutcome,
    tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
  · intro i ⟨x,y⟩ ⟨x',y'⟩ hz hz' he
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
      norm_num [Support, oppositeDesign, pairAssignment, votingOutcome] at *
  · intro h
    have hh := h 0 (1,0) (1,1) (by norm_num [pairAssignment])
    norm_num [votingOutcome] at hh

/-- T12, Table 3, pp. 9–10: use the housemate's assignment as exposure;
the AEED is one for every positive design, including both printed Table 3 laws. -/
theorem household_sutva (D : Design BinaryPair)
    (hp : ∀ i : Fin 2, 0 < pi D votingOutcome i 1 ∧ 0 < pi D votingOutcome i 0) :
    SUTVA votingOutcome votingOutcome ∧ aeed D votingOutcome votingOutcome 1 0 = 1 := by
  constructor
  · intro i z z' he; exact he
  · have hh := sutva_design_free D votingOutcome votingOutcome (fun _ e => e)
      (fun _ _ => rfl) 1 0 (by norm_num) (fun i => (hp i).1) (fun i => (hp i).2)
    simpa using hh.2

/-! The missing-first-moment counterexample on the full real assignment space. -/

/-- Embed a normalized discrete design into a larger feasible assignment set,
giving added assignments probability zero (Section 3.1, p. 3). -/
noncomputable def extendDesign {A B : Type} (f : A → B) (hf : Function.Injective f)
    (D : Design A) : Design B where
  p := Function.extend f D.p (fun _ => 0)
  nonneg := by
    intro b
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [Function.Injective.extend_apply hf]
      exact D.nonneg a
    · rw [Function.extend_apply' D.p (fun _ => 0) b hb]
  summable := by
    apply (hf.summable_iff _).mp
    · simpa only [Function.extend_comp hf] using D.summable
    · intro b hb
      exact Function.extend_apply' D.p (fun _ => 0) b hb
  total := by
    have hh : Function.support (Function.extend f D.p (fun _ => 0)) ⊆ Set.range f := by
      intro b hb
      by_contra h
      exact hb (Function.extend_apply' D.p (fun _ => 0) b h)
    rw [← hf.tsum_eq hh]
    simpa only [Function.Injective.extend_apply hf] using D.total

/-- Expectations under an embedded discrete design agree with its original
atom-weighted expectations, including non-summability cases as algebraic sums.
Existence is separately asserted using `Integrable`. -/
theorem extended_expectation_algebra {A B : Type} (f : A → B) (hf : Function.Injective f)
    (D : Design A) (Y : B → ℝ) :
    expectation (extendDesign f hf D) Y = expectation D (fun a => Y (f a)) := by
  unfold expectation
  have hh : Function.support (fun b => (extendDesign f hf D).p b * Y b) ⊆ Set.range f := by
    intro b hb
    by_contra h
    have he : (extendDesign f hf D).p b = 0 :=
      Function.extend_apply' D.p (fun _ => 0) b h
    exact hb (by simpa only [he, zero_mul])
  rw [← hf.tsum_eq hh]
  simp only [extendDesign, Function.Injective.extend_apply hf]

/-- T7: embedding a discrete design preserves its genuine signed
expectations, assuming the pulled-back outcome has a finite absolute moment. -/
theorem extended_expectation {A B : Type} (f : A → B) (hf : Function.Injective f)
    (D : Design A) (Y : B → ℝ) (_hY : Integrable D (fun a => Y (f a))) :
    expectation (extendDesign f hf D) Y = expectation D (fun a => Y (f a)) :=
  extended_expectation_algebra f hf D Y

/-- Event probabilities under an embedded discrete design agree with the
probabilities of their preimages, Section 3, p. 3. -/
theorem extended_probability {A B : Type} (f : A → B) (hf : Function.Injective f)
    (D : Design A) (E : B → Prop) :
    probability (extendDesign f hf D) E = probability D (fun a => E (f a)) := by
  unfold probability
  have hh : Function.support (fun b => if E b then (extendDesign f hf D).p b else 0)
      ⊆ Set.range f := by
    intro b hb
    by_contra h
    have he : (extendDesign f hf D).p b = 0 :=
      Function.extend_apply' D.p (fun _ => 0) b h
    exact hb (by simp only [he, ite_self])
  rw [← hf.tsum_eq hh]
  simp only [extendDesign, Function.Injective.extend_apply hf]

/-- T7(a): the support atom k has weight 2^{−k−1}, including weight 1/2
at k=0. -/
noncomputable def geometricWeight (k : ℕ) : ℝ := (1/2 : ℝ)^(k+1)

/-- T7's probability law on its countable support, before adding the remaining
real feasible assignments of zero probability. -/
noncomputable def geometricDesign : Design ℕ where
  p := geometricWeight
  nonneg := fun k => pow_nonneg (by norm_num) _
  summable := by
    change Summable (fun k : ℕ => (1/2 : ℝ)^(k+1))
    simp_rw [pow_succ]
    exact
      (summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)).mul_right (1/2)
  total := by
    simp only [geometricWeight, pow_succ, tsum_mul_right]
    rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)]
    norm_num

/-- T7's full real assignment space Ω=Z=R; Z is the identity. The power-set
probability is `probability realGeometricDesign`, not a zero measure. -/
noncomputable def realGeometricDesign : Design ℝ :=
  extendDesign (fun k : ℕ => (k : ℝ)) Nat.cast_injective geometricDesign

/-- T7: exposure one means a positive integer assignment, exposure zero
otherwise; this is defined on every real feasible assignment. -/
noncomputable def divergentExposure : ExposureMapping ℝ 1 := fun _ =>
  Function.extend (fun k : ℕ => (k : ℝ))
    (fun k => if k = 0 then 0 else 1) (fun _ => 0)

/-- T7: y_1(k)=(-1)^{k+1}2^{k+1} for positive integer k and zero elsewhere.
Every raw potential outcome is a finite real number. -/
def divergentNaturalOutcome (k : ℕ) : ℝ :=
  if k = 0 then 0 else (-1 : ℝ)^(k+1) * 2^(k+1)

/-- The T7 raw schedule on all of Z=R, with zero values at non-support points. -/
noncomputable def divergentOutcome : OutcomeSchedule ℝ 1 := fun _ =>
  Function.extend (fun k : ℕ => (k : ℝ)) divergentNaturalOutcome (fun _ => 0)

/-- T7(c): each positive integer's weighted outcome is an alternating unit
term, starting with +1 at k=1. -/
theorem divergent_weighted_term (k : ℕ) :
    geometricWeight (k+1) * divergentNaturalOutcome (k+1) = (-1 : ℝ)^k := by
  simp only [geometricWeight, divergentNaturalOutcome, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ite_false]
  calc
    (1/2 : ℝ)^(k+1+1) * ((-1 : ℝ)^(k+1+1) * 2^(k+1+1)) =
        (-1 : ℝ)^(k+1+1) * (((1/2 : ℝ) * 2)^(k+1+1)) := by rw [mul_pow]; ring
    _ = (-1 : ℝ)^k := by norm_num [pow_add]

/-- T7(c): positive and negative weighted parts through the first 2m
positive support points each sum to m, the absolute sum is 2m, and the signed
sum is zero; the next odd partial sum is one. -/
theorem divergent_partial_sums (m : ℕ) :
    (∑ k ∈ Finset.range (2*m), max ((-1 : ℝ)^k) 0) = (m : ℝ) ∧
    (∑ k ∈ Finset.range (2*m), max (-((-1 : ℝ)^k)) 0) = (m : ℝ) ∧
    (∑ k ∈ Finset.range (2*m), |(-1 : ℝ)^k|) = 2*m ∧
    (∑ k ∈ Finset.range (2*m), (-1 : ℝ)^k) = 0 ∧
    (∑ k ∈ Finset.range (2*m+1), (-1 : ℝ)^k) = 1 := by
  induction m with
  | zero => norm_num
  | succ m hm =>
    have he : (-1 : ℝ)^(2*m) = 1 := by rw [pow_mul]; norm_num
    have ho : (-1 : ℝ)^(2*m+1) = -1 := by rw [pow_add, he]; norm_num
    rcases hm with ⟨hp, hn, ha, hs, hs'⟩
    have hnext : 2*(m+1) = (2*m+1)+1 := by omega
    simp only [hnext, Finset.sum_range_succ, he, ho, pow_succ,
      mul_neg_one, neg_neg, Nat.cast_add, Nat.cast_one]
    norm_num [hp, hn, ha, hs]
    ring

/-- T7(d)–(e): the alternating weighted numerator and both its doubled HT
counterparts fail to be summable. This establishes an existence failure,
not a biased finite expectation. -/
theorem alternating_not_summable : ¬Summable (fun k : ℕ => (-1 : ℝ)^k) := by
  intro h
  have hh : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa only [abs_pow, abs_neg, abs_one, one_pow] using h.abs
  have hf := (summable_const_iff (1 : ℝ)).mp hh
  norm_num at hf

/-- T7(b),(d),(e): both exposure probabilities are one half, exposure-zero
EPO is zero, and neither the exposed raw numerator nor the HT mean exists as
a signed sum on the actual real assignment domain. -/
theorem missing_moment_counterexample :
    pi realGeometricDesign divergentExposure 0 1 = 1/2 ∧
    pi realGeometricDesign divergentExposure 0 0 = 1/2 ∧
    epo realGeometricDesign divergentExposure divergentOutcome 0 0 = 0 ∧
    ¬Summable (fun z : ℝ => realGeometricDesign.p z *
      (if divergentExposure 0 z = 1 then divergentOutcome 0 z else 0)) ∧
    ¬Integrable realGeometricDesign (ht realGeometricDesign divergentExposure divergentOutcome 1) := by
  have hcast (k : ℕ) : realGeometricDesign.p (k : ℝ) = geometricWeight k := by
    simp only [realGeometricDesign, extendDesign, geometricDesign,
      Function.Injective.extend_apply Nat.cast_injective]
  have hg (k : ℕ) : divergentExposure 0 (k : ℝ) = (if k = 0 then 0 else 1 : ℝ) := by
    simp only [divergentExposure, Function.Injective.extend_apply Nat.cast_injective]
  have hy (k : ℕ) : divergentOutcome 0 (k : ℝ) = divergentNaturalOutcome k := by
    simp only [divergentOutcome, Function.Injective.extend_apply Nat.cast_injective]
  have tailmass : (∑' k : ℕ, if k = 0 then 0 else geometricWeight k) = 1/2 := by
    have hh := geometricDesign.summable.tsum_eq_add_tsum_ite 0
    have he : geometricDesign.p 0 = (1/2 : ℝ) := by norm_num [geometricDesign, geometricWeight]
    rw [geometricDesign.total, he] at hh
    change 1 = 1/2 + (∑' k : ℕ, if k = 0 then 0 else geometricWeight k) at hh
    linarith
  have hpi1 : pi realGeometricDesign divergentExposure 0 1 = 1/2 := by
    unfold pi realGeometricDesign
    rw [extended_probability]
    unfold probability
    simp only [divergentExposure, Function.Injective.extend_apply Nat.cast_injective,
      geometricDesign]
    convert tailmass using 1
    apply tsum_congr
    intro k
    by_cases hk : k = 0 <;> simp [hk]
  have hpi0 : pi realGeometricDesign divergentExposure 0 0 = 1/2 := by
    unfold pi realGeometricDesign
    rw [extended_probability]
    unfold probability
    simp only [divergentExposure, Function.Injective.extend_apply Nat.cast_injective,
      geometricDesign]
    have heq : ∀ k : ℕ, (if (if k = 0 then 0 else 1 : ℝ) = 0 then geometricWeight k else 0) =
        if k = 0 then geometricWeight k else 0 := by
      intro k; by_cases hk : k = 0 <;> simp [hk]
    simp only [heq]
    simp [geometricWeight]
  refine ⟨hpi1, hpi0, ?_, ?_, ?_⟩
  · unfold epo
    have hn : expectation realGeometricDesign (fun z =>
        if divergentExposure 0 z = 0 then divergentOutcome 0 z else 0) = 0 := by
      unfold realGeometricDesign
      rw [extended_expectation_algebra]
      unfold expectation
      have hh : ∀ k : ℕ, geometricDesign.p k *
          (if divergentExposure 0 (k : ℝ) = 0 then divergentOutcome 0 (k : ℝ) else 0) = 0 := by
        intro k
        rw [hg, hy]
        by_cases hk : k = 0 <;> simp [hk, divergentNaturalOutcome]
      simp only [hh, tsum_zero]
    rw [hn, zero_div]
  · intro h
    have hs := h.comp_injective (Nat.cast_injective.comp Nat.succ_injective)
    apply alternating_not_summable
    exact hs.congr (fun k => by
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      rw [hcast, hg, hy]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
        ite_true]
      exact divergent_weighted_term k)
  · intro h
    have hs := (integrable_summable realGeometricDesign h).comp_injective
      (Nat.cast_injective.comp Nat.succ_injective)
    apply alternating_not_summable
    apply (hs.div_const 2).congr
    intro k
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    simp only [ht, Fin.sum_univ_one, Nat.cast_one, inv_one, one_mul,
      hpi1, hg, hy, hcast]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, ite_true]
    calc
      (geometricWeight (k+1) * (divergentNaturalOutcome (k+1) / (1/2))) / 2 =
          geometricWeight (k+1) * divergentNaturalOutcome (k+1) := by ring
      _ = (-1 : ℝ)^k := divergent_weighted_term k

/-! General corrected comparison, and the explicit printed general claims. -/

/-- Independence under the discrete design: all pairs of inverse-image events
factor. Used for Z_i versus Z_{−i} and D_i versus D_{−i} in corrected T3. -/
def Independent {Ω A B : Type} (D : Design Ω) (X : Ω → A) (Y : Ω → B) : Prop :=
  ∀ E : A → Prop, ∀ F : B → Prop,
    probability D (fun z => E (X z) ∧ F (Y z)) =
      probability D (fun z => E (X z)) * probability D (fun z => F (Y z))

/-- Mutual independence of a finite family of exposures: probabilities of
rectangular events factor. The unused coordinates can have the universal event. -/
def MutuallyIndependent {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) : Prop :=
  ∀ E : Fin N → ℝ → Prop,
    probability D (fun z => ∀ i, E i (g i z)) =
      ∏ i, probability D (fun z => E i (g i z))

/-- The vector of other units' coordinates, footnote 8, p. 7, and p. 14.
No arbitrary filler coordinate is introduced. -/
def others {N : ℕ} (v : Fin N → ℝ) (i : Fin N) : {j : Fin N // j ≠ i} → ℝ :=
  fun j => v j.val

/-- Hybrid assignment (e;w), footnote 8, p. 7; its membership in the
feasible assignment space must be established before evaluating raw outcomes. -/
def fromOthers {N : ℕ} (i : Fin N) (e : ℝ)
    (w : {j : Fin N // j ≠ i} → ℝ) : Fin N → ℝ :=
  fun j => if h : j = i then e else w ⟨j,h⟩

/-- Assignment-coordinate exposure on a feasible subset of R^N, T3(i). -/
def coordinateMapping {N : ℕ} (S : Set (Fin N → ℝ)) : ExposureMapping S N :=
  fun i z => z.val i

/-- Raw hybrid outcome at (e;Z_{−i}); zero is only an off-domain filler for
a total Lean function. The corrected comparison explicitly proves all relevant
hybrids belong to the positive support, so this filler is not an assumption. -/
noncomputable def hybridOutcome {N : ℕ} (S : Set (Fin N → ℝ))
    (y : OutcomeSchedule S N) (i : Fin N) (e : ℝ) (z : S) : ℝ :=
  if h : fromOthers i e (others z.val i) ∈ S then
    y i ⟨fromOthers i e (others z.val i),h⟩ else 0

/-- Assignment average direct effect, footnote 8, p. 7, as repaired in T3
and T5: (1/N)∑ E[y_i(d;Z_{−i})−y_i(d';Z_{−i})]. -/
noncomputable def averageDirectEffect {N : ℕ} (S : Set (Fin N → ℝ))
    (D : Design S) (y : OutcomeSchedule S N) (d d' : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, expectation D (fun z => hybridOutcome S y i d z - hybridOutcome S y i d' z)

/- The false printed assertion of general well-definedness is represented as a
closed proposition in P061_PrintedClaims and refuted in P061_Refutations using
the positive geometric design. -/


/- The false printed assertion of general HT unbiasedness is represented as a
closed proposition in P061_PrintedClaims and refuted in P061_Refutations using
the positive geometric design. -/

/-- T6(iii): with binary individualistic exposures,
AEED equals ADSE, the average of conditional own-assignment contrasts.
All design probabilities and raw schedules on the common domain are allowed. -/
theorem binary_adse_identity {N : ℕ} (D : Design (Fin N → Fin 2))
    (y : OutcomeSchedule (Fin N → Fin 2) N) (hN : 0 < N)
    (hp : ∀ i, 0 < pi D (fun i z => (z i).val) i 1)
    (hp' : ∀ i, 0 < pi D (fun i z => (z i).val) i 0) :
    aeed D (fun i z => (z i).val) y 1 0 = (N : ℝ)⁻¹ * ∑ i,
      (conditionalMean D (fun i z => (z i).val) y i 1 -
        conditionalMean D (fun i z => (z i).val) y i 0) :=
  (corrected_attribution D _ y 1 0 hN hp hp').2

/-- Exposed-outcome sum divided by the fixed number n, supplement Eq. (2),
p. 1. It is the sample mean when the realized exposure count equals n. -/
noncomputable def sampleMean {Ω : Type} {N : ℕ} (g : ExposureMapping Ω N)
    (y : OutcomeSchedule Ω N) (d : ℝ) (n : ℕ) (z : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, if g i z = d then y i z else 0

/-- T17(a)–(b), supplement Eq. (2) and the p. 2 take-away: equal marginal
probabilities n/N make the exposed-outcome sum divided by the fixed number n
unbiased for the AEPO, for arbitrary raw schedules on a finite design.
For a design with exactly n exposed units, this is the actual sample mean. -/
theorem sample_mean_unbiased {Ω : Type} [Fintype Ω] {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (n : ℕ)
    (hN : 0 < N) (hn : 0 < n) (hp : ∀ i, pi D g i d = (n : ℝ)/N) :
    expectation D (sampleMean g y d n) = aepo D g y d := by
  have he : sampleMean g y d n = ht D g y d :=
    funext (fun z => (ht_sample_mean D g y d n hN hn hp z).symm)
  rw [he]
  exact ht_unbiased D g y d (finite_type_targeted_moment D g y d)

/-- T17(c), the exact algebraic criterion for unbiased difference in means,
including completely randomized treatment of n_1 of N units. Raw outcomes
may depend on every coordinate; no NURVA restriction is imposed. -/
theorem difference_in_means_unbiased {Ω : Type} [Fintype Ω] {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (n₁ : ℕ)
    (hN : 0 < N) (hn : 0 < n₁) (hn' : n₁ < N)
    (hp : ∀ i, pi D g i 1 = (n₁ : ℝ)/N)
    (hp' : ∀ i, pi D g i 0 = ((N-n₁ : ℕ) : ℝ)/N) :
    expectation D (fun z => sampleMean g y 1 n₁ z - sampleMean g y 0 (N-n₁) z) =
      aeed D g y 1 0 := by
  rw [expectation_sub D Summable.of_finite Summable.of_finite,
    sample_mean_unbiased D g y 1 n₁ hN hn hp,
    sample_mean_unbiased D g y 0 (N-n₁) hN (Nat.sub_pos_of_lt hn') hp']
  rfl

/-- Fixed-count uniform binary assignment law, the conventional SRS and
complete-randomization designs specified by T17. -/
def CompleteRandomization {N : ℕ} (D : Design (Fin N → Fin 2)) (n : ℕ) : Prop :=
  ∀ z, D.p z = if (Finset.univ.filter (fun i => z i = 1)).card = n then
    (Nat.choose N n : ℝ)⁻¹ else 0

/-- The double-sum covariance expression, supplement Eqs. (5),(9), pp. 3–4. -/
noncomputable def htCovarianceExpression {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) : ℝ :=
  (N : ℝ)⁻¹^2 * ∑ i, ∑ j,
    ((jointPi D g i j d d' - pi D g i d * pi D g j d') /
      (pi D g i d * pi D g j d')) * epo D g y i d * epo D g y j d'

/-- Supplement Eq. (6), p. 3: the HT estimator of the HT AEPO variance. -/
noncomputable def htVarianceEstimator {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (z : Ω) : ℝ :=
  (N : ℝ)⁻¹^2 * ∑ i, ∑ j,
    ((jointPi D g i j d d - pi D g i d * pi D g j d) /
      (pi D g i d * pi D g j d)) * y i z * y j z *
      (if g i z = d ∧ g j z = d then 1 else 0) / jointPi D g i j d d

/-- Supplement Eq. (7), pp. 3–4: the conservative estimator. Ordered
pairs of zero joint probability receive the two Young-inequality square terms. -/
noncomputable def conservativeVarianceEstimator {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (z : Ω) : ℝ :=
  (N : ℝ)⁻¹^2 * ∑ i, ∑ j,
    if 0 < jointPi D g i j d d then
      ((jointPi D g i j d d - pi D g i d * pi D g j d) /
        (pi D g i d * pi D g j d)) * y i z * y j z *
        (if g i z = d ∧ g j z = d then 1 else 0) / jointPi D g i j d d
    else if jointPi D g i j d d = 0 then
      (if g i z = d then y i z^2 / 2 else 0) / pi D g i d +
      (if g j z = d then y j z^2 / 2 else 0) / pi D g j d
    else 0

/-- Supplement p. 7, regression-type estimator preceding Eq. (10).
F_i(z)=f_d(X_i,β̂(z)) represents the possibly random prediction used for unit i. -/
noncomputable def regressionEstimator {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y F : OutcomeSchedule Ω N) (d : ℝ) (z : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (if g i z = d then y i z - F i z else 0) / pi D g i d +
  (N : ℝ)⁻¹ * ∑ i, F i z


/-- T20, supplement Eq. (10), with the existence of its expectations
made explicit on general discrete support: targeted outcome/prediction moments
and integrable predictions give integrable, unbiased adjustment under the
printed prediction moment condition. No NURVA or SUTVA is imposed. -/
theorem covariate_adjustment {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y F : OutcomeSchedule Ω N) (d : ℝ) (_hN : 0 < N)
    (_hp : ∀ i, 0 < pi D g i d) (hy : TargetedMoment D g y d)
    (hF : ∀ i, Integrable D (F i)) (hFd : TargetedMoment D g F d)
    (hc : ∀ i, expectation D (fun z => (if g i z = d then F i z else 0)/pi D g i d) =
      expectation D (F i)) :
    Integrable D (regressionEstimator D g y F d) ∧
    expectation D (regressionEstimator D g y F d) = aepo D g y d := by
  have he : regressionEstimator D g y F d = fun z =>
      ht D g y d z - ht D g F d z + (N : ℝ)⁻¹ * ∑ i, F i z := by
    funext z
    simp only [regressionEstimator, ht, ← mul_sub, ← Finset.sum_sub_distrib, ← sub_div]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  have hs := integrable_sub D (ht_integrable D g y d hy) (ht_integrable D g F d hFd)
  have hf := integrable_mul D (integrable_sum D F hF) (N : ℝ)⁻¹
  have hadd : expectation D (fun z => ht D g y d z - ht D g F d z +
      (N : ℝ)⁻¹ * ∑ i, F i z) =
      expectation D (ht D g y d) - expectation D (ht D g F d) +
        (N : ℝ)⁻¹ * ∑ i, expectation D (F i) := by
    calc
      _ = expectation D (fun z => ht D g y d z - ht D g F d z) +
          expectation D (fun z => (N : ℝ)⁻¹ * ∑ i, F i z) := by
        unfold expectation
        simp only [mul_add]
        exact Summable.tsum_add (integrable_summable D hs) (integrable_summable D hf)
      _ = _ := by
        rw [expectation_sub D (ht_integrable D g y d hy) (ht_integrable D g F d hFd),
          expectation_mul_algebra, expectation_sum D F hF]
  rw [he]
  constructor
  · apply integrable_of_summable D
    simpa only [mul_add] using (integrable_summable D hs).add (integrable_summable D hf)
  · rw [hadd, ht_unbiased D g y d hy]
    have hpred : expectation D (ht D g F d) = (N : ℝ)⁻¹ * ∑ i, expectation D (F i) := by
      unfold ht
      rw [expectation_mul_algebra, expectation_sum D _ (fun i => integrable_div D (hFd i) _)]
      simp_rw [hc]
    rw [hpred]
    ring

/-- Convergence in probability in the supplement's sequence of design laws
(p. 5). Assignment spaces may change with N; probabilities are never compared
using a common sample space. -/
def ConvergesInProbability {Ω : ℕ → Type} (D : ∀ N, Design (Ω N))
    (X : ∀ N, Ω N → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun N => probability (D N) (fun z => |X N z - a| > ε)) atTop (𝓝 0)

/-- T10's corrected o(N^{1/4}) maximum-degree rate. Only a predicate on
population-indexed degree sequences is asserted here, not a CLT. -/
def MaxDegreeQuarterRate (dmax : ℕ → ℝ) : Prop :=
  Tendsto (fun N => dmax N / Real.rpow (N : ℝ) (1/4 : ℝ)) atTop (𝓝 0)

/-- T10's corrected O(1) average-degree rate, with the target's uniform
supremum interpretation (supplement p. 6, last paragraph). -/
def AverageDegreeBounded (davg : ℕ → ℝ) : Prop := ∃ C : ℝ, ∀ N, davg N ≤ C

/-- T10's corrected O(N^{1/2}) maximum-degree rate, with population size N
in the denominator rather than the supplement's sample-count symbol n. -/
def MaxDegreeHalfRate (dmax : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ N, dmax N / Real.rpow (N : ℝ) (1/2 : ℝ) ≤ C

/-- T10: transcription of the three corrected degree-rate conditions as
precise sequence predicates. This certifies their definitions, not any of the
literature attributions in the paragraph. -/
theorem corrected_degree_rates (dmax davg : ℕ → ℝ) :
    (MaxDegreeQuarterRate dmax ↔
      Tendsto (fun N => dmax N / Real.rpow (N : ℝ) (1/4 : ℝ)) atTop (𝓝 0)) ∧
    (AverageDegreeBounded davg ↔ ∃ C : ℝ, ∀ N, davg N ≤ C) ∧
    (MaxDegreeHalfRate dmax ↔
      ∃ C : ℝ, ∀ N, dmax N / Real.rpow (N : ℝ) (1/2 : ℝ) ≤ C) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! Coarsened treatment versions, P061-T1. -/

/-- Independent uniform ternary assignments of T1: the full design space is
{0,1,2}^N and every vector has probability 3^{−N}. -/
noncomputable def ternaryDesign (N : ℕ) : Design (Fin N → Fin 3) :=
  productDesign N (fun _ => uniformDesign (Fin 3))

/-- Section 6.2, p. 11: "g_i(z)=1 if z_i>0, 0 otherwise", T1. -/
def ternaryValue (a : Fin 3) : ℝ := if a = 0 then 0 else 1

/-- The exposure coordinate D_i=g_i(Z), Eq. (2), for the T1 coarsening. -/
def ternaryExposure {N : ℕ} : ExposureMapping (Fin N → Fin 3) N :=
  fun i z => ternaryValue (z i)

/-- T1's raw schedule y_i(z)=z_i, with no between-unit interference. -/
def ternaryOutcome {N : ℕ} : OutcomeSchedule (Fin N → Fin 3) N :=
  fun i z => ((z i).val : ℝ)

/-- Product designs factor probabilities of all rectangular coordinate events;
this proves the mutual independence used in T1(a). -/
theorem product_events {A : Type} [Fintype A] (N : ℕ) (q : Fin N → Design A)
    (E : Fin N → A → Prop) :
    probability (productDesign N q) (fun z => ∀ i, E i (z i)) =
      ∏ i, probability (q i) (E i) := by
  unfold probability
  rw [tsum_fintype]
  have he (z : Fin N → A) : (if ∀ i, E i (z i) then ∏ i, (q i).p (z i) else 0) =
      ∏ i, if E i (z i) then (q i).p (z i) else 0 := by
    by_cases h : ∀ i, E i (z i)
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      simp only [h, ite_false]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  trans ∑ z : Fin N → A, ∏ i, if E i (z i) then (q i).p (z i) else 0
  · apply Finset.sum_congr rfl
    intro z hz
    by_cases h : ∀ i, E i (z i)
    · simp [productDesign, h]
    · have hp : (∏ i, if E i (z i) then (q i).p (z i) else 0) = 0 := by
        obtain ⟨i, hi⟩ := not_forall.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      simp [productDesign, h, hp]
  · simp only [tsum_fintype]
    exact (Fintype.prod_sum (fun i a => if E i a then (q i).p a else 0)).symm

/-- One-coordinate event probabilities under a product design; an exact
finite marginalization lemma for T1, T2(e) and T4. -/
theorem coordinate_probability {A : Type} [Fintype A] (N : ℕ)
    (q : Fin N → Design A) (i : Fin N) (E : A → Prop) :
    probability (productDesign N q) (fun z => E (z i)) = probability (q i) E := by
  have hh := coordinate_expectation N q i (fun a => if E a then 1 else 0)
  have he {B : Type} (D : Design B) (F : B → Prop) :
      expectation D (fun z => if F z then 1 else 0) = probability D F := by
    unfold expectation probability
    apply tsum_congr
    intro z; by_cases h : F z <;> simp [h]
  simpa only [he] using hh

/-- T1(b)–(c): all ternary coarsened-exposure marginal probabilities and EPOs
are exactly 2/3, 1/3 and 3/2, 0 at every N. -/
theorem ternary_marginals (N : ℕ) (i : Fin N) :
    pi (ternaryDesign N) ternaryExposure i 1 = 2/3 ∧
    pi (ternaryDesign N) ternaryExposure i 0 = 1/3 ∧
    epo (ternaryDesign N) ternaryExposure ternaryOutcome i 1 = 3/2 ∧
    epo (ternaryDesign N) ternaryExposure ternaryOutcome i 0 = 0 := by
  have hpi1 : pi (ternaryDesign N) ternaryExposure i 1 = 2/3 := by
    unfold pi ternaryDesign ternaryExposure ternaryValue
    rw [coordinate_probability N (fun _ => uniformDesign (Fin 3)) i (fun a : Fin 3 => (if a = 0 then 0 else 1 : ℝ) = 1)]
    norm_num [probability, uniformDesign, tsum_fintype, Fin.sum_univ_succ]
  have hpi0 : pi (ternaryDesign N) ternaryExposure i 0 = 1/3 := by
    unfold pi ternaryDesign ternaryExposure ternaryValue
    rw [coordinate_probability N (fun _ => uniformDesign (Fin 3)) i (fun a : Fin 3 => (if a = 0 then 0 else 1 : ℝ) = 0)]
    norm_num [probability, uniformDesign, tsum_fintype, Fin.sum_univ_succ]
  refine ⟨hpi1, hpi0, ?_, ?_⟩
  · unfold epo
    rw [hpi1]
    change expectation (productDesign N (fun _ => uniformDesign (Fin 3)))
      (fun z => if (if z i = 0 then 0 else 1 : ℝ) = 1 then ((z i).val : ℝ) else 0) / (2/3) = 3/2
    rw [coordinate_expectation N (fun _ => uniformDesign (Fin 3)) i (fun a : Fin 3 => if (if a = 0 then 0 else 1 : ℝ) = 1 then (a.val : ℝ) else 0)]
    norm_num [expectation, uniformDesign, tsum_fintype, Fin.sum_univ_succ]
  · unfold epo
    rw [hpi0]
    change expectation (productDesign N (fun _ => uniformDesign (Fin 3)))
      (fun z => if (if z i = 0 then 0 else 1 : ℝ) = 0 then ((z i).val : ℝ) else 0) / (1/3) = 0
    rw [coordinate_expectation N (fun _ => uniformDesign (Fin 3)) i (fun a : Fin 3 => if (if a = 0 then 0 else 1 : ℝ) = 0 then (a.val : ℝ) else 0)]
    norm_num [expectation, uniformDesign, tsum_fintype, Fin.sum_univ_succ]

/-- The exposure vector encoded as compatible raw coordinates in {0,1}^N,
for the printed D_{−i} reading of the T1 direct effect. -/
def ternaryExposureAssignment {N : ℕ} (z : Fin N → Fin 3) : Fin N → Fin 3 :=
  fun i => if z i = 0 then 0 else 1

/-- T1(a)–(e): explicit independent exposures, bounded outcomes and no
interference satisfy positivity at every N, but AEED is 3/2 while both the
printed D-hybrid and repaired Z-hybrid direct effects are exactly one.
This is an exact nonvanishing gap, not an asymptotic approximation. -/
theorem coarsened_version_counterexample (N : ℕ) (hN : 0 < N) :
    MutuallyIndependent (ternaryDesign N) ternaryExposure ∧
    (∀ (i : Fin N) (z : Fin N → Fin 3), 0 ≤ ternaryOutcome i z ∧ ternaryOutcome i z ≤ 2) ∧
    (∀ (i : Fin N) (z z' : Fin N → Fin 3), z i = z' i → ternaryOutcome i z = ternaryOutcome i z') ∧
    IndividualPositivity (ternaryDesign N) ternaryExposure 1 ∧
    IndividualPositivity (ternaryDesign N) ternaryExposure 0 ∧
    (∀ i : Fin N,
      probability (ternaryDesign N) (fun z => z i = 1 ∧ ternaryExposure i z = 1) /
        pi (ternaryDesign N) ternaryExposure i 1 = 1/2 ∧
      probability (ternaryDesign N) (fun z => z i = 2 ∧ ternaryExposure i z = 1) /
        pi (ternaryDesign N) ternaryExposure i 1 = 1/2) ∧
    aeed (ternaryDesign N) ternaryExposure ternaryOutcome 1 0 = 3/2 ∧
    (∀ (i : Fin N) (z : Fin N → Fin 3), ternaryOutcome i (Function.update z i 1) -
        ternaryOutcome i (Function.update z i 0) = 1 ∧
      ternaryOutcome i (Function.update (ternaryExposureAssignment z) i 1) -
        ternaryOutcome i (Function.update (ternaryExposureAssignment z) i 0) = 1) ∧
    (N : ℝ)⁻¹ * ∑ i, expectation (ternaryDesign N) (fun z =>
      ternaryOutcome i (Function.update z i 1) - ternaryOutcome i (Function.update z i 0)) = 1 ∧
    aeed (ternaryDesign N) ternaryExposure ternaryOutcome 1 0 - 1 = 1/2 := by
  have hp1 (i : Fin N) := (ternary_marginals N i).1
  have hp0 (i : Fin N) := (ternary_marginals N i).2.1
  have hy1 (i : Fin N) := (ternary_marginals N i).2.2.1
  have hy0 (i : Fin N) := (ternary_marginals N i).2.2.2
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have htarget : aeed (ternaryDesign N) ternaryExposure ternaryOutcome 1 0 = 3/2 := by
    simp only [aeed, aepo, hy1, hy0, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_zero, sub_zero]
    field_simp
  have hd (i : Fin N) (z : Fin N → Fin 3) :
      ternaryOutcome i (Function.update z i 1) - ternaryOutcome i (Function.update z i 0) = 1 := by
    norm_num [ternaryOutcome]
  refine ⟨?_, ?_, ?_, ⟨2/3, by norm_num, fun i => by rw [hp1]⟩,
    ⟨1/3, by norm_num, fun i => by rw [hp0]⟩, ?_, htarget, ?_, ?_, ?_⟩
  · intro E
    have hh := product_events N (fun _ => uniformDesign (Fin 3))
      (fun i a => E i (ternaryValue a))
    have hmargin (i : Fin N) : probability (ternaryDesign N)
        (fun z => E i (ternaryExposure i z)) =
          probability (uniformDesign (Fin 3)) (fun a => E i (ternaryValue a)) := by
      simpa only [ternaryDesign, ternaryExposure] using
        coordinate_probability N (fun _ => uniformDesign (Fin 3)) i (fun a => E i (ternaryValue a))
    simpa only [← hmargin, ternaryDesign, ternaryExposure] using hh
  · intro i z
    exact ⟨Nat.cast_nonneg _, by
      have hb : (z i).val ≤ 2 := by have ht := (z i).isLt; omega
      change ((z i).val : ℝ) ≤ 2
      exact_mod_cast hb⟩
  · intro i z z' he
    simp only [ternaryOutcome, he]
  · intro i
    have h1 : probability (ternaryDesign N) (fun z => z i = 1 ∧ ternaryExposure i z = 1) = 1/3 := by
      rw [show probability (ternaryDesign N) (fun z => z i = 1 ∧ ternaryExposure i z = 1) =
        probability (uniformDesign (Fin 3)) (fun a => a = 1 ∧ ternaryValue a = 1) from
          by simpa only [ternaryDesign, ternaryExposure] using
            coordinate_probability N (fun _ => uniformDesign (Fin 3)) i
              (fun a : Fin 3 => a = 1 ∧ ternaryValue a = 1)]
      norm_num [probability, uniformDesign, ternaryValue, tsum_fintype, Fin.sum_univ_succ]
    have h2 : probability (ternaryDesign N) (fun z => z i = 2 ∧ ternaryExposure i z = 1) = 1/3 := by
      rw [show probability (ternaryDesign N) (fun z => z i = 2 ∧ ternaryExposure i z = 1) =
        probability (uniformDesign (Fin 3)) (fun a => a = 2 ∧ ternaryValue a = 1) from
          by simpa only [ternaryDesign, ternaryExposure] using
            coordinate_probability N (fun _ => uniformDesign (Fin 3)) i
              (fun a : Fin 3 => a = 2 ∧ ternaryValue a = 1)]
      norm_num [probability, uniformDesign, ternaryValue, tsum_fintype, Fin.sum_univ_succ]
    norm_num [h1, h2, hp1]
  · intro i z
    exact ⟨hd i z, hd i (ternaryExposureAssignment z)⟩
  · simp only [hd, expectation_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hNr
  · rw [htarget]; norm_num


/-- T1(f): no exposure-vector schedule H_1 exists for N=2: (1,0) and
(2,0) induce the same exposure vector but different outcomes for unit 0. -/
theorem coarsened_no_exposure_schedule :
    ¬∃ H : (Fin 2 → ℝ) → ℝ, ∀ z : Fin 2 → Fin 3,
      ternaryOutcome 0 z = H (fun i => ternaryExposure i z) := by
  rintro ⟨H,hH⟩
  have h1 := hH ![1,0]
  have h2 := hH ![2,0]
  have hg : (fun i : Fin 2 => ternaryExposure i ![1,0]) =
      (fun i : Fin 2 => ternaryExposure i ![2,0]) := by
    funext i; fin_cases i <;> norm_num [ternaryExposure, ternaryValue]
  rw [hg] at h1
  norm_num [ternaryOutcome] at h1 h2
  linarith

/-! Cross-design examples, Tables 4–5 and corrected Section 6.3. -/

/-- Table 4(a), p. 12: outcomes are 1/2 at (0,0),(1,1), and own treatment
at the two singly treated assignments. -/
noncomputable def attenuationOutcome (i : Fin 2) (z : BinaryPair) : ℝ :=
  if z.1 = z.2 then 1/2 else pairAssignment i z

/-- Table 4(b), p. 12: both outcomes are one exactly at (1,1), zero otherwise. -/
def amplificationOutcome (_i : Fin 2) (z : BinaryPair) : ℝ :=
  if z.1 = 1 ∧ z.2 = 1 then 1 else 0

/-- T15, Table 4, p. 12: opposite and uniform-rollout designs give contrasts
1 versus 0 (attenuation) and 0 versus 1 (amplification). Both schedules satisfy
NURVA under both designs, and both fail global SUTVA on {0,1}^2. -/
theorem equilibrium_tables :
    aeed oppositeDesign pairAssignment attenuationOutcome 1 0 = 1 ∧
    aeed sameDesign pairAssignment attenuationOutcome 1 0 = 0 ∧
    NURVA oppositeDesign pairAssignment attenuationOutcome ∧
    NURVA sameDesign pairAssignment attenuationOutcome ∧
    ¬SUTVA pairAssignment attenuationOutcome ∧
    aeed oppositeDesign pairAssignment amplificationOutcome 1 0 = 0 ∧
    aeed sameDesign pairAssignment amplificationOutcome 1 0 = 1 ∧
    NURVA oppositeDesign pairAssignment amplificationOutcome ∧
    NURVA sameDesign pairAssignment amplificationOutcome ∧
    ¬SUTVA pairAssignment amplificationOutcome := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try norm_num [aeed, aepo, epo, pi, probability, expectation,
    oppositeDesign, sameDesign, pairAssignment, attenuationOutcome, amplificationOutcome,
    tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
  · intro i ⟨x,y⟩ ⟨x',y'⟩ hz hz' he
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
      norm_num [Support, oppositeDesign, pairAssignment, attenuationOutcome] at *
  · intro i ⟨x,y⟩ ⟨x',y'⟩ hz hz' he
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
      norm_num [Support, sameDesign, pairAssignment, attenuationOutcome] at *
  · intro h
    have hh := h 0 (0,0) (0,1) (by norm_num [pairAssignment])
    norm_num [attenuationOutcome, pairAssignment] at hh
  · intro i ⟨x,y⟩ ⟨x',y'⟩ hz hz' he
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
      norm_num [Support, oppositeDesign, pairAssignment, amplificationOutcome] at *
  · intro i ⟨x,y⟩ ⟨x',y'⟩ hz hz' he
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
      norm_num [Support, sameDesign, pairAssignment, amplificationOutcome] at *
  · intro h
    have hh := h 0 (1,0) (1,1) (by norm_num [pairAssignment])
    norm_num [amplificationOutcome] at hh

/-- Full ternary two-person design space for Table 5, p. 12. -/
abbrev TernaryPair := Fin 3 × Fin 3

/-- Raw schedule y_i(z)=z_i in Table 5, fixed across both designs and
without between-unit interference (Section 6.2, p. 12). -/
def versionOutcome (i : Fin 2) (z : TernaryPair) : ℝ :=
  if i = 0 then (z.1.val : ℝ) else (z.2.val : ℝ)

/-- Table 5's coarsening of assignments 1 and 2 to the exposed category. -/
def versionExposure (i : Fin 2) (z : TernaryPair) : ℝ :=
  if (if i = 0 then z.1 else z.2) = 0 then 0 else 1

/-- Table 5, p. 12: choose one person to receive version v=1 or v=2,
with probability 1/2 per person, and give every other feasible vector mass zero. -/
noncomputable def versionDesign (v : Fin 3) (hv : v = 1 ∨ v = 2) : Design TernaryPair where
  p := fun z => if (z.1 = 0 ∧ z.2 = v) ∨ (z.1 = v ∧ z.2 = 0) then 1/2 else 0
  nonneg := fun z => by split_ifs <;> norm_num
  summable := Summable.of_finite
  total := by
    rcases hv with rfl | rfl <;>
      norm_num [tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- T15, Table 5, p. 12: the two printed designs have AEEDs one and two;
both have positive target probabilities and satisfy NURVA. The common
no-interference raw schedule fails SUTVA under the coarsened exposure. -/
theorem hidden_version_tables :
    (∀ i : Fin 2, pi (versionDesign 1 (Or.inl rfl)) versionExposure i 1 = 1/2 ∧
      pi (versionDesign 1 (Or.inl rfl)) versionExposure i 0 = 1/2 ∧
      pi (versionDesign 2 (Or.inr rfl)) versionExposure i 1 = 1/2 ∧
      pi (versionDesign 2 (Or.inr rfl)) versionExposure i 0 = 1/2) ∧
    aeed (versionDesign 1 (Or.inl rfl)) versionExposure versionOutcome 1 0 = 1 ∧
    aeed (versionDesign 2 (Or.inr rfl)) versionExposure versionOutcome 1 0 = 2 ∧
    NURVA (versionDesign 1 (Or.inl rfl)) versionExposure versionOutcome ∧
    NURVA (versionDesign 2 (Or.inr rfl)) versionExposure versionOutcome ∧
    ¬SUTVA versionExposure versionOutcome ∧
    (∀ i z z', (if i = 0 then z.1 else z.2) = (if i = 0 then z'.1 else z'.2) →
      versionOutcome i z = versionOutcome i z') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [pi, probability, versionDesign, versionExposure,
      tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · norm_num [aeed, aepo, epo, pi, probability, expectation, versionDesign,
      versionExposure, versionOutcome, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_succ, Finset.filter_singleton]
  · norm_num [aeed, aepo, epo, pi, probability, expectation, versionDesign,
      versionExposure, versionOutcome, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_succ, Finset.filter_singleton]
  · intro i ⟨x,y⟩ ⟨x',y'⟩ hz hz' he
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
      norm_num [Support, versionDesign, versionExposure, versionOutcome] at *
  · intro i ⟨x,y⟩ ⟨x',y'⟩ hz hz' he
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
      norm_num [Support, versionDesign, versionExposure, versionOutcome] at *
  · intro h
    have hh := h 0 (1,0) (2,0) (by norm_num [versionExposure])
    norm_num [versionOutcome] at hh
  · intro i z z' he
    by_cases hi : i = 0
    · have hh : z.1 = z'.1 := by simpa only [hi, ite_true] using he
      simp only [versionOutcome, hi, ite_true, hh]
    · have hh : z.2 = z'.2 := by simpa only [hi, ite_false] using he
      simp only [versionOutcome, hi, ite_false, hh]

/-- Uniform sampling–treatment support, corrected Section 6.3, p. 13:
one coordinate is treated (2) and n−1 are sampled controls (1). The remaining
coordinates are unsampled (0). This is the distinct-permutation orbit Sym. -/
def SamplingTreatmentSupport (n : ℕ) (z : Fin 4 → Fin 3) : Prop :=
  (Finset.univ.filter (fun i => z i = 2)).card = 1 ∧
    (Finset.univ.filter (fun i => z i ≠ 0)).card = n

/-- Corrected T9's N=4 raw schedule: number sampled times the indicator
that this unit is treated; it is fixed on the full ternary feasible set. -/
noncomputable def samplingTreatmentOutcome : OutcomeSchedule (Fin 4 → Fin 3) 4 :=
  fun i z => ((Finset.univ.filter (fun j => z j ≠ 0)).card : ℝ) *
    (if z i = 2 then 1 else 0)

/-- Recursive finite marginalization of assignment vectors, used only to
certify the two 12-row support laws in corrected Section 6.3 (T9). -/
theorem sum_vector_succ {A : Type} [Fintype A] (n : ℕ)
    (f : (Fin (n+1) → A) → ℝ) :
    (∑ z, f z) = ∑ a, ∑ w : Fin n → A, f (Matrix.vecCons a w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The uniform Sym orbit of footnote 10, p. 13, for T9's sample sizes
2 or 3 and one treated unit. Each orbit has exactly 12 assignments. -/
noncomputable def samplingTreatmentDesign (n : ℕ) (hn : n = 2 ∨ n = 3) :
    Design (Fin 4 → Fin 3) where
  p := fun z => if SamplingTreatmentSupport n z then 1/12 else 0
  nonneg := fun z => by split_ifs <;> norm_num
  summable := Summable.of_finite
  total := by
    rcases hn with rfl | rfl <;>
      norm_num [tsum_fintype, sum_vector_succ, SamplingTreatmentSupport,
        Fin.sum_univ_succ, Fin.card_filter_univ_succ]

set_option maxHeartbeats 1200000 in
/-- Exact support, exposure margins, NURVA and EPO values for the two
joint sampling–treatment laws in corrected Section 6.3, p. 13 (T9). -/
theorem sampling_treatment_properties (n : ℕ) (hn : n = 2 ∨ n = 3) :
    let D := samplingTreatmentDesign n hn
    (∀ z, Support D z ↔ SamplingTreatmentSupport n z) ∧
    (∀ i, pi D (fun i z => (z i).val) i 2 = 1/4 ∧
      pi D (fun i z => (z i).val) i 1 = (n-1 : ℝ)/4) ∧
    NURVA D (fun i z => (z i).val) samplingTreatmentOutcome ∧
    (∀ i, epo D (fun i z => (z i).val) samplingTreatmentOutcome i 2 = n ∧
      epo D (fun i z => (z i).val) samplingTreatmentOutcome i 1 = 0) := by
  let D := samplingTreatmentDesign n hn
  have hs (z : Fin 4 → Fin 3) : Support D z ↔ SamplingTreatmentSupport n z := by
    by_cases h : SamplingTreatmentSupport n z <;> norm_num [D, samplingTreatmentDesign, Support, h]
  have hc (z : Fin 4 → Fin 3) (hz : Support D z) :
      (Finset.univ.filter (fun j => z j ≠ 0)).card = n := (hs z |>.mp hz).2
  have hm (i : Fin 4) : pi D (fun i z => (z i).val) i 2 = 1/4 ∧
      pi D (fun i z => (z i).val) i 1 = (n-1 : ℝ)/4 := by
    rcases hn with rfl | rfl <;> fin_cases i <;>
      norm_num [pi, probability, D, samplingTreatmentDesign, tsum_fintype,
        sum_vector_succ, SamplingTreatmentSupport, Fin.sum_univ_succ,
        Fin.card_filter_univ_succ]
  refine ⟨hs, hm, ?_, ?_⟩
  · intro i z z' hz hz' he
    have he' : z i = z' i := Fin.ext (Nat.cast_injective he)
    simp only [samplingTreatmentOutcome, hc z hz, hc z' hz', he']
  · intro i
    have hnpos : (0 : ℝ) < (n-1 : ℝ)/4 := by rcases hn with rfl | rfl <;> norm_num
    constructor
    · exact (constant_cell D (fun i z => (z i).val) samplingTreatmentOutcome i 2 (n : ℝ)
        (by rw [(hm i).1]; norm_num) (fun z hz hg => by
          have hz2 : z i = 2 := Fin.ext (by exact_mod_cast hg)
          simp [samplingTreatmentOutcome, hc z hz, hz2])).2.1
    · exact (constant_cell D (fun i z => (z i).val) samplingTreatmentOutcome i 1 0
        (by rw [(hm i).2]; exact hnpos) (fun z hz hg => by
          have hz1 : z i = 1 := Fin.ext (by exact_mod_cast hg)
          simp [samplingTreatmentOutcome, hz1])).2.1

/-- T9, corrected Section 6.3: the explicit N=4, (n,k)=(2,1) and (3,1)
uniform permutation-orbit designs both have positivity and NURVA but have
AEEDs 2 and 3. SUTVA fails on the common full ternary feasible set.
Both stated supports have 12 assignments, hence the uniform weight is 1/12. -/
theorem sampling_treatment_designs_differ :
    ∃ D D' : Design (Fin 4 → Fin 3),
      (∀ z, D.p z = if SamplingTreatmentSupport 2 z then 1/12 else 0) ∧
      (∀ z, D'.p z = if SamplingTreatmentSupport 3 z then 1/12 else 0) ∧
      (∀ i, 0 < pi D (fun i z => (z i).val) i 2 ∧
        0 < pi D (fun i z => (z i).val) i 1 ∧
        0 < pi D' (fun i z => (z i).val) i 2 ∧
        0 < pi D' (fun i z => (z i).val) i 1) ∧
      NURVA D (fun i z => (z i).val) samplingTreatmentOutcome ∧
      NURVA D' (fun i z => (z i).val) samplingTreatmentOutcome ∧
      aeed D (fun i z => (z i).val) samplingTreatmentOutcome 2 1 = 2 ∧
      aeed D' (fun i z => (z i).val) samplingTreatmentOutcome 2 1 = 3 ∧
      ¬SUTVA (fun i z => (z i).val) samplingTreatmentOutcome := by
  let D := samplingTreatmentDesign 2 (Or.inl rfl)
  let D' := samplingTreatmentDesign 3 (Or.inr rfl)
  have h2 := sampling_treatment_properties 2 (Or.inl rfl)
  have h3 := sampling_treatment_properties 3 (Or.inr rfl)
  refine ⟨D, D', fun _ => rfl, fun _ => rfl, ?_, h2.2.2.1, h3.2.2.1, ?_, ?_, ?_⟩
  · intro i
    rw [h2.2.1 i |>.1, h2.2.1 i |>.2, h3.2.1 i |>.1, h3.2.1 i |>.2]
    norm_num
  · have he2 (i : Fin 4) := (h2.2.2.2 i).1
    have he1 (i : Fin 4) := (h2.2.2.2 i).2
    simp only [D, D', aeed, aepo, he2, he1, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · have he2 (i : Fin 4) := (h3.2.2.2 i).1
    have he1 (i : Fin 4) := (h3.2.2.2 i).2
    simp only [D, D', aeed, aepo, he2, he1, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · intro h
    have hh := h 0 ![2,1,0,0] ![2,1,1,0] (by norm_num)
    norm_num [samplingTreatmentOutcome, Fin.card_filter_univ_succ, Fin.sum_univ_succ] at hh


/-! Independent pairs, the all-even-size domain example and inference example. -/

/-- Identify the K disjoint binary pairs with the paper's N=2K units. The
finite product space of pairs is exactly the full binary assignment space under
this bijection, not a smaller support or a different population. -/
def pairedAssignment (K : ℕ) : ExposureMapping (Fin K → BinaryPair) (K*2) :=
  fun i z => pairAssignment (finProdFinEquiv.symm i).2 (z (finProdFinEquiv.symm i).1)

/-- Other member's assignment in the same pair; every outcome in T4 depends
only on this one other unit. -/
def pairedPartnerAssignment (K : ℕ) : OutcomeSchedule (Fin K → BinaryPair) (K*2) :=
  fun i z => votingOutcome (finProdFinEquiv.symm i).2 (z (finProdFinEquiv.symm i).1)

/-- Eq. (3) applied independently to K disjoint network edges, T2(e). -/
def pairedNetworkExposure (K : ℕ) : ExposureMapping (Fin K → BinaryPair) (K*2) :=
  fun i z => pairedAssignment K i z + 2 * pairedPartnerAssignment K i z

/-- Exposure-vector image for the K-pair network design, T2(e). -/
def InPairedNetworkImage (K : ℕ) (r : Fin (K*2) → ℝ) : Prop :=
  ∃ z : Fin K → BinaryPair, ∀ i, pairedNetworkExposure K i z = r i

/-- Raw domain {0,1}^{2K}, the literal hybrid-coordinate reading of T2(e). -/
def InPairedBinaryDomain (K : ℕ) (r : Fin (K*2) → ℝ) : Prop :=
  ∀ i, r i = 0 ∨ r i = 1

/-- T4's within-pair law: (1+ρ)/4 for equal bits, (1−ρ)/4 for unequal bits,
with 0≤ρ≤1. The law is normalized on all four pair assignments. -/
noncomputable def correlatedPairDesign (ρ : ℝ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) : Design BinaryPair where
  p := fun z => if z.1 = z.2 then (1+ρ)/4 else (1-ρ)/4
  nonneg := fun z => by split_ifs <;> apply div_nonneg <;> linarith
  summable := Summable.of_finite
  total := by norm_num [tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]; ring

/-- T4: a=ρ=1/m for m≥2. Values before m=2 are arbitrary zero fillers
so that all limit statements use actual sequences on Nat. -/
noncomputable def localParameter (m : ℕ) : ℝ := if 2 ≤ m then 1/(m : ℝ) else 0

/-- The admissible within-pair correlation bounds of T4(a). -/
theorem local_parameter_bounds (m : ℕ) : 0 ≤ localParameter m ∧ localParameter m ≤ 1 := by
  by_cases hm : 2 ≤ m
  · have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [localParameter, hm, ite_true]
    constructor
    · positivity
    · exact (div_le_one (by linarith : (0 : ℝ) < m)).mpr (by linarith)
  · simp [localParameter, hm]

/-- T4's actual design: K=m^8 independent correlated pairs, N=2m^8. -/
noncomputable def localDesign (m : ℕ) : Design (Fin (m^8) → BinaryPair) :=
  productDesign (m^8) (fun _ => correlatedPairDesign (localParameter m) (local_parameter_bounds m))

/-- T4's raw schedule on every feasible assignment: y_i(z)=1+a z_partner.
For m≥2 it is not stable within cells of the individualistic exposure mapping. -/
noncomputable def localOutcome (m : ℕ) : OutcomeSchedule (Fin (m^8) → BinaryPair) (m^8*2) :=
  fun i z => 1 + localParameter m * pairedPartnerAssignment (m^8) i z

/-- Modify the own coordinate of a binary pair, leaving the partner fixed;
the assignment-conditional interpretation of footnote 8, p. 7. -/
def replacePairOwn (i : Fin 2) (e : Fin 2) (z : BinaryPair) : BinaryPair :=
  if i = 0 then (e,z.2) else (z.1,e)

/-- Raw hybrid assignment for one unit of a population of pairs, T4's ADE. -/
def pairedHybrid (K : ℕ) (i : Fin (K*2)) (e : Fin 2) (z : Fin K → BinaryPair) : Fin K → BinaryPair :=
  Function.update z (finProdFinEquiv.symm i).1
    (replacePairOwn (finProdFinEquiv.symm i).2 e (z (finProdFinEquiv.symm i).1))

/-- T4's actual average direct effect, evaluated on feasible raw hybrids. -/
noncomputable def localDirectEffect (m : ℕ) : ℝ :=
  (m^8*2 : ℝ)⁻¹ * ∑ i, expectation (localDesign m) (fun z =>
    localOutcome m i (pairedHybrid (m^8) i 1 z) - localOutcome m i (pairedHybrid (m^8) i 0 z))

/-- T4: pair contribution
B=2{(2x−1)(1+ay)+(2y−1)(1+ax)} to the actual HT contrast's numerator. -/
noncomputable def pairContribution (a : ℝ) (z : BinaryPair) : ℝ :=
  2 * ((2*pairAssignment 0 z-1)*(1+a*pairAssignment 1 z) +
    (2*pairAssignment 1 z-1)*(1+a*pairAssignment 0 z))

/-- T4's exact variance polynomial V_m. -/
noncomputable def localV (m : ℕ) : ℝ :=
  8 + 16/(m : ℝ) + 14/(m : ℝ)^2 + 2/(m : ℝ)^3 - 4/(m : ℝ)^4

/-- T4's HT contrast, defined from the supplement's estimator, not directly
from its intended moments. -/
noncomputable def localEstimator (m : ℕ) :=
  htContrast (localDesign m) (pairedAssignment (m^8)) (localOutcome m) 1 0

/-- T4's exact standard-error scale √Var[τ̂], using the actual estimator. -/
noncomputable def localStandardError (m : ℕ) : ℝ :=
  Real.sqrt (variance (localDesign m) (localEstimator m))

/-- T4: mean, second moment and variance of the four explicitly
enumerated pair contributions, for arbitrary a and admissible ρ. -/
theorem correlated_pair_moments (a ρ : ℝ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    expectation (correlatedPairDesign ρ hρ) (pairContribution a) = 2*a*ρ ∧
    expectation (correlatedPairDesign ρ hρ) (fun z => pairContribution a z^2) =
      8*(1+ρ)*(1+a)+(6+2*ρ)*a^2 ∧
    variance (correlatedPairDesign ρ hρ) (pairContribution a) =
      8*(1+ρ)*(1+a)+(6+2*ρ)*a^2-4*a^2*ρ^2 := by
  have hm : expectation (correlatedPairDesign ρ hρ) (pairContribution a) = 2*a*ρ := by
    norm_num [expectation, correlatedPairDesign, pairContribution, pairAssignment,
      tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  refine ⟨hm, ?_, ?_⟩
  · norm_num [expectation, correlatedPairDesign, pairContribution, pairAssignment,
      tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  · unfold variance
    rw [hm]
    norm_num [expectation, correlatedPairDesign, pairContribution, pairAssignment,
      tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring

/-! Inference-scale correction, P061-T5. -/

/-- Weak convergence of the actual real estimator laws: expectations of all
bounded continuous test functions converge to their integrals against L. This
is convergence in distribution on R, allows changing assignment spaces, and
includes continuous limiting laws such as the standard normal. -/
def WeakConverges {Ω : ℕ → Type} (D : ∀ N, Design (Ω N))
    (X : ∀ N, Ω N → ℝ) (L : MeasureTheory.Measure ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, Tendsto (fun N => expectation (D N) (fun z => f (X N z)))
    atTop (𝓝 (∫ x, f x ∂L))

/-- The shifted limit law in T5 when the deterministic target gap divided
by the inferential scale tends to c≠0. -/
noncomputable def shiftedLaw (L : MeasureTheory.Measure ℝ) (c : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.map (fun x : ℝ => x+c) L

/-- T5: two standardized estimators differ exactly by the target
gap in standard-error units. The scale is strictly positive, as required by the inference correction. -/
theorem centering_identity (estimate T A s : ℝ) (_hs : 0 < s) :
    (estimate-A)/s - (estimate-T)/s = (T-A)/s := by ring

/-- T5: L_N=o(s_N) suffices when the deterministic bias is bounded by L_N.
This is a genuine limit statement with the full rate, not o(1). -/
theorem rate_bound_suffices (T A L s : ℕ → ℝ) (hs : ∀ N, 0 < s N)
    (hb : ∀ N, |T N-A N| ≤ L N)
    (hr : Tendsto (fun N => L N/s N) atTop (𝓝 0)) :
    Tendsto (fun N => (T N-A N)/s N) atTop (𝓝 0) := by
  have hN (N : ℕ) : |(T N-A N)/s N| ≤ L N/s N := by
    rw [abs_div, abs_of_pos (hs N)]
    exact div_le_div_of_nonneg_right (hb N) (hs N).le
  have hneg : Tendsto (fun N => -(L N/s N)) atTop (𝓝 0) := by simpa using hr.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg hr
    (fun N => (abs_le.mp (hN N)).1) (fun N => (abs_le.mp (hN N)).2)

/-!
Inference-transfer arguments

The varying-base Slutsky proof below is adapted from the Apache-2.0 licensed
StatLean/Stat-Lean project,
module `StatLean.AsymptoticStatistics.ForMathlib.Slutsky`.
See NOTICE at the repository root.
The results below relate atomic laws to weak convergence, recentering,
studentization, and interval probabilities. `MeasureTheory.Integrable` is
qualified to distinguish it from the atomic integrability predicate.
-/

section InferenceCompletion
open MeasureTheory

namespace Analytic

/-- Weak convergence of probability laws tested against bounded continuous real functions. -/
def WeakConvergesLaw {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))


/-- **Slutsky-by-distance for `WeakConvergesLaw`**: if `(P n).map (X n) ⇝ ν` and
`dist (X n) (Y n) →_P 0` under `P n`, then `(P n).map (Y n) ⇝ ν`.

Varying-base version (each `P n` lives on its own space `Ω n`). Adapted from
`MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`, which is stated for a
single base `μ''` on a normed additive group. The three-piece estimate
`|∫F Y − ∫F ν| ≤ L·(ε/2) + 2·‖F‖∞ · P{dist ≥ ε/2} + |∫F X − ∫F ν|` carries over
without change, using `dist` in place of `‖·-·‖`.
The underlying Mathlib proof is Apache-2.0; see NOTICE at the repository root.
-/
theorem weakConvergesLaw_slutsky_dist
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [Nonempty E]
    [OpensMeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Ω n → E} {ν : Measure E} [IsProbabilityMeasure ν]
    (hX_meas : ∀ n, AEMeasurable (X n) (P n))
    (hY_meas : ∀ n, AEMeasurable (Y n) (P n))
    (hX : WeakConvergesLaw (fun n => (P n).map (X n)) ν)
    (hDist : ∀ ε > 0,
        Tendsto (fun n => (P n).real {ω | ε ≤ dist (X n ω) (Y n ω)}) atTop (𝓝 0)) :
    WeakConvergesLaw (fun n => (P n).map (Y n)) ν := by
  classical
  have h_prob_X : ∀ n, IsProbabilityMeasure ((P n).map (X n)) := fun n =>
    (by infer_instance)
  have h_prob_Y : ∀ n, IsProbabilityMeasure ((P n).map (Y n)) := fun n =>
    (by infer_instance)
  -- Package the pushforwards as `ProbabilityMeasure` to apply the Lipschitz
  -- characterisation of weak convergence. Use local `let`-bindings to keep the
  -- subtype folded under `rw [tendsto_iff_forall_lipschitz_integral_tendsto]`.
  let pX : ℕ → ProbabilityMeasure E := fun n => ⟨(P n).map (X n), h_prob_X n⟩
  let pY : ℕ → ProbabilityMeasure E := fun n => ⟨(P n).map (Y n), h_prob_Y n⟩
  let pν : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have h_coe_X : ∀ n, (pX n : Measure E) = (P n).map (X n) := fun _ => rfl
  have h_coe_Y : ∀ n, (pY n : Measure E) = (P n).map (Y n) := fun _ => rfl
  have h_coe_ν : (pν : Measure E) = ν := rfl
  -- `hX` rewrites to `Tendsto pX atTop (𝓝 pν)`.
  have h_probmeas_tendsto : Tendsto pX atTop (𝓝 pν) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simp_rw [h_coe_X, h_coe_ν]
    exact hX f
  -- Conclude via the same bridge applied to `pY`.
  suffices h_target : Tendsto pY atTop (𝓝 pν) by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h_target
    intro f
    simpa [h_coe_Y, h_coe_ν] using h_target f
  -- Reduce to Lipschitz test functions.
  rw [tendsto_iff_forall_lipschitz_integral_tendsto] at h_probmeas_tendsto ⊢
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  simp_rw [h_coe_X, h_coe_ν] at h_probmeas_tendsto
  simp_rw [h_coe_Y, h_coe_ν]
  let x₀ : E := Classical.arbitrary E
  -- Bounded Lipschitz test function. Degenerate L = 0 ⇒ F constant.
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul, probReal_univ]
    exact tendsto_const_nhds
  -- Now `F` is `L`-Lipschitz with `L > 0`; use a classic three-piece ε-δ estimate.
  have hF_cont : Continuous F := hF_lip.continuous
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in atTop, |∫ ω, F ω ∂((P n).map (Y n))
      - ∫ ω, F ω ∂ν| < L * ε by
    intro ε hε
    convert this (ε / L) (by positivity)
    field_simp
  intro ε hε
  -- Step A: transfer the integrals from pushforward to base via `integral_map`.
  have h_push_X : ∀ n, ∫ ω, F ω ∂((P n).map (X n)) = ∫ ω, F (X n ω) ∂(P n) := fun n =>
    integral_map (hX_meas n) hF_cont.aestronglyMeasurable
  have h_push_Y : ∀ n, ∫ ω, F ω ∂((P n).map (Y n)) = ∫ ω, F (Y n ω) ∂(P n) := fun n =>
    integral_map (hY_meas n) hF_cont.aestronglyMeasurable
  -- Step B: the three-piece inequality — bound `|∫F(Y) − ∫F(ν)|` in terms of
  -- `|∫F(X) − ∫F(ν)|` plus Lipschitz-residual and tail contributions.
  have h_le : ∀ n, |∫ ω, F ω ∂((P n).map (Y n)) - ∫ ω, F ω ∂ν|
      ≤ L * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ dist (X n ω) (Y n ω)}
        + |∫ ω, F ω ∂((P n).map (X n)) - ∫ ω, F ω ∂ν| := by
    intro n
    refine (abs_sub_le (∫ ω, F ω ∂((P n).map (Y n))) (∫ ω, F ω ∂((P n).map (X n)))
      (∫ ω, F ω ∂ν)).trans ?_
    gcongr
    -- The first piece: `|∫F(Y) − ∫F(X)| ≤ L·(ε/2) + M·P{dist ≥ ε/2}`.
    rw [h_push_Y, h_push_X]
    have h_int_X : MeasureTheory.Integrable (fun ω => F (X n ω)) (P n) := by
      refine MeasureTheory.Integrable.of_bound (hF_cont.aemeasurable.comp_aemeasurable (hX_meas n)
        |>.aestronglyMeasurable) (‖F x₀‖ + M) ?_
      refine ae_of_all _ (fun a => ?_)
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans (hF_bounded _ _)
    have h_int_Y : MeasureTheory.Integrable (fun ω => F (Y n ω)) (P n) := by
      refine MeasureTheory.Integrable.of_bound (hF_cont.aemeasurable.comp_aemeasurable (hY_meas n)
        |>.aestronglyMeasurable) (‖F x₀‖ + M) ?_
      refine ae_of_all _ (fun a => ?_)
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans (hF_bounded _ _)
    have h_int_sub : MeasureTheory.Integrable (fun ω => ‖F (Y n ω) - F (X n ω)‖) (P n) :=
      (h_int_Y.sub h_int_X).norm
    rw [← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ ω, F (Y n ω) - F (X n ω) ∂(P n)‖
        ≤ ∫ ω, ‖F (Y n ω) - F (X n ω)‖ ∂(P n) := norm_integral_le_integral_norm _
      _ = ∫ ω in {a | dist (X n a) (Y n a) < ε / 2},
            ‖F (Y n ω) - F (X n ω)‖ ∂(P n)
          + ∫ ω in {a | ε / 2 ≤ dist (X n a) (Y n a)},
            ‖F (Y n ω) - F (X n ω)‖ ∂(P n) := by
          symm
          simp_rw [← not_lt]
          refine integral_add_compl₀ ?_ h_int_sub
          refine nullMeasurableSet_lt ?_ (by fun_prop)
          exact (hX_meas n).dist (hY_meas n)
      _ ≤ ∫ ω in {a | dist (X n a) (Y n a) < ε / 2}, L * (ε / 2) ∂(P n)
          + ∫ ω in {a | ε / 2 ≤ dist (X n a) (Y n a)}, M ∂(P n) := by
          gcongr ?_ + ?_
          · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_
              (fun ω hω => ?_)
            · refine nullMeasurableSet_lt ?_ (by fun_prop)
              exact (hX_meas n).dist (hY_meas n)
            · simp only [Set.mem_ofPred_eq] at hω
              have h_le : dist (Y n ω) (X n ω) ≤ ε / 2 := by
                rw [dist_comm]; exact hω.le
              have := hF_lip.dist_le_mul_of_le h_le
              simpa [Real.dist_eq, Real.norm_eq_abs] using this
          · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const (fun a => ?_)
            rw [← dist_eq_norm]
            convert hF_bounded _ _
      _ = L * (ε / 2) * (P n).real {a | dist (X n a) (Y n a) < ε / 2}
          + M * (P n).real {a | ε / 2 ≤ dist (X n a) (Y n a)} := by
          simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
            Set.univ_inter, smul_eq_mul]
          ring
      _ ≤ L * (ε / 2)
          + M * (P n).real {a | ε / 2 ≤ dist (X n a) (Y n a)} := by
          rw [mul_assoc]
          gcongr
          grw [measureReal_le_one, mul_one]
  -- Step C: the RHS tends to `L * (ε / 2) + 0 + 0`; the conclusion follows from `L * (ε / 2) < L * ε`.
  have h_tendsto : Tendsto (fun n =>
      L * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ dist (X n ω) (Y n ω)}
        + |∫ ω, F ω ∂((P n).map (X n)) - ∫ ω, F ω ∂ν|)
      atTop (𝓝 (L * (ε / 2))) := by
    suffices Tendsto (fun n =>
        L * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ dist (X n ω) (Y n ω)}
          + |∫ ω, F ω ∂((P n).map (X n)) - ∫ ω, F ω ∂ν|)
        atTop (𝓝 (L * (ε / 2) + M * 0 + 0)) by simpa using this
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · exact tendsto_const_nhds
    · exact hDist (ε / 2) (by positivity)
    · -- `|∫F(X) − ∫F(ν)| → 0` from the assumed weak convergence.
      have := h_probmeas_tendsto F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
      simp_rw [Metric.tendsto_nhds, Real.dist_eq] at this
      rw [Metric.tendsto_nhds]
      intro δ hδ
      filter_upwards [this δ hδ] with n hn
      rw [Real.dist_eq, sub_zero, abs_abs]
      exact hn
  have h_strict : (L : ℝ) * (ε / 2) < L * ε := by
    have : (0 : ℝ) < L * (ε / 2) := by positivity
    linarith [this]
  have := h_tendsto.eventually_lt_const h_strict
  filter_upwards [this] with n hn
  exact lt_of_le_of_lt (h_le n) hn

end Analytic

/-- The genuine Borel probability law induced by any of the paper's atomic designs.
The assignment domain need not be countable or carry a measurable-space instance. -/
noncomputable def designLaw {Ω E : Type} [MeasurableSpace E]
    (D : Design Ω) (X : Ω → E) : Measure E :=
  Measure.sum (fun z => ENNReal.ofReal (D.p z) • Measure.dirac (X z))

instance designLaw_isProbability {Ω E : Type} [MeasurableSpace E]
    (D : Design Ω) (X : Ω → E) :
    IsProbabilityMeasure (designLaw D X) where
  measure_univ := by
    simp only [designLaw, Measure.sum_apply _ MeasurableSet.univ,
      Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg D.nonneg D.summable, D.total]
    norm_num

/-- The original weighted expectations agree with ordinary integrals against
`designLaw`; finite mass and bounded continuity supply integrability. -/
theorem designLaw_integral {Ω E : Type} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [MeasurableSingletonClass E]
    (D : Design Ω) (X : Ω → E) (f : E →ᵇ ℝ) :
    (∫ x, f x ∂designLaw D X) = expectation D (fun z => f (X z)) := by
  have hi : MeasureTheory.Integrable (fun x => f x) (designLaw D X) := f.integrable (designLaw D X)
  rw [designLaw] at hi ⊢
  rw [integral_sum_measure hi]
  unfold expectation
  apply tsum_congr
  intro z
  simp [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (D.nonneg z)]

/-- On Borel events, the original atom-sum probability is the real-valued
probability of the induced law. This preserves zero-mass feasible assignments. -/
theorem designLaw_apply {Ω E : Type} [MeasurableSpace E]
    (D : Design Ω) (X : Ω → E) (B : Set E) (hB : MeasurableSet B) :
    (designLaw D X B).toReal = probability D (fun z => X z ∈ B) := by
  have h : designLaw D X B = ENNReal.ofReal (probability D (fun z => X z ∈ B)) := by
    rw [designLaw, Measure.sum_apply _ hB]
    unfold probability
    rw [ENNReal.ofReal_tsum_of_nonneg (fun z => by split_ifs <;> simp [D.nonneg])
      (event_summable D _)]
    apply tsum_congr
    intro z
    by_cases hz : X z ∈ B <;> simp [Measure.smul_apply, Measure.dirac_apply' _ hB, hz]
  rw [h, ENNReal.toReal_ofReal (probability_nonneg D _)]

/-- Package an already normalized measure without unfolding its subtype during elaboration. -/
noncomputable def lawProbabilityMeasure {E : Type} [MeasurableSpace E]
    (L : Measure E) [IsProbabilityMeasure L] : ProbabilityMeasure E := ⟨L, inferInstance⟩

/-- Continuous pushforwards of arbitrary atomic laws agree with pushing each atom. -/
theorem designLaw_map {Ω E F : Type} [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSingletonClass E] [MeasurableSingletonClass F]
    (D : Design Ω) (X : Ω → E) (g : E → F) (hg : Measurable g) :
    (designLaw D X).map g = designLaw D (fun z => g (X z)) := by
  rw [designLaw, Measure.map_sum hg.aemeasurable]
  congr 1
  funext z
  rw [Measure.map_smul _ hg.aemeasurable, Measure.map_dirac]

/-- The paper's bounded-test-function definition is exactly Mathlib's weak
topology on Borel probability laws, including changing assignment spaces. -/
theorem weakConverges_iff_designLaw_tendsto {Ω : ℕ → Type}
    (D : ∀ N, Design (Ω N)) (X : ∀ N, Ω N → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L] :
    WeakConverges D X L ↔
      Tendsto (fun N => lawProbabilityMeasure (designLaw (D N) (X N)))
        atTop (𝓝 (lawProbabilityMeasure L)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  simp only [lawProbabilityMeasure, ProbabilityMeasure.coe_mk, designLaw_integral, WeakConverges]

/-- The continuity-set conclusion of Portmanteau, proved from Mathlib for
the original atomic definition rather than posited as an extra hypothesis. -/
theorem weakConverges_continuitySet {Ω : ℕ → Type}
    (D : ∀ N, Design (Ω N)) (X : ∀ N, Ω N → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L] (hX : WeakConverges D X L)
    (B : Set ℝ) (hB : MeasurableSet B) (hfront : L (frontier B) = 0) :
    Tendsto (fun N => probability (D N) (fun z => X N z ∈ B))
      atTop (𝓝 (L B).toReal) := by
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    ((weakConverges_iff_designLaw_tendsto D X L).mp hX) hfront
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top L B)).comp h
  simpa only [Function.comp_def, lawProbabilityMeasure, ProbabilityMeasure.coe_mk, designLaw_apply _ _ B hB] using hreal

/-- Interval probabilities converge whenever the limit law gives no mass
to the two boundaries, with no restrictions on changing assignment domains. -/
theorem weakConverges_abs_le {Ω : ℕ → Type}
    (D : ∀ N, Design (Ω N)) (X : ∀ N, Ω N → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L] (hX : WeakConverges D X L)
    (q : ℝ) (hq : 0 < q) (hplus : L {q} = 0) (hminus : L {-q} = 0) :
    Tendsto (fun N => probability (D N) (fun z => |X N z| ≤ q))
      atTop (𝓝 (L (Set.Icc (-q) q)).toReal) := by
  have hfront : L (frontier (Set.Icc (-q) q)) = 0 := by
    rw [frontier_Icc (by linarith : -q ≤ q)]
    exact measure_union_null hminus hplus
  simpa only [Set.mem_Icc, ← abs_le] using
    weakConverges_continuitySet D X L hX (Set.Icc (-q) q) measurableSet_Icc hfront


/-- Weak convergence of atomic random variables with a general metric codomain. -/
def AtomicWeakConverges {Ω : ℕ → Type} {E : Type} [MeasurableSpace E]
    [TopologicalSpace E] (D : ∀ N, Design (Ω N)) (X : ∀ N, Ω N → E)
    (L : Measure E) : Prop :=
  ∀ f : E →ᵇ ℝ, Tendsto (fun N => expectation (D N) (fun z => f (X N z)))
    atTop (𝓝 (∫ x, f x ∂L))

/-- Integral characterization of the law of atomic random variables. -/
theorem atomicWeakConverges_iff_laws {Ω : ℕ → Type} {E : Type}
    [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    [MeasurableSingletonClass E] (D : ∀ N, Design (Ω N)) (X : ∀ N, Ω N → E)
    (L : Measure E) :
    AtomicWeakConverges D X L ↔
      Analytic.WeakConvergesLaw (fun N => designLaw (D N) (X N)) L := by
  simp only [AtomicWeakConverges, Analytic.WeakConvergesLaw, designLaw_integral]

/-- Continuous mapping for atomic variables, proved by composition of tests. -/
theorem atomicWeakConverges_map {Ω : ℕ → Type} {E F : Type}
    [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSpace F] [PseudoMetricSpace F] [OpensMeasurableSpace F]
    (D : ∀ N, Design (Ω N)) (X : ∀ N, Ω N → E) (L : Measure E)
    (hX : AtomicWeakConverges D X L) (g : E → F) (hg : Continuous g) (hgm : Measurable g) :
    AtomicWeakConverges D (fun N z => g (X N z)) (L.map g) := by
  intro f
  rw [integral_map hgm.aemeasurable f.continuous.aestronglyMeasurable]
  exact hX (f.compContinuous ⟨g, hg⟩)

/-- Varying-domain Slutsky: atomic variables at a vanishing distance have the
same limiting law. The product-law construction needs no measurability on assignments. -/
theorem atomicWeakConverges_slutsky_dist {Ω : ℕ → Type} {E : Type}
    [MeasurableSpace E] [PseudoMetricSpace E] [Nonempty E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSingletonClass E]
    (D : ∀ N, Design (Ω N)) (X Y : ∀ N, Ω N → E)
    (L : Measure E) [IsProbabilityMeasure L] (hX : AtomicWeakConverges D X L)
    (hDist : ∀ ε > 0, Tendsto (fun N => probability (D N)
      (fun z => ε ≤ dist (X N z) (Y N z))) atTop (𝓝 0)) :
    AtomicWeakConverges D Y L := by
  let P : ℕ → Measure (E × E) := fun N => designLaw (D N) (fun z => (X N z, Y N z))
  have : ∀ N, IsProbabilityMeasure (P N) := fun N => designLaw_isProbability _ _
  have hmapX (N) : (P N).map Prod.fst = designLaw (D N) (X N) :=
    designLaw_map (D N) _ Prod.fst measurable_fst
  have hmapY (N) : (P N).map Prod.snd = designLaw (D N) (Y N) :=
    designLaw_map (D N) _ Prod.snd measurable_snd
  have hXlaw : Analytic.WeakConvergesLaw (fun N => (P N).map Prod.fst) L := by
    simpa only [hmapX] using (atomicWeakConverges_iff_laws D X L).mp hX
  have hYlaw := Analytic.weakConvergesLaw_slutsky_dist
    (P := P) (X := fun _ => Prod.fst) (Y := fun _ => Prod.snd)
    (fun _ => measurable_fst.aemeasurable) (fun _ => measurable_snd.aemeasurable) hXlaw ?_
  · exact (atomicWeakConverges_iff_laws D Y L).mpr (by simpa only [hmapY] using hYlaw)
  · intro ε hε
    have hB : MeasurableSet {x : E × E | ε ≤ dist x.1 x.2} :=
      measurableSet_le measurable_const (measurable_fst.dist measurable_snd)
    simpa only [Measure.real, P, designLaw_apply _ _ _ hB, Set.mem_ofPred_eq] using hDist ε hε

/-- Event probability is monotone under event inclusion for atomic designs. -/
theorem completion_probability_mono {Ω : Type} (D : Design Ω) (A B : Ω → Prop)
    (hAB : ∀ z, A z → B z) : probability D A ≤ probability D B := by
  apply Summable.tsum_le_tsum _ (event_summable D A) (event_summable D B)
  intro z
  by_cases ha : A z
  · simp [ha, hAB z ha]
  · by_cases hb : B z <;> simp [ha, hb, D.nonneg]

/-- Zero probability of an impossible event, including arbitrary domains. -/
theorem completion_probability_false {Ω : Type} (D : Design Ω) :
    probability D (fun _ => False) = 0 := by simp [probability]

/-- The strict-tail definition of convergence in probability also controls
closed distance tails, by testing at half the positive threshold. -/
theorem convergenceInProbability_closed_tails {Ω : ℕ → Type}
    (D : ∀ N, Design (Ω N)) (X : ∀ N, Ω N → ℝ) (c : ℝ)
    (hX : ConvergesInProbability D X c) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => probability (D N) (fun z => ε ≤ |X N z - c|)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hX (ε/2) (by linarith)) (fun N => probability_nonneg (D N) _)
    (fun N => completion_probability_mono (D N) _ _ (fun z hz => by linarith))

/-- Deterministic recentering by a convergent drift shifts the limit law. -/
theorem weakConverges_add_drift {Ω : ℕ → Type}
    (D : ∀ N, Design (Ω N)) (X : ∀ N, Ω N → ℝ) (b : ℕ → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L] (c : ℝ)
    (hX : WeakConverges D X L) (hb : Tendsto b atTop (𝓝 c)) :
    WeakConverges D (fun N z => X N z + b N) (shiftedLaw L c) := by
  have : IsProbabilityMeasure (shiftedLaw L c) := by
    unfold shiftedLaw
    infer_instance
  have hshift : AtomicWeakConverges D (fun N z => X N z + c) (shiftedLaw L c) :=
    atomicWeakConverges_map D X L hX (fun x => x+c) (by fun_prop) (by fun_prop)
  apply atomicWeakConverges_slutsky_dist D (fun N z => X N z+c)
    (fun N z => X N z+b N) (shiftedLaw L c) hshift
  intro ε hε
  have hsmall : ∀ᶠ N in atTop, |b N-c| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hb) ε hε
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [hsmall] with N hN
  have he : (fun z : Ω N => ε ≤ dist (X N z+c) (X N z+b N)) = (fun _ => False) := by
    funext z
    apply propext
    rw [Real.dist_eq]
    have hd : X N z+c-(X N z+b N) = -(b N-c) := by ring
    simp only [hd, abs_neg]
    exact iff_false_intro (not_le_of_gt hN)
  rw [he, completion_probability_false]


/-- A globally continuous quotient that equals ordinary division when the
denominator is at least one half. It only regularizes the vanishing bad event. -/
noncomputable def stabilizedQuotient (x : ℝ × ℝ) : ℝ := x.1 / max x.2 (1/2)

theorem stabilizedQuotient_continuous : Continuous stabilizedQuotient := by
  apply continuous_fst.div (continuous_snd.max continuous_const)
  intro x
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (le_max_right x.2 (1/2)))

/-- Studentization under a consistent random scale preserves weak limits.
The random denominator may be zero or negative on events whose probability vanishes. -/
theorem weakConverges_div_consistent {Ω : ℕ → Type}
    (D : ∀ N, Design (Ω N)) (X Y : ∀ N, Ω N → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L] (hX : WeakConverges D X L)
    (hY : ConvergesInProbability D Y 1) :
    WeakConverges D (fun N z => X N z / Y N z) L := by
  let liftOne : ℝ → ℝ × ℝ := fun x => (x, 1)
  let M : Measure (ℝ × ℝ) := L.map liftOne
  have hlift : Continuous liftOne := by fun_prop
  have : IsProbabilityMeasure M := by dsimp [M]; infer_instance
  have hpair0 : AtomicWeakConverges D (fun N z => (X N z, (1:ℝ))) M :=
    atomicWeakConverges_map D X L hX liftOne hlift hlift.measurable
  have hpair : AtomicWeakConverges D (fun N z => (X N z, Y N z)) M := by
    apply atomicWeakConverges_slutsky_dist D (fun N z => (X N z, (1:ℝ)))
      (fun N z => (X N z, Y N z)) M hpair0
    intro ε hε
    simpa only [dist_prod_same_left, Real.dist_eq, abs_sub_comm] using
      convergenceInProbability_closed_tails D Y 1 hY ε hε
  have hlim : M.map stabilizedQuotient = L := by
    dsimp only [M]
    rw [Measure.map_map stabilizedQuotient_continuous.measurable hlift.measurable]
    have he : stabilizedQuotient ∘ liftOne = id := by
      funext x
      norm_num [stabilizedQuotient, liftOne, Function.comp_def]
    rw [he, Measure.map_id]
  have hclamp : WeakConverges D
      (fun N z => stabilizedQuotient (X N z, Y N z)) L := by
    have h := atomicWeakConverges_map D _ M hpair stabilizedQuotient
      stabilizedQuotient_continuous stabilizedQuotient_continuous.measurable
    rw [hlim] at h
    exact h
  apply atomicWeakConverges_slutsky_dist D
    (fun N z => stabilizedQuotient (X N z, Y N z))
    (fun N z => X N z / Y N z) L hclamp
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hY (1/2) (by norm_num)) (fun N => probability_nonneg (D N) _)
  intro N
  apply completion_probability_mono (D N) _ _
  intro z hz
  by_cases hy : 1/2 ≤ Y N z
  · have he : stabilizedQuotient (X N z, Y N z) = X N z / Y N z := by
      simp only [stabilizedQuotient, max_eq_left hy]
    rw [he, dist_self] at hz
    exact False.elim ((not_le_of_gt hε) hz)
  · have habs := neg_le_abs (Y N z-1)
    linarith


/-- Changing events only on a bad event changes their probability by at most
that bad event's probability. No measurability assumptions are needed for atom sums. -/
theorem probability_difference_le_bad_event {Ω : Type} (D : Design Ω)
    (A B E : Ω → Prop) (hagree : ∀ z, ¬E z → (A z ↔ B z)) :
    |probability D A - probability D B| ≤ probability D E := by
  unfold probability
  rw [← Summable.tsum_sub (event_summable D A) (event_summable D B)]
  have hnorm := norm_tsum_le_tsum_norm (((event_summable D A).sub (event_summable D B)).norm)
  simp only [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  apply Summable.tsum_le_tsum _
    (((event_summable D A).sub (event_summable D B)).abs) (event_summable D E)
  intro z
  by_cases he : E z
  · by_cases ha : A z <;> by_cases hb : B z <;>
      simp [he, ha, hb, abs_of_nonneg (D.nonneg z), D.nonneg]
  · simp [he, hagree z he]

/-- Consistent estimation of a positive deterministic scale makes the event
of a zero or negative estimated scale asymptotically negligible. -/
theorem consistent_scale_nonpositive_probability {Ω : ℕ → Type}
    (D : ∀ N, Design (Ω N)) (estimatedScale : ∀ N, Ω N → ℝ) (s : ℕ → ℝ)
    (hs : ∀ N, 0 < s N)
    (hscale : ConvergesInProbability D (fun N z => estimatedScale N z/s N) 1) :
    Tendsto (fun N => probability (D N) (fun z => estimatedScale N z ≤ 0))
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hscale (1/2) (by norm_num)) (fun N => probability_nonneg (D N) _)
  intro N
  apply completion_probability_mono (D N) _ _
  intro z hz
  have hdiv := div_nonpos_of_nonpos_of_nonneg hz (hs N).le
  have habs := neg_le_abs (estimatedScale N z/s N-1)
  linarith

/-- Portmanteau transfers to the actual unstandardized confidence interval,
even when estimated scales are not everywhere positive. The problematic scale
event has vanishing probability by consistency. -/
theorem weakConverges_scaled_interval {Ω : ℕ → Type}
    (D : ∀ N, Design (Ω N)) (error estimatedScale : ∀ N, Ω N → ℝ) (s : ℕ → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L] (hs : ∀ N, 0 < s N)
    (hscale : ConvergesInProbability D (fun N z => estimatedScale N z/s N) 1)
    (hweak : WeakConverges D (fun N z => error N z/estimatedScale N z) L)
    (q : ℝ) (hq : 0 < q) (hplus : L {q} = 0) (hminus : L {-q} = 0) :
    Tendsto (fun N => probability (D N) (fun z => |error N z| ≤ q*estimatedScale N z))
      atTop (𝓝 (L (Set.Icc (-q) q)).toReal) := by
  have hstd := weakConverges_abs_le D _ L hweak q hq hplus hminus
  have hbad := consistent_scale_nonpositive_probability D estimatedScale s hs hscale
  have hdiff : Tendsto (fun N =>
      probability (D N) (fun z => |error N z| ≤ q*estimatedScale N z) -
      probability (D N) (fun z => |error N z/estimatedScale N z| ≤ q)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbad
      (fun N => abs_nonneg _) (fun N => ?_)
    apply probability_difference_le_bad_event (D N) _ _ (fun z => estimatedScale N z ≤ 0)
    intro z hz
    have hpos : 0 < estimatedScale N z := lt_of_not_ge hz
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have h := hdiff.add hstd
  simpa only [sub_add_cancel, zero_add] using h

/-- Universal recentering and studentization theorem, with the original
weak-convergence and scale-consistency definitions on changing assignment spaces. -/
theorem inference_drift_transfer {Ω : ℕ → Type}
    (D : ∀ N, Design (Ω N)) (estimate estimatedScale : ∀ N, Ω N → ℝ)
    (T A s : ℕ → ℝ) (L : Measure ℝ) [IsProbabilityMeasure L]
    (c : ℝ) (hs : ∀ N, 0 < s N)
    (hfirst : WeakConverges D (fun N z => (estimate N z-T N)/s N) L)
    (hscale : ConvergesInProbability D (fun N z => estimatedScale N z/s N) 1)
    (hrate : Tendsto (fun N => (T N-A N)/s N) atTop (𝓝 c)) :
    WeakConverges D (fun N z => (estimate N z-A N)/estimatedScale N z) (shiftedLaw L c) := by
  have : IsProbabilityMeasure (shiftedLaw L c) := by unfold shiftedLaw; infer_instance
  have hadd := weakConverges_add_drift D (fun N z => (estimate N z-T N)/s N)
    (fun N => (T N-A N)/s N) L c hfirst hrate
  have hdiv := weakConverges_div_consistent D
    (fun N z => (estimate N z-T N)/s N+(T N-A N)/s N)
    (fun N z => estimatedScale N z/s N) (shiftedLaw L c) hadd hscale
  have he : (fun N z => ((estimate N z-T N)/s N+(T N-A N)/s N) /
      (estimatedScale N z/s N)) = (fun N z => (estimate N z-A N)/estimatedScale N z) := by
    funext N z
    rw [← add_div, sub_add_sub_cancel, div_div_div_cancel_right₀ (hs N).ne']
  rw [he] at hdiv
  exact hdiv


end InferenceCompletion

/-- T5, full corrected transfer: individualistic assignments, actual AEED
and raw-hybrid ADE, valid first-order AEED inference, consistent estimated
scale, and target gap o(s_N) give the same limiting law for inference on ADE.
The interval consequence is stated at continuity boundaries of the limiting
law, as weak convergence requires (automatic for the standard normal).
The nonzero drift alternative is a separate theorem below. -/
theorem corrected_inference_transfer (S : ∀ N : ℕ, Set (Fin N → ℝ))
    (D : ∀ N, Design (S N)) (y : ∀ N, OutcomeSchedule (S N) N) (d d' : ℝ)
    (estimate estimatedScale : ∀ N, S N → ℝ) (s : ℕ → ℝ)
    (L : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure L]
    (hs : ∀ N, 0 < s N)
    (hp : ∀ N i, 0 < pi (D N) (coordinateMapping (S N)) i d ∧
      0 < pi (D N) (coordinateMapping (S N)) i d')
    (hm : ∀ N, TargetedMoment (D N) (coordinateMapping (S N)) (y N) d ∧
      TargetedMoment (D N) (coordinateMapping (S N)) (y N) d')
    (hdom : ∀ N i z, Support (D N) z →
      fromOthers i d (others z.val i) ∈ S N ∧ fromOthers i d' (others z.val i) ∈ S N)
    (hint : ∀ N i, Integrable (D N) (hybridOutcome (S N) (y N) i d) ∧
      Integrable (D N) (hybridOutcome (S N) (y N) i d'))
    (hfirst : WeakConverges D (fun N z =>
      (estimate N z-aeed (D N) (coordinateMapping (S N)) (y N) d d')/s N) L)
    (hscale : ConvergesInProbability D (fun N z => estimatedScale N z/s N) 1)
    (hrate : Tendsto (fun N =>
      (aeed (D N) (coordinateMapping (S N)) (y N) d d' -
        averageDirectEffect (S N) (D N) (y N) d d')/s N) atTop (𝓝 0)) :
    WeakConverges D (fun N z =>
      (estimate N z-averageDirectEffect (S N) (D N) (y N) d d')/estimatedScale N z) L ∧
    (∀ q : ℝ, 0 < q → L {q} = 0 → L {-q} = 0 →
      Tendsto (fun N => probability (D N) (fun z =>
        |estimate N z-averageDirectEffect (S N) (D N) (y N) d d'| ≤ q*estimatedScale N z))
        atTop (𝓝 ((L (Set.Icc (-q) q)).toReal))) := by
  have hweak := inference_drift_transfer D estimate estimatedScale
    (fun N => aeed (D N) (coordinateMapping (S N)) (y N) d d')
    (fun N => averageDirectEffect (S N) (D N) (y N) d d') s L 0 hs hfirst hscale hrate
  have hzero : shiftedLaw L 0 = L := by simp [shiftedLaw]
  rw [hzero] at hweak
  refine ⟨hweak, ?_⟩
  intro q hq hplus hminus
  exact weakConverges_scaled_interval D
    (fun N z => estimate N z-averageDirectEffect (S N) (D N) (y N) d d')
    estimatedScale s L hs hscale hweak q hq hplus hminus

/-- T5's shifted-law alternative, expressed for deterministic centers so
it specializes to the actual AEED and ADE: a nonzero standardized drift moves
the limit law by c, despite consistent scale estimation. -/
theorem nonzero_drift_limit {Ω : ℕ → Type} (D : ∀ N, Design (Ω N))
    (estimate estimatedScale : ∀ N, Ω N → ℝ) (T A s : ℕ → ℝ)
    (L : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure L]
    (c : ℝ) (hc : c ≠ 0) (hs : ∀ N, 0 < s N)
    (hfirst : WeakConverges D (fun N z => (estimate N z-T N)/s N) L)
    (hscale : ConvergesInProbability D (fun N z => estimatedScale N z/s N) 1)
    (hrate : Tendsto (fun N => (T N-A N)/s N) atTop (𝓝 c)) :
    WeakConverges D (fun N z => (estimate N z-A N)/estimatedScale N z) (shiftedLaw L c) := by
  exact inference_drift_transfer D estimate estimatedScale T A s L c hs hfirst hscale hrate

/-- Finite total variation, T5: "TV(Q,P) = (1/2) ∑_x |Q(x)-P(x)|".
The probability normalization is supplied in the theorems that use it. -/
noncomputable def totalVariation {A : Type} [Fintype A] (Q P : A → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ x, |Q x-P x|

/-- T5: the difference between two finite-law expectations of a
function in [a,b] is bounded by (b−a) times total variation. The target's
max-minus-min range is the sharpest instance of this bound. -/
theorem expectation_total_variation {A : Type} [Fintype A]
    (Q P f : A → ℝ) (a b : ℝ) (_hQ : ∀ x, 0 ≤ Q x) (_hP : ∀ x, 0 ≤ P x)
    (hQ : ∑ x, Q x = 1) (hP : ∑ x, P x = 1)
    (hf : ∀ x, a ≤ f x ∧ f x ≤ b) :
    |(∑ x, Q x*f x) - (∑ x, P x*f x)| ≤ (b-a)*totalVariation Q P := by
  have hsum : ∑ x, (Q x-P x) = 0 := by rw [Finset.sum_sub_distrib, hQ, hP]; ring
  have he : (∑ x, Q x*f x) - (∑ x, P x*f x) =
      ∑ x, (Q x-P x)*(f x-(a+b)/2) := by
    calc
      _ = ∑ x, (Q x-P x)*f x := by
        simp only [sub_mul, Finset.sum_sub_distrib]
      _ = ∑ x, (Q x-P x)*(f x-(a+b)/2) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          hsum, zero_mul, sub_zero]
  have hab : ∀ x, |f x-(a+b)/2| ≤ (b-a)/2 := by
    intro x
    rw [abs_le]
    constructor <;> linarith [(hf x).1, (hf x).2]
  rw [he]
  calc
    |∑ x, (Q x-P x)*(f x-(a+b)/2)| ≤ ∑ x, |(Q x-P x)*(f x-(a+b)/2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |Q x-P x| * ((b-a)/2) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hab x) (abs_nonneg _)
    _ = (b-a)*totalVariation Q P := by rw [← Finset.sum_mul]; unfold totalVariation; ring

/-- Assignment vector in a neighborhood of other units, T5's sufficient
condition. Finset membership retains exactly the selected coordinates. -/
abbrev NeighborConfig {N : ℕ} (H : Finset (Fin N)) := H → Fin 2


/-- Conditional neighborhood law Q_{i,e}, T5; own exposure is assignment
e and the conditioning probability is the paper's π_i(e). -/
noncomputable def conditionalNeighborLaw {N : ℕ} (D : Design (Fin N → Fin 2))
    (i : Fin N) (H : Finset (Fin N)) (e : Fin 2) (x : NeighborConfig H) : ℝ :=
  probability D (fun z => z i = e ∧ ∀ j : H, z j.val = x j) /
    pi D (fun i z => (z i).val) i e.val

/-- Exact max-minus-min function range on a finite nonempty neighborhood
configuration space, R_{i,e} in T5's sufficient condition. -/
noncomputable def functionRange {A : Type} [Fintype A] (f : A → ℝ) : ℝ :=
  sSup (Set.range f) - sInf (Set.range f)


/-! Finite lemmas supporting the variance and consistency targets. -/

/-- Each atom in an event has weight at most the event probability; Section
3's nonnegative normalized atomic probability (p. 3). -/
theorem event_atom_le {Ω : Type} (D : Design Ω) (A : Ω → Prop) (z : Ω) (hz : A z) :
    D.p z ≤ probability D A := by
  have hh := (event_summable D A).le_tsum z
    (fun w hw => by split_ifs <;> simp [D.nonneg])
  simpa only [hz, ite_true, probability] using hh

/-- T18 Eq. (4), and T21: NURVA turns the actually revealed raw
outcome into its EPO at every supported assignment. It does not make outcomes
independent of Z across different exposure cells. -/
theorem nurva_revealed_outcome {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ)
    (hp : ∀ i, 0 < pi D g i d) (hn : NURVA D g y) (i : Fin N) (z : Ω)
    (hz : Support D z) :
    (if g i z = d then y i z else 0) = (if g i z = d then epo D g y i d else 0) := by
  by_cases hg : g i z = d
  · simp only [hg, ite_true, nurva_epo D g y hn i d (hp i) z hz hg]
  · simp only [hg, ite_false]

/-- T21: the probability-zero bound in Condition 1.1 and NURVA
imply |EPO_i(d)|/π_i(d)≤c for every unit, even on countable support. -/
theorem nurva_reweighted_bound {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d c : ℝ)
    (hp : ∀ i, 0 < pi D g i d) (hn : NURVA D g y)
    (hcap : ∀ i, probability D (fun z => |(if g i z = d then y i z else 0)/pi D g i d| > c) = 0)
    (i : Fin N) : |epo D g y i d|/pi D g i d ≤ c := by
  obtain ⟨z,hz,hg⟩ := positive_cell_has_assignment D g i d (hp i)
  by_contra h
  have hevent : |(if g i z = d then y i z else 0)/pi D g i d| > c := by
    simp only [hg, ite_true]
    rw [← nurva_epo D g y hn i d (hp i) z hz hg,
      abs_div, abs_of_pos (hp i)]
    exact lt_of_not_ge h
  have ha := event_atom_le D
    (fun w => |(if g i w = d then y i w else 0)/pi D g i d| > c) z hevent
  rw [hcap] at ha
  exact not_le_of_gt hz ha

/-- Chebyshev's exact design inequality, T1(g), T4(f), and T21.
The second centered moment is explicitly integrable; no finite-design
restriction and no unnamed limit theorem is hidden in this proof. -/
theorem design_chebyshev {Ω : Type} (D : Design Ω) (X : Ω → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hsecond : Integrable D (fun z => (X z-expectation D X)^2)) :
    probability D (fun z => |X z-expectation D X| ≥ ε) ≤ variance D X/ε^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hε)]
  unfold probability variance expectation
  rw [← tsum_mul_right]
  apply Summable.tsum_le_tsum
  · intro z
    by_cases he : ε ≤ |X z-∑' w, D.p w*X w|
    · simp only [he, ite_true]
      have hs : ε^2 ≤ (X z-∑' w, D.p w*X w)^2 := by
        nlinarith [sq_abs (X z-∑' w, D.p w*X w), abs_nonneg (X z-∑' w, D.p w*X w)]
      exact mul_le_mul_of_nonneg_left hs (D.nonneg z)
    · simp only [he, ite_false, zero_mul]
      exact mul_nonneg (D.nonneg z) (sq_nonneg _)
  · exact (event_summable D _).mul_right _
  · exact integrable_summable D hsecond

/-- Young's inequality for a missing joint-exposure pair in supplement
Eq. (7), pp. 3–4; signed EPO values are allowed. -/
theorem young_missing_pair (a b : ℝ) : |a*b| ≤ a^2/2+b^2/2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a+b), sq_nonneg (a-b)]

/-- Exact nonnegative slack for each missing ordered pair, the finite
algebra behind T19's conservative estimator. This is a supporting lemma;
it is not labelled as the full variance-estimator theorem. -/
theorem missing_pair_slack (a b : ℝ) :
    a^2/2+b^2/2-(-a*b) = (a+b)^2/2 ∧ 0 ≤ (a+b)^2/2 := by
  constructor
  · ring
  · positivity

/-- T7(a): the geometric real design has exactly the nonnegative integers
as its positive-probability support, retaining all other real feasible values. -/
theorem geometric_real_support (z : ℝ) :
    Support realGeometricDesign z ↔ ∃ k : ℕ, (k : ℝ) = z := by
  by_cases hz : ∃ k : ℕ, (k : ℝ) = z
  · obtain ⟨k,rfl⟩ := hz
    simp only [Support, realGeometricDesign, extendDesign, geometricDesign,
      Function.Injective.extend_apply Nat.cast_injective, geometricWeight]
    exact ⟨fun _ => ⟨k,rfl⟩, fun _ => pow_pos (by norm_num) _⟩
  · simp [Support, realGeometricDesign, extendDesign,
      Function.extend_apply' _ _ _ hz, hz]

/-- T7(e): the actual one-unit HT estimator is exactly 2Y1{D=1} at every
real feasible assignment, including assignments outside its positive support. -/
theorem divergent_ht_formula (z : ℝ) :
    ht realGeometricDesign divergentExposure divergentOutcome 1 z =
      2*divergentOutcome 0 z*(if divergentExposure 0 z = 1 then 1 else 0) := by
  simp only [ht, Fin.sum_univ_one, Nat.cast_one, inv_one, one_mul,
    missing_moment_counterexample.1]
  split_ifs <;> ring

/-- T7(c)–(e): the positive and negative weighted parts each have infinite
sums, witnessed by the exact growing 2m-term partial sums. Non-summability
here refers to the alternating weighted atom sequence, not totalized tsum. -/
theorem divergent_parts_not_summable :
    ¬Summable (fun k : ℕ => max ((-1 : ℝ)^k) 0) ∧
    ¬Summable (fun k : ℕ => max (-((-1 : ℝ)^k)) 0) := by
  constructor
  · intro hs
    obtain ⟨m,hm⟩ := exists_nat_gt (∑' k : ℕ, max ((-1 : ℝ)^k) 0)
    have hh := hs.sum_le_tsum (Finset.range (2*m)) (fun k hk => le_max_right _ _)
    rw [(divergent_partial_sums m).1] at hh
    exact not_lt_of_ge hh hm
  · intro hs
    obtain ⟨m,hm⟩ := exists_nat_gt (∑' k : ℕ, max (-((-1 : ℝ)^k)) 0)
    have hh := hs.sum_le_tsum (Finset.range (2*m)) (fun k hk => le_max_right _ _)
    rw [(divergent_partial_sums m).2.1] at hh
    exact not_lt_of_ge hh hm

/-- T1(d)–(e): the printed D-hybrid and the assignment Z-hybrid average
direct effects both equal one, and the AEED gap is constantly one half. -/
theorem coarsened_two_direct_averages (N : ℕ) (hN : 0 < N) :
    ((N : ℝ)⁻¹ * ∑ i, expectation (ternaryDesign N) (fun z =>
      ternaryOutcome i (Function.update (ternaryExposureAssignment z) i 1) -
        ternaryOutcome i (Function.update (ternaryExposureAssignment z) i 0))) = 1 ∧
    ((N : ℝ)⁻¹ * ∑ i, expectation (ternaryDesign N) (fun z =>
      ternaryOutcome i (Function.update z i 1) - ternaryOutcome i (Function.update z i 0))) = 1 := by
  have hd (i : Fin N) (z : Fin N → Fin 3) :
      ternaryOutcome i (Function.update z i 1) - ternaryOutcome i (Function.update z i 0) = 1 := by
    norm_num [ternaryOutcome]
  constructor <;>
    simp only [hd, expectation_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] <;>
    exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')

/-- T1(e): along populations N=n+1, the target gap converges to 1/2 and
fails to converge to zero. The finite exact gap is used without weakening it. -/
theorem coarsened_nonvanishing_gap :
    Tendsto (fun n : ℕ =>
      aeed (ternaryDesign (n+1)) ternaryExposure ternaryOutcome 1 0 - 1) atTop (𝓝 (1/2 : ℝ)) ∧
    ¬Tendsto (fun n : ℕ =>
      aeed (ternaryDesign (n+1)) ternaryExposure ternaryOutcome 1 0 - 1) atTop (𝓝 0) := by
  have he : (fun n : ℕ =>
      aeed (ternaryDesign (n+1)) ternaryExposure ternaryOutcome 1 0 - 1) =
      fun _ : ℕ => (1/2 : ℝ) := by
    funext n
    exact (coarsened_version_counterexample (n+1) (by omega)).2.2.2.2.2.2.2.2.2
  rw [he]
  refine ⟨tendsto_const_nhds, ?_⟩
  intro h
  have hc := tendsto_nhds_unique (tendsto_const_nhds (x := (1/2 : ℝ))) h
  norm_num at hc

/-- Distinct coordinates in the actual finite product design have factorized
product expectations. This is a supporting finite identity for T1(g) and T4. -/
theorem two_coordinate_expectation {A : Type} [Fintype A] (N : ℕ)
    (q : Fin N → Design A) (i j : Fin N) (hij : i ≠ j) (f h : A → ℝ) :
    expectation (productDesign N q) (fun z => f (z i)*h (z j)) =
      expectation (q i) f * expectation (q j) h := by
  have hh := product_expectation N q (fun k a =>
    (if k = i then f a else 1)*(if k = j then h a else 1))
  have he (k : Fin N) : expectation (q k) (fun a =>
      (if k = i then f a else 1)*(if k = j then h a else 1)) =
        (if k = i then expectation (q i) f else 1)*
        (if k = j then expectation (q j) h else 1) := by
    by_cases hi : k = i
    · subst k
      simp only [ite_true, hij, ite_false, mul_one]
    · by_cases hj : k = j
      · subst k
        simp only [hi, ite_false, ite_true, one_mul]
      · simp only [hi, hj, ite_false, one_mul, expectation_one]
  simpa only [he, Finset.prod_mul_distrib, Finset.prod_ite_eq',
    Finset.mem_univ, ite_true] using hh

/-- Finite-design linearity for sums of two variables; used in T1's second
moment computation. No unproved infinite interchange is involved. -/
theorem finite_expectation_add {Ω : Type} [Fintype Ω] (D : Design Ω) (f h : Ω → ℝ) :
    expectation D (fun z => f z+h z) = expectation D f+expectation D h := by
  simp only [expectation, mul_add]
  exact Summable.tsum_add Summable.of_finite Summable.of_finite

/-- Constants have their ordinary means under the normalized design. -/
theorem expectation_const {Ω : Type} (D : Design Ω) (a : ℝ) :
    expectation D (fun _ => a) = a := by
  have hh := expectation_mul_algebra D a (fun _ => 1)
  simpa only [mul_one, expectation_one] using hh

/-- Variance as the second raw moment minus the square of the mean;
finite-design identity underlying supplement Eqs. (5) and (9). -/
theorem finite_variance_moment {Ω : Type} [Fintype Ω] (D : Design Ω) (X : Ω → ℝ) :
    variance D X = expectation D (fun z => X z^2) - (expectation D X)^2 := by
  have he : (fun z => (X z-expectation D X)^2) =
      fun z => X z^2 - (2*expectation D X)*X z + (expectation D X)^2 := by
    funext z; ring
  rw [variance, he, finite_expectation_add,
    expectation_sub D Summable.of_finite Summable.of_finite,
    expectation_mul_algebra, expectation_const]
  ring

/-- Deterministic scaling of design variance, supplement Eqs. (5) and (9). -/
theorem variance_mul {Ω : Type} (D : Design Ω) (c : ℝ) (X : Ω → ℝ) :
    variance D (fun z => c*X z) = c^2*variance D X := by
  simp only [variance, expectation_mul_algebra]
  have he : (fun z => (c*X z-c*expectation D X)^2) =
      fun z => c^2*(X z-expectation D X)^2 := by
    funext z; ring
  rw [he, expectation_mul_algebra]

/-- T1(g)'s finite certificate: the sum of N independent uniform ternary
raw assignments has mean N and second moment N²+(2/3)N. -/
theorem ternary_sum_moments (N : ℕ) :
    expectation (ternaryDesign N) (fun z => ∑ i, ((z i).val : ℝ)) = N ∧
    expectation (ternaryDesign N) (fun z => (∑ i, ((z i).val : ℝ))^2) =
      (N : ℝ)^2 + (2/3 : ℝ)*N := by
  have h1 : expectation (uniformDesign (Fin 3)) (fun a => (a.val : ℝ)) = 1 := by
    norm_num [expectation, uniformDesign, tsum_fintype, Fin.sum_univ_succ]
  have h2 : expectation (uniformDesign (Fin 3)) (fun a => (a.val : ℝ)^2) = 5/3 := by
    norm_num [expectation, uniformDesign, tsum_fintype, Fin.sum_univ_succ]
  have hm (i : Fin N) : expectation (ternaryDesign N) (fun z => ((z i).val : ℝ)) = 1 := by
    exact (coordinate_expectation N (fun _ => uniformDesign (Fin 3)) i (fun a => (a.val : ℝ))).trans h1
  have hij (i j : Fin N) :
      expectation (ternaryDesign N) (fun z => ((z i).val : ℝ)*((z j).val : ℝ)) =
        if i = j then 5/3 else 1 := by
    by_cases he : i = j
    · subst j
      simpa only [ternaryDesign, ite_true, ← pow_two] using (coordinate_expectation N (fun _ => uniformDesign (Fin 3)) i (fun a => (a.val : ℝ)^2)).trans h2
    · simp only [he, ite_false]
      exact (two_coordinate_expectation N (fun _ => uniformDesign (Fin 3)) i j he (fun a => (a.val : ℝ)) (fun a => (a.val : ℝ))).trans (by rw [h1]; norm_num)
  constructor
  · rw [expectation_sum _ _ (fun _ => Summable.of_finite)]
    simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  · have he : (fun z : Fin N → Fin 3 => (∑ i, ((z i).val : ℝ))^2) =
        fun z => ∑ i, ∑ j, ((z i).val : ℝ)*((z j).val : ℝ) := by
      funext z
      rw [pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
    rw [he, expectation_sum _ _ (fun _ => Summable.of_finite)]
    simp_rw [expectation_sum _ _ (fun _ => Summable.of_finite), hij]
    have hr (i : Fin N) : (∑ j : Fin N, if i = j then (5/3 : ℝ) else 1) = N+2/3 := by
      have hp (j : Fin N) : (if i = j then (5/3 : ℝ) else 1) =
          1 + (if j = i then (2/3 : ℝ) else 0) := by
        by_cases he : i = j <;> simp [he, eq_comm] <;> norm_num
      simp only [hp, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    simp only [hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- T1(g): the actual supplement HT contrast has the displayed sum, mean,
variance and concentration bound for every population size. This concentration bound is separate from the estimand counterexample. -/
theorem coarsened_ht_moments (N : ℕ) (hN : 0 < N) :
    (∀ z : Fin N → Fin 3, htContrast (ternaryDesign N) ternaryExposure ternaryOutcome 1 0 z =
      (3 / (2 * N : ℝ)) * ∑ i, ((z i).val : ℝ)) ∧
    expectation (ternaryDesign N) (htContrast (ternaryDesign N) ternaryExposure ternaryOutcome 1 0) = 3/2 ∧
    variance (ternaryDesign N) (htContrast (ternaryDesign N) ternaryExposure ternaryOutcome 1 0) = 3/(2*N : ℝ) ∧
    (∀ ε : ℝ, 0 < ε → probability (ternaryDesign N) (fun z =>
      |htContrast (ternaryDesign N) ternaryExposure ternaryOutcome 1 0 z - 3/2| ≥ ε) ≤
        3/(2 * N * ε^2 : ℝ)) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp1 (i : Fin N) := (ternary_marginals N i).1
  have hp0 (i : Fin N) := (ternary_marginals N i).2.1
  have hterm (i : Fin N) (z : Fin N → Fin 3) :
      (if ternaryExposure i z = 1 then ternaryOutcome i z else 0)/pi (ternaryDesign N) ternaryExposure i 1 -
      (if ternaryExposure i z = 0 then ternaryOutcome i z else 0)/pi (ternaryDesign N) ternaryExposure i 0 =
      (3/2 : ℝ)*((z i).val : ℝ) := by
    by_cases hz : z i = 0
    · norm_num [hp1, hp0, ternaryExposure, ternaryValue, ternaryOutcome, hz]
    · norm_num [hp1, hp0, ternaryExposure, ternaryValue, ternaryOutcome, hz]
      ring
  have hf (z : Fin N → Fin 3) : htContrast (ternaryDesign N) ternaryExposure ternaryOutcome 1 0 z =
      (3 / (2 * N : ℝ)) * ∑ i, ((z i).val : ℝ) := by
    simp only [htContrast, ht, ← mul_sub, ← Finset.sum_sub_distrib, hterm, ← Finset.mul_sum]
    ring
  have he : htContrast (ternaryDesign N) ternaryExposure ternaryOutcome 1 0 =
      fun z => (3 / (2 * N : ℝ)) * ∑ i, ((z i).val : ℝ) := funext hf
  have hm : expectation (ternaryDesign N)
      (htContrast (ternaryDesign N) ternaryExposure ternaryOutcome 1 0) = 3/2 := by
    rw [he, expectation_mul_algebra, (ternary_sum_moments N).1]
    field_simp
  have hv : variance (ternaryDesign N)
      (htContrast (ternaryDesign N) ternaryExposure ternaryOutcome 1 0) = 3/(2*N : ℝ) := by
    rw [he, variance_mul, finite_variance_moment, (ternary_sum_moments N).1,
      (ternary_sum_moments N).2]
    field_simp
    ring
  refine ⟨hf, hm, hv, ?_⟩
  intro ε hε
  have hh := design_chebyshev (ternaryDesign N)
    (htContrast (ternaryDesign N) ternaryExposure ternaryOutcome 1 0) ε hε Summable.of_finite
  rw [hm, hv] at hh
  convert hh using 1 <;> field_simp <;> ring


/-- Reindex the N=2K units by disjoint pairs without changing the population;
finite algebra supporting T2(e) and the T4 HT numerator. -/
theorem sum_units_to_pairs (K : ℕ) (f : Fin (K*2) → ℝ) :
    (∑ i, f i) = ∑ k : Fin K, ∑ j : Fin 2, f (finProdFinEquiv (k,j)) := by
  rw [← finProdFinEquiv.sum_comp f]
  simp only [Fintype.sum_prod_type]

/-- The one partner's assignment is invariant under changing own assignment,
the exact no-own-direct-effect identity in T4's raw response schedule. -/
theorem partner_update_invariant (j : Fin 2) (e : Fin 2) (z : BinaryPair) :
    votingOutcome j (replacePairOwn j e z) = votingOutcome j z := by
  fin_cases j <;> simp [votingOutcome, replacePairOwn]

/-- T4(b): the actual assignment average direct effect is zero for every
population in the pair sequence; every required raw hybrid is feasible. -/
theorem local_ade_zero (m : ℕ) : localDirectEffect m = 0 := by
  have he (i : Fin (m^8*2)) (e : Fin 2) (z : Fin (m^8) → BinaryPair) :
      localOutcome m i (pairedHybrid (m^8) i e z) = localOutcome m i z := by
    simp only [localOutcome, pairedPartnerAssignment, pairedHybrid,
      Function.update_self, partner_update_invariant]
  simp only [localDirectEffect, he, sub_self, expectation_const,
    Finset.sum_const_zero, mul_zero]

/-- T4(a): every own-assignment margin in the actual independent-pair law
is 1/2 for both binary assignments. No equal-margin assumption is substituted
for the stated law. -/
theorem local_assignment_marginals (m : ℕ) (i : Fin (m^8*2)) :
    pi (localDesign m) (pairedAssignment (m^8)) i 1 = 1/2 ∧
    pi (localDesign m) (pairedAssignment (m^8)) i 0 = 1/2 := by
  have he (d : ℝ) : pi (localDesign m) (pairedAssignment (m^8)) i d =
      probability (correlatedPairDesign (localParameter m) (local_parameter_bounds m))
        (fun w => pairAssignment (finProdFinEquiv.symm i).2 w = d) := by
    unfold pi localDesign pairedAssignment
    exact coordinate_probability (m^8)
      (fun _ => correlatedPairDesign (localParameter m) (local_parameter_bounds m))
      (finProdFinEquiv.symm i).1 (fun w => pairAssignment (finProdFinEquiv.symm i).2 w = d)
  rw [he 1, he 0]
  generalize (finProdFinEquiv.symm i).2 = j
  fin_cases j <;> constructor <;>
    norm_num [probability, correlatedPairDesign, pairAssignment, tsum_fintype,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- T4: grouping the supplement's actual HT contrast by pairs
gives the stated sum of B contributions with its actual N denominator. -/
theorem local_estimator_pair_sum (m : ℕ) (z : Fin (m^8) → BinaryPair) :
    localEstimator m z = ((m^8*2 : ℕ) : ℝ)⁻¹ * ∑ k, pairContribution (localParameter m) (z k) := by
  have hp1 (i : Fin (m^8*2)) := (local_assignment_marginals m i).1
  have hp0 (i : Fin (m^8*2)) := (local_assignment_marginals m i).2
  simp only [localEstimator, htContrast, ht, ← mul_sub, ← Finset.sum_sub_distrib, hp1, hp0]
  rw [sum_units_to_pairs (m^8)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [pairedAssignment, localOutcome, pairedPartnerAssignment,
    Equiv.symm_apply_apply, Fin.sum_univ_two]
  generalize z k = w
  rcases w with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;>
    norm_num [pairAssignment, votingOutcome, pairContribution] <;> ring

/-- T4: a sum of K independent, identically distributed finite
pair contributions has mean K times the pair mean and variance K times the
pair variance. The law is the actual product design, not a variance axiom. -/
theorem product_sum_moments {A : Type} [Fintype A] (K : ℕ)
    (q : Design A) (f : A → ℝ) :
    expectation (productDesign K (fun _ => q)) (fun z => ∑ k, f (z k)) =
      (K : ℝ)*expectation q f ∧
    variance (productDesign K (fun _ => q)) (fun z => ∑ k, f (z k)) =
      (K : ℝ)*variance q f := by
  let D := productDesign K (fun _ => q)
  let μ := expectation q f
  let t := expectation q (fun w => f w^2)
  have hm (i : Fin K) : expectation D (fun z => f (z i)) = μ :=
    coordinate_expectation K (fun _ => q) i f
  have hmean : expectation D (fun z => ∑ i, f (z i)) = (K : ℝ)*μ := by
    rw [expectation_sum _ _ (fun _ => Summable.of_finite)]
    simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hij (i j : Fin K) : expectation D (fun z => f (z i)*f (z j)) =
      if i = j then t else μ^2 := by
    by_cases he : i = j
    · subst j
      simpa only [ite_true, ← pow_two] using
        coordinate_expectation K (fun _ => q) i (fun w => f w^2)
    · simpa only [he, ite_false, pow_two] using
        two_coordinate_expectation K (fun _ => q) i j he f f
  have hsecond : expectation D (fun z => (∑ i, f (z i))^2) =
      (K : ℝ)*((K : ℝ)*μ^2+t-μ^2) := by
    have he : (fun z : Fin K → A => (∑ i, f (z i))^2) =
        fun z => ∑ i, ∑ j, f (z i)*f (z j) := by
      funext z
      rw [pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
    rw [he, expectation_sum _ _ (fun _ => Summable.of_finite)]
    simp_rw [expectation_sum _ _ (fun _ => Summable.of_finite), hij]
    have hr (i : Fin K) : (∑ j : Fin K, if i = j then t else μ^2) =
        (K : ℝ)*μ^2+t-μ^2 := by
      have hp (j : Fin K) : (if i = j then t else μ^2) =
          μ^2+(if j = i then t-μ^2 else 0) := by
        by_cases he : i = j <;> simp [he, eq_comm]
      simp only [hp, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    simp only [hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨hmean, ?_⟩
  rw [finite_variance_moment, hmean, hsecond, finite_variance_moment]
  change (K : ℝ)*((K : ℝ)*μ^2+t-μ^2)-((K : ℝ)*μ)^2 = (K : ℝ)*(t-μ^2)
  ring

/-- T4(b)–(c): the actual AEED and mean HT contrast are 1/m²,
the raw ADE is zero, and the actual HT variance is V_m/(4m^8), for every
m≥2. Limit and coverage claims remain separate statements. -/
theorem local_finite_moments (m : ℕ) (hm : 2 ≤ m) :
    localDirectEffect m = 0 ∧
    aeed (localDesign m) (pairedAssignment (m^8)) (localOutcome m) 1 0 = 1/(m : ℝ)^2 ∧
    expectation (localDesign m) (localEstimator m) = 1/(m : ℝ)^2 ∧
    variance (localDesign m) (localEstimator m) = localV m/(4*(m : ℝ)^8) := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hK : ((m^8 : ℕ) : ℝ) ≠ 0 := by norm_cast; positivity
  have ha : localParameter m = 1/(m : ℝ) := by simp only [localParameter, hm, ite_true]
  have he : localEstimator m = fun z =>
      ((m^8*2 : ℕ) : ℝ)⁻¹ * ∑ k, pairContribution (localParameter m) (z k) :=
    funext (local_estimator_pair_sum m)
  have hpair := correlated_pair_moments (localParameter m) (localParameter m) (local_parameter_bounds m)
  have hprod := product_sum_moments (m^8)
    (correlatedPairDesign (localParameter m) (local_parameter_bounds m)) (pairContribution (localParameter m))
  have hmean : expectation (localDesign m) (localEstimator m) = 1/(m : ℝ)^2 := by
    rw [he, expectation_mul_algebra]
    change ((m^8*2 : ℕ) : ℝ)⁻¹ * expectation
      (productDesign (m^8) (fun _ => correlatedPairDesign (localParameter m) (local_parameter_bounds m)))
      (fun z => ∑ k, pairContribution (localParameter m) (z k)) = _
    rw [hprod.1, hpair.1, ha]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hunbiased : expectation (localDesign m) (localEstimator m) =
      aeed (localDesign m) (pairedAssignment (m^8)) (localOutcome m) 1 0 := by
    exact ht_contrast_unbiased _ _ _ _ _ (finite_type_targeted_moment _ _ _ _) (finite_type_targeted_moment _ _ _ _)
      Summable.of_finite Summable.of_finite
  refine ⟨local_ade_zero m, hunbiased.symm.trans hmean, hmean, ?_⟩
  rw [he, variance_mul]
  change ((m^8*2 : ℕ) : ℝ)⁻¹^2 * variance
    (productDesign (m^8) (fun _ => correlatedPairDesign (localParameter m) (local_parameter_bounds m)))
    (fun z => ∑ k, pairContribution (localParameter m) (z k)) = _
  rw [hprod.2, hpair.2.2, ha]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, localV]
  field_simp
  ring

/-- T8(iv): finite positive-probability support makes every finite real
outcome integrable, even when the feasible assignment type itself is infinite.
This is the paper's finite-support case, without discarding off-support points. -/
theorem finite_support_integrable {Ω : Type} (D : Design Ω)
    (hfin : {z : Ω | Support D z}.Finite) (f : Ω → ℝ) : Integrable D f := by
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro z hz
  change D.p z * |f z| ≠ 0 at hz
  change 0 < D.p z
  exact lt_of_le_of_ne (D.nonneg z) (Ne.symm (mul_ne_zero_iff.mp hz).1)

/-- T8(iv): the targeted absolute first moments hold on finite support
for every exposure and raw schedule, with the full feasible domain retained. -/
theorem finite_support_targeted_moment {Ω : Type} {N : ℕ} (D : Design Ω)
    (hfin : {z : Ω | Support D z}.Finite) (g : ExposureMapping Ω N)
    (y : OutcomeSchedule Ω N) (d : ℝ) : TargetedMoment D g y d := by
  intro i
  exact finite_support_integrable D hfin _

/-- T8(iv): finite positive support supplies the targeted absolute moment,
with no finiteness assumption on the full feasible intervention space. -/
theorem finite_targeted_moment {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ)
    (hfin : {z : Ω | Support D z}.Finite) : TargetedMoment D g y d :=
  finite_support_targeted_moment D hfin g y d

/-- T12, Condition 5.2 on p. 8: under global SUTVA, the EPO equals the
raw outcome at every feasible assignment in the positive exposure cell,
including feasible assignments having probability zero under this design. -/
theorem sutva_epo_global {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (hs : SUTVA g y)
    (i : Fin N) (d : ℝ) (hp : 0 < pi D g i d) (z : Ω) (hz : g i z = d) :
    epo D g y i d = y i z := by
  exact (constant_cell D g y i d (y i z) hp
    (fun w hw he => hs i w z (he.trans hz.symm))).2.1

/-- T12's design-free causal estimands under SUTVA: changing the design
while retaining the raw schedule, feasible assignment set and exposure mapping
does not change the EPOs or AEED, provided both target exposures are positive.
The hypotheses use SUTVA itself, with no extra supplied response schedule. -/
theorem sutva_design_invariance {Ω : Type} {N : ℕ} (D D' : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (hs : SUTVA g y)
    (d d' : ℝ) (_hN : 0 < N)
    (hp : ∀ i, 0 < pi D g i d ∧ 0 < pi D g i d')
    (hp' : ∀ i, 0 < pi D' g i d ∧ 0 < pi D' g i d') :
    (∀ i, epo D g y i d = epo D' g y i d ∧ epo D g y i d' = epo D' g y i d') ∧
    aeed D g y d d' = aeed D' g y d d' := by
  have he (i : Fin N) (e : ℝ) (h : 0 < pi D g i e) (h' : 0 < pi D' g i e) :
      epo D g y i e = epo D' g y i e := by
    obtain ⟨z,hz,hg⟩ := positive_cell_has_assignment D g i e h
    exact (sutva_epo_global D g y hs i e h z hg).trans
      (sutva_epo_global D' g y hs i e h' z hg).symm
  have hd (i : Fin N) := he i d (hp i).1 (hp' i).1
  have hd' (i : Fin N) := he i d' (hp i).2 (hp' i).2
  refine ⟨fun i => ⟨hd i, hd' i⟩, ?_⟩
  simp only [aeed, aepo, hd, hd']

/-- A positive event in the paper's atomic design contains a positive atom;
Section 3, p. 3, and the feasibility step of corrected T3(i). -/
theorem positive_event_has_atom {Ω : Type} (D : Design Ω) (A : Ω → Prop)
    (hA : 0 < probability D A) : ∃ z, Support D z ∧ A z := by
  by_contra h
  have he (z : Ω) : (if A z then D.p z else 0) = 0 := by
    by_cases hz : A z
    · have hn : ¬Support D z := fun hs => h ⟨z,hs,hz⟩
      have hp : D.p z = 0 := le_antisymm (le_of_not_gt hn) (D.nonneg z)
      simp [hz, hp]
    · simp [hz]
  have hzero : probability D A = 0 := by simp only [probability, he, tsum_zero]
  rw [hzero] at hA
  exact lt_irrefl _ hA

/-- Corrected T3(i), the full domain repair: independence of own assignment
from the whole other-assignment vector and positive exposure probability imply
that every relevant hybrid has a positive atom in the actual feasible set. -/
theorem independent_coordinate_hybrid_support {N : ℕ} (S : Set (Fin N → ℝ))
    (D : Design S) (i : Fin N) (e : ℝ)
    (hp : 0 < pi D (coordinateMapping S) i e)
    (hi : Independent D (fun z => z.val i) (fun z => others z.val i))
    (w : {j : Fin N // j ≠ i} → ℝ)
    (hw : 0 < probability D (fun z => others z.val i = w)) :
    ∃ z : S, Support D z ∧ z.val = fromOthers i e w := by
  have hfactor := hi (fun x => x = e) (fun r => r = w)
  have hjoint : 0 < probability D (fun z => z.val i = e ∧ others z.val i = w) := by
    rw [hfactor]
    exact mul_pos hp hw
  obtain ⟨z,hz,hze,hzw⟩ := positive_event_has_atom D _ hjoint
  refine ⟨z,hz,?_⟩
  funext j
  by_cases hji : j = i
  · simp [fromOthers, hji, hze]
  · simp only [fromOthers, dif_neg hji]
    exact congrFun hzw ⟨j,hji⟩

/-- T4: its exact variance polynomial lies in [8,20) for m≥2.
The proof uses the small certificate 0<1/m≤1/2 and explicit power bounds. -/
theorem local_variance_polynomial_bounds (m : ℕ) (hm : 2 ≤ m) :
    8 ≤ localV m ∧ localV m < 20 := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  let x : ℝ := 1/(m : ℝ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxh : x ≤ 1/2 := by dsimp [x]; exact (div_le_div_iff₀ hmp (by norm_num)).mpr (by linarith)
  have hx2 : x^2 ≤ 1/4 := by nlinarith
  have hx3 : x^3 ≤ 1/8 := by nlinarith [mul_le_mul_of_nonneg_left hx2 hx]
  have hx4 : x^4 ≤ 1/16 := by nlinarith [mul_le_mul_of_nonneg_left hx3 hx]
  have hx4x : x^4 ≤ x/8 := by nlinarith [mul_le_mul_of_nonneg_left hx3 hx]
  have he : localV m = 8+16*x+14*x^2+2*x^3-4*x^4 := by
    simp only [localV, x, div_pow, one_pow]
    ring
  rw [he]
  constructor
  · nlinarith [pow_nonneg hx 2, pow_nonneg hx 3]
  · nlinarith [pow_nonneg hx 4]

/-- T4(d): the gap divided by the actual standard error has
squared size 4m^4/V_m, at least m^4/5. This connects the finite exact target
and variance identities to the eventual inference-scale failure. -/
theorem local_standardized_gap (m : ℕ) (hm : 2 ≤ m) :
    (1/(m : ℝ)^2/localStandardError m)^2 = 4*(m : ℝ)^4/localV m ∧
    (m : ℝ)^4/5 ≤ (1/(m : ℝ)^2/localStandardError m)^2 := by
  have hv := (local_finite_moments m hm).2.2.2
  have hb := local_variance_polynomial_bounds m hm
  have hV : 0 < localV m := by linarith [hb.1]
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hvar : 0 ≤ variance (localDesign m) (localEstimator m) := by
    rw [hv]
    positivity
  have he : (1/(m : ℝ)^2/localStandardError m)^2 = 4*(m : ℝ)^4/localV m := by
    rw [div_pow]
    rw [localStandardError, Real.sq_sqrt hvar, hv]
    field_simp
  refine ⟨he, ?_⟩
  rw [he, le_div_iff₀ hV]
  have hh := mul_le_mul_of_nonneg_left hb.2.le (pow_nonneg hmp.le 4)
  nlinarith

/-- Monotonicity of the paper's atom-sum event probabilities, Section 3,
p. 3; used for the finite Chebyshev interval certificates in T4. -/
theorem probability_mono {Ω : Type} (D : Design Ω) (A B : Ω → Prop)
    (hAB : ∀ z, A z → B z) : probability D A ≤ probability D B := by
  apply Summable.tsum_le_tsum _ (event_summable D A) (event_summable D B)
  intro z
  by_cases ha : A z
  · simp [ha, hAB z ha]
  · by_cases hb : B z <;> simp [ha, hb, D.nonneg]

/-- Complementation for every event in the paper's atomic design, Section
3, p. 3. The proof retains arbitrary discrete support. -/
theorem probability_complement {Ω : Type} (D : Design Ω) (A : Ω → Prop) :
    probability D (fun z => ¬A z) = 1-probability D A := by
  unfold probability
  calc
    _ = ∑' z, (D.p z - (if A z then D.p z else 0)) := by
      apply tsum_congr
      intro z
      by_cases hz : A z <;> simp [hz]
    _ = _ := by rw [Summable.tsum_sub D.summable (event_summable D A), D.total]

/-- T4(f), the finite coverage failure: the actual ±5 standard-error HT
interval covers AEED with probability at least 24/25, but for m≥5 its ADE
coverage is bounded by V_m/m^4≤20/m^4. No normal approximation is assumed. -/
theorem local_interval_bounds (m : ℕ) (hm : 2 ≤ m) :
    24/25 ≤ probability (localDesign m) (fun z =>
      |localEstimator m z-1/(m : ℝ)^2| ≤ 5*localStandardError m) ∧
    (5 ≤ m → probability (localDesign m) (fun z => |localEstimator m z| ≤ 5*localStandardError m) ≤
      4*variance (localDesign m) (localEstimator m)/(1/(m : ℝ)^2)^2 ∧
      4*variance (localDesign m) (localEstimator m)/(1/(m : ℝ)^2)^2 = localV m/(m : ℝ)^4 ∧
      localV m/(m : ℝ)^4 ≤ 20/(m : ℝ)^4) := by
  let D := localDesign m
  let X := localEstimator m
  let δ : ℝ := 1/(m : ℝ)^2
  let s := localStandardError m
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hb := local_variance_polynomial_bounds m hm
  have hV : 0 < localV m := by linarith [hb.1]
  have hv := (local_finite_moments m hm).2.2.2
  have hmean : expectation D X = δ := (local_finite_moments m hm).2.2.1
  have hvar : 0 < variance D X := by change 0 < variance (localDesign m) (localEstimator m); rw [hv]; positivity
  have hs : 0 < s := Real.sqrt_pos.mpr hvar
  have hs2 : s^2 = variance D X := Real.sq_sqrt hvar.le
  have hlarge : probability D (fun z => |X z-δ| > 5*s) ≤ 1/25 := by
    have hh := (probability_mono D _ _ (fun z hz => le_of_lt hz)).trans
      (design_chebyshev D X (5*s) (by positivity) Summable.of_finite)
    rw [hmean] at hh
    have hr : variance D X/(5*s)^2 = 1/25 := by
      rw [mul_pow, hs2]
      field_simp
      norm_num
    exact hr ▸ hh
  refine ⟨?_, ?_⟩
  · have hh := probability_complement D (fun z => |X z-δ| > 5*s)
    simp only [not_lt] at hh
    change 24/25 ≤ probability D (fun z => |X z-δ| ≤ 5*s)
    linarith
  · intro hm5
    have hm5r : (5 : ℝ) ≤ m := by exact_mod_cast hm5
    have hpow : (5 : ℝ)^4 ≤ (m : ℝ)^4 := by gcongr
    have hgap := (local_standardized_gap m hm).2
    have hgap100 : (100 : ℝ) ≤ (δ/s)^2 := by
      change 100 ≤ (1/(m : ℝ)^2/localStandardError m)^2
      nlinarith
    rw [div_pow, le_div_iff₀ (sq_pos_of_pos hs)] at hgap100
    have hsep : 10*s ≤ δ := by nlinarith
    have hsub (z : Fin (m^8) → BinaryPair) (hz : |X z| ≤ 5*s) : |X z-δ| ≥ δ/2 := by
      have hx : X z ≤ δ/2 := by linarith [le_abs_self (X z)]
      have hh : δ/2 ≤ δ-X z := by linarith
      exact hh.trans (by rw [abs_sub_comm]; exact le_abs_self (δ-X z))
    have hh := (probability_mono D _ _ hsub).trans
      (by simpa only [hmean] using design_chebyshev D X (δ/2) (by positivity) Summable.of_finite)
    have hcover : probability D (fun z => |X z| ≤ 5*s) ≤ 4*variance D X/δ^2 := by
      convert hh using 1 <;> field_simp <;> ring
    have he : 4*variance D X/δ^2 = localV m/(m : ℝ)^4 := by
      change 4*variance (localDesign m) (localEstimator m)/(1/(m : ℝ)^2)^2 = _
      rw [hv]
      field_simp
    refine ⟨hcover, he, ?_⟩
    exact div_le_div_of_nonneg_right hb.2.le (pow_nonneg hmp.le 4)

/-- Corrected T6(i)–(ii), on a finite feasible assignment type: under the stated
positivity and moment hypotheses, EPO equals the conditional expected exposure
outcome, and AEED equals the average of the conditional exposure contrasts. -/
theorem corrected_attribution_general {Ω : Type} [Fintype Ω] {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) (_hN : 0 < N)
    (hp : ∀ i, 0 < pi D g i d) (hp' : ∀ i, 0 < pi D g i d')
    (hm : TargetedMoment D g y d) (hm' : TargetedMoment D g y d') :
    (∀ i, epo D g y i d = conditionalMean D g y i d ∧
      epo D g y i d' = conditionalMean D g y i d') ∧
    aeed D g y d d' = (N : ℝ)⁻¹ * ∑ i,
      (conditionalMean D g y i d-conditionalMean D g y i d') := by
  have hd (i : Fin N) := epo_conditional D g y i d (hp i) (hm i)
  have hd' (i : Fin N) := epo_conditional D g y i d' (hp' i) (hm' i)
  refine ⟨fun i => ⟨hd i,hd' i⟩, ?_⟩
  simp only [aeed_average_eed_algebra, eed, hd, hd']

/-! Exact second-moment development on the full atomic design space. -/

/-- Design expectation respects equality on positive-probability assignments;
zero-weight feasible interventions contribute nothing (Section 3, p. 3). -/
theorem expectation_support_congr {Ω : Type} (D : Design Ω) (f h : Ω → ℝ)
    (he : ∀ z, Support D z → f z = h z) : expectation D f = expectation D h := by
  apply tsum_congr
  intro z
  by_cases hz : Support D z
  · rw [he z hz]
  · have hp : D.p z = 0 := le_antisymm (le_of_not_gt hz) (D.nonneg z)
    simp [hp]

/-- Absolute first moments respect equality on design support; Section 3,
p. 3, and the targeted-moment correction T8. -/
theorem integrable_support_congr {Ω : Type} (D : Design Ω) (f h : Ω → ℝ)
    (he : ∀ z, Support D z → f z = h z) : Integrable D f ↔ Integrable D h := by
  have hh : (fun z => D.p z * |f z|) = (fun z => D.p z * |h z|) := by
    funext z
    by_cases hz : Support D z
    · rw [he z hz]
    · have hp : D.p z = 0 := le_antisymm (le_of_not_gt hz) (D.nonneg z)
      simp [hp]
  unfold Integrable
  rw [hh]

/-- Linearity for integrable sums, used in the supplement's second-moment
expansion in Equations (5) and (9), pp. 3–4. -/
theorem integrable_add {Ω : Type} (D : Design Ω) {f h : Ω → ℝ}
    (hf : Integrable D f) (hh : Integrable D h) : Integrable D (fun z => f z+h z) := by
  apply integrable_of_summable D
  simpa only [mul_add] using (integrable_summable D hf).add (integrable_summable D hh)

/-- Expected sums of integrable variables, supplement Equations (5),(9). -/
theorem expectation_add {Ω : Type} (D : Design Ω) {f h : Ω → ℝ}
    (hf : Integrable D f) (hh : Integrable D h) :
    expectation D (fun z => f z+h z) = expectation D f+expectation D h := by
  unfold expectation
  simp_rw [mul_add]
  exact (integrable_summable D hf).tsum_add (integrable_summable D hh)

/-- Constants have finite absolute moments under every normalized design;
a building block for supplement Equations (5),(9), pp. 3–4, and corrected T8. -/
theorem integrable_const {Ω : Type} (D : Design Ω) (a : ℝ) :
    Integrable D (fun _ => a) := D.summable.mul_right |a|

/-- A constant times an event indicator, with a fixed classical decidability
convention. Used to avoid changing indicators in the covariance expansion. -/
noncomputable def eventResponse {Ω : Type} (A : Ω → Prop) (a : ℝ) (z : Ω) : ℝ :=
  if A z then a else 0

/-- A constant revealed on an event has a finite moment, the indicator
building block of supplement Equations (4)–(9). -/
theorem integrable_event {Ω : Type} (D : Design Ω) (A : Ω → Prop) (a : ℝ) :
    Integrable D (fun z => if A z then a else 0) := by
  classical
  apply integrable_of_summable D
  exact ((event_summable D A).mul_right a).congr (fun z => by split_ifs <;> simp)

/-- Expectation of an event indicator times a constant is the constant times
the event probability; supplement Equations (5)–(8). -/
theorem expectation_event {Ω : Type} (D : Design Ω) (A : Ω → Prop) (a : ℝ) :
    expectation D (fun z => if A z then a else 0) = a*probability D A := by
  classical
  unfold expectation probability
  calc
    (∑' z, D.p z * (if A z then a else 0)) =
        ∑' z, a*(if A z then D.p z else 0) := by
      apply tsum_congr; intro z; split_ifs <;> simp [mul_comm]
    _ = _ := tsum_mul_left

/-- The centered indicator 1{D_i=d}−π_i(d), used in the covariance
expansion of supplement Equations (5) and (9). -/
noncomputable def centeredExposure {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (i : Fin N) (d : ℝ) (z : Ω) : ℝ :=
  (if g i z = d then 1 else 0)-pi D g i d

/-- Products of two centered exposure indicators have finite absolute
moments, including on infinite design support; supplement Equations (5),(9). -/
theorem centered_cross_integrable {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (i j : Fin N) (d e : ℝ) :
    Integrable D (fun z => centeredExposure D g i d z*centeredExposure D g j e z) := by
  classical
  have he : (fun z => centeredExposure D g i d z*centeredExposure D g j e z) =
      (fun z => ((eventResponse (fun w => g i w=d ∧ g j w=e) 1 z) -
        pi D g i d*(if g j z=e then 1 else 0) -
        pi D g j e*(if g i z=d then 1 else 0)) + pi D g i d*pi D g j e) := by
    funext z
    by_cases hi : g i z=d <;> by_cases hj : g j z=e <;>
      simp only [centeredExposure, eventResponse, hi, hj, and_self, and_true, and_false,
        false_and, true_and, ite_true, ite_false] <;> ring
  rw [he]
  have hIJ := integrable_event D (fun z => g i z=d ∧ g j z=e) 1
  have hIB := integrable_mul D (integrable_event D (fun z => g j z=e) 1) (pi D g i d)
  have hIA := integrable_mul D (integrable_event D (fun z => g i z=d) 1) (pi D g j e)
  exact integrable_add D (integrable_sub D (integrable_sub D hIJ hIB) hIA)
    (integrable_const D (pi D g i d*pi D g j e))

/-- Covariance of two exposure indicators is π_ij(d,e)−π_i(d)π_j(e),
including diagonal pairs; supplement Equations (5),(9), pp. 3–4. -/
theorem centered_cross_expectation {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (i j : Fin N) (d e : ℝ) :
    expectation D (fun z => centeredExposure D g i d z*centeredExposure D g j e z) =
      jointPi D g i j d e-pi D g i d*pi D g j e := by
  classical
  have he : (fun z => centeredExposure D g i d z*centeredExposure D g j e z) =
      (fun z => ((eventResponse (fun w => g i w=d ∧ g j w=e) 1 z) -
        pi D g i d*(if g j z=e then 1 else 0) -
        pi D g j e*(if g i z=d then 1 else 0)) + pi D g i d*pi D g j e) := by
    funext z
    by_cases hi : g i z=d <;> by_cases hj : g j z=e <;>
      simp only [centeredExposure, eventResponse, hi, hj, and_self, and_true, and_false,
        false_and, true_and, ite_true, ite_false] <;> ring
  have hIJ := integrable_event D (fun z => g i z=d ∧ g j z=e) 1
  have hIB := integrable_mul D (integrable_event D (fun z => g j z=e) 1) (pi D g i d)
  have hIA := integrable_mul D (integrable_event D (fun z => g i z=d) 1) (pi D g j e)
  rw [he]
  have hlin := expectation_add D (integrable_sub D (integrable_sub D hIJ hIB) hIA)
    (integrable_const D (pi D g i d*pi D g j e))
  have hlin' := expectation_sub D (integrable_sub D hIJ hIB) hIA
  have hlin'' := expectation_sub D hIJ hIB
  calc
    _ = ((expectation D (fun z => eventResponse (fun w => g i w=d ∧ g j w=e) 1 z) -
        expectation D (fun z => pi D g i d*(if g j z=e then 1 else 0))) -
        expectation D (fun z => pi D g j e*(if g i z=d then 1 else 0))) +
        expectation D (fun _ => pi D g i d*pi D g j e) := by
      exact hlin.trans (congrArg (fun x => x+expectation D (fun _ => pi D g i d*pi D g j e))
        (hlin'.trans (congrArg (fun x => x-expectation D (fun z => pi D g j e*(if g i z=d then 1 else 0))) hlin'')))
    _ = _ := by
      have hE : expectation D (fun z => eventResponse (fun w => g i w=d ∧ g j w=e) 1 z) =
          jointPi D g i j d e := by
        simpa only [eventResponse, one_mul, jointPi] using expectation_event D (fun z => g i z=d ∧ g j z=e) 1
      rw [hE]
      simp only [expectation_mul_algebra, expectation_event, expectation_const, one_mul]
      change jointPi D g i j d e - pi D g i d*pi D g j e -
        pi D g j e*pi D g i d + pi D g i d*pi D g j e = _
      ring

/-- Under NURVA the centered HT mean is a finite linear combination of
centered exposure indicators on support; supplement Equations (4),(5). -/
theorem centered_ht_on_support {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ)
    (hp : ∀ i, 0 < pi D g i d) (hn : NURVA D g y) (z : Ω) (hz : Support D z) :
    ht D g y d z-expectation D (ht D g y d) =
      (N : ℝ)⁻¹ * ∑ i, (epo D g y i d/pi D g i d)*centeredExposure D g i d z := by
  classical
  rw [ht_unbiased D g y d (global_nurva_targeted_moment D g y d hp hn)]
  unfold ht aepo
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [nurva_revealed_outcome D g y d hp hn i z hz]
  unfold centeredExposure
  split_ifs <;> field_simp [(hp i).ne'] <;> ring

/-- The supported product of centered HT means is a finite double sum of
integrable indicator products; supplement Equations (5),(9). -/
theorem centered_ht_product {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d e : ℝ)
    (hp : ∀ i, 0 < pi D g i d) (hp' : ∀ i, 0 < pi D g i e) (hn : NURVA D g y)
    (z : Ω) (hz : Support D z) :
    (ht D g y d z-expectation D (ht D g y d)) *
      (ht D g y e z-expectation D (ht D g y e)) =
      (N : ℝ)⁻¹^2 * ∑ i, ∑ j,
        ((epo D g y i d/pi D g i d)*(epo D g y j e/pi D g j e)) *
          (centeredExposure D g i d z*centeredExposure D g j e z) := by
  rw [centered_ht_on_support D g y d hp hn z hz, centered_ht_on_support D g y e hp' hn z hz]
  rw [mul_mul_mul_comm, Finset.sum_mul_sum]
  simp only [pow_two]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- NURVA implies the second moments needed by all HT covariance and
variance formulas, even for a countably infinite assignment support. -/
theorem nurva_second_moment {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d e : ℝ)
    (hp : ∀ i, 0 < pi D g i d) (hp' : ∀ i, 0 < pi D g i e) (hn : NURVA D g y) :
    Integrable D (fun z => (ht D g y d z-expectation D (ht D g y d))*
      (ht D g y e z-expectation D (ht D g y e))) := by
  apply (integrable_support_congr D _ _
    (centered_ht_product D g y d e hp hp' hn)).2
  exact integrable_mul D (integrable_sum D _ (fun i => integrable_sum D _
    (fun j => integrable_mul D (centered_cross_integrable D g i j d e) _))) _

/-- Exact HT covariance under NURVA, supplement Equation (9); d=e also
proves the variance formula in Equation (5). No support finiteness is imposed. -/
theorem nurva_covariance_formula {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d e : ℝ)
    (hp : ∀ i, 0 < pi D g i d) (hp' : ∀ i, 0 < pi D g i e) (hn : NURVA D g y) :
    covariance D (ht D g y d) (ht D g y e) = htCovarianceExpression D g y d e := by
  unfold covariance
  rw [expectation_support_congr D _ _ (centered_ht_product D g y d e hp hp' hn)]
  rw [expectation_mul_algebra, expectation_sum D _ (fun i => integrable_sum D _
    (fun j => integrable_mul D (centered_cross_integrable D g i j d e) _))]
  simp_rw [expectation_sum D _ (fun j => integrable_mul D (centered_cross_integrable D g _ j d e) _)]
  simp_rw [expectation_mul_algebra, centered_cross_expectation]
  unfold htCovarianceExpression
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Design variance equals covariance with itself, on the moment domain
of supplement Equation (5). This is only the defining algebra. -/
theorem variance_eq_covariance {Ω : Type} (D : Design Ω) (X : Ω → ℝ) :
    variance D X = covariance D X X := by simp only [variance, covariance, pow_two]

/-- The variance of a difference is the sum of variances minus twice the
covariance, assuming the stated finite first and centered second moments;
supplement Equation (9), p. 4. -/
theorem variance_difference {Ω : Type} (D : Design Ω) (X Y : Ω → ℝ)
    (hX : Integrable D X) (hY : Integrable D Y)
    (hXX : Integrable D (fun z => (X z-expectation D X)^2))
    (hYY : Integrable D (fun z => (Y z-expectation D Y)^2))
    (hXY : Integrable D (fun z => (X z-expectation D X)*(Y z-expectation D Y))) :
    variance D (fun z => X z-Y z) = variance D X+variance D Y-2*covariance D X Y := by
  unfold variance covariance
  rw [expectation_sub D hX hY]
  have he : (fun z => (X z-Y z-(expectation D X-expectation D Y))^2) =
      (fun z => ((X z-expectation D X)^2+(Y z-expectation D Y)^2) -
        2*((X z-expectation D X)*(Y z-expectation D Y))) := by funext z; ring
  rw [he, expectation_sub D (integrable_add D hXX hYY) (integrable_mul D hXY 2),
    expectation_add D hXX hYY, expectation_mul_algebra]

/-- T18, supplement Eqs. (4),(5),(9): the supported revealed-outcome
identity, estimator reduction, exact variance/covariance expressions, and
the variance of the HT AEED contrast under NURVA. Countable support is allowed. -/
theorem nurva_exact_variances {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d d' : ℝ) (_hN : 0 < N)
    (hp : ∀ i, 0 < pi D g i d ∧ 0 < pi D g i d') (hn : NURVA D g y) :
    (∀ i z, Support D z →
      (if g i z = d then y i z else 0) =
        (if g i z = d then epo D g y i d else 0)) ∧
    (∀ z, Support D z → ht D g y d z =
      (N : ℝ)⁻¹ * ∑ i, (if g i z = d then epo D g y i d else 0)/pi D g i d) ∧
    variance D (ht D g y d) = htCovarianceExpression D g y d d ∧
    covariance D (ht D g y d) (ht D g y d') = htCovarianceExpression D g y d d' ∧
    variance D (htContrast D g y d d') = variance D (ht D g y d) +
      variance D (ht D g y d') - 2 * covariance D (ht D g y d) (ht D g y d') := by
  have hpd : ∀ i, 0 < pi D g i d := fun i => (hp i).1
  have hpe : ∀ i, 0 < pi D g i d' := fun i => (hp i).2
  have hv (e : ℝ) (he : ∀ i, 0 < pi D g i e) :
      variance D (ht D g y e) = htCovarianceExpression D g y e e := by
    rw [variance_eq_covariance]
    exact nurva_covariance_formula D g y e e he he hn
  refine ⟨fun i z hz => nurva_revealed_outcome D g y d hpd hn i z hz, ?_,
    hv d hpd, nurva_covariance_formula D g y d d' hpd hpe hn, ?_⟩
  · intro z hz
    unfold ht
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [nurva_revealed_outcome D g y d hpd hn i z hz]
  · exact variance_difference D _ _
      (ht_integrable D g y d (global_nurva_targeted_moment D g y d hpd hn))
      (ht_integrable D g y d' (global_nurva_targeted_moment D g y d' hpe hn))
      (by simpa only [pow_two] using nurva_second_moment D g y d d hpd hpd hn)
      (by simpa only [pow_two] using nurva_second_moment D g y d' d' hpe hpe hn)
      (nurva_second_moment D g y d d' hpd hpe hn)

/-! Conditioning identities for the corrected direct-effect comparison. -/

/-- Fiberwise weighted sum of a response depending only on W. Grouping
assignments with the same other-coordinate vector is the calculation in T3. -/
theorem fiber_weighted_sum {Ω B : Type} (D : Design Ω) (A : Ω → Prop)
    (W : Ω → B) (f : B → ℝ) (b : B) :
    (∑' z : W ⁻¹' {b}, D.p z * (if A z then f (W z) else 0)) =
      probability D (fun z => A z ∧ W z=b)*f b := by
  classical
  rw [tsum_subtype (W ⁻¹' {b}) (fun z => D.p z*(if A z then f (W z) else 0))]
  unfold probability
  calc
    (∑' z, (W ⁻¹' {b}).indicator (fun z => D.p z*(if A z then f (W z) else 0)) z) =
        ∑' z, (if A z ∧ W z=b then D.p z else 0)*f b := by
      apply tsum_congr
      intro z
      by_cases hW : W z=b <;> by_cases hA : A z <;>
        simp [Set.indicator, hW, hA]
    _ = _ := by
      rw [tsum_mul_right]
      congr 1
      apply tsum_congr
      intro z
      by_cases hA : A z <;> by_cases hW : W z=b <;> simp [hA,hW]

/-- Absolute moment of an event-restricted response can be tested after
grouping by its covariate W. All within-fiber sums automatically converge. -/
theorem integrable_fiber_iff {Ω B : Type} (D : Design Ω) (A : Ω → Prop)
    (W : Ω → B) (f : B → ℝ) :
    Integrable D (fun z => if A z then f (W z) else 0) ↔
      Summable (fun b => probability D (fun z => A z ∧ W z=b)*|f b|) := by
  classical
  have hpart : ∀ z : Ω, ∃! b : B, z ∈ W ⁻¹' {b} := by
    intro z
    exact ⟨W z, rfl, fun b hb => hb.symm⟩
  have hnonneg : 0 ≤ (fun z => D.p z*|if A z then f (W z) else 0|) := by
    intro z; exact mul_nonneg (D.nonneg z) (abs_nonneg _)
  have hfib (b : B) : Summable (fun z : W ⁻¹' {b} =>
      D.p z*|if A z then f (W z) else 0|) := by
    have hsub := (event_summable D A).subtype (W ⁻¹' {b})
    exact (hsub.mul_right |f b|).congr (fun z => by
      have hz : W z.val=b := z.property
      by_cases hA : A z.val <;> simp [hA, hz])
  have he (b : B) : (∑' z : W ⁻¹' {b}, D.p z*|if A z then f (W z) else 0|) =
      probability D (fun z => A z ∧ W z=b)*|f b| := by
    simpa only [apply_ite abs, abs_zero] using fiber_weighted_sum D A W (fun b => |f b|) b
  unfold Integrable
  rw [summable_partition hnonneg hpart]
  simp only [he]
  exact ⟨fun h => h.2, fun h => ⟨hfib,h⟩⟩

/-- A genuine signed expectation can be regrouped over W's fibers.
This is the sum over Z_{−i} or D_{−i} in the corrected statement T3. -/
theorem expectation_fibers {Ω B : Type} (D : Design Ω) (A : Ω → Prop)
    (W : Ω → B) (f : B → ℝ)
    (hf : Integrable D (fun z => if A z then f (W z) else 0)) :
    expectation D (fun z => if A z then f (W z) else 0) =
      ∑' b, probability D (fun z => A z ∧ W z=b)*f b := by
  have hh := (integrable_summable D hf).hasSum.tsum_fiberwise W
  unfold expectation
  rw [← hh.tsum_eq]
  exact tsum_congr (fiber_weighted_sum D A W f)

/-- Independence removes conditioning on a positive-probability event,
with targeted integrability sufficient for the unconditional response moment.
This supplies the exact comparison in both alternatives of corrected T3. -/
theorem independent_event_expectation {Ω A B : Type} (D : Design Ω)
    (X : Ω → A) (W : Ω → B) (E : A → Prop) (f : B → ℝ)
    (hp : 0 < probability D (fun z => E (X z))) (hi : Independent D X W)
    (hf : Integrable D (fun z => if E (X z) then f (W z) else 0)) :
    Integrable D (fun z => f (W z)) ∧
      expectation D (fun z => if E (X z) then f (W z) else 0) =
        probability D (fun z => E (X z))*expectation D (fun z => f (W z)) := by
  classical
  let p := probability D (fun z => E (X z))
  have he (b : B) := hi E (fun w => w=b)
  have hs := (integrable_fiber_iff D (fun z => E (X z)) W f).1 hf
  have hs' : Summable (fun b => probability D (fun z => W z=b)*|f b|) := by
    exact (hs.div_const p).congr (fun b => by
      dsimp [p]
      rw [he b]
      field_simp [hp.ne'])
  have hfull : Integrable D (fun z => f (W z)) := by
    have hh := (integrable_fiber_iff D (fun _ => True) W f).2 (by simpa using hs')
    simpa using hh
  refine ⟨hfull, ?_⟩
  rw [expectation_fibers D _ W f hf]
  have hfullEq := expectation_fibers D (fun _ => True) W f (by simpa using hfull)
  simp only [ite_true, true_and] at hfullEq
  rw [hfullEq]
  simp_rw [he, mul_assoc]
  exact tsum_mul_left

/-- Replacing the own coordinate with its original value recovers the full
assignment vector; footnote 8, p. 7. -/
theorem fromOthers_reconstruct {N : ℕ} (v : Fin N → ℝ) (i : Fin N) :
    fromOthers i (v i) (others v i) = v := by
  funext j
  by_cases h : j=i <;> simp [fromOthers, others, h]

/-- T3(i), corrected comparison: independent assignment coordinates, positive
exposures and the targeted moment imply feasibility of all relevant hybrids,
the unit conditional-mean identities, and exact equality of AEED and ADE.
No SUTVA, NURVA or no-interference restriction is imposed. -/
theorem corrected_coordinate_comparison {N : ℕ} (S : Set (Fin N → ℝ))
    (D : Design S) (y : OutcomeSchedule S N) (d d' : ℝ) (_hN : 0 < N)
    (hp : ∀ i, 0 < pi D (coordinateMapping S) i d ∧ 0 < pi D (coordinateMapping S) i d')
    (hm : TargetedMoment D (coordinateMapping S) y d)
    (hm' : TargetedMoment D (coordinateMapping S) y d')
    (hi : ∀ i, Independent D (fun z => z.val i) (fun z => others z.val i)) :
    (∀ i e, e = d ∨ e = d' → ∀ w,
      0 < probability D (fun z => others z.val i = w) →
      ∃ z : S, Support D z ∧ z.val = fromOthers i e w) ∧
    (∀ i e, e = d ∨ e = d' → Integrable D (hybridOutcome S y i e) ∧
      epo D (coordinateMapping S) y i e = expectation D (hybridOutcome S y i e)) ∧
    aeed D (coordinateMapping S) y d d' = averageDirectEffect S D y d d' := by
  classical
  have hunit (i : Fin N) (e : ℝ) (he : e=d ∨ e=d') :
      Integrable D (hybridOutcome S y i e) ∧
      epo D (coordinateMapping S) y i e = expectation D (hybridOutcome S y i e) := by
    have hpe : 0 < pi D (coordinateMapping S) i e := by
      rcases he with rfl | rfl
      · exact (hp i).1
      · exact (hp i).2
    have hme : Integrable D (fun z => if coordinateMapping S i z=e then y i z else 0) := by
      rcases he with rfl | rfl
      · exact hm i
      · exact hm' i
    let F := fun w => if h : fromOthers i e w ∈ S then y i ⟨fromOthers i e w,h⟩ else 0
    have hraw : (fun z : S => if z.val i=e then y i z else 0) =
        (fun z => if z.val i=e then F (others z.val i) else 0) := by
      funext z
      by_cases hz : z.val i=e
      · have hv : fromOthers i e (others z.val i)=z.val := by
          rw [← hz]; exact fromOthers_reconstruct z.val i
        simp [hz, F, hv]
      · simp [hz]
    have hF : Integrable D (fun z => if z.val i=e then F (others z.val i) else 0) := by
      rw [← hraw]; exact hme
    have hh := independent_event_expectation D (fun z : S => z.val i)
      (fun z => others z.val i) (fun a => a=e) F hpe (hi i) hF
    refine ⟨hh.1, ?_⟩
    unfold epo
    change expectation D (fun z : S => if z.val i=e then y i z else 0)/pi D (coordinateMapping S) i e = _
    rw [hraw, hh.2]
    exact mul_div_cancel_left₀ _ hpe.ne'
  refine ⟨?_, hunit, ?_⟩
  · intro i e he w hw
    apply independent_coordinate_hybrid_support S D i e _ (hi i) w hw
    rcases he with rfl | rfl
    · exact (hp i).1
    · exact (hp i).2
  · unfold averageDirectEffect
    rw [aeed_average_eed_algebra]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi'
    rw [expectation_sub D (hunit i d (Or.inl rfl)).1 (hunit i d' (Or.inr rfl)).1]
    exact congrArg₂ (· - ·) (hunit i d (Or.inl rfl)).2 (hunit i d' (Or.inr rfl)).2

/-- T3(ii), the alternative correction for general exposures: a consistent
schedule H on exposure vectors, independence of own and other exposures,
positivity, and targeted moments imply the stated unit and average identities.
Taking H total merely extends its required domain by arbitrary unused values. -/
theorem corrected_exposure_schedule_comparison {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N)
    (H : Fin N → (Fin N → ℝ) → ℝ) (d d' : ℝ) (_hN : 0 < N)
    (hp : ∀ i, 0 < pi D g i d ∧ 0 < pi D g i d')
    (hm : TargetedMoment D g y d) (hm' : TargetedMoment D g y d')
    (hi : ∀ i, Independent D (g i) (fun z => others (fun j => g j z) i))
    (hc : ∀ i z, Support D z → g i z = d ∨ g i z = d' →
      y i z = H i (fun j => g j z)) :
    (∀ i e, e = d ∨ e = d' →
      Integrable D (fun z => H i (fromOthers i e (others (fun j => g j z) i))) ∧
      epo D g y i e =
        expectation D (fun z => H i (fromOthers i e (others (fun j => g j z) i)))) ∧
    aeed D g y d d' = (N : ℝ)⁻¹ * ∑ i,
      expectation D (fun z => H i (fromOthers i d (others (fun j => g j z) i)) -
        H i (fromOthers i d' (others (fun j => g j z) i))) := by
  classical
  have hunit (i : Fin N) (e : ℝ) (he : e=d ∨ e=d') := by
    have hpe : 0 < pi D g i e := by
      rcases he with rfl | rfl
      · exact (hp i).1
      · exact (hp i).2
    have hme : Integrable D (fun z => if g i z=e then y i z else 0) := by
      rcases he with rfl | rfl
      · exact hm i
      · exact hm' i
    let W := fun z => others (fun j => g j z) i
    let F := fun w => H i (fromOthers i e w)
    have hraw : ∀ z, Support D z → (if g i z=e then y i z else 0) =
        (if g i z=e then F (W z) else 0) := by
      intro z hz
      by_cases hg : g i z=e
      · have hv : fromOthers i e (W z)=(fun j => g j z) := by
          rw [← hg]; exact fromOthers_reconstruct _ i
        have he' : g i z=d ∨ g i z=d' := hg ▸ he
        simp [hg, F, hv, hc i z hz he']
      · simp [hg]
    have hF := (integrable_support_congr D _ _ hraw).1 hme
    have hh := independent_event_expectation D (g i) W (fun a => a=e) F hpe (hi i) hF
    have hepo : epo D g y i e=expectation D (fun z => F (W z)) := by
      unfold epo
      rw [expectation_support_congr D _ _ hraw, hh.2]
      exact mul_div_cancel_left₀ _ hpe.ne'
    exact And.intro hh.1 hepo
  refine ⟨hunit, ?_⟩
  rw [aeed_average_eed_algebra]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  rw [expectation_sub D (hunit i d (Or.inl rfl)).1 (hunit i d' (Or.inr rfl)).1]
  exact congrArg₂ (· - ·) (hunit i d (Or.inl rfl)).2 (hunit i d' (Or.inr rfl)).2

/-- Finite variance bound from the exact formula and Condition 1.1 under
NURVA: Var(HT) ≤ N⁻² ∑_ij |π_ij−π_iπ_j| c². This is the finite
inequality used in supplement Proposition 1, pp. 5–6. -/
theorem nurva_variance_bound {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d c : ℝ)
    (hN : 0 < N) (hc : 0 ≤ c) (hp : ∀ i, 0 < pi D g i d) (hn : NURVA D g y)
    (hcap : ∀ i, probability D (fun z => |(if g i z=d then y i z else 0)/pi D g i d| > c)=0) :
    variance D (ht D g y d) ≤
      (N : ℝ)⁻¹^2 * (∑ i, ∑ j, |jointPi D g i j d d-pi D g i d*pi D g j d|)*c^2 := by
  rw [(nurva_exact_variances D g y d d hN (fun i => ⟨hp i,hp i⟩) hn).2.2.1]
  unfold htCovarianceExpression
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hi' := nurva_reweighted_bound D g y d c hp hn hcap i
  have hj' := nurva_reweighted_bound D g y d c hp hn hcap j
  have hr : |epo D g y i d/pi D g i d| ≤ c := by
    simpa only [abs_div, abs_of_pos (hp i)] using hi'
  have hs : |epo D g y j d/pi D g j d| ≤ c := by
    simpa only [abs_div, abs_of_pos (hp j)] using hj'
  calc
    _ = (jointPi D g i j d d-pi D g i d*pi D g j d)*
        (epo D g y i d/pi D g i d)*(epo D g y j d/pi D g j d) := by ring
    _ ≤ |(jointPi D g i j d d-pi D g i d*pi D g j d)*
        (epo D g y i d/pi D g i d)*(epo D g y j d/pi D g j d)| := le_abs_self _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, mul_assoc, pow_two]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hr hs (abs_nonneg _) hc) (abs_nonneg _)

/-- The exact finite Chebyshev bound used in supplement Proposition 1:
Pr(|HT−AEPO|>ε) ≤ b c²/(N² ε²), under the printed cap and NURVA. -/
theorem nurva_chebyshev_bound {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d b c ε : ℝ)
    (hN : 0 < N) (hc : 0 ≤ c) (hε : 0 < ε)
    (hp : ∀ i, 0 < pi D g i d) (hn : NURVA D g y)
    (hcap : ∀ i, probability D (fun z => |(if g i z=d then y i z else 0)/pi D g i d| > c)=0)
    (hb : ∑ i, ∑ j, |jointPi D g i j d d-pi D g i d*pi D g j d|=b) :
    probability D (fun z => |ht D g y d z-aepo D g y d| > ε) ≤ b*c^2/(N:ℝ)^2/ε^2 := by
  have hu := ht_unbiased D g y d (global_nurva_targeted_moment D g y d hp hn)
  have hv := nurva_variance_bound D g y d c hN hc hp hn hcap
  rw [hb] at hv
  have hsecond : Integrable D (fun z => (ht D g y d z-expectation D (ht D g y d))^2) := by
    simpa only [pow_two] using nurva_second_moment D g y d d hp hp hn
  have hh := (probability_mono D _ _ (fun z hz => le_of_lt hz)).trans
    (design_chebyshev D (ht D g y d) ε hε hsecond)
  rw [hu] at hh
  apply hh.trans
  apply (div_le_div_of_nonneg_right hv (sq_nonneg ε)).trans_eq
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- T21, supplement Proposition 1, p. 5: under all three printed conditions
and NURVA, the HT estimation error is o_p(1). Both ratio limits use population
size N, and Condition 1.2 is retained even though its separate rate is redundant. -/
theorem ht_consistency {Ω : ℕ → Type} (D : ∀ N, Design (Ω N))
    (g : ∀ N, ExposureMapping (Ω N) N) (y : ∀ N, OutcomeSchedule (Ω N) N)
    (d : ℝ) (b c : ℕ → ℝ) (hb : ∀ N, 0 ≤ b N) (hc : ∀ N, 0 ≤ c N)
    (hp : ∀ N, ∀ i, 0 < pi (D N) (g N) i d)
    (hn : ∀ N, NURVA (D N) (g N) (y N))
    (h1 : ∀ N i, probability (D N) (fun z =>
      |(if g N i z = d then y N i z else 0) / pi (D N) (g N) i d| > c N) = 0)
    (h2eq : ∀ N, ∑ i, ∑ j, |jointPi (D N) (g N) i j d d -
      pi (D N) (g N) i d * pi (D N) (g N) j d| = b N)
    (h2rate : Tendsto (fun N => b N / (N : ℝ)^2) atTop (𝓝 0))
    (h3 : Tendsto (fun N => b N * c N^2 / (N : ℝ)^2) atTop (𝓝 0)) :
    ConvergesInProbability D
      (fun N z => ht (D N) (g N) (y N) d z - aepo (D N) (g N) (y N) d) 0 := by
  intro ε hε
  have hlim : Tendsto (fun N => b N*c N^2/(N:ℝ)^2/ε^2) atTop (𝓝 (0:ℝ)) := by
    simpa using h3.div_const (ε^2)
  have hupper : ∀ᶠ N in atTop, probability (D N) (fun z =>
      |ht (D N) (g N) (y N) d z-aepo (D N) (g N) (y N) d-0| > ε) ≤
      b N*c N^2/(N:ℝ)^2/ε^2 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa only [sub_zero] using nurva_chebyshev_bound (D N) (g N) (y N) d (b N) (c N) ε
      (by omega) (hc N) hε (hp N) (hn N) (h1 N) (h2eq N)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall (fun N => probability_nonneg (D N) _)) hupper

/-- T5's finite neighborhood configurations for an arbitrary finite assignment
alphabet. -/
abbrev GeneralNeighborConfig {N : ℕ} (A : Type) (H : Finset (Fin N)) := H → A

/-- Unconditional neighborhood law in corrected T5, for general finite
assignment labels rather than only 0 and 1. -/
noncomputable def generalNeighborLaw {A : Type} {N : ℕ} (D : Design (Fin N → A))
    (H : Finset (Fin N)) (x : GeneralNeighborConfig A H) : ℝ :=
  probability D (fun z => ∀ j : H, z j.val=x j)

/-- Conditional neighborhood law in corrected T5, given own assignment e.
Only positive-probability own assignments are used in its theorem. -/
noncomputable def conditionalGeneralNeighborLaw {A : Type} {N : ℕ} (D : Design (Fin N → A))
    (i : Fin N) (H : Finset (Fin N)) (e : A) (x : GeneralNeighborConfig A H) : ℝ :=
  probability D (fun z => z i=e ∧ ∀ j : H, z j.val=x j) /
    probability D (fun z => z i=e)

/-- T5's local-TV sufficient bias bound, with arbitrary finite assignment
labels encoded injectively as real coordinates. Each neighborhood excludes
its own unit, and both target probabilities are positive. -/
theorem local_total_variation_bias_bound {A : Type} [Fintype A] [Nonempty A] {N : ℕ}
    (label : A → ℝ) (hlabel : Function.Injective label) (D : Design (Fin N → A))
    (y : OutcomeSchedule (Fin N → A) N) (H : Fin N → Finset (Fin N))
    (f : ∀ i, A → GeneralNeighborConfig A (H i) → ℝ) (d d' : A) (_hN : 0 < N)
    (hH : ∀ i, i ∉ H i)
    (hp : ∀ i, 0 < pi D (fun i z => label (z i)) i (label d) ∧
      0 < pi D (fun i z => label (z i)) i (label d'))
    (hy : ∀ i e, e=d ∨ e=d' → ∀ z,
      y i (Function.update z i e) = f i e (fun j => z j.val)) :
    |aeed D (fun i z => label (z i)) y (label d) (label d') -
      (N : ℝ)⁻¹ * ∑ i, expectation D (fun z =>
        y i (Function.update z i d)-y i (Function.update z i d'))| ≤
      (N : ℝ)⁻¹ * ∑ i,
        (functionRange (f i d) * totalVariation (conditionalGeneralNeighborLaw D i (H i) d) (generalNeighborLaw D (H i)) +
         functionRange (f i d') * totalVariation (conditionalGeneralNeighborLaw D i (H i) d') (generalNeighborLaw D (H i))) := by
  classical
  have hunit (i : Fin N) (e : A) (he : e=d ∨ e=d') :
      |epo D (fun i z => label (z i)) y i (label e) -
        expectation D (fun z => y i (Function.update z i e))| ≤
      functionRange (f i e)*totalVariation
        (conditionalGeneralNeighborLaw D i (H i) e) (generalNeighborLaw D (H i)) := by
    let W := fun z : Fin N → A => (fun j : H i => z j.val)
    have hπ : pi D (fun i z => label (z i)) i (label e) = probability D (fun z => z i=e) := by
      unfold pi
      congr 1
      funext z
      simp only [hlabel.eq_iff]
    have hp' : 0 < probability D (fun z => z i=e) := by
      rw [← hπ]
      rcases he with rfl | rfl
      · exact (hp i).1
      · exact (hp i).2
    have hraw : (fun z => if label (z i)=label e then y i z else 0) =
        (fun z => if z i=e then f i e (W z) else 0) := by
      funext z
      by_cases hz : z i=e
      · have hu : Function.update z i e=z := by rw [← hz]; exact Function.update_eq_self i z
        have hh := hy i e he z
        rw [hu] at hh
        simp [hz, hh, W]
      · have hl : label (z i) ≠ label e := fun h => hz (hlabel h)
        simp [hz,hl]
    have hQ : (∑ x, conditionalGeneralNeighborLaw D i (H i) e x*f i e x) =
        epo D (fun i z => label (z i)) y i (label e) := by
      unfold epo
      rw [hraw, hπ, expectation_fibers D (fun z => z i=e) W (f i e) Summable.of_finite, tsum_fintype]
      simp only [conditionalGeneralNeighborLaw, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      have hprob : probability D (fun z => z i=e ∧ ∀ j : H i, z j.val=x j) =
          probability D (fun z => z i=e ∧ W z=x) := by
        congr 1; funext z; simp only [W, funext_iff]
      rw [hprob]
      ring
    have hP : (∑ x, generalNeighborLaw D (H i) x*f i e x) =
        expectation D (fun z => y i (Function.update z i e)) := by
      have hf : (fun z => y i (Function.update z i e)) = (fun z => f i e (W z)) := funext (hy i e he)
      rw [hf]
      have hh := expectation_fibers D (fun _ => True) W (f i e) (by simpa using (show Integrable D (fun z => f i e (W z)) from Summable.of_finite))
      simp only [ite_true, true_and, tsum_fintype] at hh
      rw [hh]
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      unfold generalNeighborLaw
      congr 1; funext z; simp only [W, funext_iff]
    have hsum (B : (Fin N → A) → Prop) :
        (∑ x, probability D (fun z => B z ∧ W z=x)) = probability D B := by
      have hh := expectation_fibers D B W (fun _ => 1) Summable.of_finite
      simp only [tsum_fintype, mul_one, expectation_event, one_mul] at hh
      exact hh.symm
    have hQsum : ∑ x, conditionalGeneralNeighborLaw D i (H i) e x = 1 := by
      unfold conditionalGeneralNeighborLaw
      rw [← Finset.sum_div]
      have hh : (∑ x : GeneralNeighborConfig A (H i), probability D (fun z => z i=e ∧ ∀ j : H i, z j.val=x j)) =
          probability D (fun z => z i=e) := by
        simpa only [W, funext_iff] using hsum (fun z => z i=e)
      rw [hh, div_self hp'.ne']
    have hPsum : ∑ x, generalNeighborLaw D (H i) x = 1 := by
      have hh := hsum (fun _ => True)
      simp only [true_and] at hh
      have ht : probability D (fun _ => True) = 1 := by simpa only [probability, ite_true] using D.total
      rw [ht] at hh
      simpa only [generalNeighborLaw, W, funext_iff] using hh
    have hbounds (x : GeneralNeighborConfig A (H i)) :
        sInf (Set.range (f i e)) ≤ f i e x ∧ f i e x ≤ sSup (Set.range (f i e)) :=
      ⟨csInf_le (Set.finite_range (f i e)).bddBelow ⟨x,rfl⟩,
       le_csSup (Set.finite_range (f i e)).bddAbove ⟨x,rfl⟩⟩
    have hh := expectation_total_variation
      (conditionalGeneralNeighborLaw D i (H i) e) (generalNeighborLaw D (H i)) (f i e)
      (sInf (Set.range (f i e))) (sSup (Set.range (f i e)))
      (fun x => div_nonneg (probability_nonneg D _) hp'.le)
      (fun x => probability_nonneg D _) hQsum hPsum hbounds
    rw [hQ,hP] at hh
    exact hh
  have halg : aeed D (fun i z => label (z i)) y (label d) (label d') -
      (N:ℝ)⁻¹ * ∑ i, expectation D (fun z => y i (Function.update z i d)-y i (Function.update z i d')) =
      (N:ℝ)⁻¹ * ∑ i,
        ((epo D (fun i z => label (z i)) y i (label d)-expectation D (fun z => y i (Function.update z i d))) -
         (epo D (fun i z => label (z i)) y i (label d')-expectation D (fun z => y i (Function.update z i d')))) := by
    simp_rw [expectation_sub D (show Integrable D (fun z => y _ (Function.update z _ d)) from Summable.of_finite)
      (show Integrable D (fun z => y _ (Function.update z _ d')) from Summable.of_finite)]
    simp only [aeed, aepo, Finset.sum_sub_distrib]
    ring
  rw [halg, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  exact (abs_sub _ _).trans (add_le_add (hunit i d (Or.inl rfl)) (hunit i d' (Or.inr rfl)))

set_option maxHeartbeats 800000 in
/-- T19, supplement Eqs. (6)–(8): under NURVA the first variance estimator
is unbiased if all joint probabilities are positive, and the second is
conservative in expectation with no joint-positivity condition. -/
theorem nurva_variance_estimators {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (_hN : 0 < N)
    (hp : ∀ i, 0 < pi D g i d) (hn : NURVA D g y) :
    ((∀ i j, 0 < jointPi D g i j d d) →
      expectation D (htVarianceEstimator D g y d) = variance D (ht D g y d)) ∧
    expectation D (conservativeVarianceEstimator D g y d) ≥ variance D (ht D g y d) := by
  classical
  let P := fun (i j : Fin N) (z : Ω) =>
    ((jointPi D g i j d d-pi D g i d*pi D g j d)/(pi D g i d*pi D g j d)) *
      y i z*y j z*(if g i z=d ∧ g j z=d then 1 else 0)/jointPi D g i j d d
  let C := fun (i j : Fin N) =>
    ((jointPi D g i j d d-pi D g i d*pi D g j d)/(pi D g i d*pi D g j d)) *
      epo D g y i d*epo D g y j d
  have hP (i j : Fin N) : Integrable D (P i j) ∧
      expectation D (P i j) = C i j/jointPi D g i j d d*jointPi D g i j d d := by
    let J := fun z => g i z=d ∧ g j z=d
    have he : ∀ z, Support D z → P i j z = eventResponse J (C i j/jointPi D g i j d d) z := by
      intro z hz
      by_cases hi : g i z=d <;> by_cases hj : g j z=d
      · have hi' := (nurva_epo D g y hn i d (hp i) z hz hi).symm
        have hj' := (nurva_epo D g y hn j d (hp j) z hz hj).symm
        simp only [P, C, eventResponse, J, hi, hj, and_self, ite_true, hi', hj', mul_one]
      · simp [P, eventResponse, J, hi, hj]
      · simp [P, eventResponse, J, hi, hj]
      · simp [P, eventResponse, J, hi, hj]
    refine ⟨(integrable_support_congr D _ _ he).2 (integrable_event D J _), ?_⟩
    rw [expectation_support_congr D _ _ he]
    exact expectation_event D J _
  let S := fun (i : Fin N) (z : Ω) => (if g i z=d then y i z^2/2 else 0)/pi D g i d
  have hS (i : Fin N) : Integrable D (S i) ∧ expectation D (S i)=epo D g y i d^2/2 := by
    have he : ∀ z, Support D z → S i z=eventResponse (fun z => g i z=d) (epo D g y i d^2/2/pi D g i d) z := by
      intro z hz
      by_cases hi : g i z=d
      · have hi' := (nurva_epo D g y hn i d (hp i) z hz hi).symm
        simp [S,eventResponse,hi,hi']
      · simp [S,eventResponse,hi]
    refine ⟨(integrable_support_congr D _ _ he).2 (integrable_event D _ _), ?_⟩
    rw [expectation_support_congr D _ _ he]
    change expectation D (fun z => if g i z=d then epo D g y i d^2/2/pi D g i d else 0) = _
    rw [expectation_event]
    exact div_mul_cancel₀ _ (hp i).ne'
  let R := fun (i j : Fin N) (z : Ω) =>
    if 0 < jointPi D g i j d d then P i j z
    else if jointPi D g i j d d=0 then S i z+S j z else 0
  let M := fun (i j : Fin N) => if 0 < jointPi D g i j d d then C i j
    else epo D g y i d^2/2+epo D g y j d^2/2
  have hR (i j : Fin N) : Integrable D (R i j) ∧ expectation D (R i j)=M i j := by
    by_cases hr : 0 < jointPi D g i j d d
    · simp only [R, M, hr, ite_true]
      exact ⟨(hP i j).1, (hP i j).2.trans (div_mul_cancel₀ _ hr.ne')⟩
    · have hr0 : jointPi D g i j d d=0 :=
        le_antisymm (le_of_not_gt hr) (probability_nonneg D _)
      simp only [R, M, hr, ite_false]
      simp only [hr0, ite_true]
      exact ⟨integrable_add D (hS i).1 (hS j).1,
        (expectation_add D (hS i).1 (hS j).1).trans (congrArg₂ (· + ·) (hS i).2 (hS j).2)⟩
  have hvar : variance D (ht D g y d)=(N:ℝ)⁻¹^2*∑ i, ∑ j, C i j :=
    (nurva_exact_variances D g y d d _hN (fun i => ⟨hp i,hp i⟩) hn).2.2.1
  constructor
  · intro hjoint
    change expectation D (fun z => (N:ℝ)⁻¹^2*∑ i, ∑ j, P i j z) = _
    rw [expectation_mul_algebra, expectation_sum D _ (fun i => integrable_sum D _ (fun j => (hP i j).1))]
    simp_rw [expectation_sum D _ (fun j => (hP _ j).1)]
    rw [hvar]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact (hP i j).2.trans (div_mul_cancel₀ _ (hjoint i j).ne')
  · rw [hvar]
    change (N:ℝ)⁻¹^2*(∑ i, ∑ j, C i j) ≤
      expectation D (fun z => (N:ℝ)⁻¹^2*∑ i, ∑ j, R i j z)
    rw [expectation_mul_algebra, expectation_sum D _ (fun i => integrable_sum D _ (fun j => (hR i j).1))]
    simp_rw [expectation_sum D _ (fun j => (hR _ j).1)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    rw [(hR i j).2]
    by_cases hr : 0 < jointPi D g i j d d
    · simp [M,hr]
    · have hr0 : jointPi D g i j d d=0 :=
        le_antisymm (le_of_not_gt hr) (probability_nonneg D _)
      simp only [M,hr,ite_false]
      simp only [C,hr0,zero_sub]
      have hc : -(pi D g i d*pi D g j d)/(pi D g i d*pi D g j d) = -1 := by
        field_simp [(hp i).ne',(hp j).ne']
      rw [hc]
      nlinarith [sq_nonneg (epo D g y i d+epo D g y j d)]


/-- Each coordinate of a finite product design is independent of the whole
vector of remaining coordinates, not merely pairwise independent. T4 uses
this for a correlated pair versus all other independently assigned pairs. -/
theorem product_coordinate_independent {A B : Type} [Fintype A] (K : ℕ)
    (q : Fin K → Design A) (i : Fin K) (f : A → B) :
    Independent (productDesign K q) (fun z => f (z i))
      (fun z => fun j : {j : Fin K // j ≠ i} => z j.val) := by
  classical
  let e := Equiv.funSplitAt i A
  have he (r : A × ({j : Fin K // j ≠ i} → A)) :
      (e.symm r) i=r.1 ∧ (fun j : {j : Fin K // j ≠ i} => (e.symm r) j.val)=r.2 := by
    exact Prod.mk.inj (e.apply_symm_apply r)
  have hw (r : A × ({j : Fin K // j ≠ i} → A)) :
      (∏ j, (q j).p (e.symm r j)) = (q i).p r.1*∏ j : {j : Fin K // j ≠ i}, (q j.val).p (r.2 j) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, (he r).1]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [congrFun (he r).2 j]
  have hfac (E : B → Prop) (F : ({j : Fin K // j ≠ i} → A) → Prop) :
      probability (productDesign K q) (fun z => E (f (z i)) ∧ F (fun j => z j.val)) =
      (∑ a, if E (f a) then (q i).p a else 0) *
      (∑ w : {j : Fin K // j ≠ i} → A, if F w then ∏ j, (q j.val).p (w j) else 0) := by
    unfold probability
    rw [tsum_fintype, ← e.symm.sum_comp, Fintype.sum_prod_type]
    calc
      _ = ∑ a, ∑ w : {j : Fin K // j ≠ i} → A,
          (if E (f a) then (q i).p a else 0)*(if F w then ∏ j, (q j.val).p (w j) else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro w hw'
        dsimp only [productDesign]
        simp only [(he (a,w)).1, (he (a,w)).2, hw (a,w)]
        by_cases hE : E (f a) <;> by_cases hF : F w <;> simp [hE,hF]
      _ = _ := by rw [Finset.sum_mul_sum]
  have ht : ∑ a, (q i).p a=1 := by rw [← tsum_fintype (L := .unconditional A)]; exact (q i).total
  have ht' : (∑ w : {j : Fin K // j ≠ i} → A, ∏ j, (q j.val).p (w j))=1 := by
    rw [← Fintype.prod_sum]
    have hh (j : {j : Fin K // j ≠ i}) : ∑ a, (q j.val).p a=1 := by
      rw [← tsum_fintype (L := .unconditional A)]; exact (q j.val).total
    simp only [hh,Finset.prod_const_one]
  intro E F
  have hj := hfac E F
  have hE := hfac E (fun _ => True)
  have hF := hfac (fun _ => True) F
  simp only [and_true,ite_true,ht',mul_one] at hE
  simp only [true_and,ite_true,ht,one_mul] at hF
  rw [hj,hE,hF]

/-- T4(a): every full binary assignment has positive mass and every partner
outcome lies in [1,3/2], for the explicit parameter a=ρ=1/m, m≥2. -/
theorem local_support_and_bounds (m : ℕ) (hm : 2 ≤ m) :
    (∀ z, Support (localDesign m) z) ∧
    (∀ i z, 1 ≤ localOutcome m i z ∧ localOutcome m i z ≤ 3/2) := by
  have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
  have ha : localParameter m=1/(m:ℝ) := by simp only [localParameter,hm,ite_true]
  have ha0 : 0 ≤ localParameter m := (local_parameter_bounds m).1
  have ha1 : localParameter m ≤ 1/2 := by rw [ha]; exact (div_le_div_iff₀ (by linarith : (0:ℝ)<m) (by norm_num : (0:ℝ)<2)).2 (by linarith)
  constructor
  · intro z
    change 0 < ∏ k, (correlatedPairDesign (localParameter m) (local_parameter_bounds m)).p (z k)
    apply Finset.prod_pos
    intro k hk
    dsimp [correlatedPairDesign]
    split_ifs <;> linarith
  · intro i z
    have hb : 0 ≤ pairedPartnerAssignment (m^8) i z ∧ pairedPartnerAssignment (m^8) i z ≤ 1 := by
      unfold pairedPartnerAssignment votingOutcome
      split_ifs
      · constructor
        · positivity
        · exact_mod_cast (Nat.le_of_lt_succ (z (finProdFinEquiv.symm i).1).2.is_lt)
      · constructor
        · positivity
        · exact_mod_cast (Nat.le_of_lt_succ (z (finProdFinEquiv.symm i).1).1.is_lt)
    dsimp [localOutcome]
    constructor <;> nlinarith [mul_nonneg ha0 hb.1]

/-- T4(a),(c): the covariance and the two exact conditional means in the
correlated-pair design; the proof enumerates only one four-atom pair. -/
theorem local_unit_epos_and_covariance (m : ℕ) (hm : 2 ≤ m) :
    (∀ i, epo (localDesign m) (pairedAssignment (m^8)) (localOutcome m) i 1 =
      1+(1/(m:ℝ))*((1+1/(m:ℝ))/2) ∧
      epo (localDesign m) (pairedAssignment (m^8)) (localOutcome m) i 0 =
      1+(1/(m:ℝ))*((1-1/(m:ℝ))/2)) ∧
    (∀ k : Fin (m^8), covariance (localDesign m) (fun z => pairAssignment 0 (z k))
      (fun z => pairAssignment 1 (z k))=1/(4*m:ℝ)) := by
  have ha : localParameter m=1/(m:ℝ) := by simp only [localParameter,hm,ite_true]
  have hm0 : (m:ℝ) ≠ 0 := by
    have hh : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  let q := correlatedPairDesign (localParameter m) (local_parameter_bounds m)
  constructor
  · intro i
    have he (d : ℝ) : expectation (localDesign m) (fun z =>
        if pairedAssignment (m^8) i z=d then localOutcome m i z else 0) =
        expectation q (fun w => if pairAssignment (finProdFinEquiv.symm i).2 w=d then
          1+localParameter m*votingOutcome (finProdFinEquiv.symm i).2 w else 0) := by
      convert coordinate_expectation (m^8) (fun _ => q) (finProdFinEquiv.symm i).1
        (fun w => if pairAssignment (finProdFinEquiv.symm i).2 w=d then
          1+localParameter m*votingOutcome (finProdFinEquiv.symm i).2 w else 0) using 1 <;>
        congr 1 <;> funext z <;>
        simp only [q,localDesign,localOutcome,pairedAssignment,pairedPartnerAssignment] <;>
        split_ifs <;> rfl
    unfold epo
    rw [(local_assignment_marginals m i).1,(local_assignment_marginals m i).2,he 1,he 0]
    have hpj := (finProdFinEquiv.symm i).2.is_lt
    generalize hj : (finProdFinEquiv.symm i).2=j
    fin_cases j <;> norm_num [expectation,q,correlatedPairDesign, pairAssignment,votingOutcome,
      tsum_fintype,Fintype.sum_prod_type,Fin.sum_univ_two,ha] <;> constructor <;> ring
  · intro k
    have hmean (j : Fin 2) : expectation (localDesign m) (fun z => pairAssignment j (z k))=1/2 := by
      rw [show localDesign m=productDesign (m^8) (fun _ => q) from rfl,coordinate_expectation]
      fin_cases j <;> norm_num [expectation,q,correlatedPairDesign,pairAssignment,
        tsum_fintype,Fintype.sum_prod_type,Fin.sum_univ_two] <;> ring
    unfold covariance
    rw [hmean 0,hmean 1]
    rw [show localDesign m=productDesign (m^8) (fun _ => q) from rfl]
    rw [coordinate_expectation (m^8) (fun _ => q) k
      (fun w => (pairAssignment 0 w-1/2)*(pairAssignment 1 w-1/2))]
    norm_num [expectation,q,correlatedPairDesign,pairAssignment,
      tsum_fintype,Fintype.sum_prod_type,Fin.sum_univ_two,ha]
    field_simp
    ring

/-- T4(a)–(f): the full concrete sequence counterexample, including degree-one
locality (independence from all other pairs and one partner in the outcome),
positive support, exact targets/variance, standardized gap and both Chebyshev
coverage bounds. The paired encoding is the full {0,1}^{2m^8} space. -/
theorem local_inference_counterexample (m : ℕ) (hm : 2 ≤ m) :
    (∀ z, Support (localDesign m) z) ∧
    (∀ i, pi (localDesign m) (pairedAssignment (m^8)) i 1 = 1/2 ∧
      pi (localDesign m) (pairedAssignment (m^8)) i 0 = 1/2) ∧
    (∀ i z, 1 ≤ localOutcome m i z ∧ localOutcome m i z ≤ 3/2) ∧
    (∀ i, Independent (localDesign m) (pairedAssignment (m^8) i)
      (fun z => fun k : {k : Fin (m^8) // k ≠ (finProdFinEquiv.symm i).1} => z k.val)) ∧
    (∀ k : Fin (m^8), covariance (localDesign m) (fun z => pairAssignment 0 (z k))
      (fun z => pairAssignment 1 (z k)) = 1/(4*m : ℝ)) ∧
    localDirectEffect m = 0 ∧
    (∀ i, epo (localDesign m) (pairedAssignment (m^8)) (localOutcome m) i 1 =
      1+(1/(m : ℝ))*((1+1/(m : ℝ))/2) ∧
      epo (localDesign m) (pairedAssignment (m^8)) (localOutcome m) i 0 =
      1+(1/(m : ℝ))*((1-1/(m : ℝ))/2)) ∧
    aeed (localDesign m) (pairedAssignment (m^8)) (localOutcome m) 1 0 = 1/(m : ℝ)^2 ∧
    expectation (localDesign m) (localEstimator m) = 1/(m : ℝ)^2 ∧
    variance (localDesign m) (localEstimator m) = localV m/(4*(m : ℝ)^8) ∧
    8 ≤ localV m ∧ localV m < 20 ∧
    (1/(m : ℝ)^2/localStandardError m)^2 = 4*(m : ℝ)^4/localV m ∧
    (m : ℝ)^4/5 ≤ (1/(m : ℝ)^2/localStandardError m)^2 ∧
    24/25 ≤ probability (localDesign m) (fun z =>
      |localEstimator m z - 1/(m : ℝ)^2| ≤ 5*localStandardError m) ∧
    (5 ≤ m → probability (localDesign m) (fun z => |localEstimator m z| ≤ 5*localStandardError m) ≤
      4*variance (localDesign m) (localEstimator m)/(1/(m : ℝ)^2)^2 ∧
      4*variance (localDesign m) (localEstimator m)/(1/(m : ℝ)^2)^2 = localV m/(m : ℝ)^4 ∧
      localV m/(m : ℝ)^4 ≤ 20/(m : ℝ)^4) := by
  have hbase := local_support_and_bounds m hm
  have hunit := local_unit_epos_and_covariance m hm
  have hmoment := local_finite_moments m hm
  have hV := local_variance_polynomial_bounds m hm
  have hgap := local_standardized_gap m hm
  have hcov := local_interval_bounds m hm
  refine ⟨hbase.1,local_assignment_marginals m,hbase.2,?_,hunit.2,hmoment.1,hunit.1,
    hmoment.2.1,hmoment.2.2.1,hmoment.2.2.2,hV.1,hV.2,hgap.1,hgap.2,hcov.1,hcov.2⟩
  intro i
  exact product_coordinate_independent (m^8)
    (fun _ => correlatedPairDesign (localParameter m) (local_parameter_bounds m))
    (finProdFinEquiv.symm i).1 (pairAssignment (finProdFinEquiv.symm i).2)

/-- T4's asymptotic conclusions along N=2m^8: the target gap vanishes, the
variance is of exact order N^{-1}, the squared standardized gap diverges,
and coverage of the ADE by the valid AEED interval tends to zero. -/
theorem local_inference_limits :
    Tendsto (fun (m : ℕ) => aeed (localDesign m) (pairedAssignment (m^8)) (localOutcome m) 1 0 -
      localDirectEffect m) atTop (𝓝 0) ∧
    Tendsto (fun (m : ℕ) => (m^8*2 : ℝ)*variance (localDesign m) (localEstimator m)) atTop (𝓝 4) ∧
    Tendsto (fun (m : ℕ) => ((aeed (localDesign m) (pairedAssignment (m^8)) (localOutcome m) 1 0 -
      localDirectEffect m)/localStandardError m)^2) atTop atTop ∧
    Tendsto (fun (m : ℕ) => probability (localDesign m)
      (fun z => |localEstimator m z - localDirectEffect m| ≤ 5*localStandardError m)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun m : ℕ => (m:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hV : Tendsto localV atTop (𝓝 (8:ℝ)) := by
    have hh := (((tendsto_const_nhds (x := (8:ℝ))).add (hinv.const_mul 16)).add
      ((hinv.pow 2).const_mul 14)).add ((hinv.pow 3).const_mul 2) |>.sub ((hinv.pow 4).const_mul 4)
    change Tendsto (fun m : ℕ => 8+16/(m:ℝ)+14/(m:ℝ)^2+2/(m:ℝ)^3-4/(m:ℝ)^4) atTop (𝓝 (8:ℝ))
    simpa [div_eq_mul_inv,inv_pow] using hh
  have hdelta : ∀ᶠ m in atTop, aeed (localDesign m) (pairedAssignment (m^8)) (localOutcome m) 1 0-
      localDirectEffect m=1/(m:ℝ)^2 := by
    filter_upwards [eventually_ge_atTop 2] with m hm
    rw [(local_finite_moments m hm).2.1,local_ade_zero,sub_zero]
  have hgap : Tendsto (fun m : ℕ => aeed (localDesign m) (pairedAssignment (m^8)) (localOutcome m) 1 0-
      localDirectEffect m) atTop (𝓝 0) := by
    have hh : Tendsto (fun m : ℕ => 1/(m:ℝ)^2) atTop (𝓝 0) := by
      simpa [one_div,inv_pow] using hinv.pow 2
    apply hh.congr'
    filter_upwards [hdelta] with m hm
    exact hm.symm
  have hvarEq : ∀ᶠ (m : ℕ) in atTop,
      (m^8*2:ℝ)*variance (localDesign m) (localEstimator m)=localV m/2 := by
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hm0 : (m:ℝ) ≠ 0 := by
      have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
      linarith
    rw [(local_finite_moments m hm).2.2.2]
    field_simp
    ring
  have hvar : Tendsto (fun m : ℕ => (m^8*2:ℝ)*variance (localDesign m) (localEstimator m)) atTop (𝓝 4) := by
    have hh : Tendsto (fun m : ℕ => localV m/2) atTop (𝓝 (4:ℝ)) := by convert hV.div_const 2 using 1 <;> norm_num
    apply hh.congr'
    filter_upwards [hvarEq] with m hm
    exact hm.symm
  have hpow : Tendsto (fun m : ℕ => (m:ℝ)^4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (4:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hlow : Tendsto (fun m : ℕ => (m:ℝ)^4/5) atTop atTop := by
    simpa only [div_eq_mul_inv] using hpow.atTop_mul_const (by norm_num : (0:ℝ) < (5:ℝ)⁻¹)
  have hstd : Tendsto (fun m : ℕ => ((aeed (localDesign m) (pairedAssignment (m^8)) (localOutcome m) 1 0-
      localDirectEffect m)/localStandardError m)^2) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hlow
    filter_upwards [eventually_ge_atTop 2,hdelta] with m hm hδ
    rw [hδ]
    exact (local_standardized_gap m hm).2
  have hboundlim : Tendsto (fun m : ℕ => 20/(m:ℝ)^4) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,inv_pow] using (hinv.pow 4).const_mul 20
  have hcover : Tendsto (fun m : ℕ => probability (localDesign m)
      (fun z => |localEstimator m z-localDirectEffect m| ≤ 5*localStandardError m)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hboundlim
      (Filter.Eventually.of_forall (fun m => probability_nonneg (localDesign m) _))
    filter_upwards [eventually_ge_atTop 5] with m hm
    have hh := (local_interval_bounds m (by omega)).2 hm
    simpa only [local_ade_zero,sub_zero] using (hh.1.trans_eq hh.2.1).trans hh.2.2
  exact ⟨hgap,hvar,hstd,hcover⟩


/-- Permuting the population indices preserves the treated count. This is
the exchangeability step for the SRS/complete-randomization law in T17. -/
theorem permuted_treated_count {N : ℕ} (s : Equiv.Perm (Fin N)) (z : Fin N → Fin 2) :
    (Finset.univ.filter (fun i => z (s i)=1)).card = (Finset.univ.filter (fun i => z i=1)).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Equiv.sum_comp s (fun i => if z i=1 then (1:ℕ) else 0)

/-- T17: uniform fixed-count binary randomization has marginal probabilities
n/N and (N−n)/N, derived by exchangeability and the exact exposed count. -/
theorem complete_randomization_marginals {N : ℕ} (D : Design (Fin N → Fin 2))
    (n : ℕ) (hn : 0 < n) (hn' : n < N) (hdesign : CompleteRandomization D n) :
    ∀ i, pi D (fun i z => (z i).val) i 1=(n:ℝ)/N ∧
      pi D (fun i z => (z i).val) i 0=((N-n:ℕ):ℝ)/N := by
  classical
  have hN : 0 < N := lt_trans hn hn'
  have hN0 : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hequal (i j : Fin N) : pi D (fun i z => (z i).val) i 1=pi D (fun i z => (z i).val) j 1 := by
    let s := Equiv.swap i j
    let e : (Fin N → Fin 2) ≃ (Fin N → Fin 2) :=
      { toFun := fun z k => z (s k), invFun := fun z k => z (s k),
        left_inv := by intro z; funext k; simp [s],
        right_inv := by intro z; funext k; simp [s] }
    have hmass (z : Fin N → Fin 2) : D.p (e z)=D.p z := by
      rw [hdesign (e z),hdesign z]
      have hc := permuted_treated_count s z
      change (if (Finset.univ.filter (fun k => z (s k)=1)).card=n then _ else _) = _
      rw [hc]
    have hown (z : Fin N → Fin 2) : e z i=z j := by simp [e,s]
    unfold pi probability
    rw [tsum_fintype,tsum_fintype,← e.sum_comp]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [hown,hmass]
  let X := fun z : Fin N → Fin 2 => ((Finset.univ.filter (fun i => z i=1)).card:ℝ)
  have hX (z : Fin N → Fin 2) : X z=∑ i, if ((z i).val:ℝ)=1 then (1:ℝ) else 0 := by
    simp only [X,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    generalize hz : z i=b
    fin_cases b <;> norm_num
  have hXsupport (z : Fin N → Fin 2) (hz : Support D z) : X z=(n:ℝ) := by
    have hc : (Finset.univ.filter (fun i => z i=1)).card=n := by
      by_contra hc
      have hp0 : D.p z=0 := by simp only [hdesign z,hc,ite_false]
      exact (ne_of_gt hz) hp0
    exact congrArg (fun k : ℕ => (k:ℝ)) hc
  have hsum : (∑ i, pi D (fun i z => (z i).val) i 1)=(n:ℝ) := by
    have he : expectation D X=(n:ℝ) :=
      (expectation_support_congr D X (fun _ => (n:ℝ)) hXsupport).trans (expectation_const D _)
    rw [show X=(fun z => ∑ i, if ((z i).val:ℝ)=1 then (1:ℝ) else 0) from funext hX,
      expectation_sum D _ (fun _ => Summable.of_finite)] at he
    simpa only [expectation_event,one_mul,pi] using he
  intro i
  have hprod : (N:ℝ)*pi D (fun i z => (z i).val) i 1=(n:ℝ) := by
    calc
      _ = ∑ j : Fin N, pi D (fun i z => (z i).val) i 1 := by simp
      _ = ∑ j : Fin N, pi D (fun i z => (z i).val) j 1 :=
        Finset.sum_congr rfl (fun j hj => hequal i j)
      _ = _ := hsum
  have ht : pi D (fun i z => (z i).val) i 1=(n:ℝ)/N := by
    apply (eq_div_iff hN0).2
    simpa only [mul_comm] using hprod
  refine ⟨ht, ?_⟩
  have hcomp : pi D (fun i z => (z i).val) i 0=1-pi D (fun i z => (z i).val) i 1 := by
    unfold pi
    have hf : (fun z : Fin N → Fin 2 => ((z i).val:ℝ)=0) =
        (fun z => ¬((z i).val:ℝ)=1) := by
      funext z
      generalize hz : z i=b
      fin_cases b <;> norm_num
    rw [hf,probability_complement]
  rw [hcomp,ht,Nat.cast_sub hn'.le]
  field_simp

/-- T5: two pushforward laws of the same nonnegative finite
coupling have total variation at most its mass where the two values differ.
The weights need not sum to one for this finite inequality. -/
theorem coupling_total_variation {B A : Type} [Fintype B] [Fintype A]
    (C : B → ℝ) (hC : ∀ b, 0 ≤ C b) (F G : B → A) :
    totalVariation (fun x => ∑ b, if F b=x then C b else 0)
      (fun x => ∑ b, if G b=x then C b else 0) ≤
      ∑ b, if F b≠G b then C b else 0 := by
  classical
  have inner (b : B) :
      (∑ x, |(if F b=x then C b else 0)-(if G b=x then C b else 0)|) ≤
      2*(if F b≠G b then C b else 0) := by
    by_cases h : F b=G b
    · simp [h]
    · simp only [h, ne_eq, not_false_eq_true, ite_true]
      calc
        _ ≤ ∑ x, (|(if F b=x then C b else 0)|+|(if G b=x then C b else 0)|) :=
          Finset.sum_le_sum (fun x hx => by simpa using abs_sub_le (if F b=x then C b else 0) 0 (if G b=x then C b else 0))
        _ = 2*C b := by
          simp only [apply_ite abs,abs_zero,abs_of_nonneg (hC b),Finset.sum_add_distrib]
          simp [eq_comm]
          ring
  unfold totalVariation
  calc
    (1/2:ℝ)*∑ x, |(∑ b, if F b=x then C b else 0)-(∑ b, if G b=x then C b else 0)| ≤
        (1/2:ℝ)*∑ x, ∑ b, |(if F b=x then C b else 0)-(if G b=x then C b else 0)| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro x hx
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = (1/2:ℝ)*∑ b, ∑ x, |(if F b=x then C b else 0)-(if G b=x then C b else 0)| := by
      rw [Finset.sum_comm]
    _ ≤ (1/2:ℝ)*∑ b, 2*(if F b≠G b then C b else 0) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b hb => inner b)) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Index-swap bijection on binary assignment vectors; the coupling in T5
turns an untreated distinguished unit into a treated one by this swap. -/
def swapAssignment {N : ℕ} (i j : Fin N) :
    (Fin N → Fin 2) ≃ (Fin N → Fin 2) where
  toFun := fun z k => z (Equiv.swap i j k)
  invFun := fun z k => z (Equiv.swap i j k)
  left_inv := by intro z; funext k; simp
  right_inv := by intro z; funext k; simp

/-- T5's index swap preserves the actual uniform fixed-count law. -/
theorem complete_randomization_swap_mass {N : ℕ} (D : Design (Fin N → Fin 2))
    (n : ℕ) (hd : CompleteRandomization D n) (i j : Fin N) (z : Fin N → Fin 2) :
    D.p (swapAssignment i j z)=D.p z := by
  rw [hd (swapAssignment i j z),hd z]
  have hc := permuted_treated_count (Equiv.swap i j) z
  change (if (Finset.univ.filter (fun k => z (Equiv.swap i j k)=1)).card=n then _ else _) = _
  rw [hc]

/-- In T5's fixed-count law, the treated and untreated coordinate counts,
weighted by the assignment's atom mass, equal that mass times n and N−n,
respectively. The identities also hold for zero-weight assignments. -/
theorem complete_randomization_weighted_counts {N : ℕ} (D : Design (Fin N → Fin 2))
    (n : ℕ) (hn : n ≤ N) (hd : CompleteRandomization D n) (z : Fin N → Fin 2) :
    (∑ j, if z j=1 then D.p z else 0)=D.p z*n ∧
    (∑ j, if z j=0 then D.p z else 0)=D.p z*((N-n:ℕ):ℝ) := by
  classical
  have hc : (Finset.univ.filter (fun j : Fin N => z j=1)).card+
      (Finset.univ.filter (fun j : Fin N => z j=0)).card=N := by
    have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j : Fin N => z j=1)
    have he : (fun j : Fin N => ¬z j=1)=(fun j => z j=0) := by
      funext j
      generalize hz : z j=b
      fin_cases b <;> norm_num
    simpa only [he, Finset.card_univ,Fintype.card_fin] using hh
  by_cases ht : (Finset.univ.filter (fun j : Fin N => z j=1)).card=n
  · have hu : (Finset.univ.filter (fun j : Fin N => z j=0)).card=N-n := by omega
    constructor <;> simp [← Finset.sum_filter,ht,hu,mul_comm]
  · have hp0 : D.p z=0 := by simp [hd z,ht]
    simp [hp0]

/-- The own-bit conditioning event and its real-valued exposure event are
identical; T5 retains the paper's real coordinate notation. -/
theorem binary_pi_probability {N : ℕ} (D : Design (Fin N → Fin 2))
    (i : Fin N) (e : Fin 2) :
    pi D (fun i z => (z i).val) i e.val=probability D (fun z => z i=e) := by
  unfold pi probability
  apply tsum_congr
  intro z
  have he : ((z i).val:ℝ)=(e.val:ℝ) ↔ z i=e := by
    constructor
    · intro h; apply Fin.ext; exact_mod_cast h
    · intro h; rw [h]
  by_cases hz : z i=e <;> simp [he,hz]

/-- The mass of untreated-own/treated-other assignments, summed over other
indices, is n times the untreated-own probability; the swap-coupling row sum. -/
theorem complete_randomization_pair_sum {N : ℕ} (D : Design (Fin N → Fin 2))
    (n : ℕ) (hn : n ≤ N) (hd : CompleteRandomization D n) (i : Fin N) :
    (∑ j, probability D (fun z => z i=0 ∧ z j=1))=
      n*pi D (fun i z => (z i).val) i 0 := by
  classical
  have hp := binary_pi_probability D i 0
  simp only [Fin.val_zero,Nat.cast_zero] at hp
  rw [hp]
  unfold probability
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z, if z i=0 then D.p z*n else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hi : z i=0
      · simp only [hi,true_and]
        exact (complete_randomization_weighted_counts D n hn hd z).1
      · simp [hi]
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z hz; split_ifs <;> ring

/-- Exchangeability gives the joint probability that unit i is untreated and a
specified other unit j is treated: n π_i(0)/(N−1). -/
theorem complete_randomization_pair_mass {N : ℕ} (D : Design (Fin N → Fin 2))
    (n : ℕ) (hn : 0 < n) (hn' : n < N) (hd : CompleteRandomization D n)
    (i j : Fin N) (hji : j≠i) :
    probability D (fun z => z i=0 ∧ z j=1)=
      (n*pi D (fun i z => (z i).val) i 0)/((N-1:ℕ):ℝ) := by
  classical
  let P := fun k => probability D (fun z => z i=0 ∧ z k=1)
  have hi : P i=0 := by
    unfold P probability
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro z hz
    by_cases h : z i=0 <;> simp [h]
  have hequal (k : Fin N) (hki : k≠i) : P k=P j := by
    let e := swapAssignment j k
    have hown (z : Fin N → Fin 2) : e z i=z i := by
      simp [e,swapAssignment,Equiv.swap_apply_def,hji,hki,Ne.symm hji,Ne.symm hki]
    have hother (z : Fin N → Fin 2) : e z k=z j := by simp [e,swapAssignment]
    unfold P probability
    rw [tsum_fintype,tsum_fintype,← e.sum_comp]
    apply Finset.sum_congr rfl
    intro z hz
    have hmass : D.p (e z)=D.p z := complete_randomization_swap_mass D n hd j k z
    by_cases hi0 : z i=0 <;> by_cases hj1 : z j=1 <;> simp [hown,hother,hmass,hi0,hj1]
  have hs : (∑ k∈Finset.univ.erase i, P k)=n*pi D (fun i z => (z i).val) i 0 := by
    have hh := complete_randomization_pair_sum D n hn'.le hd i
    change (∑ k, P k)=_ at hh
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),hi,add_zero] at hh
    exact hh
  have he : ((N-1:ℕ):ℝ)*P j=n*pi D (fun i z => (z i).val) i 0 := by
    calc
      _ = ∑ k∈Finset.univ.erase i, P j := by simp
      _ = ∑ k∈Finset.univ.erase i, P k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hequal k (Finset.mem_erase.mp hk).1).symm
      _ = _ := hs
  have hden : ((N-1:ℕ):ℝ)≠0 := by
    have hN : 1 < N := lt_of_le_of_lt hn hn'
    exact_mod_cast (Nat.sub_pos_of_lt hN).ne'
  apply (eq_div_iff hden).2
  simpa only [P,mul_comm] using he

/-- T5's swap coupling has exactly the conditional neighborhood law given
own assignment zero as its first marginal, and the law given one as its
second marginal. All sums are over the full feasible binary vector space. -/
theorem complete_randomization_coupling_marginals {N : ℕ} (D : Design (Fin N → Fin 2))
    (n : ℕ) (hn : 0 < n) (hn' : n < N) (hd : CompleteRandomization D n)
    (i : Fin N) (H : Finset (Fin N)) (x : NeighborConfig H) :
    let p0 := pi D (fun i z => (z i).val) i 0
    let C := fun b : (Fin N → Fin 2) × Fin N =>
      if b.1 i=0 ∧ b.1 b.2=1 then D.p b.1/(n*p0) else 0
    let R := fun z : Fin N → Fin 2 => (fun j : H => z j.val)
    (∑ b, if R b.1=x then C b else 0)=conditionalNeighborLaw D i H 0 x ∧
    (∑ b, if R (swapAssignment i b.2 b.1)=x then C b else 0)=
      conditionalNeighborLaw D i H 1 x := by
  classical
  dsimp only
  let R := fun z : Fin N → Fin 2 => (fun j : H => z j.val)
  let p0 := pi D (fun i z => (z i).val) i 0
  let p1 := pi D (fun i z => (z i).val) i 1
  let den : ℝ := n*p0
  have hp := complete_randomization_marginals D n hn hn' hd i
  have hN : (0:ℝ)<N := by exact_mod_cast (lt_trans hn hn')
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hnR' : (n:ℝ)<N := by exact_mod_cast hn'
  have hp0 : 0<p0 := by dsimp [p0]; rw [hp.2,Nat.cast_sub hn'.le]; positivity
  have hp1 : 0<p1 := by dsimp [p1]; rw [hp.1]; positivity
  have hden : 0<den := mul_pos hnR hp0
  have hcoef0 : (n:ℝ)/den=1/p0 := by dsimp [den]; field_simp
  have hcoef1 : ((N-n:ℕ):ℝ)/den=1/p1 := by
    dsimp [den,p0,p1]
    rw [hp.1,hp.2,Nat.cast_sub hn'.le]
    have hs0 : (N:ℝ)-(n:ℝ)≠0 := (sub_pos.mpr hnR').ne'
    field_simp [hN.ne',hnR.ne',hs0] <;> ring
  have hR (z : Fin N → Fin 2) : R z=x ↔ ∀ j : H, z j.val=x j := by
    exact funext_iff
  have hcond (e : Fin 2) : conditionalNeighborLaw D i H e x =
      (∑ z, if z i=e ∧ R z=x then D.p z else 0)/
        pi D (fun i z => (z i).val) i e.val := by
    unfold conditionalNeighborLaw probability
    simp only [tsum_fintype,← hR]
  constructor
  · change (∑ b : (Fin N → Fin 2) × Fin N,
      if R b.1=x then (if b.1 i=0 ∧ b.1 b.2=1 then D.p b.1/den else 0) else 0)=_
    rw [Fintype.sum_prod_type,hcond 0]
    calc
      _ = ∑ z, if z i=0 ∧ R z=x then (D.p z*n)/den else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hi : z i=0 <;> by_cases hr : R z=x
        · simp only [hi,hr,ite_true,true_and]
          calc
            _ = (∑ j, if z j=1 then D.p z else 0)/den := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> simp
            _ = _ := by rw [(complete_randomization_weighted_counts D n hn'.le hd z).1]
        · simp [hr]
        · simp [hi,hr]
        · simp [hr]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hz' : z i=0 ∧ R z=x
        · simp only [hz'.1,hz'.2,true_and,ite_true]
          have he : D.p z*n/den=D.p z/p0 := by rw [mul_div_assoc,hcoef0,mul_one_div]
          simpa only [p0,p1,Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one] using he
        · simp [hz']
  · change (∑ b : (Fin N → Fin 2) × Fin N,
      if R (swapAssignment i b.2 b.1)=x then
        (if b.1 i=0 ∧ b.1 b.2=1 then D.p b.1/den else 0) else 0)=_
    rw [Fintype.sum_prod_type,Finset.sum_comm,hcond 1]
    have hswap (j : Fin N) :
        (∑ z, if R (swapAssignment i j z)=x then
          (if z i=0 ∧ z j=1 then D.p z/den else 0) else 0)=
        ∑ z, if R z=x then (if z j=0 ∧ z i=1 then D.p z/den else 0) else 0 := by
      rw [← (swapAssignment i j).sum_comp]
      apply Finset.sum_congr rfl
      intro z hz
      have hh : swapAssignment i j (swapAssignment i j z)=z := by
        funext k; simp [swapAssignment]
      rw [hh,complete_randomization_swap_mass D n hd]
      simp [swapAssignment]
    simp_rw [hswap]
    rw [Finset.sum_comm]
    calc
      _ = ∑ z, if z i=1 ∧ R z=x then (D.p z*((N-n:ℕ):ℝ))/den else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hi : z i=1 <;> by_cases hr : R z=x
        · simp only [hi,hr,ite_true,and_true,true_and]
          calc
            _ = (∑ j, if z j=0 then D.p z else 0)/den := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> simp
            _ = _ := by rw [(complete_randomization_weighted_counts D n hn'.le hd z).2]
        · simp [hr]
        · simp [hi,hr]
        · simp [hr]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hz' : z i=1 ∧ R z=x
        · simp only [hz'.1,hz'.2,true_and,ite_true]
          have he : D.p z*((N-n:ℕ):ℝ)/den=D.p z/p1 := by rw [mul_div_assoc,hcoef1,mul_one_div]
          simpa only [p0,p1,Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one] using he
        · simp [hz']


/-- T5: complete randomization bounds the TV distance of the
two neighborhood laws by the number of other units in H_i divided by N−1. -/
theorem complete_randomization_neighbor_tv {N : ℕ} (D : Design (Fin N → Fin 2))
    (n : ℕ) (hn : 0 < n) (hn' : n < N) (hdesign : CompleteRandomization D n)
    (i : Fin N) (H : Finset (Fin N)) (hH : i ∉ H) :
    totalVariation (conditionalNeighborLaw D i H 1) (conditionalNeighborLaw D i H 0) ≤
      (H.card : ℝ)/((N-1 : ℕ) : ℝ) := by
  classical
  let R := fun z : Fin N → Fin 2 => (fun j : H => z j.val)
  let p0 := pi D (fun i z => (z i).val) i 0
  let den : ℝ := n*p0
  let C := fun b : (Fin N → Fin 2) × Fin N =>
    if b.1 i=0 ∧ b.1 b.2=1 then D.p b.1/den else 0
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hN : (0:ℝ)<N := by exact_mod_cast (lt_trans hn hn')
  have hNp : (n:ℝ)<N := by exact_mod_cast hn'
  have hp0 : 0<p0 := by
    dsimp [p0]
    rw [(complete_randomization_marginals D n hn hn' hdesign i).2,Nat.cast_sub hn'.le]
    positivity
  have hden : 0<den := mul_pos hnR hp0
  have hC (b : (Fin N → Fin 2) × Fin N) : 0≤C b := by
    dsimp [C]
    split_ifs
    · exact div_nonneg (D.nonneg _) hden.le
    · rfl
  have hM : ((N-1:ℕ):ℝ)≠0 := by
    have hN' : 1<N := lt_of_le_of_lt hn hn'
    exact_mod_cast (Nat.sub_pos_of_lt hN').ne'
  have hmargin := complete_randomization_coupling_marginals D n hn hn' hdesign i H
  have hm0 : (fun x => ∑ b, if R b.1=x then C b else 0)=conditionalNeighborLaw D i H 0 :=
    funext (fun x => (hmargin x).1)
  have hm1 : (fun x => ∑ b, if R (swapAssignment i b.2 b.1)=x then C b else 0)=
      conditionalNeighborLaw D i H 1 := funext (fun x => (hmargin x).2)
  have htv := coupling_total_variation C hC
    (fun b => R (swapAssignment i b.2 b.1)) (fun b => R b.1)
  have htv' : totalVariation (conditionalNeighborLaw D i H 1) (conditionalNeighborLaw D i H 0) ≤
      ∑ b, if R (swapAssignment i b.2 b.1)≠R b.1 then C b else 0 := by
    convert htv using 1
    · unfold totalVariation
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      apply congrArg₂ (· - ·)
      · calc
          _ = ∑ b, if R (swapAssignment i b.2 b.1)=x then C b else 0 := congrFun hm1.symm x
          _ = _ := by
            apply Finset.sum_congr rfl
            intro b hb
            by_cases h : R (swapAssignment i b.2 b.1)=x <;> simp [h]
      · calc
          _ = ∑ b, if R b.1=x then C b else 0 := congrFun hm0.symm x
          _ = _ := by
            apply Finset.sum_congr rfl
            intro b hb
            by_cases h : R b.1=x <;> simp [h]
    · apply Finset.sum_congr rfl
      intro b hb
      by_cases h : R (swapAssignment i b.2 b.1)=R b.1 <;> simp [h]
  have hsame (b : (Fin N → Fin 2) × Fin N) (hj : b.2∉H) :
      R (swapAssignment i b.2 b.1)=R b.1 := by
    funext k
    have hki : k.val≠i := by intro he; apply hH; rw [← he]; exact k.property
    have hkj : k.val≠b.2 := by intro he; apply hj; rw [← he]; exact k.property
    simp [R,swapAssignment,Equiv.swap_apply_def,hki,hkj]
  have hbound : (∑ b, if R (swapAssignment i b.2 b.1)≠R b.1 then C b else 0) ≤
      ∑ b, if b.2∈H then C b else 0 := by
    apply Finset.sum_le_sum
    intro b hb
    by_cases hj : b.2∈H
    · simp only [hj,ite_true]
      split_ifs
      · exact le_rfl
      · exact hC b
    · simp [hj,hsame b hj]
  have hratio (j : Fin N) (hj : j∈H) :
      probability D (fun z => z i=0 ∧ z j=1)/den=1/((N-1:ℕ):ℝ) := by
    have hji : j≠i := by intro he; exact hH (he ▸ hj)
    rw [complete_randomization_pair_mass D n hn hn' hdesign i j hji]
    change ((n*p0)/((N-1:ℕ):ℝ))/den=1/((N-1:ℕ):ℝ)
    have he : (n:ℝ)*p0=den := rfl
    rw [he]
    field_simp [hden.ne',hM]
  calc
    _ ≤ ∑ b, if R (swapAssignment i b.2 b.1)≠R b.1 then C b else 0 := htv'
    _ ≤ ∑ b, if b.2∈H then C b else 0 := hbound
    _ = ∑ j∈H, probability D (fun z => z i=0 ∧ z j=1)/den := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      simp [C,Finset.sum_ite_irrel,← Finset.sum_div,probability,tsum_fintype,← Finset.sum_filter]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : z i=0 ∧ z j=1 <;> simp [h]
    _ = ∑ j∈H, (1:ℝ)/((N-1:ℕ):ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hratio j hj
    _ = _ := by simp; ring


/-- Finite T5 range R=max f−min f is nonnegative on a nonempty
configuration space. -/
theorem functionRange_nonneg {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) :
    0≤functionRange f := by
  unfold functionRange
  exact sub_nonneg.mpr (csInf_le_csSup (Set.range_nonempty f)
    (Set.finite_range f).bddBelow (Set.finite_range f).bddAbove)

/-- Binary own-assignment conditioning in T5 gives the same neighborhood
law with bit labels and with their injective real-coordinate labels. -/
theorem binary_neighbor_laws_agree {N : ℕ} (D : Design (Fin N → Fin 2))
    (i : Fin N) (H : Finset (Fin N)) (e : Fin 2) :
    conditionalGeneralNeighborLaw D i H e=conditionalNeighborLaw D i H e := by
  funext x
  unfold conditionalGeneralNeighborLaw conditionalNeighborLaw
  rw [binary_pi_probability]

/-- T5: the unconditional neighborhood distribution is the
mixture of the two positive own-assignment conditional distributions. -/
theorem binary_neighbor_mixture {N : ℕ} (D : Design (Fin N → Fin 2))
    (i : Fin N) (H : Finset (Fin N))
    (hp0 : 0<probability D (fun z => z i=0))
    (hp1 : 0<probability D (fun z => z i=1)) :
    generalNeighborLaw D H = (fun x =>
      probability D (fun z => z i=1)*conditionalGeneralNeighborLaw D i H 1 x+
      probability D (fun z => z i=0)*conditionalGeneralNeighborLaw D i H 0 x) := by
  classical
  funext x
  unfold generalNeighborLaw conditionalGeneralNeighborLaw
  rw [← mul_div_assoc,mul_div_cancel_left₀ _ hp1.ne',← mul_div_assoc,mul_div_cancel_left₀ _ hp0.ne']
  unfold probability
  rw [tsum_fintype,tsum_fintype,tsum_fintype,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  generalize he : z i=b
  fin_cases b <;> by_cases hx : ∀ j : H, z j.val=x j <;> simp [hx,he]

/-- The two conditional-to-unconditional TV distances of a binary
mixture sum to the conditional-to-conditional TV distance. This is the
weighted-mixture calculation used in T5. -/
theorem tv_binary_mixture {A : Type} [Fintype A] (Q1 Q0 : A → ℝ)
    (p1 p0 : ℝ) (hp1 : 0≤p1) (hp0 : 0≤p0) (htotal : p1+p0=1) :
    totalVariation Q1 (fun x => p1*Q1 x+p0*Q0 x)+
      totalVariation Q0 (fun x => p1*Q1 x+p0*Q0 x)=totalVariation Q1 Q0 := by
  have h1 (x : A) : Q1 x-(p1*Q1 x+p0*Q0 x)=p0*(Q1 x-Q0 x) := by
    have he : p1=1-p0 := by linarith
    rw [he]; ring
  have h0 (x : A) : Q0 x-(p1*Q1 x+p0*Q0 x)=p1*(Q0 x-Q1 x) := by
    have he : p0=1-p1 := by linarith
    rw [he]; ring
  unfold totalVariation
  simp_rw [h1,h0,abs_mul,abs_of_nonneg hp0,abs_of_nonneg hp1,abs_sub_comm]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  rw [show p0=1-p1 by linarith]
  ring

/-- T5: in uniform complete randomization, if all local
response ranges are at most R and each other-unit neighborhood has at most
k units, the actual AEED/raw-hybrid ADE bias is at most R k/(N−1).
No stability assumption on outcomes is imposed. -/
theorem complete_randomization_local_bias_bound {N : ℕ} (D : Design (Fin N → Fin 2))
    (y : OutcomeSchedule (Fin N → Fin 2) N) (n k : ℕ) (R : ℝ)
    (hn : 0<n) (hn' : n<N) (hd : CompleteRandomization D n)
    (H : Fin N → Finset (Fin N)) (hH : ∀ i, i∉H i)
    (hk : ∀ i, (H i).card≤k)
    (f : ∀ i, Fin 2 → NeighborConfig (H i) → ℝ)
    (hr : ∀ i e, functionRange (f i e)≤R)
    (hy : ∀ i e z, y i (Function.update z i e)=f i e (fun j => z j.val)) :
    ((N:ℝ)⁻¹*∑ i,
      (functionRange (f i 1)*totalVariation (conditionalGeneralNeighborLaw D i (H i) 1) (generalNeighborLaw D (H i))+
       functionRange (f i 0)*totalVariation (conditionalGeneralNeighborLaw D i (H i) 0) (generalNeighborLaw D (H i)))) ≤
      R*k/((N-1:ℕ):ℝ) ∧
    |aeed D (fun i z => (z i).val) y 1 0 -
      (N:ℝ)⁻¹*∑ i, expectation D (fun z =>
        y i (Function.update z i 1)-y i (Function.update z i 0))| ≤
      R*k/((N-1:ℕ):ℝ) := by
  classical
  have hN : 0<N := lt_trans hn hn'
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hM : (0:ℝ)<((N-1:ℕ):ℝ) := by
    have hN' : 1<N := lt_of_le_of_lt hn hn'
    exact_mod_cast (Nat.sub_pos_of_lt hN')
  have hp (i : Fin N) : 0<pi D (fun i z => (z i).val) i 1 ∧
      0<pi D (fun i z => (z i).val) i 0 := by
    rw [(complete_randomization_marginals D n hn hn' hd i).1,
      (complete_randomization_marginals D n hn hn' hd i).2]
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    have hNn : (0:ℝ)<((N-n:ℕ):ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hn')
    have hNR : (0:ℝ)<N := by exact_mod_cast hN
    exact ⟨div_pos hnR hNR,div_pos hNn hNR⟩
  have hR : 0≤R := (functionRange_nonneg (f ⟨0,hN⟩ 0)).trans (hr _ _)
  have label_inj : Function.Injective (fun b : Fin 2 => (b.val:ℝ)) := by
    intro a b he
    change (a.val:ℝ)=(b.val:ℝ) at he
    apply Fin.ext
    exact_mod_cast he
  have hb := local_total_variation_bias_bound (fun b : Fin 2 => (b.val:ℝ)) label_inj
    D y H f 1 0 hN hH (by simpa using hp) (fun i e he z => hy i e z)
  simp only [Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one] at hb
  have hunit (i : Fin N) :
      functionRange (f i 1)*totalVariation (conditionalGeneralNeighborLaw D i (H i) 1) (generalNeighborLaw D (H i))+
      functionRange (f i 0)*totalVariation (conditionalGeneralNeighborLaw D i (H i) 0) (generalNeighborLaw D (H i)) ≤
      R*k/((N-1:ℕ):ℝ) := by
    let p1 := probability D (fun z => z i=1)
    let p0 := probability D (fun z => z i=0)
    have hp1 : 0<p1 := by
      dsimp [p1]
      rw [← binary_pi_probability D i 1]
      simpa only [Fin.val_one,Nat.cast_one] using (hp i).1
    have hp0 : 0<p0 := by
      dsimp [p0]
      rw [← binary_pi_probability D i 0]
      simpa only [Fin.val_zero,Nat.cast_zero] using (hp i).2
    have htotal : p1+p0=1 := by
      unfold p1 p0 probability
      rw [tsum_fintype,tsum_fintype,← Finset.sum_add_distrib,← D.total,tsum_fintype]
      apply Finset.sum_congr rfl
      intro z hz
      generalize he : z i=b
      fin_cases b <;> simp [he]
    have htv : totalVariation (conditionalGeneralNeighborLaw D i (H i) 1) (generalNeighborLaw D (H i))+
        totalVariation (conditionalGeneralNeighborLaw D i (H i) 0) (generalNeighborLaw D (H i)) ≤
        ((H i).card:ℝ)/((N-1:ℕ):ℝ) := by
      rw [binary_neighbor_mixture D i (H i) hp0 hp1,
        tv_binary_mixture _ _ p1 p0 hp1.le hp0.le htotal,
        binary_neighbor_laws_agree,binary_neighbor_laws_agree]
      exact complete_randomization_neighbor_tv D n hn hn' hd i (H i) (hH i)
    have nonneg (e : Fin 2) : 0≤totalVariation
        (conditionalGeneralNeighborLaw D i (H i) e) (generalNeighborLaw D (H i)) := by
      unfold totalVariation
      positivity
    calc
      _ ≤ R*(totalVariation (conditionalGeneralNeighborLaw D i (H i) 1) (generalNeighborLaw D (H i))+
          totalVariation (conditionalGeneralNeighborLaw D i (H i) 0) (generalNeighborLaw D (H i))) := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (hr i 1) (nonneg 1))
          (mul_le_mul_of_nonneg_right (hr i 0) (nonneg 0))
      _ ≤ R*(((H i).card:ℝ)/((N-1:ℕ):ℝ)) := mul_le_mul_of_nonneg_left htv hR
      _ ≤ R*((k:ℝ)/((N-1:ℕ):ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hR
        exact div_le_div_of_nonneg_right (by exact_mod_cast hk i) hM.le
      _ = _ := by ring
  have hBound : (N:ℝ)⁻¹*∑ i,
      (functionRange (f i 1)*totalVariation (conditionalGeneralNeighborLaw D i (H i) 1) (generalNeighborLaw D (H i))+
       functionRange (f i 0)*totalVariation (conditionalGeneralNeighborLaw D i (H i) 0) (generalNeighborLaw D (H i))) ≤
      R*k/((N-1:ℕ):ℝ) := by
    calc
      _ ≤ (N:ℝ)⁻¹*∑ i : Fin N, R*k/((N-1:ℕ):ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi => hunit i)) (inv_nonneg.mpr (Nat.cast_nonneg N))
      _ = _ := by simp; field_simp
  exact ⟨hBound,hb.trans hBound⟩


/-- T5's pair example for T4: for y_i=1+a Z_partner,
the response range is a, each conditional/unconditional neighbor-law TV
distance is ρ/2, and their range-weighted sum aρ equals the actual AEED.
Both own-assignment hybrid direct effects are exactly zero. Independent
replication of this pair is the already defined T4 population design. -/
theorem correlated_pair_neighbor_bound_attained (a ρ : ℝ) (ha : 0≤a)
    (hρ : 0≤ρ ∧ ρ≤1) :
    let D := correlatedPairDesign ρ hρ
    let Q := fun (e b : Fin 2) => probability D (fun z => z.1=e ∧ z.2=b)/
      probability D (fun z => z.1=e)
    let P := fun b : Fin 2 => probability D (fun z => z.2=b)
    let f := fun b : Fin 2 => 1+a*(b.val:ℝ)
    let y : OutcomeSchedule BinaryPair 2 := fun i z => 1+a*votingOutcome i z
    functionRange f=a ∧ (∀ e, totalVariation (Q e) P=ρ/2) ∧
    (functionRange f*totalVariation (Q 1) P+functionRange f*totalVariation (Q 0) P=a*ρ) ∧
    aeed D pairAssignment y 1 0=a*ρ ∧
    (∀ i z, y i (replacePairOwn i 1 z)-y i (replacePairOwn i 0 z)=0) := by
  classical
  dsimp only
  let D := correlatedPairDesign ρ hρ
  let Q := fun (e b : Fin 2) => probability D (fun z => z.1=e ∧ z.2=b)/
    probability D (fun z => z.1=e)
  let P := fun b : Fin 2 => probability D (fun z => z.2=b)
  let f := fun b : Fin 2 => 1+a*(b.val:ℝ)
  let y : OutcomeSchedule BinaryPair 2 := fun i z => 1+a*votingOutcome i z
  have hrange : Set.range f={1,1+a} := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      fin_cases b <;> norm_num [f]
    · intro hx
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0,by norm_num [f]⟩
      · exact ⟨1,by norm_num [f]⟩
  have hr : functionRange f=a := by
    unfold functionRange
    rw [hrange,csSup_pair,csInf_pair]
    change max 1 (1+a)-min 1 (1+a)=a
    rw [max_eq_right (by linarith),min_eq_left (by linarith)]
    ring
  have hprob0 (e : Fin 2) : probability D (fun z => z.1=e)=1/2 := by
    fin_cases e <;> norm_num [D,probability,correlatedPairDesign,tsum_fintype,
      Fintype.sum_prod_type,Fin.sum_univ_two] <;> ring
  have hP (b : Fin 2) : P b=1/2 := by
    fin_cases b <;> norm_num [P,D,probability,correlatedPairDesign,tsum_fintype,
      Fintype.sum_prod_type,Fin.sum_univ_two] <;> ring
  have hQ (e b : Fin 2) : Q e b=if e=b then (1+ρ)/2 else (1-ρ)/2 := by
    dsimp [Q]
    rw [hprob0]
    fin_cases e <;> fin_cases b <;>
      norm_num [D,probability,correlatedPairDesign,tsum_fintype,
        Fintype.sum_prod_type,Fin.sum_univ_two] <;> ring
  have htv (e : Fin 2) : totalVariation (Q e) P=ρ/2 := by
    unfold totalVariation
    simp_rw [hQ,hP]
    have hplus : (1+ρ)/2-1/2=ρ/2 := by ring
    have hminus : (1-ρ)/2-1/2= -ρ/2 := by ring
    fin_cases e <;> norm_num [Fin.sum_univ_two,hplus,hminus,abs_div,abs_neg,
      abs_of_nonneg hρ.1] <;> ring
  have hpi (i e : Fin 2) : pi D pairAssignment i e.val=1/2 := by
    fin_cases i <;> fin_cases e <;> norm_num [D,pi,probability,pairAssignment,
      correlatedPairDesign,tsum_fintype,Fintype.sum_prod_type,Fin.sum_univ_two] <;> ring
  have hpi1 (i : Fin 2) : pi D pairAssignment i 1=1/2 := by simpa using hpi i 1
  have hpi0 (i : Fin 2) : pi D pairAssignment i 0=1/2 := by simpa using hpi i 0
  refine ⟨hr,htv,?_,?_,?_⟩
  · rw [hr,htv 1,htv 0]; ring
  · change aeed D pairAssignment y 1 0=a*ρ
    rw [aeed_average_eed_algebra]
    unfold eed epo
    simp_rw [hpi1,hpi0]
    norm_num [D,y,expectation,pairAssignment,votingOutcome,correlatedPairDesign,
      tsum_fintype,Fintype.sum_prod_type,Fin.sum_univ_two]
    ring
  · intro i z
    fin_cases i <;> simp [y,votingOutcome,replacePairOwn]


/-- T17's standard-design specialization, retaining the actual uniform
fixed-count law and deriving its marginal probabilities rather than assuming
them. The first component gives the margins, the second the survey conclusion,
and the third the experiment conclusion. -/
theorem complete_randomization_unbiased {N : ℕ} (D : Design (Fin N → Fin 2))
    (y : OutcomeSchedule (Fin N → Fin 2) N) (n : ℕ) (hn : 0 < n) (hn' : n < N)
    (hdesign : CompleteRandomization D n) :
    (∀ i, pi D (fun i z => (z i).val) i 1 = (n : ℝ)/N ∧
      pi D (fun i z => (z i).val) i 0 = ((N-n : ℕ) : ℝ)/N) ∧
    expectation D (sampleMean (fun i z => (z i).val) y 1 n) =
      aepo D (fun i z => (z i).val) y 1 ∧
    expectation D (fun z => sampleMean (fun i z => (z i).val) y 1 n z -
      sampleMean (fun i z => (z i).val) y 0 (N-n) z) =
      aeed D (fun i z => (z i).val) y 1 0 := by
  have hp := complete_randomization_marginals D n hn hn' hdesign
  have hN : 0 < N := lt_trans hn hn'
  exact ⟨hp,sample_mean_unbiased D _ y 1 n hN hn (fun i => (hp i).1),
    difference_in_means_unbiased D _ y n hN hn hn' (fun i => (hp i).1) (fun i => (hp i).2)⟩

/-- T2(e): the paired exposure at unit (k,j) is the original two-person
network exposure j of pair k. -/
theorem paired_network_coordinate (K : ℕ) (k : Fin K) (j : Fin 2) (z : Fin K → BinaryPair) :
    pairedNetworkExposure K (finProdFinEquiv (k,j)) z=networkExposure j (z k) := by
  simp only [pairedNetworkExposure,pairedAssignment,pairedPartnerAssignment,
    Equiv.symm_apply_apply,networkExposure]

/-- T2(e): projecting any feasible full exposure vector onto one pair gives
a member of the original two-person exposure image. -/
theorem paired_network_image_projection (K : ℕ) (r : Fin (K*2) → ℝ)
    (hr : InPairedNetworkImage K r) (k : Fin K) :
    InNetworkImage (r (finProdFinEquiv (k,0)),r (finProdFinEquiv (k,1))) := by
  obtain ⟨z,hz⟩ := hr
  refine ⟨z k, ?_⟩
  apply Prod.ext
  · exact (paired_network_coordinate K k 0 z).symm.trans (hz _)
  · exact (paired_network_coordinate K k 1 z).symm.trans (hz _)

/-- T2(e): both literal raw-coordinate hybrids are feasible exactly when
every coordinate other than the overwritten own coordinate is binary. -/
theorem binary_hybrid_domain {K : ℕ} (r : Fin (K*2) → ℝ) (i : Fin (K*2)) :
    (InPairedBinaryDomain K (Function.update r i 1) ∧
      InPairedBinaryDomain K (Function.update r i 0)) ↔
      ∀ j, j ≠ i → r j=0 ∨ r j=1 := by
  classical
  constructor
  · intro h j hj
    simpa only [Function.update_of_ne hj] using h.1 j
  · intro h
    constructor <;> intro j <;> by_cases hj : j=i
    · subst j; simp [Function.update_self]
    · simpa only [Function.update_of_ne hj] using h j hj
    · subst j; simp [Function.update_self]
    · simpa only [Function.update_of_ne hj] using h j hj

/-- T2(e): both exposures of an unmodified pair are binary iff neither
member was assigned treatment. -/
theorem network_pair_binary (w : BinaryPair) :
    (∀ j : Fin 2, networkExposure j w=0 ∨ networkExposure j w=1) ↔ w=(0,0) := by
  rcases w with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;>
    norm_num [networkExposure,pairAssignment,votingOutcome,Fin.forall_fin_two]

/-- T2(e): the other member's exposure is binary iff the overwritten own
raw assignment was zero. The unmodified own exposure is not being evaluated. -/
theorem network_partner_binary (j : Fin 2) (w : BinaryPair) :
    (∀ l : Fin 2, l ≠ j → networkExposure l w=0 ∨ networkExposure l w=1) ↔
      pairAssignment j w=0 := by
  rcases w with ⟨x,y⟩
  fin_cases j <;> fin_cases x <;> fin_cases y <;>
    norm_num [networkExposure,pairAssignment,votingOutcome,Fin.forall_fin_two]

/-- T2(e): the full raw-domain event is rectangular across pairs. The
selected pair requires own bit zero; all other pairs must be (0,0). -/
theorem paired_raw_domain_event (K : ℕ) (k₀ : Fin K) (j₀ : Fin 2) (z : Fin K → BinaryPair) :
    (InPairedBinaryDomain K (Function.update (fun i => pairedNetworkExposure K i z) (finProdFinEquiv (k₀,j₀)) 1) ∧
     InPairedBinaryDomain K (Function.update (fun i => pairedNetworkExposure K i z) (finProdFinEquiv (k₀,j₀)) 0)) ↔
      ∀ k, if k=k₀ then pairAssignment j₀ (z k)=0 else z k=(0,0) := by
  classical
  rw [binary_hybrid_domain]
  have hall : (∀ i : Fin (K*2), i ≠ finProdFinEquiv (k₀,j₀) →
      pairedNetworkExposure K i z=0 ∨ pairedNetworkExposure K i z=1) ↔
      ∀ k : Fin K, ∀ j : Fin 2, (k,j) ≠ (k₀,j₀) →
        networkExposure j (z k)=0 ∨ networkExposure j (z k)=1 := by
    constructor
    · intro h k j hj
      have hh := h (finProdFinEquiv (k,j)) (fun he => hj (finProdFinEquiv.injective he))
      simpa only [paired_network_coordinate] using hh
    · intro h i hi
      let k := (finProdFinEquiv.symm i).1
      let j := (finProdFinEquiv.symm i).2
      have he : finProdFinEquiv (k,j)=i := finProdFinEquiv.apply_symm_apply i
      have hne : (k,j) ≠ (k₀,j₀) := fun hh => hi (he.symm.trans (congrArg finProdFinEquiv hh))
      have hh := h k j hne
      simpa only [← he,paired_network_coordinate] using hh
  rw [hall]
  apply forall_congr'
  intro k
  by_cases hk : k=k₀
  · subst k
    simpa only [ite_true,Prod.mk.injEq,true_and,ne_eq] using network_partner_binary j₀ (z k₀)
  · have hne (j : Fin 2) : (k,j) ≠ (k₀,j₀) := fun hh => hk (congrArg Prod.fst hh)
    simp only [hk,ite_false]
    constructor
    · intro h
      exact (network_pair_binary (z k)).1 (fun j => h j (hne j))
    · intro h j hj
      exact (network_pair_binary (z k)).2 h j

/-- T2(e): the same positivity, SUTVA and domain defect at every even N=2K
for independent copies of the adjacent pair; raw outcomes remain own assignment. -/
theorem network_domain_all_even (K : ℕ) (_hK : 0 < K) :
    let D := productDesign K (fun _ => uniformDesign BinaryPair)
    (∀ i : Fin (K*2), ∀ e : Fin 4, pi D (pairedNetworkExposure K) i e.val = 1/4) ∧
    (∀ i : Fin (K*2), epo D (pairedNetworkExposure K) (pairedAssignment K) i 1 = 1 ∧
      epo D (pairedNetworkExposure K) (pairedAssignment K) i 0 = 0) ∧
    aeed D (pairedNetworkExposure K) (pairedAssignment K) 1 0 = 1 ∧
    SUTVA (pairedNetworkExposure K) (pairedAssignment K) ∧
    (∀ i z, ¬(InPairedNetworkImage K (Function.update (fun j => pairedNetworkExposure K j z) i 1) ∧
      InPairedNetworkImage K (Function.update (fun j => pairedNetworkExposure K j z) i 0))) ∧
    (∀ i, probability D (fun z =>
      InPairedBinaryDomain K (Function.update (fun j => pairedNetworkExposure K j z) i 1) ∧
      InPairedBinaryDomain K (Function.update (fun j => pairedNetworkExposure K j z) i 0)) =
        (1/2 : ℝ) * (1/4 : ℝ)^(K-1)) := by
  classical
  dsimp only
  let D := productDesign K (fun _ => uniformDesign BinaryPair)
  have hpi (i : Fin (K*2)) (e : Fin 4) : pi D (pairedNetworkExposure K) i e.val=1/4 := by
    have he := coordinate_probability K (fun _ => uniformDesign BinaryPair)
      (finProdFinEquiv.symm i).1 (fun w => networkExposure (finProdFinEquiv.symm i).2 w=e.val)
    exact he.trans (network_domain_counterexample.1 _ e)
  have hepo (i : Fin (K*2)) : epo D (pairedNetworkExposure K) (pairedAssignment K) i 1=1 ∧
      epo D (pairedNetworkExposure K) (pairedAssignment K) i 0=0 := by
    have he (d : ℝ) : expectation D (fun z => if pairedNetworkExposure K i z=d then pairedAssignment K i z else 0) =
        expectation (uniformDesign BinaryPair) (fun w => if networkExposure (finProdFinEquiv.symm i).2 w=d then
          pairAssignment (finProdFinEquiv.symm i).2 w else 0) := by
      convert coordinate_expectation K (fun _ => uniformDesign BinaryPair) (finProdFinEquiv.symm i).1
        (fun w => if networkExposure (finProdFinEquiv.symm i).2 w=d then pairAssignment (finProdFinEquiv.symm i).2 w else 0) using 1 <;>
        congr 1 <;> funext z <;>
        simp only [D,pairedNetworkExposure,pairedAssignment,pairedPartnerAssignment,networkExposure] <;> split_ifs <;> rfl
    have hp1 := hpi i 1
    have hp0 := hpi i 0
    norm_num at hp1 hp0
    unfold epo
    rw [hp1,hp0,he 1,he 0]
    generalize (finProdFinEquiv.symm i).2=j
    fin_cases j <;> norm_num [expectation,uniformDesign,networkExposure,pairAssignment,votingOutcome,
      tsum_fintype,Fintype.sum_prod_type,Fin.sum_univ_two]
  have hae : aeed D (pairedNetworkExposure K) (pairedAssignment K) 1 0=1 := by
    simp only [aeed,aepo,fun i => (hepo i).1,fun i => (hepo i).2,Finset.sum_const,
      Finset.sum_const_zero,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,mul_zero,sub_zero]
    exact inv_mul_cancel₀ (by exact_mod_cast (Nat.mul_pos _hK (by norm_num)).ne')
  have hs : SUTVA (pairedNetworkExposure K) (pairedAssignment K) := by
    intro i z w hi
    exact network_domain_counterexample.2.2.2.1 (finProdFinEquiv.symm i).2
      (z (finProdFinEquiv.symm i).1) (w (finProdFinEquiv.symm i).1) hi
  refine ⟨hpi,hepo,hae,hs,?_,?_⟩
  · intro i z hh
    let k := (finProdFinEquiv.symm i).1
    let j := (finProdFinEquiv.symm i).2
    have hi : finProdFinEquiv (k,j)=i := finProdFinEquiv.apply_symm_apply i
    have h1 := paired_network_image_projection K _ hh.1 k
    have h0 := paired_network_image_projection K _ hh.2 k
    have hd := network_domain_counterexample.2.2.2.2.1 (z k)
    have hjcase : j=0 ∨ j=1 := by omega
    rcases hjcase with hj | hj
    · apply hd.1
      constructor
      · simpa [← hi,hj,Function.update_apply,finProdFinEquiv.injective.eq_iff,paired_network_coordinate] using h1
      · simpa [← hi,hj,Function.update_apply,finProdFinEquiv.injective.eq_iff,paired_network_coordinate] using h0
    · apply hd.2
      constructor
      · simpa [← hi,hj,Function.update_apply,finProdFinEquiv.injective.eq_iff,paired_network_coordinate] using h1
      · simpa [← hi,hj,Function.update_apply,finProdFinEquiv.injective.eq_iff,paired_network_coordinate] using h0
  · intro i
    let k₀ := (finProdFinEquiv.symm i).1
    let j₀ := (finProdFinEquiv.symm i).2
    have hi : finProdFinEquiv (k₀,j₀)=i := finProdFinEquiv.apply_symm_apply i
    have hf : (fun z => InPairedBinaryDomain K (Function.update (fun j => pairedNetworkExposure K j z) i 1) ∧
        InPairedBinaryDomain K (Function.update (fun j => pairedNetworkExposure K j z) i 0)) =
        (fun z => ∀ k, if k=k₀ then pairAssignment j₀ (z k)=0 else z k=(0,0)) := by
      funext z
      exact propext (by simpa only [hi] using paired_raw_domain_event K k₀ j₀ z)
    rw [hf,product_events K (fun _ => uniformDesign BinaryPair)
      (fun k w => if k=k₀ then pairAssignment j₀ w=0 else w=(0,0))]
    have hp (k : Fin K) : probability (uniformDesign BinaryPair)
        (fun w => if k=k₀ then pairAssignment j₀ w=0 else w=(0,0)) =
        if k=k₀ then 1/2 else 1/4 := by
      by_cases hk : k=k₀
      · simp only [hk,ite_true]
        have hh (j : Fin 2) : probability (uniformDesign BinaryPair) (fun w => pairAssignment j w=0)=1/2 := by
          fin_cases j <;> norm_num [probability,uniformDesign,pairAssignment,tsum_fintype,Fintype.sum_prod_type,Fin.sum_univ_two]
        exact hh j₀
      · simp only [hk,ite_false]
        norm_num [probability,uniformDesign,tsum_fintype,Fintype.sum_prod_type,Fin.sum_univ_two]
    simp_rw [hp]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ k₀]
    simp only [ite_true]
    have hn (j : {k : Fin K // k ≠ k₀}) : (j.val=k₀) = False := propext ⟨fun h => j.property h,False.elim⟩
    simp only [hn,ite_false,Finset.prod_const,Finset.card_univ]
    have hcard : Fintype.card {k : Fin K // k ≠ k₀}=K-1 := by
      simp [Fintype.card_subtype_compl,Fintype.card_fin]
    rw [hcard]


end AronowAudit.P061

