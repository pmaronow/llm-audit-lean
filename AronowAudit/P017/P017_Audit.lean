import Mathlib.Tactic
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.CDF

/-! Formalization of *Data-Adaptive Causal Effects and Superefficiency*, PDF pp. 1–3.
The paper leaves the sampling design unspecified. Population and sampling measures
are separate genuine probability measures. Sample sizes use `ℕ`; assertions at a
fixed size require `1 ≤ n`, and changing the value at zero does not change a limit.
The extended radius includes the case `c = +∞`.
-/

namespace AronowAudit.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- Section 2, PDF p. 1: “the expectation over the distribution G”. -/
def populationMean {Ω : Type*} [MeasurableSpace Ω] (G : Measure Ω) (τ : Ω → ℝ) : ℝ :=
  ∫ ω, τ ω ∂G

/-- Section 2, PDF p. 1: “the support of the distribution of τ as Supp_G[τ]”.
This is the closed support of the pushforward law, not the range of the function. -/
def effectSupport {Ω : Type*} [MeasurableSpace Ω] (G : Measure Ω) (τ : Ω → ℝ) : Set ℝ :=
  (G.map τ).support

/-- Assumption 1, PDF p. 1: “inf(Supp_G[τ])”, allowing minus infinity. -/
def supportInf (S : Set ℝ) : EReal := sInf ((fun x : ℝ => (x : EReal)) '' S)

/-- Assumption 1, PDF p. 1: “sup(Supp_G[τ])”, allowing plus infinity. -/
def supportSup (S : Set ℝ) : EReal := sSup ((fun x : ℝ => (x : EReal)) '' S)

/-- Assumption 1, PDF p. 1: “min(sup(Supp_G[τ]) − E_G[τ],
E_G[τ] − inf(Supp_G[τ])) = c > 0”. Nonnegative extended radius;
under integrability and a probability law the two distances are nonnegative. -/
def effectRadius {Ω : Type*} [MeasurableSpace Ω] (G : Measure Ω) (τ : Ω → ℝ) : ℝ≥0∞ :=
  (min (supportSup (effectSupport G τ) - (populationMean G τ : EReal))
    ((populationMean G τ : EReal) - supportInf (effectSupport G τ))).toENNReal

/-- Definition 2, PDF p. 2: “the target parameter” equals the estimate within c
of the population mean, and equals the nearer endpoint otherwise. Finite radius. -/
def clipReal (μ c x : ℝ) : ℝ := min (μ + c) (max (μ - c) x)

/-- Definition 2, PDF p. 2, extended-support reading: at infinite radius the
target equals every real estimate. At finite radius this uses `clipReal`. -/
def clipTarget (μ : ℝ) (c : ℝ≥0∞) (x : ℝ) : ℝ :=
  if c = ⊤ then x else clipReal μ c.toReal x

/-- P017-E002 correction: “r(x) = x − C(x)”; the actual estimation error. -/
def residual (μ c x : ℝ) : ℝ := x - clipReal μ c x

/-- Definition 2's event `|hatθ − μ| ≤ c`, including infinite c. -/
def inside (μ : ℝ) (c : ℝ≥0∞) (x : ℝ) : Prop := ENNReal.ofReal |x - μ| ≤ c

/-- Proposition 1, PDF p. 2: “a nonnegative weighting … w_Fn”. The
ordinary finite-ratio reading requires measurability, nonnegativity, integrable
weight and weighted effect, and a strictly positive denominator. Weights may
depend on every full-data variable and on the realized empirical distribution. -/
def AdmissibleWeight {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ w : Ω → ℝ) : Prop :=
  Measurable w ∧ (∀ ω, 0 ≤ w ω) ∧ Integrable w G ∧
    0 < (∫ ω, w ω ∂G) ∧ Integrable (fun ω => w ω * τ ω) G

/-- Proposition 1, PDF p. 2: “E_G[w_Fn τ] / E_G[w_Fn]”. -/
def weightedMean {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ w : Ω → ℝ) : ℝ :=
  (∫ ω, w ω * τ ω ∂G) / (∫ ω, w ω ∂G)

/-- Proposition 1's representation for a realized value of the target. -/
def Representable {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t : ℝ) : Prop :=
  ∃ w, AdmissibleWeight G τ w ∧ weightedMean G τ w = t

/-- Sampling “Pr” in Propositions 3–4 and Corollary 1, PDF pp. 2–3.
Real-valued probabilities are used only with genuine probability measures. -/
def pr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) : ℝ := P.real A

/-- “sqrt(n)” in Definition 1, PDF p. 2. -/
def sqrtN (n : ℕ) : ℝ := Real.sqrt (n : ℝ)

/-- The standard `o_p(a_n)` reading: every positive
threshold has exceedance probability tending to zero (PDF p. 2, proofs). -/
def LittleOp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → Tendsto (fun n => pr P {ω | |V n ω| > η * a n}) atTop (𝓝 0)

/-- “O_p(1)” in Proposition 2 and the correction to Proposition 3:
for each ε > 0, a fixed bound controls the tails at every sufficiently large n. -/
def BoundedInProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (V : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop,
    pr P {ω | |V n ω| > M} < ε

/-- Ordinary consistency for the finite population mean, used by corrected
Proposition 3's proof (P017-E002). -/
def Consistent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hat : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  ∀ b : ℝ, 0 < b → Tendsto (fun n => pr P {ω | |hat n ω - μ| > b}) atTop (𝓝 0)

/-- Definition 1, PDF p. 2: “sqrt(n)(hatθ − θ₀) = N(0, σ²) + o_p(1),
for some 0 < σ² < ∞”. The weak-convergence reading uses Mathlib's
convergence in distribution to the actual Gaussian probability law. -/
def RootNNormal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hat : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  ∃ v : ℝ≥0, 0 < v ∧ TendstoInDistribution
    (fun n ω => sqrtN n * (hat n ω - μ)) atTop (fun z : ℝ => z)
    (fun _ => P) (gaussianReal 0 v)

/-- Proposition 4, PDF p. 3: “sqrt(n)(hatθ − E_G[τ]) = N(0, σ²) + ε”.
The normal and remainder may be dependent; their equality is almost sure. -/
def NormalRemainder {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hat Z ε : ℕ → Ω → ℝ) (μ : ℝ) (v : ℝ≥0) : Prop :=
  (∀ n, 1 ≤ n → Measurable (Z n) ∧ P.map (Z n) = gaussianReal 0 v) ∧
  (∀ n, 1 ≤ n → Measurable (ε n) ∧ Integrable (fun ω => ε n ω ^ 2) P) ∧
  (∀ n, 1 ≤ n → ∀ᵐ ω ∂P, sqrtN n * (hat n ω - μ) = Z n ω + ε n ω)

/-- Proposition 4's “E[ε²] = o(n^(-1/2))”, equivalently sqrt(n) E[ε_n²] → 0. -/
def SmallRemainderMS {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ε : ℕ → Ω → ℝ) : Prop :=
  Tendsto (fun n => sqrtN n * (∫ ω, ε n ω ^ 2 ∂P)) atTop (𝓝 0)

/-- Proposition 4's “E[(hatθ − θ_Fn)²] = o(n^(-1))”, equivalently n MSE → 0. -/
def SmallMSE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V : ℕ → Ω → ℝ) : Prop :=
  Tendsto (fun n : ℕ => (n : ℝ) * (∫ ω, V n ω ^ 2 ∂P)) atTop (𝓝 0)

/-- The “standard Normal CDF” Φ in the proofs of Propositions 3–4, PDF pp. 2–3. -/
def normalCDF (x : ℝ) : ℝ := pr (gaussianReal 0 1) (Iic x)

/-- The normal-tail integral in Proposition 4, PDF p. 3, with its missing
differential restored (P017-T11). This is a Lebesgue integral over `(c,∞)`. -/
def normalTail (n : ℕ) (c σ : ℝ) : ℝ :=
  2 * ∫ x in Ioi c, x ^ 2 * (sqrtN n / (σ * Real.sqrt (2 * Real.pi))) *
    Real.exp (-(x ^ 2 * (n : ℝ)) / (2 * σ ^ 2))

/-- Exact finite content of Definition 2: the clipped value lies in its interval. -/
theorem clipReal_bounds (μ c x : ℝ) (hc : 0 ≤ c) :
    μ - c ≤ clipReal μ c x ∧ clipReal μ c x ≤ μ + c := by
  unfold clipReal
  constructor
  · exact le_min (by linarith) (le_max_left _ _)
  · exact min_le_left _ _

/-- Exact finite content of Definition 2: equality with the estimate is
equivalent to membership in the clipping interval (PDF p. 2). -/
theorem clipReal_eq_self_iff (μ c x : ℝ) (hc : 0 ≤ c) :
    clipReal μ c x = x ↔ |x - μ| ≤ c := by
  constructor
  · intro h
    have hb := clipReal_bounds μ c x hc
    rw [h] at hb
    exact abs_le.mpr (by constructor <;> linarith [hb.1, hb.2])
  · intro h
    rcases abs_le.mp h with ⟨hl, hu⟩
    simp only [clipReal, max_eq_right (by linarith : μ - c ≤ x),
      min_eq_right (by linarith : x ≤ μ + c)]

/-- Proposition 2's printed pointwise inequality, PDF p. 2:
`|θ_Fn − μ| ≤ |hatθ − μ|`. No heterogeneity is required. -/
theorem clipReal_distance (μ c x : ℝ) (hc : 0 ≤ c) :
    |clipReal μ c x - μ| ≤ |x - μ| := by
  simp only [clipReal, min_def, max_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;>
    linarith [le_abs_self (x - μ), neg_le_abs (x - μ)]

/-- Definition 2's exact equality event, including radius zero and infinity. -/
theorem clipTarget_eq_self_iff (μ : ℝ) (c : ℝ≥0∞) (x : ℝ) :
    clipTarget μ c x = x ↔ inside μ c x := by
  by_cases hc : c = ⊤
  · simp [clipTarget, inside, hc]
  · simp only [clipTarget, hc, ↓reduceIte, inside,
      ENNReal.ofReal_le_iff_le_toReal hc]
    exact clipReal_eq_self_iff μ c.toReal x ENNReal.toReal_nonneg

/-- Proposition 2's pointwise distance inequality with arbitrary extended radius. -/
theorem clipTarget_distance (μ : ℝ) (c : ℝ≥0∞) (x : ℝ) :
    |clipTarget μ c x - μ| ≤ |x - μ| := by
  by_cases hc : c = ⊤
  · simp [clipTarget, hc]
  · simpa only [clipTarget, hc, ↓reduceIte] using
      clipReal_distance μ c.toReal x ENNReal.toReal_nonneg

/-- P017-T7(d), T8's infinite-radius case: the actual error and the residual
of an independently clipped auxiliary normal part vanish. The intermediate
difference from the actual target remains y−x and need not vanish. -/
theorem infinite_radius_facts {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (hat : ℕ → Ξ → ℝ) (μ : ℝ) :
    (∀ x y : ℝ, x - clipTarget μ ⊤ x = 0 ∧ y - clipTarget μ ⊤ x = y - x) ∧
    SmallMSE P (fun n ω => hat n ω - clipTarget μ ⊤ (hat n ω)) := by
  constructor
  · intro x y
    simp [clipTarget]
  · unfold SmallMSE
    simp only [clipTarget, ↓reduceIte, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero, mul_zero]
    exact tendsto_const_nhds

/-- Corrected Proposition 4, P017-T8(a): for ordered arguments the change of
the clip lies between zero and the argument change. -/
theorem ordered_clip_changes (μ c x y : ℝ) (hc : 0 ≤ c) (hxy : x ≤ y) :
    0 ≤ clipReal μ c y - clipReal μ c x ∧
    clipReal μ c y - clipReal μ c x ≤ y - x := by
  simp only [clipReal, min_def, max_def]
  split_ifs <;> constructor <;> linarith

/-- Corrected Proposition 4, P017-T8(a): the clip and its residual are each
1-Lipschitz; this does not assume independence of normal and remainder terms. -/
theorem clip_and_residual_lipschitz (μ c x y : ℝ) (hc : 0 ≤ c) :
    |clipReal μ c x - clipReal μ c y| ≤ |x - y| ∧
    |residual μ c x - residual μ c y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · have hb := ordered_clip_changes μ c x y hc h
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    constructor
    · apply abs_le.mpr
      constructor <;> linarith [hb.1, hb.2]
    · apply abs_le.mpr
      unfold residual
      constructor <;> linarith [hb.1, hb.2]

  · have hb := ordered_clip_changes μ c y x hc h
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    constructor
    · apply abs_le.mpr
      constructor <;> linarith [hb.1, hb.2]
    · apply abs_le.mpr
      unfold residual
      constructor <;> linarith [hb.1, hb.2]

/-- P017-T8(c), finite pointwise certificate: the clipped residual is zero
inside the interval, and its square is bounded by the tail square and by
the fourth power divided by c². -/
theorem residual_tail_fourth_bound (μ c x : ℝ) (hc : 0 < c) :
    residual μ c x ^ 2 ≤ (if |x - μ| > c then (x - μ) ^ 2 else 0) ∧
    (if |x - μ| > c then (x - μ) ^ 2 else 0) ≤ (x - μ) ^ 4 / c ^ 2 := by
  have hcenter : residual μ c μ = 0 := by
    unfold residual
    rw [(clipReal_eq_self_iff _ _ _ hc.le).mpr (by simpa using hc.le), sub_self]
  have hdist := (clip_and_residual_lipschitz μ c x μ hc.le).2
  rw [hcenter, sub_zero] at hdist
  have hs : residual μ c x ^ 2 ≤ (x - μ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hdist
  by_cases hx : |x - μ| > c
  · simp only [hx, ↓reduceIte]
    refine ⟨hs, ?_⟩
    have hc2 : c ^ 2 ≤ (x - μ) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hc.le (abs_nonneg _)).mpr hx.le
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    calc
      (x - μ) ^ 2 * c ^ 2 ≤ (x - μ) ^ 2 * (x - μ) ^ 2 :=
        mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
      _ = (x - μ) ^ 4 := by ring
  · have hr : residual μ c x = 0 := by
      unfold residual
      rw [(clipReal_eq_self_iff _ _ _ hc.le).mpr (le_of_not_gt hx), sub_self]
    simp only [hx, ↓reduceIte, hr, zero_pow (by decide : 2 ≠ 0), le_refl, true_and]
    positivity

/-- P017-T8(b),(e), exact perturbation step before integration: both the actual
residual and the intermediate normal-to-actual-target difference have square
at most twice the unperturbed residual square plus twice the perturbation square. -/
theorem perturbation_square_bounds (μ c x δ : ℝ) (hc : 0 ≤ c) :
    residual μ c (x + δ) ^ 2 ≤ 2 * residual μ c x ^ 2 + 2 * δ ^ 2 ∧
    (x - clipReal μ c (x + δ)) ^ 2 ≤ 2 * residual μ c x ^ 2 + 2 * δ ^ 2 := by
  have hr := (clip_and_residual_lipschitz μ c (x + δ) x hc).2
  have hp := (clip_and_residual_lipschitz μ c (x + δ) x hc).1
  have hdiff : (residual μ c (x + δ) - residual μ c x) ^ 2 ≤ δ ^ 2 := by
    simpa only [sq_abs, add_sub_cancel_left] using
      (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hr
  have hproj : (clipReal μ c (x + δ) - clipReal μ c x) ^ 2 ≤ δ ^ 2 := by
    simpa only [sq_abs, add_sub_cancel_left] using
      (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hp
  constructor
  · nlinarith [sq_nonneg (residual μ c (x + δ) - 2 * residual μ c x)]
  · unfold residual at *
    nlinarith [sq_nonneg (x - clipReal μ c (x + δ) - 2 * (x - clipReal μ c x))]

/-- P017-T13(d)'s exact union-bound step, before identifying the Gaussian tail. -/
theorem sum_failure_union_bound {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (tilde u : Ξ → ℝ) (μ c : ℝ) :
    pr P {ω | |tilde ω + u ω - μ| > c} ≤
      pr P {ω | |tilde ω - μ| > c / 2} + pr P {ω | |u ω| > c / 2} := by
  apply le_trans (measureReal_mono (s₂ := {ω | |tilde ω - μ| > c / 2} ∪ {ω | |u ω| > c / 2}) ?_)
    (measureReal_union_le _ _)
  intro ω hω
  change c < |tilde ω + u ω - μ| at hω
  by_contra h
  have ha : |tilde ω - μ| ≤ c / 2 := le_of_not_gt (fun h1 => h (Or.inl h1))
  have hb : |u ω| ≤ c / 2 := le_of_not_gt (fun h2 => h (Or.inr h2))
  have ht := abs_add_le (tilde ω - μ) (u ω)
  have heq : tilde ω - μ + u ω = tilde ω + u ω - μ := by ring
  rw [heq] at ht
  linarith

/-- Exact part of P017-T7(a): an exceedance of the actual error requires
an estimate outside the clipping interval, for every positive scale. -/
theorem clipping_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hat : Ω → ℝ)
    (μ c η a : ℝ) (hc : 0 ≤ c) (hη : 0 < η) (ha : 0 < a) :
    pr P {ω | |hat ω - clipReal μ c (hat ω)| > η * a} ≤
      pr P {ω | |hat ω - μ| > c} := by
  refine measureReal_mono ?_ (measure_ne_top P _)
  intro ω h
  change η * a < |hat ω - clipReal μ c (hat ω)| at h
  by_contra hout
  have hi : |hat ω - μ| ≤ c := le_of_not_gt hout
  rw [(clipReal_eq_self_iff μ c (hat ω) hc).mpr hi, sub_self, abs_zero] at h
  exact (not_lt_of_ge (mul_pos hη ha).le) h

/-- Consistency step in the corrected proof, P017-T7(b): a fixed-radius tail
is contained in a root-n tail once the root-n threshold exceeds M. -/
theorem consistency_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hat : Ω → ℝ)
    (μ b M : ℝ) (n : ℕ) (hb : 0 < b) (hM : M < b * sqrtN n) :
    pr P {ω | |hat ω - μ| > b} ≤
      pr P {ω | sqrtN n * |hat ω - μ| > M} := by
  refine measureReal_mono ?_ (measure_ne_top P _)
  intro ω hω
  have hs : 0 ≤ sqrtN n := Real.sqrt_nonneg _
  have := mul_le_mul_of_nonneg_left hω.le hs
  dsimp at *
  nlinarith

/-- Universal endpoint obstruction for P017-T1(d), allowing weights on the
entire full-data space: an a.s. strictly sub-endpoint effect has strictly
sub-endpoint weighted mean for every integrable nonnegative positive weight. -/
theorem unattainable_upper_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ w : Ω → ℝ) (hw : Integrable w G)
    (hwt : Integrable (fun ω => w ω * τ ω) G)
    (hwn : ∀ᵐ ω ∂G, 0 ≤ w ω) (ht : ∀ᵐ ω ∂G, τ ω < 1)
    (hwp : 0 < ∫ ω, w ω ∂G) : weightedMean G τ w < 1 := by
  have hle : (fun ω => w ω * τ ω) ≤ᵐ[G] w := by
    filter_upwards [hwn, ht] with ω hwω htω
    exact mul_le_of_le_one_right hwω htω.le
  have hneq : (∫ ω, w ω * τ ω ∂G) ≠ ∫ ω, w ω ∂G := by
    intro heq
    have hae := (integral_eq_iff_of_ae_le hwt hw hle).mp heq
    have hwzero : w =ᵐ[G] 0 := by
      filter_upwards [hae, ht] with ω hω htω
      have hmul : w ω * (1 - τ ω) = 0 := by
        change w ω * τ ω = w ω at hω
        nlinarith
      rcases mul_eq_zero.mp hmul with h | h
      · exact h
      · linarith
    have hz : (∫ ω, w ω ∂G) = 0 := by
      calc
        (∫ ω, w ω ∂G) = ∫ ω, (0 : ℝ) ∂G := integral_congr_ae hwzero
        _ = 0 := by simp
    linarith
  exact (div_lt_one hwp).mpr
    (lt_of_le_of_ne (integral_mono_ae hwt hw hle) hneq)

/-- P017-T2's atom construction: the normalized indicator weight is measurable,
nonnegative and integrable, has expectation one and weighted mean t. -/
theorem atom_weight_representation {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ) (hτ : Measurable τ)
    (t : ℝ) (hp : 0 < pr G {ω | τ ω = t}) :
    ∃ w, AdmissibleWeight G τ w ∧ (∫ ω, w ω ∂G) = 1 ∧ weightedMean G τ w = t := by
  let S := {ω | τ ω = t}
  have hm : MeasurableSet S := measurableSet_eq_fun hτ measurable_const
  let p := pr G S
  have hp' : 0 < p := hp
  let w : Ω → ℝ := S.indicator (fun _ => 1 / p)
  have hwi : Integrable w G := (integrable_const (1 / p)).indicator hm
  have hwτ : (fun ω => w ω * τ ω) = S.indicator (fun _ => t / p) := by
    funext ω
    by_cases hω : τ ω = t <;> simp [w, S, hω] <;> ring
  have hd : (∫ ω, w ω ∂G) = 1 := by
    rw [integral_indicator_const (1 / p) hm]
    change p * (1 / p) = 1
    field_simp [hp'.ne']
  have hn : (∫ ω, w ω * τ ω ∂G) = t := by
    rw [hwτ, integral_indicator_const (t / p) hm]
    change p * (t / p) = t
    field_simp [hp'.ne']
  refine ⟨w, ⟨measurable_const.indicator hm, ?_, hwi, by rw [hd]; norm_num, ?_⟩, hd, ?_⟩
  · intro ω
    by_cases hω : ω ∈ S
    · simpa only [w, indicator_of_mem hω] using (one_div_pos.mpr hp').le
    · simp [w, hω]
  · rw [hwτ]
    exact (integrable_const (t / p)).indicator hm
  · simp only [weightedMean, hd, hn, div_one]

/-- P017-T2 necessity: a strictly one-sided a.s. effect cannot have weighted
mean t, even when the weighting depends on all full-data coordinates. -/
theorem strictly_one_sided_not_representable {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t : ℝ)
    (hs : (∀ᵐ ω ∂G, τ ω < t) ∨ (∀ᵐ ω ∂G, t < τ ω)) : ¬ Representable G τ t := by
  rintro ⟨w, ⟨hwm, hwn, hwi, hwp, hwτ⟩, hmean⟩
  have hnum : (∫ ω, w ω * τ ω ∂G) = t * (∫ ω, w ω ∂G) :=
    (div_eq_iff hwp.ne').mp hmean
  have hzero : w =ᵐ[G] 0 := by
    rcases hs with hs | hs
    · have hi : Integrable (fun ω => w ω * (t - τ ω)) G := by
        convert (hwi.mul_const t).sub hwτ using 1 <;> ext ω <;> dsimp <;> ring
      have hnon : 0 ≤ᵐ[G] (fun ω => w ω * (t - τ ω)) :=
        hs.mono (fun ω hω => mul_nonneg (hwn ω) (by linarith))
      have hz : (∫ ω, w ω * (t - τ ω) ∂G) = 0 := by
        have he : (fun ω => w ω * (t - τ ω)) = (fun ω => w ω * t - w ω * τ ω) := by
          funext ω; ring
        rw [he, integral_sub (hwi.mul_const t) hwτ, integral_mul_const, hnum]
        ring
      have hae := (integral_eq_zero_iff_of_nonneg_ae hnon hi).mp hz
      filter_upwards [hae, hs] with ω hω hsω
      exact (mul_eq_zero.mp hω).resolve_right (by linarith)
    · have hi : Integrable (fun ω => w ω * (τ ω - t)) G := by
        convert hwτ.sub (hwi.mul_const t) using 1 <;> ext ω <;> dsimp <;> ring
      have hnon : 0 ≤ᵐ[G] (fun ω => w ω * (τ ω - t)) :=
        hs.mono (fun ω hω => mul_nonneg (hwn ω) (by linarith))
      have hz : (∫ ω, w ω * (τ ω - t) ∂G) = 0 := by
        have he : (fun ω => w ω * (τ ω - t)) = (fun ω => w ω * τ ω - w ω * t) := by
          funext ω; ring
        rw [he, integral_sub hwτ (hwi.mul_const t), integral_mul_const, hnum]
        ring
      have hae := (integral_eq_zero_iff_of_nonneg_ae hnon hi).mp hz
      filter_upwards [hae, hs] with ω hω hsω
      exact (mul_eq_zero.mp hω).resolve_right (by linarith)
  have hz : (∫ ω, w ω ∂G) = 0 := by
    rw [integral_congr_ae hzero]
    simp
  linarith

/-- P017-T2 sufficiency for straddling values: a bounded two-region simple
weight balances the positive and negative centered first moments. It is an
equivalent unnormalized version of the displayed mixture weight in P017-E001. -/
theorem straddling_weight_representation {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (t : ℝ)
    (hl : 0 < pr G {ω | τ ω < t}) (hu : 0 < pr G {ω | t < τ ω}) : Representable G τ t := by
  let L := {ω | τ ω < t}
  let U := {ω | t < τ ω}
  have hmL : MeasurableSet L := measurableSet_lt hτm measurable_const
  have hmU : MeasurableSet U := measurableSet_lt measurable_const hτm
  let fL : Ω → ℝ := L.indicator (fun ω => t - τ ω)
  let fU : Ω → ℝ := U.indicator (fun ω => τ ω - t)
  have hiL : Integrable fL G := ((integrable_const t).sub hτi).indicator hmL
  have hiU : Integrable fU G := (hτi.sub (integrable_const t)).indicator hmU
  have hnL : 0 ≤ fL := by
    intro ω; by_cases hω : τ ω < t <;> simp [fL, L, hω] <;> linarith
  have hnU : 0 ≤ fU := by
    intro ω; by_cases hω : t < τ ω <;> simp [fU, U, hω] <;> linarith
  have hsL : Function.support fL = L := by
    ext ω
    by_cases hω : τ ω < t
    · simp [Function.support, fL, L, hω, sub_ne_zero.mpr hω.ne']
    · simp [Function.support, fL, L, hω]
  have hsU : Function.support fU = U := by
    ext ω
    by_cases hω : t < τ ω
    · simp [Function.support, fU, U, hω, sub_ne_zero.mpr hω.ne']
    · simp [Function.support, fU, U, hω]
  let a := ∫ ω, fL ω ∂G
  let b := ∫ ω, fU ω ∂G
  have ha : 0 < a := by
    apply (integral_pos_iff_support_of_nonneg hnL hiL).mpr
    rw [hsL]
    exact pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp hl.ne')
  have hb : 0 < b := by
    apply (integral_pos_iff_support_of_nonneg hnU hiU).mpr
    rw [hsU]
    exact pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp hu.ne')
  let w : Ω → ℝ := fun ω => b * L.indicator (fun _ => (1 : ℝ)) ω + a * U.indicator (fun _ => (1 : ℝ)) ω
  have hwi : Integrable w G :=
    (((integrable_const (1 : ℝ)).indicator hmL).const_mul b).add
      (((integrable_const (1 : ℝ)).indicator hmU).const_mul a)
  have hprod : (fun ω => w ω * τ ω) =
      (fun ω => b * L.indicator τ ω + a * U.indicator τ ω) := by
    funext ω
    simp only [w, Set.indicator]
    split_ifs <;> ring
  have hwτ : Integrable (fun ω => w ω * τ ω) G := by
    rw [hprod]
    exact ((hτi.indicator hmL).const_mul b).add ((hτi.indicator hmU).const_mul a)
  have hd : (∫ ω, w ω ∂G) = b * pr G L + a * pr G U := by
    rw [integral_add (((integrable_const (1 : ℝ)).indicator hmL).const_mul b)
      (((integrable_const (1 : ℝ)).indicator hmU).const_mul a)]
    simp only [integral_const_mul, integral_indicator_const (1 : ℝ) hmL,
      integral_indicator_const (1 : ℝ) hmU, smul_eq_mul, mul_one, pr]
  have hdp : 0 < ∫ ω, w ω ∂G := by
    rw [hd]
    exact add_pos (mul_pos hb hl) (mul_pos ha hu)
  have hcenter : (fun ω => w ω * (τ ω - t)) = (fun ω => b * (-fL ω) + a * fU ω) := by
    funext ω
    simp only [w, fL, fU, L, U, Set.indicator]
    split_ifs <;> ring
  have hz : (∫ ω, w ω * (τ ω - t) ∂G) = 0 := by
    have hneg : Integrable (fun ω => b * -fL ω) G := by
      simpa only [Pi.neg_apply] using hiL.neg.const_mul b
    rw [hcenter, integral_add hneg (hiU.const_mul a),
      integral_const_mul, integral_neg, integral_const_mul]
    change b * (-a) + a * b = 0
    ring
  have hnum : (∫ ω, w ω * τ ω ∂G) = t * (∫ ω, w ω ∂G) := by
    have he : (fun ω => w ω * (τ ω - t)) = (fun ω => w ω * τ ω - w ω * t) := by
      funext ω; ring
    rw [he, integral_sub hwτ (hwi.mul_const t), integral_mul_const] at hz
    nlinarith
  refine ⟨w, ⟨?_, ?_, hwi, hdp, hwτ⟩, ?_⟩
  · exact (measurable_const.mul (measurable_const.indicator hmL)).add
      (measurable_const.mul (measurable_const.indicator hmU))
  · intro ω
    simp only [w, Set.indicator]
    split_ifs <;> positivity
  · exact (div_eq_iff hdp.ne').mpr hnum

/-- Full corrected weighted-mean fact, P017-T2, PDF p. 2 and P017-E001:
the target is attained exactly when it is an atom or has positive mass on both sides. -/
theorem weighted_mean_characterization {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (t : ℝ) :
    Representable G τ t ↔
      0 < pr G {ω | τ ω = t} ∨
        (0 < pr G {ω | τ ω < t} ∧ 0 < pr G {ω | t < τ ω}) := by
  constructor
  · intro hrep
    by_contra hbad
    have h0 : pr G {ω | τ ω = t} = 0 :=
      le_antisymm (le_of_not_gt (fun h => hbad (Or.inl h))) measureReal_nonneg
    have hn0 : ∀ᵐ ω ∂G, τ ω ≠ t := by
      rw [ae_iff]
      simpa only [not_not] using (measureReal_eq_zero_iff).mp h0
    by_cases hl : 0 < pr G {ω | τ ω < t}
    · have hz : pr G {ω | t < τ ω} = 0 :=
        le_antisymm (le_of_not_gt (fun h => hbad (Or.inr ⟨hl, h⟩))) measureReal_nonneg
      have hn : ∀ᵐ ω ∂G, ¬ t < τ ω := by
        rw [ae_iff]
        simpa only [not_not] using (measureReal_eq_zero_iff).mp hz
      apply strictly_one_sided_not_representable G τ t (Or.inl ?_) hrep
      filter_upwards [hn, hn0] with ω hω hω0
      exact lt_of_le_of_ne (le_of_not_gt hω) hω0
    · have hz : pr G {ω | τ ω < t} = 0 :=
        le_antisymm (le_of_not_gt hl) measureReal_nonneg
      have hn : ∀ᵐ ω ∂G, ¬ τ ω < t := by
        rw [ae_iff]
        simpa only [not_not] using (measureReal_eq_zero_iff).mp hz
      apply strictly_one_sided_not_representable G τ t (Or.inr ?_) hrep
      filter_upwards [hn, hn0] with ω hω hω0
      exact lt_of_le_of_ne (le_of_not_gt hω) hω0.symm
  · rintro (h | ⟨hl, hu⟩)
    · obtain ⟨w, hw, _, hmean⟩ := atom_weight_representation G τ hτm t h
      exact ⟨w, hw, hmean⟩
    · exact straddling_weight_representation G τ hτm hτi t hl hu


/-- P017-E001 correction: a value in the support hull is admissible when it
is strictly interior or is a finite endpoint carrying positive probability. -/
def InteriorOrEndpointAtom {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (t : ℝ) : Prop :=
  (supportInf (effectSupport G τ) < (t : EReal) ∧
    (t : EReal) < supportSup (effectSupport G τ)) ∨
  (((t : EReal) = supportInf (effectSupport G τ) ∨
    (t : EReal) = supportSup (effectSupport G τ)) ∧ 0 < pr G {ω | τ ω = t})

/-- P017-T2(i): every finite value strictly between the closed support bounds
has positive probability on both sides, including one-sided unbounded supports. -/
theorem support_interior_straddles {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ) (hτm : Measurable τ)
    (t : ℝ) (hL : supportInf (effectSupport G τ) < (t : EReal))
    (hU : (t : EReal) < supportSup (effectSupport G τ)) :
    0 < pr G {ω | τ ω < t} ∧ 0 < pr G {ω | t < τ ω} := by
  constructor
  · by_contra h
    have hz : G {ω | τ ω < t} = 0 :=
      (measureReal_eq_zero_iff).mp (le_antisymm (le_of_not_gt h) measureReal_nonneg)
    have hae : ∀ᵐ ω ∂G, t ≤ τ ω := by
      rw [ae_iff]
      simpa only [not_le] using hz
    have hs : effectSupport G τ ⊆ Ici t :=
      Measure.support_subset_of_isClosed isClosed_Ici
        ((mem_ae_map_iff hτm.aemeasurable measurableSet_Ici).mpr hae)
    have hbound : (t : EReal) ≤ supportInf (effectSupport G τ) := by
      apply le_sInf
      rintro x ⟨y, hy, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hs hy)
    exact (not_lt_of_ge hbound) hL
  · by_contra h
    have hz : G {ω | t < τ ω} = 0 :=
      (measureReal_eq_zero_iff).mp (le_antisymm (le_of_not_gt h) measureReal_nonneg)
    have hae : ∀ᵐ ω ∂G, τ ω ≤ t := by
      rw [ae_iff]
      simpa only [not_le] using hz
    have hs : effectSupport G τ ⊆ Iic t :=
      Measure.support_subset_of_isClosed isClosed_Iic
        ((mem_ae_map_iff hτm.aemeasurable measurableSet_Iic).mpr hae)
    have hbound : supportSup (effectSupport G τ) ≤ (t : EReal) := by
      apply sSup_le
      rintro x ⟨y, hy, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hs hy)
    exact (not_lt_of_ge hbound) hU

/-- P017-T2 support bridge: a positive-probability effect event has a point
in the closed effect support. This excludes substituting the function's range. -/
theorem positive_event_meets_support {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ) (hτm : Measurable τ)
    (S : Set ℝ) (hmS : MeasurableSet S) (hp : 0 < pr G (τ ⁻¹' S)) :
    (S ∩ effectSupport G τ).Nonempty := by
  have hpos : 0 < (G.map τ) S := by
    rw [Measure.map_apply hτm hmS]
    exact pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp hp.ne')
  exact Measure.nonempty_inter_support_of_pos hpos

/-- P017-T2(iii): every ordinary nonnegative weighted causal effect lies
between the effect-support bounds, including infinite bounds. -/
theorem representable_support_bounds {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (t : ℝ) (hr : Representable G τ t) :
    supportInf (effectSupport G τ) ≤ (t : EReal) ∧ (t : EReal) ≤ supportSup (effectSupport G τ) := by
  rcases (weighted_mean_characterization G τ hτm hτi t).mp hr with h | ⟨hl, hu⟩
  · obtain ⟨x, hx, hxs⟩ := positive_event_meets_support G τ hτm {t} (measurableSet_singleton _) h
    have hxt : x = t := mem_singleton_iff.mp hx
    subst x
    exact ⟨sInf_le ⟨t, hxs, rfl⟩, le_sSup ⟨t, hxs, rfl⟩⟩
  · obtain ⟨x, hx, hxs⟩ := positive_event_meets_support G τ hτm (Iio t) measurableSet_Iio hl
    obtain ⟨y, hy, hys⟩ := positive_event_meets_support G τ hτm (Ioi t) measurableSet_Ioi hu
    have hmin : supportInf (effectSupport G τ) ≤ (x : EReal) := sInf_le ⟨x, hxs, rfl⟩
    have hmax : (y : EReal) ≤ supportSup (effectSupport G τ) := le_sSup ⟨y, hys, rfl⟩
    exact ⟨hmin.trans (EReal.coe_le_coe_iff.mpr hx.le),
      (EReal.coe_le_coe_iff.mpr hy.le).trans hmax⟩

/-- P017-T2 support consequences, explicitly: every finite interior value
is attained; a finite support endpoint is attained exactly when it has an
atom; no value outside the support bounds is attained. -/
theorem weighted_support_consequences {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) :
    (∀ t : ℝ, supportInf (effectSupport G τ) < (t : EReal) →
      (t : EReal) < supportSup (effectSupport G τ) → Representable G τ t) ∧
    (∀ t : ℝ, ((t : EReal) = supportInf (effectSupport G τ) ∨
      (t : EReal) = supportSup (effectSupport G τ)) →
      (Representable G τ t ↔ 0 < pr G {ω | τ ω = t})) ∧
    (∀ t : ℝ, ((t : EReal) < supportInf (effectSupport G τ) ∨
      supportSup (effectSupport G τ) < (t : EReal)) → ¬ Representable G τ t) := by
  refine ⟨fun t hl hu => (weighted_mean_characterization G τ hτm hτi t).mpr
    (Or.inr (support_interior_straddles G τ hτm t hl hu)), ?_, ?_⟩
  · intro t hend
    constructor
    · intro hr
      rcases (weighted_mean_characterization G τ hτm hτi t).mp hr with ha | ⟨hl, hu⟩
      · exact ha
      · have hs : ∀ᵐ ω ∂G, τ ω ∈ effectSupport G τ :=
          ae_of_ae_map hτm.aemeasurable (Measure.support_mem_ae (μ := G.map τ))
        rcases hend with hL | hU
        · have hnon : ∀ᵐ ω ∂G, t ≤ τ ω := hs.mono (fun ω hω =>
            EReal.coe_le_coe_iff.mp (by rw [hL]; exact sInf_le ⟨τ ω, hω, rfl⟩))
          have hz : G {ω | τ ω < t} = 0 := by
            simpa only [not_le] using (ae_iff.mp hnon)
          have hzR : pr G {ω | τ ω < t} = 0 := (measureReal_eq_zero_iff).mpr hz
          linarith
        · have hnon : ∀ᵐ ω ∂G, τ ω ≤ t := hs.mono (fun ω hω =>
            EReal.coe_le_coe_iff.mp (by rw [hU]; exact le_sSup ⟨τ ω, hω, rfl⟩))
          have hz : G {ω | t < τ ω} = 0 := by
            simpa only [not_le] using (ae_iff.mp hnon)
          have hzR : pr G {ω | t < τ ω} = 0 := (measureReal_eq_zero_iff).mpr hz
          linarith
    · intro hp
      exact (weighted_mean_characterization G τ hτm hτi t).mpr (Or.inl hp)
  · intro t hout hr
    have hb := representable_support_bounds G τ hτm hτi t hr
    rcases hout with hl | hu
    · exact not_lt_of_ge hb.1 hl
    · exact not_lt_of_ge hb.2 hu

/-- P017-T4's finite support geometry: when 0 < d < c, the entire clipping
interval lies strictly between the effect-support bounds. -/
theorem interior_radius_support {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) (τ : Ω → ℝ) (d : ℝ) (hd : 0 < d)
    (hsmall : ENNReal.ofReal d < effectRadius G τ) (x : ℝ) :
    supportInf (effectSupport G τ) < (clipReal (populationMean G τ) d x : EReal) ∧
      (clipReal (populationMean G τ) d x : EReal) < supportSup (effectSupport G τ) := by
  let μ := populationMean G τ
  let L := supportInf (effectSupport G τ)
  let U := supportSup (effectSupport G τ)
  let q := min (U - (μ : EReal)) ((μ : EReal) - L)
  have hq : 0 < q := EReal.toENNReal_pos_iff.mp
    ((ENNReal.ofReal_pos.mpr hd).trans hsmall)
  have hds : (d : EReal) < q := by
    have h := EReal.coe_ennreal_lt_coe_ennreal_iff.mpr hsmall
    change (ENNReal.ofReal d : EReal) < (q.toENNReal : EReal) at h
    rw [EReal.coe_ennreal_ofReal, max_eq_left hd.le, EReal.coe_toENNReal hq.le] at h
    exact h
  have hdu : (d : EReal) < U - (μ : EReal) := hds.trans_le (min_le_left _ _)
  have hdl : (d : EReal) < (μ : EReal) - L := hds.trans_le (min_le_right _ _)
  have hUpper : ((μ + d : ℝ) : EReal) < U := by
    have h := (EReal.lt_sub_iff_add_lt (.inl (EReal.coe_ne_bot μ))
      (.inl (EReal.coe_ne_top μ))).mp hdu
    simpa only [EReal.coe_add, add_comm] using h
  have hLower : L < ((μ - d : ℝ) : EReal) := by
    have h := (EReal.lt_sub_iff_add_lt (.inr (EReal.coe_ne_top d))
      (.inr (EReal.coe_ne_bot d))).mp hdl
    rw [EReal.coe_sub, EReal.lt_sub_iff_add_lt (.inl (EReal.coe_ne_bot d))
      (.inl (EReal.coe_ne_top d))]
    simpa only [add_comm] using h
  have hb := clipReal_bounds μ d x hd.le
  exact ⟨hLower.trans_le (EReal.coe_le_coe_iff.mpr hb.1),
    (EReal.coe_le_coe_iff.mpr hb.2).trans_lt hUpper⟩


/-- P017-T4, corrected Definition 2 / Proposition 1 using a fixed finite
radius 0 < d < c: every realized target is a nonnegative weighted full-data
causal effect. No condition on the estimate is assumed. Such a radius exists. -/
theorem interior_radius_representation {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ) :
    (∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d < effectRadius G τ) ∧
    (∀ d : ℝ, 0 < d → ENNReal.ofReal d < effectRadius G τ →
      ∀ x : ℝ, Representable G τ (clipReal (populationMean G τ) d x)) := by
  constructor
  · by_cases hInfinity : effectRadius G τ = ⊤
    · exact ⟨1, by norm_num, by simp [hInfinity]⟩
    · have hcR : 0 < (effectRadius G τ).toReal := ENNReal.toReal_pos hc.ne' hInfinity
      exact ⟨(effectRadius G τ).toReal / 2, half_pos hcR,
        (ENNReal.ofReal_lt_iff_lt_toReal (half_pos hcR).le hInfinity).mpr (half_lt_self hcR)⟩
  · intro d hd hsmall x
    have hb := interior_radius_support G τ d hd hsmall x
    have hmass := support_interior_straddles G τ hτm _ hb.1 hb.2
    exact (weighted_mean_characterization G τ hτm hτi _).mpr (Or.inr hmass)

/-- P017-T4 companions (i)–(ii): the repaired target contracts distance,
has zero error exactly in the radius-d interval, and has the exact event bound. -/
theorem interior_radius_finite_companions {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : Ξ → ℝ) (μ d : ℝ) (hd : 0 < d) :
    (∀ x, |clipReal μ d x - μ| ≤ |x - μ|) ∧
    (∀ x, clipReal μ d x = x ↔ |x - μ| ≤ d) ∧
    (∀ η a : ℝ, 0 < η → 0 < a →
      pr P {ω | |hat ω - clipReal μ d (hat ω)| > η * a} ≤
        pr P {ω | |hat ω - μ| > d}) := by
  exact ⟨fun x => clipReal_distance μ d x hd.le,
    fun x => clipReal_eq_self_iff μ d x hd.le,
    fun η a hη ha => clipping_event_bound P hat μ d η a hd.le hη ha⟩

/-- P017-T4(iii)'s qualification: the original radius-c support condition
does not imply zero error for a target clipped at d<c. A constant estimator
at this explicit value lies in the original interval and outside the new one. -/
theorem smaller_radius_changes_target (μ c d : ℝ) (hd : 0 < d) (hdc : d < c) :
    ∃ x : ℝ, |x - μ| ≤ c ∧ clipReal μ c x = x ∧ clipReal μ d x ≠ x := by
  have hc : 0 < c := hd.trans hdc
  have hx : |(μ + c) - μ| ≤ c := by simp [abs_of_pos hc]
  refine ⟨μ + c, hx, (clipReal_eq_self_iff _ _ _ hc.le).mpr hx, ?_⟩
  intro h
  have hb := (clipReal_bounds μ d (μ + c) hd.le).2
  rw [h] at hb
  linarith

/-- P017-T7's stronger, consistency-only correction: the actual clipping error
is o_p(a_n) for every positive deterministic sequence, not just n^(-1/2). -/
theorem consistent_clipping_all_rates {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (μ c : ℝ) (hc : 0 < c) (hh : Consistent P hat μ)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    LittleOp P (fun n ω => hat n ω - clipReal μ c (hat n ω)) a := by
  intro η hη
  apply squeeze_zero (fun n => measureReal_nonneg)
    (fun n => clipping_event_bound P (hat n) μ c η (a n) hc.le hη (ha n))
    (hh c hc)

/-- Root-n asymptotic normality implies tight root-n errors and consistency;
this is the asymptotic step explicitly used in P017-T7(b), T14 and T16. -/
theorem root_normal_tight_and_consistent {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (μ : ℝ) (hh : RootNNormal P hat μ) :
    BoundedInProbability P (fun n ω => sqrtN n * (hat n ω - μ)) ∧ Consistent P hat μ := by
  rcases hh with ⟨v, hv, hweak⟩
  let γ := gaussianReal 0 v
  letI : NullSingletonClass γ := nullSingletonClass_gaussianReal hv.ne'
  have htENN : Tendsto (fun M : ℝ => γ {x | M < |x|}) atTop (𝓝 0) := by
    simpa only [iSup_singleton, Real.norm_eq_abs] using
      (tendsto_measure_norm_gt_of_isTightMeasureSet
        (isTightMeasureSet_singleton (μ := γ)))
  have ht : Tendsto (fun M : ℝ => pr γ {x | M < |x|}) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp htENN
  have hbounded : BoundedInProbability P (fun n ω => sqrtN n * (hat n ω - μ)) := by
    intro ε hε
    obtain ⟨M, hMp, hM⟩ :=
      ((ht.eventually (Iio_mem_nhds (half_pos hε))).and (eventually_gt_atTop (0 : ℝ))).exists
    have hnull : γ (frontier {x : ℝ | M < |x|}) = 0 := by
      have hsub : {x : ℝ | M = |x|} ⊆ {M, -M} := by
        intro x hx
        change M = |x| at hx
        rcases le_total 0 x with hx0 | hx0
        · rw [abs_of_nonneg hx0] at hx
          simp only [mem_insert_iff, mem_singleton_iff]
          exact Or.inl hx.symm
        · rw [abs_of_nonpos hx0] at hx
          simp only [mem_insert_iff, mem_singleton_iff]
          exact Or.inr (by linarith)
      exact measure_mono_null
        ((frontier_lt_subset_eq continuous_const continuous_abs).trans hsub)
        (((Set.finite_singleton (-M)).insert M).measure_zero γ)
    have hs : MeasurableSet {x : ℝ | M < |x|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have hpENN := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hweak.tendsto (E := {x : ℝ | M < |x|}) (by simpa [γ] using hnull)
    simp only [Measure.map_id'] at hpENN
    have hp : Tendsto (fun n => pr P {ω | M < |sqrtN n * (hat n ω - μ)|})
        atTop (𝓝 (pr γ {x | M < |x|})) := by
      have hpR := (ENNReal.tendsto_toReal (measure_ne_top γ _)).comp hpENN
      have hmap (n : ℕ) :
          (P.map (fun ω => sqrtN n * (hat n ω - μ))) {x : ℝ | M < |x|} =
          P {ω | M < |sqrtN n * (hat n ω - μ)|} :=
        Measure.map_apply_of_aemeasurable (hweak.forall_aemeasurable n) hs
      simpa only [pr, Measure.real, Function.comp_def, ProbabilityMeasure.coe_mk, hmap] using hpR
    exact ⟨M, hM, hp.eventually (Iio_mem_nhds (hMp.trans (half_lt_self hε)))⟩
  refine ⟨hbounded, ?_⟩
  intro b hb
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le measureReal_nonneg)
  · intro ε hε
    rcases hbounded ε hε with ⟨M, hM, htail⟩
    have hg : Tendsto (fun n : ℕ => b * sqrtN n) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hb
    filter_upwards [htail, hg.eventually (eventually_gt_atTop M)] with n hn hnM
    have hle := consistency_event_bound P (hat n) μ b M n hb hnM
    have heq : {ω | sqrtN n * |hat n ω - μ| > M} =
        {ω | |sqrtN n * (hat n ω - μ)| > M} := by
      ext ω
      simp only [mem_setOf_eq, abs_mul, sqrtN, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
    rw [heq] at hle
    exact hle.trans_lt hn

/-- P017-T7, the full corrected proof of Proposition 3: root-n errors are tight,
the estimator is consistent, every positive normalization gives o_p error for
the actual target, and infinite c makes that error identically zero. -/
theorem corrected_proposition3 {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hh : RootNNormal P hat (populationMean G τ)) :
    BoundedInProbability P (fun n ω => sqrtN n * (hat n ω - populationMean G τ)) ∧
    Consistent P hat (populationMean G τ) ∧
    (∀ a : ℕ → ℝ, (∀ n, 0 < a n) → LittleOp P
      (fun n ω => hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω)) a) ∧
    (effectRadius G τ = ⊤ → ∀ n ω,
      hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω) = 0) := by
  have hb := root_normal_tight_and_consistent P hat (populationMean G τ) hh
  refine ⟨hb.1, hb.2, ?_, ?_⟩
  · intro a ha
    by_cases hInfinity : effectRadius G τ = ⊤
    · intro η hη
      have he : ∀ n, {ω | |hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω)| > η * a n} = ∅ := by
        intro n
        ext ω
        simp [clipTarget, hInfinity, not_lt_of_ge (mul_pos hη (ha n)).le]
      simp only [he, pr, measureReal_empty]
      exact tendsto_const_nhds
    · simpa only [clipTarget, hInfinity, ↓reduceIte] using
        consistent_clipping_all_rates P hat (populationMean G τ) (effectRadius G τ).toReal
          (ENNReal.toReal_pos hc.ne' hInfinity) hb.2 a ha
  · intro hInfinity n ω
    simp [clipTarget, hInfinity]


/-- Exact support-bound step in Corollary 1 and P017-T4(iii): the printed
maximum condition forces every supported estimate into the stated interval. -/
theorem support_interval_of_condition (S : Set ℝ) (μ d : ℝ)
    (hcond : max (supportSup S - (μ : EReal)) ((μ : EReal) - supportInf S) ≤ (d : EReal)) :
    S ⊆ {x | |x - μ| ≤ d} := by
  intro x hx
  change |x - μ| ≤ d
  have hxL : supportInf S ≤ (x : EReal) := sInf_le ⟨x, hx, rfl⟩
  have hxU : (x : EReal) ≤ supportSup S := le_sSup ⟨x, hx, rfl⟩
  have hU := (le_max_left (supportSup S - (μ : EReal)) ((μ : EReal) - supportInf S)).trans hcond
  have hL := (le_max_right (supportSup S - (μ : EReal)) ((μ : EReal) - supportInf S)).trans hcond
  have hxUpper : (x : EReal) ≤ ((μ + d : ℝ) : EReal) := by
    have hh := (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot μ))
      (.inl (EReal.coe_ne_top μ))).mp hU
    simpa only [EReal.coe_add, add_comm] using hxU.trans hh
  have hxLower : ((μ - d : ℝ) : EReal) ≤ (x : EReal) := by
    have hh := (EReal.sub_le_iff_le_add (.inr (EReal.coe_ne_top d))
      (.inr (EReal.coe_ne_bot d))).mp hL
    have hld : ((μ - d : ℝ) : EReal) ≤ supportInf S := by
      rw [EReal.coe_sub, EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot d))
        (.inl (EReal.coe_ne_top d))]
      simpa only [add_comm] using hh
    exact hld.trans hxL
  have hu : x ≤ μ + d := EReal.coe_le_coe_iff.mp hxUpper
  have hl : μ - d ≤ x := EReal.coe_le_coe_iff.mp hxLower
  exact abs_le.mpr (by constructor <;> linarith)

/-- Corollary 1's support step gives an almost-sure interval event under the
actual sampling measure, not just a deterministic range restriction. -/
theorem support_interval_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : Ξ → ℝ) (hhm : Measurable hat)
    (μ d : ℝ) (hcond : max (supportSup (effectSupport P hat) - (μ : EReal))
      ((μ : EReal) - supportInf (effectSupport P hat)) ≤ (d : EReal)) :
    pr P {ω | |hat ω - μ| ≤ d} = 1 := by
  have hs : ∀ᵐ ω ∂P, hat ω ∈ effectSupport P hat :=
    ae_of_ae_map hhm.aemeasurable (Measure.support_mem_ae (μ := P.map hat))
  have hi : ∀ᵐ ω ∂P, |hat ω - μ| ≤ d :=
    hs.mono (fun ω hω => support_interval_of_condition _ μ d hcond hω)
  have hm : MeasurableSet {ω | |hat ω - μ| ≤ d} := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      measurableSet_le (hhm.sub (measurable_const : Measurable (fun _ : Ξ => μ))).norm
        (measurable_const : Measurable (fun _ : Ξ => d))
  have hp := (mem_ae_iff_prob_eq_one hm).mp hi
  simp only [pr, Measure.real, hp, ENNReal.toReal_one]

/-- P017-T10(a)–(c), corrected proof of Corollary 1, PDF p. 2: its support
condition gives interval probability one, equality probability one, and exact
equality of the two events. A zero interval probability would instead give
zero equality probability. Extended bounds include infinite c. -/
theorem corollary1_corrected {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : Ξ → ℝ) (hhm : Measurable hat)
    (hcond : max (supportSup (effectSupport P hat) - (populationMean G τ : EReal))
      ((populationMean G τ : EReal) - supportInf (effectSupport P hat)) ≤ (effectRadius G τ : EReal)) :
    (effectSupport P hat ⊆ {x | inside (populationMean G τ) (effectRadius G τ) x}) ∧
    pr P {ω | inside (populationMean G τ) (effectRadius G τ) (hat ω)} = 1 ∧
    {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} =
      {ω | inside (populationMean G τ) (effectRadius G τ) (hat ω)} ∧
    pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} = 1 ∧
    (pr P {ω | inside (populationMean G τ) (effectRadius G τ) (hat ω)} = 0 →
      pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} = 0) := by
  have heq : {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} =
      {ω | inside (populationMean G τ) (effectRadius G τ) (hat ω)} := by
    ext ω
    exact eq_comm.trans (clipTarget_eq_self_iff _ _ _)
  have hsub : effectSupport P hat ⊆ {x | inside (populationMean G τ) (effectRadius G τ) x} := by
    by_cases hInfinity : effectRadius G τ = ⊤
    · simp [inside, hInfinity]
    · intro x hx
      apply (ENNReal.ofReal_le_iff_le_toReal hInfinity).mpr
      apply support_interval_of_condition _ _ _ _ hx
      simpa only [EReal.coe_ennreal_toReal hInfinity] using hcond
  have hp : pr P {ω | inside (populationMean G τ) (effectRadius G τ) (hat ω)} = 1 := by
    by_cases hInfinity : effectRadius G τ = ⊤
    · simp [inside, hInfinity, pr]
    · have hcond' : max (supportSup (effectSupport P hat) - (populationMean G τ : EReal))
          ((populationMean G τ : EReal) - supportInf (effectSupport P hat)) ≤
          ((effectRadius G τ).toReal : EReal) := by
        simpa only [EReal.coe_ennreal_toReal hInfinity] using hcond
      simpa only [inside, ENNReal.ofReal_le_iff_le_toReal hInfinity] using
        support_interval_probability P hat hhm (populationMean G τ) (effectRadius G τ).toReal hcond'
  exact ⟨hsub, hp, heq, by rw [heq]; exact hp, fun h => by rw [heq]; exact h⟩

/-- P017-T4(iii): Corollary 1 for the repaired target uses d in its sufficient
support condition. The original condition with c is not substituted for it. -/
theorem interior_radius_corollary {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : Ξ → ℝ) (hhm : Measurable hat)
    (μ d : ℝ) (hd : 0 < d)
    (hcond : max (supportSup (effectSupport P hat) - (μ : EReal))
      ((μ : EReal) - supportInf (effectSupport P hat)) ≤ (d : EReal)) :
    pr P {ω | hat ω = clipReal μ d (hat ω)} = 1 := by
  have heq : {ω | hat ω = clipReal μ d (hat ω)} = {ω | |hat ω - μ| ≤ d} := by
    ext ω
    exact eq_comm.trans (clipReal_eq_self_iff μ d (hat ω) hd.le)
  rw [heq]
  exact support_interval_probability P hat hhm μ d hcond

/-- P017-T10(d), the first remark after Corollary 1: full real effect support
gives infinite radius, so every estimate equals its target in every realization. -/
theorem full_real_support {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hS : effectSupport G τ = univ) :
    effectRadius G τ = ⊤ ∧ ∀ x, clipTarget (populationMean G τ) (effectRadius G τ) x = x := by
  have hU : supportSup univ = ⊤ := by
    simp only [supportSup, image_univ]
    change sSup (range Real.toEReal) = ⊤
    rw [EReal.range_coe_eq_Ioo, csSup_Ioo (bot_lt_top : (⊥ : EReal) < ⊤)]
  have hL : supportInf univ = ⊥ := by
    simp only [supportInf, image_univ]
    change sInf (range Real.toEReal) = ⊥
    rw [EReal.range_coe_eq_Ioo, csInf_Ioo (bot_lt_top : (⊥ : EReal) < ⊤)]
  have hc : effectRadius G τ = ⊤ := by
    simp only [effectRadius, hS, hU, hL, EReal.top_sub_coe, EReal.coe_sub_bot,
      min_self, EReal.toENNReal_top]
  exact ⟨hc, fun x => by simp [clipTarget, hc]⟩

/-- P017-T10(e), the second remark: nonnegative unbounded effect support has
c = μ; a positive probability of negative estimates defeats exact equality. -/
theorem positive_support_negative_estimates {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hS : effectSupport G τ = Ici 0)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : Ξ → ℝ) (hhm : Measurable hat)
    (hneg : 0 < pr P {ω | hat ω < 0}) :
    effectRadius G τ = ENNReal.ofReal (populationMean G τ) ∧
    ¬ (max (supportSup (effectSupport P hat) - (populationMean G τ : EReal))
      ((populationMean G τ : EReal) - supportInf (effectSupport P hat)) ≤ (effectRadius G τ : EReal)) ∧
    pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} ≤
      1 - pr P {ω | hat ω < 0} ∧
    pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} < 1 := by
  have hU : supportSup (Ici 0) = ⊤ := by
    simp only [supportSup]
    change sSup (Real.toEReal '' Ici 0) = ⊤
    rw [EReal.image_coe_Ici, EReal.coe_zero, csSup_Ico (by simp : (0 : EReal) < ⊤)]
  have hL : supportInf (Ici 0) = 0 := by
    simp only [supportInf]
    change sInf (Real.toEReal '' Ici 0) = 0
    rw [EReal.image_coe_Ici, EReal.coe_zero, csInf_Ico (by simp : (0 : EReal) < ⊤)]
  have hc : effectRadius G τ = ENNReal.ofReal (populationMean G τ) := by
    simp only [effectRadius, hS, hU, hL, EReal.top_sub_coe, min_top_left, sub_zero,
      EReal.real_coe_toENNReal]
  have hτnon : ∀ᵐ ω ∂G, 0 ≤ τ ω := by
    have hs : ∀ᵐ ω ∂G, τ ω ∈ effectSupport G τ :=
      ae_of_ae_map hτm.aemeasurable (Measure.support_mem_ae (μ := G.map τ))
    simpa only [hS, mem_Ici] using hs
  have hμ : 0 ≤ populationMean G τ := integral_nonneg_of_ae hτnon
  have hsub : {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} ⊆
      {ω | hat ω < 0}ᶜ := by
    intro ω hω hnegative
    change hat ω < 0 at hnegative
    have hi := (clipTarget_eq_self_iff _ _ _).mp hω.symm
    have hab : |hat ω - populationMean G τ| ≤ populationMean G τ := by
      simpa only [inside, hc, ENNReal.ofReal_le_iff_le_toReal ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hμ] using hi
    have hl := (abs_le.mp hab).1
    linarith
  have hm : MeasurableSet {ω | hat ω < 0} := measurableSet_lt hhm measurable_const
  have hb : pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} ≤
      1 - pr P {ω | hat ω < 0} := by
    exact (measureReal_mono hsub).trans_eq (probReal_compl_eq_one_sub hm)
  have hlt : pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} < 1 := by
    linarith
  refine ⟨hc, ?_, hb, hlt⟩
  intro hcond
  have hp := (corollary1_corrected G τ hτm hτi P hat hhm hcond).2.2.2.1
  linarith


/-- P017-T13(a)–(b), repaired sentence after Proposition 3: the clipping
interval is exactly the zero-error event, and its probability tends to one.
The actual effect support need not equal this interval. -/
theorem corrected_zero_error_sentence {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hhm : ∀ n, Measurable (hat n)) (hh : RootNNormal P hat (populationMean G τ)) :
    (∀ n, {ω | inside (populationMean G τ) (effectRadius G τ) (hat n ω)} =
      {ω | hat n ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω)}) ∧
    Tendsto (fun n => pr P {ω | inside (populationMean G τ) (effectRadius G τ) (hat n ω)}) atTop (𝓝 1) := by
  refine ⟨?_, ?_⟩
  · intro n
    ext ω
    exact (clipTarget_eq_self_iff _ _ _).symm.trans eq_comm
  · by_cases hInfinity : effectRadius G τ = ⊤
    · simp only [inside, hInfinity, le_top, setOf_true, pr, probReal_univ]
      exact tendsto_const_nhds
    · have hcon := (root_normal_tight_and_consistent P hat (populationMean G τ) hh).2
      have hcR : 0 < (effectRadius G τ).toReal := ENNReal.toReal_pos hc.ne' hInfinity
      have heq : ∀ n, pr P {ω | inside (populationMean G τ) (effectRadius G τ) (hat n ω)} =
          1 - pr P {ω | |hat n ω - populationMean G τ| > (effectRadius G τ).toReal} := by
        intro n
        have hm : MeasurableSet {ω | |hat n ω - populationMean G τ| > (effectRadius G τ).toReal} := by
          simpa only [Real.norm_eq_abs, Pi.sub_apply] using
            measurableSet_lt
              (measurable_const : Measurable (fun _ : Ξ => (effectRadius G τ).toReal))
              ((hhm n).sub
                (measurable_const : Measurable (fun _ : Ξ => populationMean G τ))).norm
        have hs : {ω | inside (populationMean G τ) (effectRadius G τ) (hat n ω)} =
            {ω | |hat n ω - populationMean G τ| > (effectRadius G τ).toReal}ᶜ := by
          ext ω
          simp [inside, ENNReal.ofReal_le_iff_le_toReal hInfinity, not_lt]
        rw [hs]
        exact probReal_compl_eq_one_sub hm
      simp only [heq]
      simpa using tendsto_const_nhds.sub (hcon _ hcR)


/-- P017-T14, Proposition 3 as printed, PDF p. 2: under Assumption 1 and
Definition 1, the root-n-scaled error for the actual data-adaptive target
converges to zero in probability. The printed proof steps are not assumed. -/
theorem proposition3 {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hc : 0 < effectRadius G τ)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hh : RootNNormal P hat (populationMean G τ)) :
    LittleOp P (fun n ω => sqrtN n *
      (hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))) (fun _ => 1) := by
  intro η hη
  by_cases hInfinity : effectRadius G τ = ⊤
  · simp only [clipTarget, hInfinity, ↓reduceIte, sub_self, mul_zero, abs_zero, mul_one,
      not_lt_of_ge hη.le, setOf_false, pr, measureReal_empty]
    exact tendsto_const_nhds
  · have hcon := (root_normal_tight_and_consistent P hat (populationMean G τ) hh).2
    have hcR : 0 < (effectRadius G τ).toReal := ENNReal.toReal_pos hc.ne' hInfinity
    apply squeeze_zero (fun n => measureReal_nonneg) _ (hcon _ hcR)
    intro n
    refine measureReal_mono ?_ (measure_ne_top P _)
    intro ω hω
    change η * 1 < |sqrtN n *
      (hat n ω - clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))| at hω
    by_contra hout
    have hi : |hat n ω - populationMean G τ| ≤ (effectRadius G τ).toReal := le_of_not_gt hout
    have heq : clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω) = hat n ω := by
      simp only [clipTarget, hInfinity, ↓reduceIte]
      exact (clipReal_eq_self_iff _ _ _ hcR.le).mpr hi
    rw [heq, sub_self, mul_zero, abs_zero, mul_one] at hω
    exact (not_lt_of_ge hη.le) hω


/-- P017-T16, Proposition 2 as printed, PDF p. 2: the data-adaptive target
is within root-n stochastic order of the population mean. No positive-radius
assumption is added: constant effects (c=0) and infinite c are included. -/
theorem proposition2 {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
    (hh : RootNNormal P hat (populationMean G τ)) :
    BoundedInProbability P (fun n ω => sqrtN n *
      (clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω) - populationMean G τ)) := by
  intro ε hε
  obtain ⟨M, hM, htail⟩ := (root_normal_tight_and_consistent P hat (populationMean G τ) hh).1 ε hε
  refine ⟨M, hM, htail.mono ?_⟩
  intro n hn
  apply lt_of_le_of_lt _ hn
  refine measureReal_mono ?_ (measure_ne_top P _)
  intro ω hω
  change M < |sqrtN n *
    (clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω) - populationMean G τ)| at hω
  change M < |sqrtN n * (hat n ω - populationMean G τ)|
  have hd := clipTarget_distance (populationMean G τ) (effectRadius G τ) (hat n ω)
  have hmul := mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg (n : ℝ))
  have hω' : M < sqrtN n *
      |clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω) - populationMean G τ| := by
    simpa only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ)), sqrtN] using hω
  simpa only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ)), sqrtN] using
    lt_of_lt_of_le hω' hmul

/-- The equiprobable two-point law; not a definition
in the paper. P017-E001, P017-E002, P017-N001. -/
def fairPair (a b : ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac a + (1 / 2 : ℝ≥0∞) • Measure.dirac b

instance fairPair_probability (a b : ℝ) : IsProbabilityMeasure (fairPair a b) := by
  constructor
  norm_num [fairPair, Measure.add_apply, Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two

/-- P017-T1's Uniform(0,1) effect law, P017-E001.
Restriction of Lebesgue measure to (0,1) has total mass one. -/
def uniform01 : Measure ℝ := volume.restrict (Ioo 0 1)

instance uniform01_probability : IsProbabilityMeasure uniform01 := by
  constructor
  simp [uniform01, Real.volume_Ioo]

/-- P017-T1 full-data law: independent τ~Uniform(0,1), B=±1, T=0/1.
Coordinates are τ, (B,T); independence is imposed by the product measure. -/
def ipwPopulation : Measure (ℝ × (ℝ × ℝ)) :=
  uniform01.prod ((fairPair (-1) 1).prod (fairPair 0 1))

instance ipwPopulation_probability : IsProbabilityMeasure ipwPopulation := by
  unfold ipwPopulation
  infer_instance

/-- P017-T1: “Y(0)=B and Y(1)=B+τ” (P017-E001). -/
def ipwY0 (ω : ℝ × (ℝ × ℝ)) : ℝ := ω.2.1
/-- P017-T1: “Y(1)=B+τ”, P017-E001. -/
def ipwY1 (ω : ℝ × (ℝ × ℝ)) : ℝ := ω.2.1 + ω.1

/-- P017-T1: the unit effect is Y(1)−Y(0), not a new unrelated random variable. -/
def ipwEffect (ω : ℝ × (ℝ × ℝ)) : ℝ := ipwY1 ω - ipwY0 ω

/-- P017-T1: observed pair (T,Y) with Y=T Y(1)+(1−T)Y(0). -/
def ipwObserved (ω : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (ω.2.2, ω.2.2 * ipwY1 ω + (1 - ω.2.2) * ipwY0 ω)

/-- P017-T1: inverse-probability summand X=2TY−2(1−T)Y, defined even
when a sample has no treated units (P017-E001). -/
def ipwSummand (ω : ℝ × (ℝ × ℝ)) : ℝ :=
  2 * (ipwObserved ω).1 * (ipwObserved ω).2 -
    2 * (1 - (ipwObserved ω).1) * (ipwObserved ω).2

/-- IID units in the counterexamples; the infinite product is an actual
probability measure. Index i represents printed unit i+1. -/
def iidSamples {Ω : Type*} [MeasurableSpace Ω] (G : Measure Ω) : Measure (ℕ → Ω) :=
  Measure.infinitePi (fun _ : ℕ => G)

instance iidSamples_probability {Ω : Type*} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] : IsProbabilityMeasure (iidSamples G) := by
  unfold iidSamples
  infer_instance

/-- “F_n … an empirical distribution”, Section 2, PDF p. 1: the equally
weighted empirical law of the first n observed records. -/
def empiricalObserved {Ω D : Type*} [MeasurableSpace D]
    (O : Ω → D) (n : ℕ) (s : ℕ → Ω) : Measure D :=
  (1 / (n : ℝ≥0∞)) • ∑ i ∈ Finset.range n, Measure.dirac (O (s i))

/-- Estimators: the arithmetic mean of the first n summands. -/
def sampleMean {Ω : Type*} (X : Ω → ℝ) (n : ℕ) (s : ℕ → Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X (s i)) / (n : ℝ)

/-- P017-T1: the bad upper/lower endpoint sample events, every B_i=b and T_i=0. -/
def ipwBadEvent (b : ℝ) (n : ℕ) : Set (ℕ → ℝ × (ℝ × ℝ)) :=
  {s | ∀ i ∈ Finset.range n, (s i).2.1 = b ∧ (s i).2.2 = 0}

/-- P017-T1(c),(f), exact positive event probabilities for the actual product
sampling law: either all-control/all-B event has probability 4^(-n). -/
theorem ipw_bad_event_probability (b : ℝ) (hb : b = -1 ∨ b = 1) (n : ℕ) :
    pr (iidSamples ipwPopulation) (ipwBadEvent b n) = (1 / 4 : ℝ) ^ n := by
  let A : Set (ℝ × (ℝ × ℝ)) := univ ×ˢ ({b} ×ˢ {0})
  have hm : MeasurableSet A := MeasurableSet.univ.prod
    ((measurableSet_singleton b).prod (measurableSet_singleton 0))
  have heq : ipwBadEvent b n = Set.pi (↑(Finset.range n)) (fun _ => A) := by
    ext s
    simp [ipwBadEvent, Set.mem_pi, A, Prod.ext_iff]
  have hA : ipwPopulation A = (1 / 4 : ℝ≥0∞) := by
    simp only [ipwPopulation, A, Measure.prod_prod, measure_univ, one_mul]
    rcases hb with rfl | rfl <;>
      norm_num [fairPair, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply] <;>
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
      norm_num
  unfold pr Measure.real iidSamples
  rw [heq, Measure.infinitePi_pi _ (fun _ _ => hm)]
  simp only [hA, Finset.prod_const, Finset.card_range, ENNReal.toReal_pow]
  norm_num

/-- P017-T1(c),(f), the estimator on each bad event equals the explicit
number 2 or −2; this is not an arbitrary externally assigned estimate. -/
theorem ipw_bad_event_estimator (b : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (s : ℕ → ℝ × (ℝ × ℝ)) (hs : s ∈ ipwBadEvent b n) :
    sampleMean ipwSummand n s = -2 * b := by
  have hX : ∀ i ∈ Finset.range n, ipwSummand (s i) = -2 * b := by
    intro i hi
    rcases hs i hi with ⟨hB, hT⟩
    simp [ipwSummand, ipwObserved, ipwY0, ipwY1, hB, hT]
  have hsum : (∑ i ∈ Finset.range n, ipwSummand (s i)) = (n : ℝ) * (-2 * b) := by
    calc
      _ = ∑ i ∈ Finset.range n, -2 * b := Finset.sum_congr rfl hX
      _ = _ := by simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn))
  simp only [sampleMean, hsum]
  field_simp

/-- P017-T1: the upper and lower bad events are disjoint at every positive size. -/
theorem ipw_bad_events_disjoint (n : ℕ) (hn : 1 ≤ n) :
    Disjoint (ipwBadEvent (-1) n) (ipwBadEvent 1 n) := by
  rw [Set.disjoint_left]
  intro s hu hl
  have h0 : 0 ∈ Finset.range n := Finset.mem_range.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha := (hu 0 h0).1
  have hb := (hl 0 h0).1
  linarith


/-- P017-T5/T6's full-data law at μ=0: independent X~N(0,1) and R=±1,
with Y(0)=0, Y(1)=R, effect R, and observed X. P017-E002. -/
def normalPopulation : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (fairPair (-1) 1)

instance normalPopulation_probability : IsProbabilityMeasure normalPopulation := by
  unfold normalPopulation
  infer_instance

/-- P017-T5/T6: “Y_i(0)=0”, P017-E002. -/
def normalY0 (_ : ℝ × ℝ) : ℝ := 0
/-- P017-T5/T6: “Y_i(1)=μ+R_i”, evaluated at μ=0, P017-E002. -/
def normalY1 (ω : ℝ × ℝ) : ℝ := ω.2
/-- P017-T5/T6: the effect Y(1)−Y(0), P017-E002. -/
def normalEffect (ω : ℝ × ℝ) : ℝ := normalY1 ω - normalY0 ω

/-- P017-T5/T6: “tildeθ_n = bar X_n”, P017-E002. -/
def normalMean (n : ℕ) (s : ℕ → ℝ × ℝ) : ℝ := sampleMean Prod.fst n s

/-- P017-T5/T6: “hatθ_n = bar X_n + 1/n”, a statistic of the observed X sample. -/
def shiftedNormalMean (n : ℕ) (s : ℕ → ℝ × ℝ) : ℝ := normalMean n s + 1 / (n : ℝ)

/-- P017-T5/T6: “D_n = tildeθ_n − θ_Fn”; θ_Fn clips the perturbed estimate. -/
def shiftedDifference (n : ℕ) (s : ℕ → ℝ × ℝ) : ℝ :=
  normalMean n s - clipReal 0 1 (shiftedNormalMean n s)

/-- P017-T5/T6: the exactly normal Z_n and the deterministic ε_n=n^(-1/2). -/
def normalZ (n : ℕ) (s : ℕ → ℝ × ℝ) : ℝ := sqrtN n * normalMean n s
/-- P017-T5/T6: “ε_n=n^(-1/2)”, P017-E002. -/
def normalEpsilon (n : ℕ) (_ : ℕ → ℝ × ℝ) : ℝ := 1 / sqrtN n

/-- P017-T6's remainder hypothesis, verified without assuming any normal-tail
bound: E[ε_n²]=1/n and sqrt(n) E[ε_n²]→0 for the actual constant ε_n. -/
theorem normal_shift_remainder_ms :
    (∀ n : ℕ, 1 ≤ n → (∫ s, normalEpsilon n s ^ 2 ∂iidSamples normalPopulation) = 1 / (n : ℝ)) ∧
    SmallRemainderMS (iidSamples normalPopulation) normalEpsilon := by
  have hInt : ∀ n, (∫ s, normalEpsilon n s ^ 2 ∂iidSamples normalPopulation) = (1 / sqrtN n) ^ 2 := by
    intro n
    simp [normalEpsilon]
  constructor
  · intro n hn
    rw [hInt n, div_pow, one_pow, sqrtN, Real.sq_sqrt (Nat.cast_nonneg n)]
  · have hid : ∀ n, sqrtN n * (1 / sqrtN n) ^ 2 = 1 / sqrtN n := by
      intro n
      by_cases h : sqrtN n = 0
      · simp [h]
      · field_simp
    unfold SmallRemainderMS
    simp only [hInt, hid]
    simpa only [one_div, sqrtN, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))

/-- P017-T5(a)–(b), finite algebra: any positive shift makes the printed
intermediate difference zero only when the unperturbed estimate equals 1. -/
theorem shifted_clip_zero_iff (x δ : ℝ) (hδ : 0 < δ) :
    x - clipReal 0 1 (x + δ) = 0 ↔ x = 1 := by
  simp only [clipReal, min_def, max_def]
  split_ifs <;> constructor <;> intro h <;> linarith

/-- P017-T6(a), exact algebra at n=25: on |tildeθ|≤1/2 the target is the
perturbed estimate and its squared difference from tildeθ is 1/625, not zero. -/
theorem shifted_25_central (x : ℝ) (hx : |x| ≤ 1 / 2) :
    -(23 / 50 : ℝ) ≤ x + 1 / 25 ∧ x + 1 / 25 ≤ 27 / 50 ∧
    clipReal 0 1 (x + 1 / 25) = x + 1 / 25 ∧
    (x - clipReal 0 1 (x + 1 / 25)) ^ 2 = 1 / 625 := by
  rcases abs_le.mp hx with ⟨hl, hu⟩
  have ht : clipReal 0 1 (x + 1 / 25) = x + 1 / 25 :=
    (clipReal_eq_self_iff 0 1 (x + 1 / 25) (by norm_num)).mpr
      (abs_le.mpr (by constructor <;> linarith))
  refine ⟨by linarith, by linarith, ht, ?_⟩
  rw [ht]
  ring


/-- P017-T12's independent Uniform[0,1) component, P017-N001. -/
def uniformHalfOpen01 : Measure ℝ := volume.restrict (Ico 0 1)

instance uniformHalfOpen01_probability : IsProbabilityMeasure uniformHalfOpen01 := by
  constructor
  simp [uniformHalfOpen01, Real.volume_Ico]

/-- P017-T12's effect noise: 1/4 δ_(-1) + 1/4 δ_1 + 1/2 Uniform[-1,1].
The last summand is 1/4 times Lebesgue restriction, giving continuous mass 1/2. -/
def slowEffectLaw : Measure ℝ :=
  (1 / 4 : ℝ≥0∞) • Measure.dirac (-1) + (1 / 4 : ℝ≥0∞) • Measure.dirac 1 +
    (1 / 4 : ℝ≥0∞) • volume.restrict (Icc (-1) 1)

instance slowEffectLaw_probability : IsProbabilityMeasure slowEffectLaw := by
  constructor
  norm_num [slowEffectLaw, Measure.add_apply, Measure.smul_apply, Real.volume_Icc]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- P017-T12 full-data law: mutually independent X~N(0,1), U~Uniform[0,1),
effect V~slowEffectLaw, D~Bernoulli(1/2). Coordinates X,(U,(V,D)). -/
def slowPopulation : Measure (ℝ × (ℝ × (ℝ × ℝ))) :=
  (gaussianReal 0 1).prod (uniformHalfOpen01.prod (slowEffectLaw.prod (fairPair 0 1)))

instance slowPopulation_probability : IsProbabilityMeasure slowPopulation := by
  unfold slowPopulation
  infer_instance

/-- P017-T12: “Y_i(0)=0”, P017-N001. -/
def slowY0 (_ : ℝ × (ℝ × (ℝ × ℝ))) : ℝ := 0
/-- P017-T12: “Y_i(1)=μ+V_i”, evaluated at μ=0, P017-N001. -/
def slowY1 (ω : ℝ × (ℝ × (ℝ × ℝ))) : ℝ := ω.2.2.1
/-- P017-T12: the effect Y(1)−Y(0), P017-N001. -/
def slowEffect (ω : ℝ × (ℝ × (ℝ × ℝ))) : ℝ := slowY1 ω - slowY0 ω


/-- P017-T12: “W_n = {sum U_i}”, the fractional part (not a single chosen unit). -/
def rareUniform (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  Int.fract (∑ i ∈ Finset.range n, (s i).2.1)

/-- P017-T12: “B_n = 1{W_n < p_n}”, symmetric in the first n unit records. -/
def rareFlag (p : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  if rareUniform n s < p n then 1 else 0

/-- P017-T12: “bar X_n”, the untruncated arithmetic mean of the normal coordinates. -/
def smallNormalMean (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  sampleMean Prod.fst n s
/-- P017-T12: “A_n=max(-1/2,min(bar X_n,1/2))”, P017-N001. -/
def smallNormalClip (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  clipReal 0 (1 / 2) (smallNormalMean n s)

/-- P017-T12: “hatθ_n = A_n + 10 B_n”. -/
def rareEstimator (p : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  smallNormalClip n s + 10 * rareFlag p n s

/-- P017-T12(c): exact decomposition remainder
“ε_n = sqrt(n)(A_n − bar X_n + 10 B_n)”. -/
def rareRemainder (p : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  sqrtN n * (smallNormalClip n s - smallNormalMean n s + 10 * rareFlag p n s)

/-- P017-T12(e): “p_n = 1/(1+floor(log_2 n))”. Nat.log is the integer
floor of the base-2 logarithm for n≥1. -/
def slowP (n : ℕ) : ℝ := 1 / ((1 + Nat.log 2 n : ℕ) : ℝ)

/-- P017-T12(e), small exact certificates for the concrete probabilities;
the powers bound Nat.log without enumerating either large sample size. -/
theorem slow_probability_numbers :
    slowP 1000 = 1 / 10 ∧ slowP (10 ^ 12) = 1 / 40 ∧
    ∀ k : ℕ, slowP (2 ^ k) = 1 / ((k + 1 : ℕ) : ℝ) := by
  have h9 : Nat.log 2 1000 = 9 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h39 : Nat.log 2 (10 ^ 12) = 39 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  refine ⟨by norm_num [slowP, h9], by norm_num [slowP, h39], ?_⟩
  intro k
  simp only [slowP, Nat.log_pow (by norm_num : 1 < 2), Nat.add_comm]

/-- P017-T12's concrete sequence satisfies the required positive-probability
and vanishing-probability conditions; its logarithm is handled by power bounds. -/
theorem slow_probability_positive_limit :
    (∀ n : ℕ, 0 < slowP n ∧ slowP n ≤ 1) ∧ Tendsto slowP atTop (𝓝 0) := by
  constructor
  · intro n
    have hden : (1 : ℝ) ≤ ((1 + Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 1 + Nat.log 2 n)
    constructor
    · exact one_div_pos.mpr (by linarith)
    · simpa only [slowP, div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  · have hlog : Tendsto (fun n : ℕ => Nat.log 2 n) atTop atTop := by
      apply tendsto_atTop_atTop.mpr
      intro k
      exact ⟨2 ^ k, fun n hn => Nat.le_log_of_pow_le (by norm_num) hn⟩
    have hden : Tendsto (fun n : ℕ => ((1 + Nat.log 2 n : ℕ) : ℝ)) atTop atTop :=
      tendsto_atTop_mono (fun n => by
        dsimp only [Function.comp_def]
        exact_mod_cast (by omega : Nat.log 2 n ≤ 1 + Nat.log 2 n))
        (tendsto_natCast_atTop_atTop.comp hlog)
    unfold slowP
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hden

/-- P017-T12(d), finite algebra: B=0 gives zero error; B=1 gives target 1
and error A+9 in [17/2,19/2]. These bounds hold for every normal input. -/
theorem rare_estimator_finite (x : ℝ) :
    let A := clipReal 0 (1 / 2) x
    clipReal 0 1 A = A ∧
    (19 / 2 : ℝ) ≤ A + 10 ∧ A + 10 ≤ 21 / 2 ∧
    clipReal 0 1 (A + 10) = 1 ∧
    (17 / 2 : ℝ) ≤ A + 9 ∧ A + 9 ≤ 19 / 2 := by
  dsimp
  have hb := clipReal_bounds 0 (1 / 2) x (by norm_num)
  have hid : clipReal 0 1 (clipReal 0 (1 / 2) x) = clipReal 0 (1 / 2) x :=
    (clipReal_eq_self_iff _ _ _ (by norm_num)).mpr
      (abs_le.mpr (by constructor <;> linarith [hb.1, hb.2]))
  have htop : clipReal 0 1 (clipReal 0 (1 / 2) x + 10) = 1 := by
    simp only [clipReal, min_def, max_def]
    split_ifs <;> linarith [hb.1, hb.2]
  exact ⟨hid, by linarith [hb.1], by linarith [hb.2], htop,
    by linarith [hb.1], by linarith [hb.2]⟩


end
end AronowAudit.P017



