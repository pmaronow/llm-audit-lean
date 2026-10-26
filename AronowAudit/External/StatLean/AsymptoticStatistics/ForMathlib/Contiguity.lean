/-
Documentation corrected for llm-audit-lean.
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Contiguity of sequences of probability measures

Contiguity (van der Vaart §6.3-§6.7), weak convergence, and Le Cam's third
lemma under asymptotic density comparison.

Main declarations:
* `WeakConverges` — test-function-based weak convergence of measures.
* `Contiguous` — contiguity of measure sequences.
* `uniform_integrability_exp_L_of_integral_tendsto_one` — uniform integrability
  under asymptotic exponential normalization.
* `weak_limit_under_Q_of_lecam_third_of_integral_comparison` — Le Cam's third
  lemma from an integral-comparison bound (vdV Theorem 6.6).
-/

set_option linter.style.longFile 3800

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- Weak convergence of a sequence of probability measures (convergence in law).

Test-function characterization: for every bounded continuous real-valued `f`, the
`f`-integrals converge. Equivalent to convergence in the weak topology on
`MeasureTheory.ProbabilityMeasure E`, but given in unpacked form for convenience. -/
def WeakConverges {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))

/-- **Continuous mapping theorem for weak convergence**: if `μ_n` weakly converges to
`ν` on `E` and `f : E → F` is continuous and measurable, then the pushforwards by `f`
weakly converge to the pushforward of the limit. Standard application of
`BoundedContinuousFunction.compContinuous` + `integral_map`. -/
lemma WeakConverges.map {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSpace F] [TopologicalSpace F] [PseudoMetricSpace F]
    [OpensMeasurableSpace F]
    {μ : ℕ → Measure E} {ν : Measure E}
    (hμν : WeakConverges μ ν) {f : E → F}
    (hf_cont : Continuous f) (hf_meas : Measurable f) :
    WeakConverges (fun n => (μ n).map f) (ν.map f) := by
  intro g
  -- `g ∘ f` is a bounded continuous function on `E`.
  let g_comp_f : E →ᵇ ℝ := g.compContinuous ⟨f, hf_cont⟩
  -- Both `∫ g d(μ.map f)` and `∫ g d(ν.map f)` rewrite to `∫ (g ∘ f) dμ` / `∫ (g ∘ f) dν`.
  have h_rewrite : ∀ ρ : Measure E,
      ∫ y, g y ∂(ρ.map f) = ∫ x, g_comp_f x ∂ρ := by
    intro ρ
    rw [MeasureTheory.integral_map hf_meas.aemeasurable
      g.continuous.aestronglyMeasurable]
    rfl
  simp_rw [h_rewrite]
  exact hμν g_comp_f

/-- **Subsequence preservation** of weak convergence. If `μ_n ⇝ ν` and `φ : ℕ → ℕ`
is strictly monotone, then `μ_{φ k} ⇝ ν`. -/
lemma WeakConverges.comp {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    {μ : ℕ → Measure E} {ν : Measure E}
    (h : WeakConverges μ ν) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeakConverges (fun k => μ (φ k)) ν :=
  fun f => (h f).comp hφ.tendsto_atTop

/-- **Weak-limit uniqueness** on a Polish-adjacent Borel space. If a sequence of
measures weakly converges to two finite measures, they agree. Pure consequence of
`ext_of_forall_integral_eq_of_IsFiniteMeasure` + `tendsto_nhds_unique`. -/
lemma WeakConverges.unique
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    [HasOuterApproxClosed E]
    {μ : ℕ → Measure E} {ν ν' : Measure E}
    [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h₁ : WeakConverges μ ν) (h₂ : WeakConverges μ ν') :
    ν = ν' :=
  MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
    (fun f => tendsto_nhds_unique (h₁ f) (h₂ f))

/-- **Marginal weak-limit identification**. If `μ_n ⇝ π` jointly on `E × F` and
`(μ_n.map snd) ⇝ ν` on `F`, then `π.map Prod.snd = ν`. Proof: continuous-mapping
gives `(μ_n.map snd) ⇝ π.map snd`, then apply weak-limit uniqueness. -/
lemma WeakConverges.snd_eq
    {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSpace F] [TopologicalSpace F] [PseudoMetricSpace F]
    [BorelSpace F] [HasOuterApproxClosed F]
    {μ : ℕ → Measure (E × F)} {π : Measure (E × F)} [IsFiniteMeasure π]
    {ν : Measure F} [IsFiniteMeasure ν]
    (hπ : WeakConverges μ π)
    (hν : WeakConverges (fun n => (μ n).map Prod.snd) ν) :
    π.map Prod.snd = ν :=
  have : IsFiniteMeasure (π.map Prod.snd) :=
    MeasureTheory.Measure.isFiniteMeasure_map π Prod.snd
  WeakConverges.unique (hπ.map continuous_snd measurable_snd) hν


/-- **Commuting `withDensity` past `Measure.map`**:
`(μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ`, for measurable `φ` and `h`.

Useful for pushing a density through a measurable pushforward — e.g., when a joint
law `π_tilted = π.map φ` is `withDensity`-ed against a function `h` that factors
through `φ`, the calculation can be pulled back to `π` under the composed density. -/
lemma Measure.withDensity_map_eq_map_withDensity
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : MeasureTheory.Measure α) (φ : α → β) (hφ : Measurable φ)
    (h : β → ℝ≥0∞) (hh : Measurable h) :
    (μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ := by
  refine MeasureTheory.Measure.ext (fun A hA => ?_)
  rw [MeasureTheory.withDensity_apply _ hA,
      MeasureTheory.Measure.map_apply hφ hA,
      MeasureTheory.withDensity_apply _ (hφ hA),
      MeasureTheory.setLIntegral_map hA hh hφ]
  rfl


namespace Contiguity

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- **Contiguity** (van der Vaart §6.3). A family `Q` is contiguous with respect to `P`
along filter `l` (written informally `Q ⊲ P`) if any sequence of measurable events whose
`P`-probabilities tend to 0 also has `Q`-probabilities tending to 0. -/
def Contiguous (l : Filter ι) (P Q : ∀ i, Measure (Ω i)) : Prop :=
  ∀ A : ∀ i, Set (Ω i), (∀ i, MeasurableSet (A i)) →
    Tendsto (fun i => (P i) (A i)) l (𝓝 0) →
    Tendsto (fun i => (Q i) (A i)) l (𝓝 0)

/-- **Mutual contiguity**: both directions. -/
def MutuallyContiguous (l : Filter ι) (P Q : ∀ i, Measure (Ω i)) : Prop :=
  Contiguous l P Q ∧ Contiguous l Q P


lemma Contiguous.trans {l : Filter ι} {P Q R : ∀ i, Measure (Ω i)}
    (h₁ : Contiguous l P Q) (h₂ : Contiguous l Q R) :
    Contiguous l P R := fun A hA hP => h₂ A hA (h₁ A hA hP)

lemma MutuallyContiguous.symm {l : Filter ι} {P Q : ∀ i, Measure (Ω i)}
    (h : MutuallyContiguous l P Q) : MutuallyContiguous l Q P :=
  ⟨h.2, h.1⟩




/-! ## Le Cam's first lemma — asymptotic log normality criterion

vdV Example 6.5. If the log-likelihood ratio `log dQ_n/dP_n` is asymptotically normal
under `P_n` with mean `-σ²/2` and variance `σ²`, then `P_n ⊲⊳ Q_n`.

The criterion involves uniform integrability of the likelihood ratio and
the corresponding reverse log-likelihood ratio under `Q`.
-/

section LeCamFirst

/-- **Gaussian mgf at 1**: `∫ exp(x) dN(-v/2, v) = 1`. This is the multiplicative
normalization underlying Le Cam 1 — if `W ~ N(-v/2, v)`, then `E[exp W] = 1`, which is
exactly what keeps the likelihood ratio's mass normalized. -/
private lemma integral_exp_gaussianReal_neg_half_var (v : NNReal) :
    ∫ x, Real.exp x ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) = 1 := by
  have hX :
      Measure.map (id : ℝ → ℝ) (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)
        = ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v :=
    Measure.map_id
  have h := ProbabilityTheory.mgf_gaussianReal ⟨aemeasurable_id, hX⟩ 1
  rw [ProbabilityTheory.mgf] at h
  simp only [one_mul, id_eq] at h
  rw [show (-(v : ℝ) / 2 * 1 + (v : ℝ) * 1 ^ 2 / 2 : ℝ) = 0 by ring, Real.exp_zero] at h
  exact h

/-- Truncated exponential `min(exp x, M)` as a bounded continuous function, for `M ≥ 0`. -/
private noncomputable def truncExpBCF (M : ℝ) (hM : 0 ≤ M) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (Real.exp x) M)
    (Real.continuous_exp.min continuous_const)
    M
    (fun x => by
      rw [Real.norm_eq_abs]
      have h_nonneg : 0 ≤ min (Real.exp x) M :=
        le_min (Real.exp_pos x).le hM
      rw [abs_of_nonneg h_nonneg]
      exact min_le_right _ _)

@[simp] private lemma truncExpBCF_apply (M : ℝ) (hM : 0 ≤ M) (x : ℝ) :
    truncExpBCF M hM x = min (Real.exp x) M := rfl

/-- As `M → ∞` (over naturals), `∫ min(exp x, M) dN(-v/2, v) → 1`.

Dominated convergence: `min(exp x, M) ↑ exp x` pointwise, dominated by `exp x` which is
integrable under the log-normal-tilt Gaussian (mgf exists at 1). The limit equals
`∫ exp = 1` by the Gaussian mgf. -/
private lemma tendsto_integral_truncExp_gaussianReal (v : NNReal) :
    Tendsto
      (fun M : ℕ =>
        ∫ x, min (Real.exp x) (M : ℝ) ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))
      atTop (𝓝 1) := by
  set ν : Measure ℝ := ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v with hν_def
  have h_exp_int : Integrable (fun x => Real.exp x) ν := by
    have := ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := -(v : ℝ) / 2) (v := v) 1
    simpa using this
  have h_lim : ∀ᵐ x ∂ν,
      Tendsto (fun M : ℕ => min (Real.exp x) (M : ℝ)) atTop (𝓝 (Real.exp x)) := by
    refine Eventually.of_forall (fun x => ?_)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈Real.exp x⌉₊] with M hM
    have : Real.exp x ≤ (M : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hM)
    exact (min_eq_left this).symm
  have h_dom : ∀ M : ℕ, ∀ᵐ x ∂ν, ‖min (Real.exp x) (M : ℝ)‖ ≤ Real.exp x := by
    intro M
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    have h_nonneg : 0 ≤ min (Real.exp x) (M : ℝ) :=
      le_min (Real.exp_pos x).le (Nat.cast_nonneg _)
    rw [abs_of_nonneg h_nonneg]
    exact min_le_left _ _
  have h_meas : ∀ M : ℕ, AEStronglyMeasurable (fun x => min (Real.exp x) (M : ℝ)) ν :=
    fun M => (Real.continuous_exp.min continuous_const).aestronglyMeasurable
  have h_tendsto :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (F := fun M x =>
      min (Real.exp x) (M : ℝ)) (f := fun x => Real.exp x) (bound := fun x => Real.exp x)
      h_meas h_exp_int h_dom h_lim
  rw [integral_exp_gaussianReal_neg_half_var] at h_tendsto
  exact h_tendsto


/-- **For fixed `M ≥ 0`, weak convergence transfers to integrals of the truncated
exponential**: `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN(-v/2, v)` as `n → ∞`.

Follows from `WeakConverges` applied to `truncExpBCF M`, after rewriting the map-integral
via `MeasureTheory.integral_map`. -/
private lemma tendsto_integral_truncExp_L
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))
    (M : ℝ) (hM : 0 ≤ M) :
    Tendsto
      (fun n => ∫ ω, min (Real.exp (L n ω)) M ∂(P n)) atTop
      (𝓝 (∫ x, min (Real.exp x) M ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))) := by
  have h_bcf := h_weak (truncExpBCF M hM)
  -- Use `integral_map` to swap `(P n).map (L n)` integrals back to integrals in `P n`.
  have h_map_n : ∀ n,
      ∫ x, truncExpBCF M hM x ∂((P n).map (L n))
        = ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    intro n
    rw [MeasureTheory.integral_map (hL_meas n).aemeasurable
        (truncExpBCF M hM).continuous.aestronglyMeasurable]
    simp
  simp only [h_map_n] at h_bcf
  simpa using h_bcf


end LeCamFirst

section ReverseDirection


/-! ### Gaussian shift identity

Tilting `N(-v/2, v)` by `exp` yields `N(v/2, v)`; reflecting `N(v/2, v)`
through zero yields `N(-v/2, v)`. The resulting integral identity is
`∫ f(-x) · exp(x) dN(-v/2, v) = ∫ f(y) dN(-v/2, v)`.
-/


end ReverseDirection





/-! ## Le Cam variants under asymptotic density comparison

The two lemmas below replace the **exact** change-of-measure
hypothesis `hL_is_log_ratio` (`Q n = (P n).withDensity (exp ∘ L n)`, which forces absolute
continuity) by asymptotic data: an integral-comparison bound with
vanishing slack and a mass hypothesis `∫ exp(L n) dP_n → 1`. Their conclusions agree
with the exact-density formulations. -/

/-- **Uniform-integrability of `exp(L n)` from `∫ exp(L n) dP_n → 1`.**

The exact identity `hL_is_log_ratio` is replaced by integrability of
`exp(L n)` and the asymptotic normalization `∫ exp(L n) dP_n → 1`.
These hypotheses require finite exponential integrals tending to one; they do not
require each tilted measure to have mass at most one or control the singular mass
of `Q n` relative to `P n`. Such interpretations require additional
likelihood-comparison assumptions.

The proof uses Gaussian truncation. The exact term `1 − ∫min` becomes
`(∫ exp(L n) dP_n) − ∫min = (1 + δₙ) − ∫min`. Split ε across the `δₙ` slack and the
truncation gap; `δₙ = o(1)` is absorbable but must be carried explicitly (UI only needs
`≤ ε` eventually). -/
lemma uniform_integrability_exp_L_of_integral_tendsto_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    -- Each exponential integral is finite.
    (h_exp_int : ∀ n, Integrable (fun ω => Real.exp (L n ω)) (P n))
    -- The exponential integrals tend to one.
    (h_mass : Tendsto (fun n => ∫ ω, Real.exp (L n ω) ∂(P n)) atTop (𝓝 1))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε := by
  intro ε hε
  -- Step 1: pick a natural M₀ with `∫ min(exp, M₀) dN ≥ 1 - ε/4`.
  have h_gaussian := tendsto_integral_truncExp_gaussianReal v
  have h_ev :
      ∀ᶠ M : ℕ in atTop,
        1 - ε / 4 ≤
          ∫ x, min (Real.exp x) (M : ℝ)
            ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
    have h_mem : Set.Ici (1 - ε / 4) ∈ 𝓝 (1 : ℝ) :=
      Ici_mem_nhds (by linarith)
    exact h_gaussian h_mem
  obtain ⟨M₀, hM₀⟩ := h_ev.exists
  set M : ℝ := (M₀ : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨M, hM_nonneg, ?_⟩
  -- Step 2: for fixed M, get `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN`.
  have h_trunc_tendsto :=
    tendsto_integral_truncExp_L P L hL_meas v h_weak M hM_nonneg
  -- Step 3a: pick N₁ so that for n ≥ N₁, `∫ min(exp(L n), M) dP_n ≥ 1 - ε/2`.
  have h_target :
      ∀ᶠ n : ℕ in atTop,
        1 - ε / 2 ≤ ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    have h_mem : Set.Ioi (1 - ε / 2) ∈ 𝓝 (∫ x, min (Real.exp x) M
        ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) := by
      apply Ioi_mem_nhds
      linarith [hM₀]
    filter_upwards [h_trunc_tendsto h_mem] with n hn
    exact le_of_lt (Set.mem_Ioi.mp hn)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_target
  -- Step 3b: from `h_mass`, pick N₂ so that for n ≥ N₂, `∫ exp(L n) dP_n ≤ 1 + ε/2`.
  have h_mass_ub :
      ∀ᶠ n : ℕ in atTop,
        ∫ ω, Real.exp (L n ω) ∂(P n) ≤ 1 + ε / 2 := by
    have h_mem : Set.Iic (1 + ε / 2) ∈ 𝓝 (1 : ℝ) :=
      Iic_mem_nhds (by linarith)
    filter_upwards [h_mass h_mem] with n hn
    exact Set.mem_Iic.mp hn
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp h_mass_ub
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  -- Step 4: rearrange using `∫ exp(L n) dP_n ≤ 1 + ε/2` and `∫min ≥ 1 - ε/2`.
  have h_exp_int_n := h_exp_int n
  have h_trunc_int : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int_n.mono' ?_ ?_
    · exact ((Real.continuous_exp.measurable.comp
        (hL_meas n)).min measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact min_le_left _ _
      · exact le_min (Real.exp_pos _).le hM_nonneg
  have h_diff_eq :
      ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        = (∫ ω, Real.exp (L n ω) ∂(P n))
          - ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    rw [MeasureTheory.integral_sub h_exp_int_n h_trunc_int]
  rw [h_diff_eq]
  linarith [hN₁ n hn₁, hN₂ n hn₂]

/-- **Le Cam's third lemma from an integral-comparison bound.**

Assume the integral-comparison hypothesis `h_integral_comparison`:
for some `ρ → 0` and every bounded continuous `f`,
`|∫ f(X n) dQ_n − ∫ f(X n)·exp(L n) dP_n| ≤ ‖f‖·ρ_n`. The vanishing
slack does not affect the weak limit.

The proof combines bounded-continuous truncation, the residue estimate, the
target-side dominated-convergence argument, and an ε/4 bound for the
integral-comparison error. -/
theorem weak_limit_under_Q_of_lecam_third_of_integral_comparison
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (X : ∀ n, Ω n → E) (L : ∀ n, Ω n → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) (hL_meas : ∀ n, Measurable (L n))
    -- Asymptotic integral comparison without a common-support assumption.
    (h_integral_comparison :
      ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
        ∀ (f : E →ᵇ ℝ) (n : ℕ),
          |∫ ω, f (X n ω) ∂(Q n)
            - ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)| ≤ ‖f‖ * ρ n)
    (π : Measure (E × ℝ)) [IsProbabilityMeasure π]
    (h_joint_weak :
      WeakConverges (fun n => (P n).map (fun ω => (X n ω, L n ω))) π)
    (h_UI : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε)
    (h_exp_int_π : Integrable (fun p : E × ℝ => Real.exp p.2) π)
    (h_exp_int_π_eq_one : ∫ p, Real.exp p.2 ∂π = 1) :
    WeakConverges (fun n => (Q n).map (X n))
      ((π.withDensity (fun p => ENNReal.ofReal (Real.exp p.2))).map Prod.fst) := by
  intro f
  -- Rewrite RHS (target integral over tilted marginal) as ∫ f(p.1)·exp(p.2) dπ.
  have h_target_rewrite : ∫ x, f x ∂((π.withDensity
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2))).map Prod.fst)
      = ∫ p, f p.1 * Real.exp p.2 ∂π := by
    have h_exp_meas_snd : Measurable (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2)) :=
      (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
    have h_exp_lt_top : ∀ᵐ p ∂π, ENNReal.ofReal (Real.exp p.2) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable
        f.continuous.aestronglyMeasurable]
    rw [integral_withDensity_eq_integral_toReal_smul h_exp_meas_snd h_exp_lt_top
        (fun p => f p.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    change (ENNReal.ofReal (Real.exp p.2)).toReal • f p.1 = f p.1 * Real.exp p.2
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
  rw [h_target_rewrite]
  -- Map-integral identities: `bₙ` (under `Q n`) and `aₙ` (under `P n`, tilted).
  have h_bn_map : ∀ n, ∫ x, f x ∂((Q n).map (X n)) = ∫ ω, f (X n ω) ∂(Q n) := fun n =>
    MeasureTheory.integral_map (hX_meas n).aemeasurable f.continuous.aestronglyMeasurable
  have h_an_map : ∀ n,
      ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
        = ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n) := by
    intro n
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : E × ℝ => f p.1 * Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      ((f.continuous.comp continuous_fst).mul
        (Real.continuous_exp.comp continuous_snd)).aestronglyMeasurable
    rw [MeasureTheory.integral_map h_joint_meas.aemeasurable h_integrand_meas]
  -- ── Slack data from the integral comparison. ─────────────────────────────────────────
  obtain ⟨ρ, hρ_tendsto, hρ_bound⟩ := h_integral_comparison
  -- Eventual integrability of `exp(L n)` under `P n`, recovered from the comparison applied
  -- to the constant `1` BCF: `|1 - ∫ exp(L n) dP_n| ≤ ‖(1 : E →ᵇ ℝ)‖ · ρ n`, and the RHS → 0.
  have h_eventually_int :
      ∀ᶠ n in atTop, Integrable (fun ω => Real.exp (L n ω)) (P n) := by
    have hg1_bound := hρ_bound (1 : E →ᵇ ℝ)
    -- `∫ (1 : E →ᵇ ℝ)(X n) dQ_n = 1` and `(1 : E →ᵇ ℝ)(X n ω)·exp(L n ω) = exp(L n ω)`.
    have h_one_apply : ∀ n ω, ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) = 1 := by
      intro n ω; rw [BoundedContinuousFunction.coe_one]; rfl
    have hg1_simp : ∀ n,
        |(1 : ℝ) - ∫ ω, Real.exp (L n ω) ∂(P n)| ≤ ‖(1 : E →ᵇ ℝ)‖ * ρ n := by
      intro n
      have hb := hg1_bound n
      have h1 : ∫ ω, ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) ∂(Q n) = 1 := by
        simp only [h_one_apply, integral_const, smul_eq_mul, mul_one, probReal_univ]
      have h2 : (fun ω => ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) * Real.exp (L n ω))
          = fun ω => Real.exp (L n ω) := by
        funext ω; rw [h_one_apply]; ring
      rw [h1, h2] at hb
      exact hb
    -- `‖(1 : E →ᵇ ℝ)‖ · ρ n → 0`, so eventually `< 1`.
    have h_slack_zero : Tendsto (fun n => ‖(1 : E →ᵇ ℝ)‖ * ρ n) atTop (𝓝 0) := by
      have := hρ_tendsto.const_mul ‖(1 : E →ᵇ ℝ)‖
      simpa using this
    have h_ev_lt_one : ∀ᶠ n in atTop, ‖(1 : E →ᵇ ℝ)‖ * ρ n < 1 := by
      have h_mem : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
      filter_upwards [h_slack_zero h_mem] with n hn using Set.mem_Iio.mp hn
    filter_upwards [h_ev_lt_one] with n hn
    by_contra h_not_int
    have h_zero : ∫ ω, Real.exp (L n ω) ∂(P n) = 0 := integral_undef h_not_int
    have hb := hg1_simp n
    rw [h_zero, sub_zero, abs_one] at hb
    linarith
  -- The residue estimate applies after enlarging the threshold so that
  -- `exp(L n)` is integrable under `P n`.
  have h_map_tendsto : Tendsto
      (fun n => ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω))))
      atTop (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂π)) := by
    -- Residue bound on both sides via BCF truncation + triangle inequality.
    have hfbound : ∀ p : E × ℝ, |f p.1| ≤ ‖f‖ := fun p => f.norm_coe_le_norm _
    have h_exp_nonneg : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos _).le
    have h_residue_EℝR :
        ∀ (μ : Measure (E × ℝ)) (M : ℝ), 0 ≤ M →
          Integrable (fun p : E × ℝ => Real.exp p.2) μ →
          |∫ p, f p.1 * Real.exp p.2 ∂μ - ∫ p, f p.1 * min (Real.exp p.2) M ∂μ|
            ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
      intro μ M hM h_exp_int
      have h_min_nn : ∀ p : E × ℝ, 0 ≤ min (Real.exp p.2) M := fun p =>
        le_min (h_exp_nonneg _) hM
      have h_min_le : ∀ p : E × ℝ, min (Real.exp p.2) M ≤ Real.exp p.2 :=
        fun p => min_le_left _ _
      have h_min_meas : Measurable (fun p : E × ℝ => min (Real.exp p.2) M) :=
        (Real.continuous_exp.measurable.comp measurable_snd).min measurable_const
      have h_min_int : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) μ := by
        refine h_exp_int.mono' h_min_meas.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Real.norm_eq_abs, abs_of_nonneg (h_min_nn p)]
        exact h_min_le p
      have hf_ae :
          AEStronglyMeasurable (fun p : E × ℝ => f p.1) μ :=
        (f.continuous.comp continuous_fst).aestronglyMeasurable
      have hf_bound_ae : ∀ᵐ p ∂μ, ‖f p.1‖ ≤ ‖f‖ :=
        Filter.Eventually.of_forall (fun p => f.norm_coe_le_norm _)
      have h_fexp_int : Integrable (fun p : E × ℝ => f p.1 * Real.exp p.2) μ :=
        h_exp_int.bdd_mul hf_ae hf_bound_ae
      have h_fmin_int :
          Integrable (fun p : E × ℝ => f p.1 * min (Real.exp p.2) M) μ :=
        h_min_int.bdd_mul hf_ae hf_bound_ae
      rw [← integral_sub h_fexp_int h_fmin_int]
      have h_diff_eq :
          (fun p : E × ℝ => f p.1 * Real.exp p.2 - f p.1 * min (Real.exp p.2) M)
            = fun p => f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) := by
        funext p; ring
      rw [h_diff_eq]
      calc |∫ p, f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ|
          ≤ ∫ p, |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)| ∂μ :=
            abs_integral_le_integral_abs
        _ = ∫ p, |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
            change |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)|
              = |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M)
            rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (h_min_le p))]
        _ ≤ ∫ p, ‖f‖ * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun p => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (h_min_le p))))
              ((h_exp_int.sub h_min_int).const_mul ‖f‖)
              (Filter.Eventually.of_forall (fun p => ?_))
            refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (h_min_le p))
            exact hfbound p
        _ = ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ :=
            integral_const_mul _ _
    -- Target-side tendsto: as M → ∞, ∫ min(exp p.2, M) dπ → ∫ exp p.2 dπ = 1 (DCT under π).
    have h_target_tendsto : Tendsto
        (fun M : ℕ => ∫ p, min (Real.exp p.2) (M : ℝ) ∂π) atTop (𝓝 1) := by
      have h_lim : ∀ᵐ p ∂π,
          Tendsto (fun M : ℕ => min (Real.exp p.2) (M : ℝ)) atTop (𝓝 (Real.exp p.2)) := by
        refine Filter.Eventually.of_forall (fun p => ?_)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈Real.exp p.2⌉₊] with M hM
        have : Real.exp p.2 ≤ (M : ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast hM)
        exact (min_eq_left this).symm
      have h_dom : ∀ M : ℕ, ∀ᵐ p ∂π,
          ‖min (Real.exp p.2) (M : ℝ)‖ ≤ Real.exp p.2 := by
        intro M
        refine Filter.Eventually.of_forall (fun p => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) (Nat.cast_nonneg _))]
        exact min_le_left _ _
      have h_meas : ∀ M : ℕ,
          AEStronglyMeasurable (fun p : E × ℝ => min (Real.exp p.2) (M : ℝ)) π :=
        fun M => ((Real.continuous_exp.comp continuous_snd).min
          continuous_const).aestronglyMeasurable
      have h_conv := MeasureTheory.tendsto_integral_of_dominated_convergence
        (F := fun (M : ℕ) (p : E × ℝ) => min (Real.exp p.2) (M : ℝ))
        (f := fun p : E × ℝ => Real.exp p.2) (bound := fun p : E × ℝ => Real.exp p.2)
        h_meas h_exp_int_π h_dom h_lim
      rw [h_exp_int_π_eq_one] at h_conv
      exact h_conv
    -- Start ε argument.
    rw [Metric.tendsto_nhds]
    intro ε hε
    set C : ℝ := ‖f‖ + 1 with hC_def
    have hC_pos : 0 < C := by positivity
    have hnorm_le_C : ‖f‖ ≤ C := by simp [hC_def]
    have hthresh_pos : 0 < ε / (3 * C) := by positivity
    -- UI threshold on sequence side.
    obtain ⟨M_UI, hM_UI_nonneg, N_UI, hN_UI⟩ :=
      h_UI (ε / (3 * C)) hthresh_pos
    -- Target-side pick M_target so `1 - ε/(3C) < ∫ min(exp, M_target) dπ`.
    have h_ev_target : ∀ᶠ M : ℕ in atTop,
        (1 : ℝ) - ε / (3 * C) < ∫ p, min (Real.exp p.2) (M : ℝ) ∂π := by
      have h_mem : Set.Ioi ((1 : ℝ) - ε / (3 * C)) ∈ 𝓝 (1 : ℝ) :=
        Ioi_mem_nhds (by linarith)
      exact h_target_tendsto h_mem
    obtain ⟨M_target, hM_target⟩ := h_ev_target.exists
    -- Take M := max M_UI (M_target : ℝ).
    set M : ℝ := max M_UI (M_target : ℝ) with hM_def
    have hM_nonneg : 0 ≤ M := le_max_of_le_left hM_UI_nonneg
    have hM_ge_UI : M_UI ≤ M := le_max_left _ _
    have hM_ge_target : (M_target : ℝ) ≤ M := le_max_right _ _
    -- BCF `g_M(p) := f(p.1) · min(exp(p.2), M)`, norm ≤ ‖f‖ · M.
    let g_M : E × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p => f p.1 * min (Real.exp p.2) M)
      ((f.continuous.comp continuous_fst).mul
        ((Real.continuous_exp.comp continuous_snd).min continuous_const))
      (‖f‖ * M)
      (fun p => by
        rw [Real.norm_eq_abs, abs_mul]
        have h2 : 0 ≤ min (Real.exp p.2) M :=
          le_min (h_exp_nonneg _) hM_nonneg
        rw [abs_of_nonneg h2]
        refine mul_le_mul ?_ (min_le_right _ _) h2 (norm_nonneg _)
        exact hfbound p)
    have hg_M_apply : ∀ p, g_M p = f p.1 * min (Real.exp p.2) M := fun _ => rfl
    -- Weak convergence at g_M.
    have h_weak_gM := h_joint_weak g_M
    rw [Metric.tendsto_nhds] at h_weak_gM
    have hε3_pos : (0 : ℝ) < ε / 3 := by linarith
    obtain ⟨N_weak, hN_weak⟩ :=
      Filter.eventually_atTop.mp (h_weak_gM (ε / 3) hε3_pos)
    -- Eventual-integrability threshold.
    obtain ⟨N_int, hN_int⟩ := Filter.eventually_atTop.mp h_eventually_int
    rw [Filter.eventually_atTop]
    refine ⟨max (max N_UI N_weak) N_int, fun n hn => ?_⟩
    have hn_UI : N_UI ≤ n := le_of_max_le_left (le_of_max_le_left hn)
    have hn_weak : N_weak ≤ n := le_of_max_le_right (le_of_max_le_left hn)
    have hn_int : N_int ≤ n := le_of_max_le_right hn
    -- Sequence-side: `exp` integrable under `P n` (eventual) and under `(P n).map (X_n, L_n)`.
    have h_exp_int_Pn : Integrable (fun ω => Real.exp (L n ω)) (P n) := hN_int n hn_int
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_exp_int_map_n :
        Integrable (fun p : E × ℝ => Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      (MeasureTheory.integrable_map_measure
        (Real.continuous_exp.comp continuous_snd).aestronglyMeasurable
        h_joint_meas.aemeasurable).mpr h_exp_int_Pn
    -- UI bound at enlarged M: monotonicity of min(exp, ·) in M.
    have h_min_mono_M : ∀ ω,
        min (Real.exp (L n ω)) M_UI ≤ min (Real.exp (L n ω)) M :=
      fun ω => min_le_min_left _ hM_ge_UI
    have h_int_trunc_UI : Integrable
        (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI) (P n) := by
      refine h_exp_int_Pn.sub ?_
      refine h_exp_int_Pn.mono'
        ((Real.continuous_exp.measurable.comp (hL_meas n)).min
          measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (le_min (h_exp_nonneg _) hM_UI_nonneg)]
      exact min_le_left _ _
    have h_UI_bound_Pn :
        ∫ ω, (Real.exp (L n ω) - min (Real.exp (L n ω)) M) ∂(P n) ≤ ε / (3 * C) :=
      calc ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
          ≤ ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI ∂(P n) :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun ω => sub_nonneg.mpr (min_le_left _ _)))
              h_int_trunc_UI
              (Filter.Eventually.of_forall
                (fun ω => by linarith [h_min_mono_M ω]))
        _ ≤ ε / (3 * C) := hN_UI n hn_UI
    have h_UI_bound_map_n :
        ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
            ∂((P n).map (fun ω => (X n ω, L n ω)))
          ≤ ε / (3 * C) := by
      rw [MeasureTheory.integral_map h_joint_meas.aemeasurable]
      · exact h_UI_bound_Pn
      · exact ((Real.continuous_exp.comp continuous_snd).sub
          ((Real.continuous_exp.comp continuous_snd).min
            continuous_const)).aestronglyMeasurable
    -- Target-side residue bound:
    have h_trunc_int_π : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) π := by
      refine h_exp_int_π.mono'
        ((Real.continuous_exp.comp continuous_snd).min
          continuous_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
      exact min_le_left _ _
    have h_target_trunc_M_lb :
        (1 : ℝ) - ε / (3 * C) ≤ ∫ p, min (Real.exp p.2) M ∂π := by
      have h_mono :
          ∫ p, min (Real.exp p.2) (M_target : ℝ) ∂π
            ≤ ∫ p, min (Real.exp p.2) M ∂π := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall
            (fun p => le_min (h_exp_nonneg _) (Nat.cast_nonneg _)))
          h_trunc_int_π
          (Filter.Eventually.of_forall (fun p => min_le_min_left _ hM_ge_target))
      linarith [hM_target]
    have h_target_bound_π :
        ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π ≤ ε / (3 * C) := by
      rw [integral_sub h_exp_int_π h_trunc_int_π, h_exp_int_π_eq_one]
      linarith [h_target_trunc_M_lb]
    -- Apply residue bound on both sides.
    have h_res_map_n := h_residue_EℝR ((P n).map (fun ω => (X n ω, L n ω))) M hM_nonneg
      h_exp_int_map_n
    have h_res_π := h_residue_EℝR π M hM_nonneg h_exp_int_π
    -- Triangle inequality.
    rw [Real.dist_eq]
    have h_weak_bound :
        |∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω))) - ∫ p, g_M p ∂π| < ε / 3 := by
      have := hN_weak n hn_weak
      rwa [Real.dist_eq] at this
    have h_res_nonneg : 0 ≤ ‖f‖ := norm_nonneg _
    have h_seq_piece :
        |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
          - ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))| ≤ ε / 3 := by
      have h_gM_eq :
          ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
            = ∫ p, f p.1 * min (Real.exp p.2) M
                ∂((P n).map (fun ω => (X n ω, L n ω))) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
      rw [h_gM_eq]
      calc |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
              - ∫ p, f p.1 * min (Real.exp p.2) M
                  ∂((P n).map (fun ω => (X n ω, L n ω)))|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
                ∂((P n).map (fun ω => (X n ω, L n ω))) := h_res_map_n
        _ ≤ ‖f‖ * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_left h_UI_bound_map_n h_res_nonneg
        _ ≤ C * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
        _ = ε / 3 := by field_simp
    have h_target_piece :
        |∫ p, g_M p ∂π - ∫ p, f p.1 * Real.exp p.2 ∂π| ≤ ε / 3 := by
      have h_gM_eq :
          ∫ p, g_M p ∂π = ∫ p, f p.1 * min (Real.exp p.2) M ∂π :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
      rw [h_gM_eq, abs_sub_comm]
      calc |∫ p, f p.1 * Real.exp p.2 ∂π - ∫ p, f p.1 * min (Real.exp p.2) M ∂π|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π := h_res_π
        _ ≤ ‖f‖ * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_left h_target_bound_π h_res_nonneg
        _ ≤ C * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
        _ = ε / 3 := by field_simp
    set A := ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
    set B := ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
    set D := ∫ p, g_M p ∂π
    set E' := ∫ p, f p.1 * Real.exp p.2 ∂π
    have h_split : A - E' = (A - B) + (B - D) + (D - E') := by ring
    rw [h_split]
    calc |(A - B) + (B - D) + (D - E')|
        ≤ |(A - B) + (B - D)| + |D - E'| := abs_add_le _ _
      _ ≤ |A - B| + |B - D| + |D - E'| := by linarith [abs_add_le (A - B) (B - D)]
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h_seq_piece, h_weak_bound, h_target_piece]
      _ = ε := by ring
  -- ── Bridge `aₙ` (map form → `P n` form) to `bₙ = ∫ f d((Q n).map X)` via the slack. ───
  have h_a_tendsto : Tendsto
      (fun n => ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)) atTop
      (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂π)) :=
    h_map_tendsto.congr h_an_map
  -- Slack `bₙ - aₙ → 0` from `|bₙ - aₙ| ≤ ‖f‖·ρ n` and `‖f‖·ρ n → 0`.
  have h_slack_tendsto : Tendsto
      (fun n => (∫ ω, f (X n ω) ∂(Q n))
        - ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)) atTop (𝓝 0) := by
    have h_norm_zero : Tendsto (fun n => ‖f‖ * ρ n) atTop (𝓝 0) := by
      have := hρ_tendsto.const_mul ‖f‖
      simpa using this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h_norm_zero
    rw [Real.norm_eq_abs]
    exact hρ_bound f n
  -- Conclude: `bₙ = aₙ + (bₙ - aₙ) → target + 0 = target`.
  have h_sum := h_a_tendsto.add h_slack_tendsto
  rw [add_zero] at h_sum
  refine (h_sum.congr (fun n => ?_)).congr (fun n => (h_bn_map n).symm)
  ring

/-! ## Le Cam's first lemma (vdV Lemma 6.4)

Van der Vaart's four equivalent characterizations of contiguity use the
event formulation `Contiguous atTop P Q` (`Q ⊲ P`) in statement (i) and
the statistic formulation in statement (iv). Statements (ii) and (iii)
concern weak limit points of `dPₙ/dQₙ` under `Qₙ` and `dQₙ/dPₙ` under `Pₙ`.
The Radon–Nikodym derivative `Measure.rnDeriv (P n) (Q n)` represents
`dPₙ/dQₙ`; `.toReal` gives a real-valued ratio and `.map` its law.
-/

section LeCamFirstEquivalence


end LeCamFirstEquivalence

end Contiguity
end AsymptoticStatistics
