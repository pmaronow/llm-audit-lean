import SAP.P019a.Defs.WholeW2
import SAP.P019a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W2

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
open SAP.P019a.Bridge

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false
universe u

/-- Population pushforward, including null sets. Prove the integral identity by
`MeasureTheory.integral_map` and `MeasureTheory.integral_fintype` for the finite
observable law (singleton masses are its defining fiber probabilities). Finite
range gives integrability, including all masked first/second moments. Sum fibers
for event probabilities. For the last equivalence, the bad event is a finite
union of fibers, so it is null exactly when each bad fiber has mass zero.
Expected size: 150-250 lines; no independence or asymptotic theorem is needed. -/
def T11_L1 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (J : ℕ) (S : T11Population J Ω),
    (∀ f : T11Observation J → ℝ,
      Integrable (fun ω => f (S.observe ω)) S.law ∧
      S.mean f = S.finiteStudy.law.mean f) ∧
    (∀ D : T11Observation J → Prop, S.prob D = S.finiteStudy.law.prob D) ∧
    (∀ D : T11Observation J → Prop,
      (∀ᵐ ω ∂S.law, D (S.observe ω)) ↔
        ∀ t, 0 < S.finiteStudy.law.mass t → D t)

/-- IID sample pushforward, on every finite sample size, including n = 0.
Use `MeasureTheory.Measure.pi_map_pi` with the measurable observation map in
every coordinate. Identify the resulting finite product law by singleton
masses: a sample atom has mass the product of its coordinate masses, exactly
`FiniteLaw.iid`. Sum over the event (all subsets of the finite observation
sample space are measurable). This includes arbitrary events of all sample
statistics; there is no positivity or occupancy premise.
Expected size: 100-200 lines; do not prove a new limit theorem. -/
def T11_L2 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (J : ℕ) (S : T11Population J Ω)
    (n : ℕ) (D : (Fin n → T11Observation J) → Prop),
    (S.sampleLaw n).real {s | D (S.sampleObservations s)} =
      (S.finiteStudy.law.iid n).prob D

/-- Finite probabilities do not depend on the decision procedure for an event. -/
theorem finite_prob_normalize {A : Type*} [Fintype A] (P : FiniteLaw A)
    (D : A → Prop) [d : DecidablePred D] :
    @FiniteLaw.prob A _ P D d =
      @FiniteLaw.prob A _ P D (fun a => Classical.propDecidable (D a)) := by
  exact congrArg (fun k => @FiniteLaw.prob A _ P D k) (Subsingleton.elim _ _)

/-- The same harmless normalization for conditional means. -/
theorem finite_ce_normalize {A : Type*} [Fintype A] (P : FiniteLaw A)
    (f : A → ℝ) (D : A → Prop) [d : DecidablePred D] :
    @FiniteLaw.ce A _ P f D d =
      @FiniteLaw.ce A _ P f D (fun a => Classical.propDecidable (D a)) := by
  exact congrArg (fun k => @FiniteLaw.ce A _ P f D k) (Subsingleton.elim _ _)

/-- The quantile definition is used only at genuine normal probabilities.
These facts discharge the old guards, without adding a leaf. -/
theorem normal_quantile_valid (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    {x : ℝ | 1 - α / 2 ≤ normalCDF x}.Nonempty ∧
    BddBelow {x : ℝ | 1 - α / 2 ≤ normalCDF x} := by
  classical
  have hq : normalCDF (normalQuantile (1 - α / 2)) = 1 - α / 2 :=
    AronowAudit.P019.Wave1.npu_quantile_cdf α hα hα1
  have hm : StrictMono normalCDF := AronowAudit.P019.Wave1.npu_strictMono
  have hset : {x : ℝ | 1 - α / 2 ≤ normalCDF x} =
      Set.Ici (normalQuantile (1 - α / 2)) := by
    ext x
    change (1 - α / 2 ≤ normalCDF x) ↔ normalQuantile (1 - α / 2) ≤ x
    conv_lhs => rw [← hq]
    exact hm.le_iff_le
  rw [hset]
  exact ⟨Set.nonempty_Ici, bddBelow_Ici⟩

/-- All completion choices give the same printed formulas on their domain. -/
theorem finite_domain_completions {A : Type*} [Fintype A] (S : Study A)
    {n : ℕ} (s : Fin n → A) (hd : T11FiniteDomain S s) (c1 c0 cV : ℝ) :
    S.muHat s c1 c0 = S.muHat s 0 0 ∧
    S.muVarianceHat s c1 c0 cV = S.muVarianceHat s 0 0 0 := by
  classical
  have h1 : S.cellCount s true false ≠ 0 := by have := hd.2.1; omega
  have h0 : S.cellCount s false false ≠ 0 := by have := hd.2.2.1; omega
  have he : S.muHat s c1 c0 = S.muHat s 0 0 := by
    simp only [Study.muHat, Study.cellMean, ite_eq_right h1, ite_eq_right h0]
  refine ⟨he, ?_⟩
  simp only [Study.muVarianceHat, ite_eq_left hd.2, he]

/-- Positive population cells and the existing strong laws make every
printed interval denominator available eventually, almost surely. -/
theorem finite_domain_eventual {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (S : Study A) (hs : S.standing) :
    ∀ᵐ ω ∂AronowAudit.P019.Wave1.t19_product (toLaw S.law),
      ∀ᶠ n in atTop,
        T11FiniteDomain S (AronowAudit.P019.Wave1.t19_sample n ω) := by
  classical
  let T := toStudy S
  have hp := AronowAudit.P019.regularity_probabilities T hs.2.2.2
  have hy : T.law.prob (fun t => T.Y t = true) < 1 := by
    have hh := hp.2 false
    rw [AronowAudit.P019.prob_false] at hh
    linarith
  have hg : 0 < T.gamma := hp.1 true
  have hg1 : T.gamma < 1 := by
    have hh := hp.1 false
    rw [AronowAudit.P019.prob_false] at hh
    change 0 < 1 - T.gamma at hh
    linarith
  filter_upwards [AronowAudit.P019.Wave1.t19_ybar_ae T,
    AronowAudit.P019.Wave1.t19_gamma_ae T,
    AronowAudit.P019.Wave1.t19_cell_ae T true false 0 (hs.2.2.2.1 true false).1,
    AronowAudit.P019.Wave1.t19_cell_ae T false false 0 (hs.2.2.2.1 false false).1]
    with ω hY hG h1 h0
  filter_upwards [eventually_gt_atTop (0 : ℕ), h1.2.1, h0.2.1,
    hY.eventually_lt_const hy, hG.eventually_const_lt hg, hG.eventually_lt_const hg1]
    with n hn hn1 hn0 hYn hGn hGn1
  exact ⟨hn, hn1, hn0, hYn, hGn, hGn1⟩

/-- Reuse the proved Wald limit, and discard only an event whose probability
vanishes. All fixed completion values are allowed; none is imposed on the
paper's undefined formulas. -/
theorem finite_domain_coverage {A : Type*} [Fintype A] (S : Study A)
    (hs : S.standing) :
    Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s => T11FiniteDomain S s))
      atTop (nhds 1) ∧
    ∀ α : ℝ, 0 < α → α < 1 → ∀ c1 c0 cV : ℝ,
      Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
        T11FiniteDomain S s ∧ |S.muHat s c1 c0 - S.mu| ≤
          normalQuantile (1 - α / 2) * Real.sqrt (S.muVarianceHat s c1 c0 cV)))
        atTop (nhds (1 - α)) := by
  classical
  let : MeasurableSpace A := ⊤
  have : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  have he := finite_domain_eventual S hs
  constructor
  · have hdiff := AronowAudit.P019.Wave1.t19_indicator_transfer (toLaw S.law)
      (fun _ s => T11FiniteDomain S s) (fun _ _ => True) (by
        filter_upwards [he] with ω hω
        filter_upwards [hω] with n hn
        exact iff_true_intro hn)
    have hdiff' : Tendsto (fun n : ℕ =>
        (S.law.iid n).prob (fun s => T11FiniteDomain S s) - 1) atTop (nhds 0) := by
      simpa only [AronowAudit.P019.FiniteLaw.prob, ite_true,
        AronowAudit.P019.mean_const, iid_eq, mean_eq, FiniteLaw.prob] using hdiff
    simpa only [sub_add_cancel, zero_add] using hdiff'.add_const 1
  · intro α hα hα1 c1 c0 cV
    have hw := (AronowAudit.P019.Wave1.combined_asymptotic_inference_proof
      (toStudy S) hs c1 c0 cV).2.2.2 α hα hα1
    have hdiff := AronowAudit.P019.Wave1.t19_indicator_transfer (toLaw S.law)
      (fun _ s => T11FiniteDomain S s ∧ |S.muHat s c1 c0 - S.mu| ≤
        normalQuantile (1 - α / 2) * Real.sqrt (S.muVarianceHat s c1 c0 cV))
      (fun _ s => |S.muHat s c1 c0 - S.mu| ≤
        normalQuantile (1 - α / 2) * Real.sqrt (S.muVarianceHat s c1 c0 cV)) (by
        filter_upwards [he] with ω hω
        filter_upwards [hω] with n hn
        simp only [hn, true_and])
    change Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
      |S.muHat s c1 c0 - S.mu| ≤ normalQuantile (1 - α / 2) *
        Real.sqrt (S.muVarianceHat s c1 c0 cV))) atTop (nhds (1 - α)) at hw
    have hdiff' : Tendsto (fun n : ℕ =>
        (S.law.iid n).prob (fun s => T11FiniteDomain S s ∧
          |S.muHat s c1 c0 - S.mu| ≤ normalQuantile (1 - α / 2) *
            Real.sqrt (S.muVarianceHat s c1 c0 cV)) -
        (S.law.iid n).prob (fun s => |S.muHat s c1 c0 - S.mu| ≤
          normalQuantile (1 - α / 2) * Real.sqrt (S.muVarianceHat s c1 c0 cV)))
        atTop (nhds 0) := by
      simpa only [iid_eq, prob_eq, finite_prob_normalize] using hdiff
    simpa only [sub_add_cancel, zero_add] using hdiff'.add hw

/-- Assemble the population identities from their existing donors, transfer
all iid event probabilities, and remove the exceptional undefined samples. -/
theorem T11_assembly (h1 : T11_L1.{u}) (h2 : T11_L2.{u}) :
    T11WholeStatement.{u} := by
  classical
  intro Ω _ J S
  obtain ⟨hmI, hp, hae⟩ := h1 Ω J S
  have hm (f : T11Observation J → ℝ) : S.mean f = S.finiteStudy.law.mean f :=
    (hmI f).2
  have hc (f : T11Observation J → ℝ) (D : T11Observation J → Prop) :
      S.ce f D = S.finiteStudy.law.ce f D := by
    simp only [T11Population.ce, FiniteLaw.ce, hm, hp]
  have hv (f : T11Observation J → ℝ) :
      S.variance f = S.finiteStudy.law.variance f := by
    simp only [T11Population.variance, FiniteLaw.variance, hm]
  have hcv (f : T11Observation J → ℝ) (D : T11Observation J → Prop) :
      S.cv f D = S.finiteStudy.law.cv f D := by
    simp only [T11Population.cv, FiniteLaw.cv, hc]
  have hmu : S.mu = S.finiteStudy.mu := by
    simpa only [T11Population.mu, Study.mu, T11Population.finiteStudy,
      finite_prob_normalize] using hp (fun t => t.X = true)
  have hmono : S.monotone → S.finiteStudy.monotone := by
    exact (hae (fun t => t.Y = true → t.X = true)).mp
  have hdesign : S.noLiarsDesign → S.finiteStudy.noLiarsDesign := by
    exact (hae (fun t => (t.V : ℝ) = (t.W : ℝ) + bitVal t.X * bitVal t.Z)).mp
  have hind : S.treatmentIndependent → S.finiteStudy.treatmentIndependent := by
    intro hi f z
    simpa only [hm, hp, T11Population.finiteStudy, finite_prob_normalize] using hi f z
  have hW : S.finiteStudy.W = T11Observation.W := rfl
  have hX : S.finiteStudy.X = T11Observation.X := rfl
  have hY : S.finiteStudy.Y = T11Observation.Y := rfl
  have hZ : S.finiteStudy.Z = T11Observation.Z := rfl
  have hV : S.finiteStudy.V = T11Observation.V := rfl
  have hcell (z y : Bool) : S.finiteStudy.cell z y = T11Observation.cell z y := rfl
  have hstanding : S.standing → S.finiteStudy.standing := by
    rintro ⟨hmon, hdes, hi, hn⟩
    refine ⟨hmono hmon, hdesign hdes, hind hi, ?_⟩
    simpa only [T11Population.nondegenerate, Study.nondegenerate,
      hcell, hp, hcv, hv, hV, hZ, hY,
      FiniteLaw.cv, finite_prob_normalize, finite_ce_normalize] using hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hdes hi hz0 hz1
    have hz0' : 0 < S.finiteStudy.law.prob (fun t => t.Z = false) := by
      simpa only [hp, hcell, hZ, finite_prob_normalize] using hz0
    have hz1' : 0 < S.finiteStudy.law.prob (fun t => t.Z = true) := by
      simpa only [hp, hcell, hZ, finite_prob_normalize] using hz1
    obtain ⟨ht, hct⟩ := AronowAudit.P019.list_arm_expansion (toStudy S.finiteStudy)
      (hdesign hdes) (hind hi) hz0'.ne' hz1'.ne'
    have ht' : S.ce (fun t => (t.V : ℝ)) (fun t => t.Z = true) =
        S.mean (fun t => (t.W : ℝ)) + S.mu := by
      simpa only [hc, hm, hmu, toStudy, mean_eq, ce_eq, AronowAudit.P019.Study.mu,
        Study.mu, T11Population.finiteStudy, prob_eq, finite_prob_normalize,
        finite_ce_normalize] using ht
    have hc' : S.ce (fun t => (t.V : ℝ)) (fun t => t.Z = false) =
        S.mean (fun t => (t.W : ℝ)) := by
      simpa only [hc, hm, toStudy, ce_eq, mean_eq, T11Population.finiteStudy,
        finite_ce_normalize] using hct
    refine ⟨ht', hc', ?_⟩
    rw [ht', hc']
    ring
  · intro hmon hy
    have hy' : 0 < S.finiteStudy.law.prob (fun t => t.Y = true) := by
      simpa only [hp, T11Population.finiteStudy, finite_prob_normalize] using hy
    have hh := AronowAudit.P019.monotone_yes_mean (toStudy S.finiteStudy)
      (hmono hmon) hy'.ne'
    simpa only [hc, toStudy, ce_eq, T11Population.finiteStudy, bitVal,
      AronowAudit.P019.bitVal, finite_ce_normalize] using hh
  · intro hs
    obtain ⟨hD, hW⟩ := finite_domain_coverage S.finiteStudy (hstanding hs)
    constructor
    · convert hD using 1
      funext n
      exact h2 Ω J S n (fun s => T11FiniteDomain S.finiteStudy s)
    · intro α hα hα1 c1 c0 cV
      convert hW α hα hα1 c1 c0 cV using 1
      funext n
      simpa only [T11Population.intervalDomain, T11Population.estimate,
        T11Population.varianceEstimate, hmu, finite_prob_normalize] using
        h2 Ω J S n (fun s => T11FiniteDomain S.finiteStudy s ∧
          |S.finiteStudy.muHat s c1 c0 - S.finiteStudy.mu| ≤
            normalQuantile (1 - α / 2) * Real.sqrt (S.finiteStudy.muVarianceHat s c1 c0 cV))
  · intro hmon hdes hi hz0 hz1
    have hz0' : 0 < S.finiteStudy.law.prob (S.finiteStudy.cell false true) := by
      simpa only [hp, hcell, hZ, finite_prob_normalize] using hz0
    have hz1' : 0 < S.finiteStudy.law.prob (S.finiteStudy.cell true true) := by
      simpa only [hp, hcell, hZ, finite_prob_normalize] using hz1
    have hh := AronowAudit.P019.placebo_one_identity (toStudy S.finiteStudy)
      (hmono hmon) (hdesign hdes) (hind hi) hz0'.ne' hz1'.ne'
    change S.finiteStudy.listMean true true - S.finiteStudy.listMean false true = 1 at hh
    have ht : S.finiteStudy.listMean true true = S.finiteStudy.listMean false true + 1 := by
      linarith only [hh]
    simpa only [hc, Study.listMean, hcell, hV, finite_ce_normalize] using ht

end
end SAP.P019a.WH.W2
