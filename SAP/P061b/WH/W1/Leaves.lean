import SAP.P061b.Defs.WholeW1
import SAP.P061b.Bridge
import AronowAudit.P061.P061_SamplingCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b.WH.W1
open Bridge
open scoped BigOperators Classical

/-- Transport the printed uniform binary law to the exposed-set law on a
larger feasible set, retaining every zero-mass intervention. Prove this by the
injection b ↦ (binaryAssignmentW1 b, hZ b): every supported point is in its finite
range, and the exposure mask of its image is b. Reindex the event sums along this
injection (or identify the design with extendDesign of its binary pullback).
The mass of each mask is then exactly its one binary atom. Supported treatment
counts follow from the law, and the binary control set is the complement.
About 120–200 lines; no moment assumption on raw outcomes is involved. -/
def T17_L1 : Prop :=
  ∀ {N : ℕ} (Z : Set (Fin N → ℝ)) (D : AtomicDesign Z) (n : ℕ),
    ContainsBinaryCubeW1 Z → 0 < n → n < N → UniformBinaryDesignW1 D n →
    {z : Z | InSupport D z}.Finite ∧
    SimpleRandomExposureW1 D coordinateExposureW1 1 n ∧
    (∀ z, InSupport D z →
      (∀ i, coordinateExposureW1 i z = 0 ∨ coordinateExposureW1 i z = 1) ∧
      (Finset.univ.filter (fun i => coordinateExposureW1 i z = 1)).card = n ∧
      (Finset.univ.filter (fun i => coordinateExposureW1 i z = 0)).card = N - n)

/-- Existing mask lemmas give counts and all SRS marginals, including n = N.
There is no restriction on the raw support or outcomes. -/
theorem srs_factsW1 {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Schedule Ω N) (d : ℝ) (n : ℕ) (hn : 0 < n) (hle : n ≤ N)
    (hs : SimpleRandomExposureW1 D g d n) :
    (∀ z, InSupport D z → (Finset.univ.filter (fun i => g i z = d)).card = n) ∧
    (∀ i, exposureProbability D g i d = (n : ℝ) / N) := by
  have hs' : AronowAudit.P061.SamplingCompletion.SimpleRandomExposure
      (toAudit D) g d n := hs
  constructor
  · intro z hz
    have hmask := AronowAudit.P061.SamplingCompletion.support_mask (toAudit D) g d z hz
    have hc : (Finset.univ.filter (fun i =>
        AronowAudit.P061.SamplingCompletion.exposureMask g d z i = 1)).card = n := by
      by_contra hc
      have hp0 : (AronowAudit.P061.SamplingCompletion.maskDesign
          (toAudit D) g d).p (AronowAudit.P061.SamplingCompletion.exposureMask g d z) = 0 := by
        simp [hs' (AronowAudit.P061.SamplingCompletion.exposureMask g d z), hc]
      exact (ne_of_gt hmask) hp0
    convert hc using 1
    congr 1
    ext i
    by_cases hg : g i z = d <;>
      simp [AronowAudit.P061.SamplingCompletion.exposureMask, hg]
  · intro i
    change AronowAudit.P061.pi (toAudit D) g i d = _
    rw [← AronowAudit.P061.SamplingCompletion.mask_pi (toAudit D) g d i]
    exact AronowAudit.P061.SamplingCompletion.canonical_treatment_marginal
      _ n hn hle hs' i

/-- The whole survey assertion is a short assembly of existing count/marginal
and moment-qualified HT lemmas; the single leaf supplies the larger-set design
transport needed for the completely randomized experiment. -/
theorem T17_assembly (h1 : T17_L1) : T17WholeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ω N D g y d n hN hn hp z
    exact AronowAudit.P061.ht_sample_mean (toAudit D) g y d n hN hn hp z
  · intro Ω N D g y d n hn hle hs hm
    obtain ⟨hc, hp⟩ := srs_factsW1 D g d n hn hle hs
    have he : htMean D g y d = exposedMean g y d n :=
      funext (fun z => AronowAudit.P061.ht_sample_mean (toAudit D) g y d n
        (lt_of_lt_of_le hn hle) hn hp z)
    refine ⟨hc, hp, congrFun he, ?_, ?_⟩
    · rw [← he]
      exact AronowAudit.P061.ht_integrable (toAudit D) g y d hm
    · rw [← he]
      exact AronowAudit.P061.ht_unbiased (toAudit D) g y d hm
  · intro N Z D y n hZ hn hlt hd
    obtain ⟨hfin, hs, hc⟩ := h1 Z D n hZ hn hlt hd
    have hcr := AronowAudit.P061.PaperDomains.difference_in_means_CR_general_T17
      (toAudit D) coordinateExposureW1 y n hn hlt hs hfin
      (fun i z hz => (hc z hz).1 i)
    refine ⟨fun z hz => (hc z hz).2, hcr.1, ?_, ?_, ?_, hcr.2⟩
    · exact AronowAudit.P061.finite_support_targeted_moment (toAudit D) hfin _ _ _
    · exact AronowAudit.P061.finite_support_targeted_moment (toAudit D) hfin _ _ _
    · exact AronowAudit.P061.finite_support_integrable (toAudit D) hfin _

/-- The two variance-estimator formulas have finite first moments under NURVA.
For each positive joint cell, replace the revealed outcomes by their EPOs using
nurva_epo, obtaining a constant times that joint-event indicator. For a missing
pair, the conservative summand is the sum of two constant marginal-event
indicators. Apply integrable_support_congr, integrable_event, integrable_add,
integrable_sum twice, and integrable_mul. The local hP/hS/hR arguments in
nurva_variance_estimators are exact donors. About 70–120 lines. -/
def T19_L1 : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N) (d : ℝ),
    (∀ i, 0 < exposureProbability D g i d) → SupportStable D g y →
    ((∀ i j, 0 < jointExposureProbability D g i j d d) →
      HasFirstMoment D (htVarianceEstimate D g y d)) ∧
    HasFirstMoment D (conservativeVarianceEstimate D g y d)

/-- Each pair's Young bound is unbiasedly estimable with marginal probabilities
alone. On support, each summand equals the constant a_i²/(2*pi_i) on its exposure
event and zero elsewhere, where a_i is its EPO. Use nurva_epo, then
integrable_support_congr and expectation_support_congr, integrable_event and
expectation_event, and div_mul_cancel₀ with marginal positivity. Add the two
identities. The hS calculation inside nurva_variance_estimators is the donor.
About 35–60 lines; diagonal pairs are allowed and require no special case. -/
def T19_L2 : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g y : Schedule Ω N) (d : ℝ),
    (∀ i, 0 < exposureProbability D g i d) → SupportStable D g y →
    ∀ i j, HasFirstMoment D (youngPairEstimateW1 D g y d i j) ∧
      designMean D (youngPairEstimateW1 D g y d i j) =
        exposureMean D g y i d ^ 2 / 2 + exposureMean D g y j d ^ 2 / 2

/-- No one observed-data statistic estimates a missing-cell EPO product over
the full NURVA model. First derive i ≠ j from positive marginals and zero joint
probability, and disjointness on support from event_atom_le. For (a,b) in
{0,1}² use the schedule with value a in unit i's target exposure cell, value b in
unit j's target cell, and zero in every other cell. These schedules are globally
stable, hence NURVA, and constant_cell makes their EPOs a,b. For any supported
assignment at least one target cell is absent, so the observed-data vectors have
zero mixed difference after *any* fixed statistic is applied. The four statistic
evaluations are integrable by the assumed universal property. Take the
expectation of (T11 - T10) - (T01 - T00), using expectation_sub and
expectation_support_congr, to obtain 0 = 1. No finite-support assumption is used.
About 120–200 lines; the statistic may inspect the full assignment and outcome
vector, and it is fixed before the unknown outcome schedule is varied. -/
def T19_L3 : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g : Schedule Ω N) (d : ℝ) (i j : Fin N),
    0 < exposureProbability D g i d → 0 < exposureProbability D g j d →
    jointExposureProbability D g i j d d = 0 →
    ¬∃ T : Ω × (Fin N → ℝ) → ℝ, UnbiasedProductStatisticW1 D g d i j T

/-- Existing variance and Young theorems provide all algebraic identities and
inequalities. The leaves certify estimator moments, the pairwise bound's mean,
and the missing-pair statistical impossibility assertion. -/
theorem T19_assembly (h1 : T19_L1) (h2 : T19_L2) (h3 : T19_L3) :
    T19WholeStatement := by
  intro Ω N D g y d hN hp hn
  have hm := AronowAudit.P061.global_nurva_targeted_moment (toAudit D) g y d hp hn
  have hv := AronowAudit.P061.nurva_variance_estimators (toAudit D) g y d hN hp hn
  have hf := (AronowAudit.P061.nurva_exact_variances (toAudit D) g y d d hN
    (fun i => ⟨hp i, hp i⟩) hn).2.2.1
  have hvm := h1 D g y d hp hn
  refine ⟨hm, AronowAudit.P061.ht_integrable (toAudit D) g y d hm, ?_,
    ?_, hvm.2, hv.2, ?_, ?_⟩
  · change AronowAudit.P061.Integrable (toAudit D) (fun z =>
      (AronowAudit.P061.ht (toAudit D) g y d z -
        AronowAudit.P061.expectation (toAudit D) (AronowAudit.P061.ht (toAudit D) g y d)) ^ 2)
    simpa only [pow_two] using
      AronowAudit.P061.nurva_second_moment (toAudit D) g y d d hp hp hn
  · intro hj
    exact ⟨hvm.1 hj, hv.1 hj, (hv.1 hj).trans hf⟩
  · intro i j
    exact ⟨AronowAudit.P061.young_missing_pair _ _, h2 D g y d hp hn i j⟩
  · intro i j hj
    refine ⟨?_, ?_, h3 D g d i j (hp i) (hp j) hj⟩
    · intro he
      subst j
      have heq : jointExposureProbability D g i i d d = exposureProbability D g i d := by
        simp only [jointExposureProbability, exposureProbability, and_self]
      rw [heq] at hj
      exact (ne_of_gt (hp i)) hj
    · intro z hz he
      have hle : D.p z ≤ jointExposureProbability D g i j d d :=
        AronowAudit.P061.event_atom_le (toAudit D) (fun w => g i w = d ∧ g j w = d) z he
      rw [hj] at hle
      exact (not_lt_of_ge hle) hz

end SAP.P061b.WH.W1
