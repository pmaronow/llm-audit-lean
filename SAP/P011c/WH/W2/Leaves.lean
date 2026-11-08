import SAP.P011c.Defs.WholeW2
import SAP.P011c.Bridge
import AronowAudit.P011.P011_CorollariesCompletion
import AronowAudit.P011.Wave1.PackageOLS
import AronowAudit.P011.Wave1.Gap.GP011B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c.WH.W2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- The finite-sample homoskedastic oracle underestimation bound, with no
cross-row assumptions. Prove this by extracting the per-row argument of
`HomoskedasticCompletion.homoskedastic_repair_completed` through `Bridge.toModel`.
First prove `1 ≤ gFactor m ≤ 1+c2` directly using `degree_row_sum`. The bound on
weighted outcomes gives their L2 moments by `ProbabilityCompletion.weighted_memLp`.
Use `pairwise_correlation_repair` and `CorrelationCompletion.meanVariance_nonneg`
to bound n Var by the common marginal variance times the degree factor.
Write sampleVariance = meanVariance + meanSpread + varianceRemainder, retaining
the nonnegative meanSpread. The underestimation error is at most
(1+c2)|varianceRemainder|. Apply `remainder_memLp_two`, `remainder_second_bound`
with d=1+c2, and `second_moment_tail` at ε/(1+c2). This is about 100–150 lines;
neither a positive marginal variance nor identical means is needed. Shared by T37. -/
def T36_L1 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (m : Model n) (c1 c2 : ℝ),
    0 < c1 → 0 < c2 → Dependency m →
    (∀ᵐ y ∂m.law, ∀ i, |weighted m y i - beta m| ≤ c1) →
    (∀ i, (degree m.G i : ℝ) ≤ c2) → Homoskedastic m →
    ∀ ε : ℝ, 0 < ε →
      probability m {y | (n : ℝ) *
        (var m (betaHat m) - V2 m.G (weighted m y)) > ε} ≤
        4 * (1 + c2)^3 * c1^4 / ((n : ℝ) * ε^2)

/-- Forget only the extra nesting condition in the existing donor predicate. -/
theorem wholeScaling_of_scaling (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) : WholeW2Scaling F c1 c2 c3 c4 := h.2

/-- The existing OLS path witness already refutes variance conservativeness alone. -/
theorem T35_assembly : T35WholeStatement := by
  open AronowAudit.P011.Wave1 in
  obtain ⟨hs, hv, hrank, hmean, htheta, hmax, _⟩ := PackageOLS.assemble_witness
    PropositionOne.n1_proof PropositionOne.n2_proof PropositionOne.n3_proof
    PropositionOne.n4_proof PropositionOne.n5_proof PropositionOne.n6_proof
    PropositionOne.n7_proof PropositionOne.n8_proof PropositionOne.n9_proof
    PropositionOne.n10_proof CorollaryOne.n1_proof CorollaryOne.n3_proof
    PackageOLS.n1_proof PackageOLS.n2_proof PackageOLS.n3_proof
  refine ⟨Bridge.fromFamily AronowAudit.P011.Wave1.PropositionOne.PF,
    AronowAudit.P011.Wave1.PackageOLS.olsDesign,
    AronowAudit.P011.Wave1.CorollaryOne.oracleChoice,
    wholeScaling_of_scaling _ _ _ _ _ hs, hs.1, hv, hrank, hmean, htheta, hmax, ?_⟩
  exact AronowAudit.P011.Wave1.CorollaryOne.not_conservative_of
    AronowAudit.P011.Wave1.PropositionOne.n2_proof
    AronowAudit.P011.Wave1.PropositionOne.n5_proof
    AronowAudit.P011.Wave1.PropositionOne.n7_proof
    AronowAudit.P011.Wave1.PropositionOne.n8_proof
    AronowAudit.P011.Wave1.PropositionOne.n9_proof
    AronowAudit.P011.Wave1.PropositionOne.n10_proof
    AronowAudit.P011.Wave1.CorollaryOne.n3_proof

/-- A finite bound proportional to 1/n tends to zero; no nesting is used. -/
theorem oracle_conservative (h1 : T36_L1) (F : Family) (c1 c2 c3 c4 : ℝ)
    (hs : WholeW2Scaling F c1 c2 c3 c4) (hhom : ∀ k, Homoskedastic (F.model k)) :
    Conservative F (fun k y => V2 (F.model k).G (weighted (F.model k) y)) := by
  rcases hs with ⟨hc1, hc2, _, _, hdep, hbound, hdegree, _, _⟩
  intro ε hε
  have hn : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_)
    (hn.const_div_atTop (4 * (1 + c2)^3 * c1^4 / ε^2))
  have hr := h1 (F.size k) (F.positive k) (F.model k) c1 c2 hc1 hc2
    (hdep k) (hbound k) (hdegree k) (hhom k) ε hε
  have he : 4 * (1 + c2)^3 * c1^4 / ((F.size k : ℝ) * ε^2) =
      (4 * (1 + c2)^3 * c1^4 / ε^2) / (F.size k : ℝ) := by ring
  rw [he] at hr
  exact hr

/-- The alternating independent-sign witness has n-scaled error tending to one. -/
theorem oracle_nonconsistency :
    ∃ F : Family, WholeW2Scaling F 2 1 1 2 ∧ Nested F ∧
      (∀ k, Homoskedastic (F.model k)) ∧
      ¬ InProbability F
        (fun k y => (F.size k : ℝ) * V2 (F.model k).G (weighted (F.model k) y))
        (scaledTrue F) := by
  obtain ⟨hs, _, hhom, _, htail, _, _⟩ :=
    AronowAudit.P011.Wave1.alternating_counterexample_proof
  refine ⟨Bridge.fromFamily AronowAudit.P011.alternatingFamily,
    wholeScaling_of_scaling _ _ _ _ _ hs, hs.1, fun k => (hhom k).1, ?_⟩
  intro hconv
  change AronowAudit.P011.InProbability AronowAudit.P011.alternatingFamily
    (fun k y => (AronowAudit.P011.alternatingFamily.size k : ℝ) *
      AronowAudit.P011.V2 (AronowAudit.P011.alternatingFamily.model k).G
        (AronowAudit.P011.weighted (AronowAudit.P011.alternatingFamily.model k) y))
    (AronowAudit.P011.scaledTrue AronowAudit.P011.alternatingFamily) at hconv
  have hz := hconv (1 / 2) (by norm_num)
  have hz' : Tendsto (fun k => AronowAudit.P011.probability
      (AronowAudit.P011.alternatingFamily.model k)
      {y | |(k + 1 : ℝ) * AronowAudit.P011.V2
        (AronowAudit.P011.alternatingFamily.model k).G
        (AronowAudit.P011.weighted (AronowAudit.P011.alternatingFamily.model k) y) -
        AronowAudit.P011.scaledTrue AronowAudit.P011.alternatingFamily k| > 1/2})
      atTop (𝓝 0) := by
    simpa only [AronowAudit.P011.alternatingFamily, Nat.cast_add, Nat.cast_one] using hz
  have he : (0 : ℝ) = 1 := tendsto_nhds_unique hz' htail
  norm_num at he

theorem T36_assembly (h1 : T36_L1) : T36WholeStatement :=
  ⟨oracle_conservative h1, oracle_nonconsistency⟩

/-- Lemma 1 and monotonicity of underestimation events transport the shared bound. -/
theorem T37_assembly (h1 : T36_L1) : T37WholeStatement := by
  intro F c1 c2 c3 c4 hs hhom hv A hm
  have h0 := oracle_conservative h1 F c1 c2 c3 c4 hs hhom
  have hb (k : ℕ) (y : Fin (F.size k) → ℝ) :=
    AronowAudit.P011.lemma_one (F.positive k) (F.model k).R (F.model k).G
      (A k y) (F.model k).d (hv k) (weighted (F.model k) y) (hm k y)
  have hmax : Conservative F (fun k y => V2 (A k y) (weighted (F.model k) y)) :=
    AronowAudit.P011.CorollaryCompletion.conservative_mono (Bridge.toFamily F)
      _ _ h0 (fun k y => (hb k y).1)
  exact ⟨hmax, AronowAudit.P011.CorollaryCompletion.conservative_mono
    (Bridge.toFamily F) _ _ hmax (fun k y => (hb k y).2.1)⟩

end
end SAP.P011c.WH.W2
