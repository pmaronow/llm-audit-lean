import SAP.P027a.Defs.WholeW1
import SAP.P027a.WH.W1.Helpers
import SAP.P027a.Bridge
import AronowAudit.P027.Wave1.UniformStart.N5
import AronowAudit.P027.Wave1.AePartition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W1

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory SAP.P027a.Bridge
attribute [local instance] Classical.propDecidable

/-- Identify the eight-unit periodic continuous-start law, including cell masses
and expectations of every sample statistic. Prove the finite interval partition
by four cases, normalize restricted Lebesgue measure using `Real.volume_Ico`,
use `periodic8_systematic` for selection, and apply `UniformStart.n5_proof` to
integrate the four constants. No arbitrary statistic needs extra regularity:
it is a function of one of finitely many measurable samples. About 120 lines. -/
def T1_L1 : Prop := FourPhaseStartWhole periodic8 periodicSize8 2 10

/-- Export the remaining finite-population algebra in T2. Regroup A using
`aggregation_A_preserved` and `oneDraw_joint`; expand the square of the sum.
Use `periodic_ht_expectations`, finite-sum distributivity, `mean_bias_identity`
and the positive cardinality N=2rm. Nonpositivity and both equality criteria
follow from `periodic_negative_square`. About 120 lines. -/
def T2_L1 : Prop := PeriodicFiniteWholeExtras

/-- Derive signal/noise representations, all integrability certificates and both
ratios of averaged quantities from the claimed second moments. Use
`periodic_size_moments`, `centered_outcomes_linear` and
`phase_centered_total_formula` for the representations. Integrability of each
T_g² is `phase_centered_second_moment`; finite sums give V, H=V-S and A=-S.
Scale by N², apply `integral_sub` with those certificates, and use
`periodic_model_moments`. D>0 implies positive averaged variances. About 250 lines. -/
def T2_L2 : Prop := PeriodicOutcomeWholeExtras

/-- Transfer the quadratic correction and C2 bias from a general almost-sure
cluster law to the exact lift of its representative law. Use
`aggregation_ae_partition_bridge` for all joints and A. Joints of the exact
lift agree, so unfold `quadraticA` termwise. Finally `c2_expectation` cancels the
variance in each C2 bias, leaving A+A-star. No equality at null atoms or
full-support hypothesis is needed. About 100 lines. -/
def T4_L1 : Prop :=
  ∀ {G Ω : Type} [Fintype G] [Fintype Ω]
    (n : G → ℕ) (hn : ∀ g, 0 < n g)
    (D : Design (Σ g, Fin (n g)) Ω), Valid D → Positive D → WholeAEClusters n D →
  ∀ y : (Σ g, Fin (n g)) → ℝ,
    let Dc := wholeRepDesign n hn D
    quadraticA D y = quadraticA (liftDesign Dc n) y ∧
    wholeC2Bias D y = wholeC2Bias (liftDesign Dc n) y

/-- Finite Lagrange identity in one numbered group. Expand the ordered sum of
(yi-yj)² to 2*(n*sum yi²-(sum yi)²), remove its zero diagonal, and split the
strict-order halves, swapping indices in one half. Alternatively induct on n
using `Fin.sum_univ_succ`. Includes n=0 and n=1, where both sides are zero.
Nonnegativity is easy glue in the assembly. About 100 lines. -/
def T4_L2 : Prop :=
  ∀ (n : ℕ) (y : Fin n → ℝ),
    (n:ℝ)*(∑ i, y i^2)-(∑ i, y i)^2 =
      ∑ i, ∑ j, if i < j then (y i-y j)^2 else 0

/-- Identify the random-size witness's continuous-start law on [0,8), not just
its intervalwise samples. The cells are [0,1),[1,4),[4,5),[5,8), with masses
1/8,3/8,1/8,3/8. Use `random8_systematic`, normalized restricted Lebesgue
measure, `Real.volume_Ico`, and `UniformStart.n5_proof`. This is the same finite
partition argument as T1_L1 with different endpoints. About 120 lines. -/
def T10_L1 : Prop := FourPhaseStartWhole random8 randomSize8 1 3

/-- Assembly of the periodic witness. All rational computations, scaling,
table substitutions and fixed-fraction nonvanishing are proved in the helpers. -/
theorem T1_assembly (h1 : T1_L1) : T1WholeStatement := by
  exact ⟨periodic8_core, h1, periodic8_details, periodic_start_core, periodic_inclusions,
    periodic_sizes, alternating_family_core, alternating_family_details⟩

/-- Assemble the full finite and outcome formulas with the existing design law,
the derived empirical calibration and the genuine fixed-q limit. -/
theorem T2_assembly (h1 : T2_L1) (h2 : T2_L2) : T2WholeStatement := by
  exact ⟨periodic_start_core, periodic_inclusions, periodic_sizes, periodic_bias_core,
    h1, periodic_outcome_core, h2, periodic_calibration, periodic_limit⟩

/-- Both finite witnesses are fully computational; there is no remaining leaf. -/
theorem T3_assembly : T3WholeStatement := by
  exact ⟨cluster_core, cluster_design_details, cluster_value_details⟩

/-- Transfer all existing exact-lift formulas to the general almost-sure input,
then append Lagrange's identity and the explicit increasing/decreasing examples. -/
theorem T4_assembly (h1 : T4_L1) (h2 : T4_L2) : T4WholeStatement := by
  refine ⟨?_, ?_, aggregation_reduction, cluster_core.2⟩
  · intro G Ω _ _ n hn D hv hp hae y
    let Dc := wholeRepDesign n hn D
    let Y := groupTotal n y
    let S := groupSquares n y
    let Δ := wholeC2Bias D y - wholeC2Bias Dc Y
    have hvc : Valid Dc := hv
    rcases ae_preservation_core n hn D hv hp hae y with
      ⟨hpc, hpi, hj, hsupp, hvar, hA⟩
    have hpc' : Positive Dc := hpc
    rcases h1 n hn D hv hp hae y with ⟨hquad, hbias⟩
    rcases aggregation_exact_core Dc hvc hpc' n hn y with
      ⟨hpres, hquadform, hchange, hdegree⟩
    have hΔ : Δ = wholeC2Bias (liftDesign Dc n) y - wholeC2Bias Dc Y := by
      dsimp [Δ]
      rw [hbias]
    have heq : Δ = wholeEdgeSum Dc
        (fun g h => (n h:ℝ)*S g+(n g:ℝ)*S h-Y g^2-Y h^2) := by
      rw [hΔ]
      exact hchange.1
    have hequal : (∀ g h, g ≠ h ∧ joint Dc g h = 0 → n g = n h) → 0 ≤ Δ := by
      intro hs
      rw [hΔ]
      exact hchange.2.1 hs
    refine ⟨hvc, hpc', hpi, hj, ?_, hsupp, hvar, ?_, hA, ?_, quadraticA_edge Dc Y,
      c2_bias_add D hv hp y, c2_bias_add Dc hvc hpc' Y, heq, ?_, ?_, hequal, ?_,
      (c2_bias_squared Dc hvc hpc' Y).trans (squared_edge Dc Y),
      c2_bias_squared D hv hp y, hchange.2.2.2.1, ?_⟩
    · intro g
      exact AronowAudit.P027.joint_self (toAudit Dc hvc) g
    · rw [hA]
      rfl
    · rw [hquad]
      exact hquadform
    · exact (sub_neg).symm
    · intro v hy
      have hc : Δ = -v^2*wholeEdgeSum Dc (fun g h => ((n g:ℝ)-n h)^2) := by
        rw [hΔ]
        exact (hchange.2.2.1 v hy).trans (by dsimp [wholeEdgeSum]; ring)
      have he : 0 ≤ wholeEdgeSum Dc (fun g h => ((n g:ℝ)-n h)^2) := by
        apply div_nonneg _ (by norm_num)
        apply Finset.sum_nonneg
        intro g _
        apply Finset.sum_nonneg
        intro h _
        split_ifs <;> positivity
      have hle : Δ ≤ 0 := by
        rw [hc]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg v)) he
      refine ⟨hc, hle, ?_, fun hs => le_antisymm hle (hequal hs)⟩
      intro hv0 hedge
      have hyf : y = (fun _ => v) := funext hy
      have hs : wholeC2Bias (liftDesign Dc n) (fun _ => v) <
          wholeC2Bias Dc (groupTotal n (fun _ => v)) :=
        AronowAudit.P027.constant_aggregation_strict (toAudit Dc hvc) hpc' n hn v hv0 hedge
      change Δ < 0
      rw [hΔ]
      dsimp only [Y]
      rw [hyf]
      exact sub_neg.mpr hs
    · change (∑ g, (zeroNeighborSize Dc n g-(zeroNeighborCount Dc g:ℝ)*(n g:ℝ))*S g) ≤ Δ
      rw [hΔ]
      exact hdegree
    · rw [hbias]
      exact hchange.2.2.2.2
  · intro n y
    refine ⟨h2 n y, ?_⟩
    rw [h2 n y]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity

/-- The finite computations and the positive normalized size support are already
proved; only the concrete continuous-start identification is passed as a leaf. -/
theorem T10_assembly (h1 : T10_L1) : T10WholeStatement := by
  exact ⟨random8_core, h1, random8_details, random_size_support⟩

end
end SAP.P027a.WH.W1
