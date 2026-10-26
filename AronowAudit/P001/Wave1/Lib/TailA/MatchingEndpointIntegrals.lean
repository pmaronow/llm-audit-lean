import AronowAudit.P001.Wave1.Lib.TailA.MatchingExchangeability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Integrate the pinned limits against the actual donor density. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA

local instance instDecidableMatchingEndpointIntegrals (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

def matchingEndpointLimit (k : Fin 3) (p : ℝ) : ℝ :=
  match k.val with
  | 0 => markedOriginalLimit p
  | 1 => markedBootstrapLimit p
  | _ => markedReplicaLimit p

theorem matching_endpoint_pinned_limit (k : Fin 3) (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) :
    Tendsto (fun n => mean (MatchProduct n)
      (fun z => matchingEndpointMoment k (pin n p z) 0)) atTop
        (nhds (matchingEndpointLimit k p)) := by
  have hh := pinned_cell_second_moments p hp
  fin_cases k
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2

theorem matching_endpoint_integrated_limit (k : Fin 3) :
    Tendsto (fun n => mean (MatchProduct (n+1))
      (fun z => matchingEndpointMoment k z 0)) atTop
      (nhds (∫ p in Set.Icc (1/4 : ℝ) (3/4), 2*p*matchingEndpointLimit k p)) := by
  obtain ⟨C,hC,hbound⟩ := marked_pinned_integrands_bounded
  simp_rw [matching_endpoint_disintegration,integral_Icc_eq_integral_Ioo]
  apply tendsto_integral_of_dominated_convergence (fun _ => 2*C)
  · intro n
    exact (measurable_const.mul measurable_id |>.mul
      (matching_endpoint_pinned_measurable k n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    have hpin : |mean (MatchProduct n)
        (fun z => matchingEndpointMoment k (pin n p z) 0)| ≤ C := by
      have hh := hbound n p ⟨le_of_lt hp.1,le_of_lt hp.2⟩
      fin_cases k
      · exact hh.1
      · exact hh.2.1
      · exact hh.2.2
    rw [Real.norm_eq_abs,abs_mul]
    have hp2 : |2*p| ≤ 2 := by rw [abs_of_pos (by linarith [hp.1])]; linarith [hp.2]
    exact mul_le_mul hp2 hpin (abs_nonneg _) (by norm_num)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    exact tendsto_const_nhds.mul (matching_endpoint_pinned_limit k p hp)

/-- The three elementary score integrals, packaged for any quadratic in r. -/
theorem matching_endpoint_score_polynomial (A B C : ℝ) :
    (∫ p in Set.Icc (1/4 : ℝ) (3/4),
      2*p*(A+B*((1-p)/p)+C*((1-p)/p)^2)) =
        A/2+B/2+C*(2*Real.log 3-3/2) := by
  have hid : Integrable (fun p : ℝ => p) (volume.restrict (Set.Icc (1/4 : ℝ) (3/4))) :=
    continuous_id.continuousOn.integrableOn_Icc
  have hinv : Integrable (fun p : ℝ => 1/p) (volume.restrict (Set.Icc (1/4 : ℝ) (3/4))) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.div continuousOn_id (fun p hp => by linarith [hp.1])
  have hi : (∫ p in Set.Icc (1/4 : ℝ) (3/4), p) = (1/4 : ℝ) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num)]
    norm_num [integral_id]
  have hv : (∫ p : ℝ in Set.Icc (1/4 : ℝ) (3/4), 1/p) = Real.log 3 := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num),
      integral_one_div_of_pos (by norm_num) (by norm_num)]
    norm_num
  calc
    _ = ∫ p in Set.Icc (1/4 : ℝ) (3/4),
        ((2*A-2*B+2*C)*p+(2*B-4*C))+(2*C)*(1/p) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
      have hp0 : p ≠ 0 := by linarith [hp.1]
      field_simp
      <;> ring
    _ = A/2+B/2+C*(2*Real.log 3-3/2) := by
      have hlin : Integrable (fun p : ℝ => (2*A-2*B+2*C)*p+(2*B-4*C))
          (volume.restrict (Set.Icc (1/4 : ℝ) (3/4))) :=
        (hid.const_mul (2*A-2*B+2*C)).add (integrable_const (2*B-4*C))
      rw [integral_add hlin (hinv.const_mul (2*C)),
        integral_add (hid.const_mul (2*A-2*B+2*C)) (integrable_const (2*B-4*C)),
        integral_const_mul,integral_const_mul,hi,hv,integral_const]
      norm_num [Real.volume_Icc,smul_eq_mul]
      ring

theorem matching_endpoint_original_integral :
    (∫ p in Set.Icc (1/4 : ℝ) (3/4), 2*p*markedOriginalLimit p) = matchV := by
  have hh := matching_endpoint_score_polynomial 1 3 (3/2)
  convert hh using 1
  · apply integral_congr_ae
    exact ae_of_all _ (fun p => by unfold markedOriginalLimit; ring)
  · unfold matchV
    ring

theorem matching_endpoint_bootstrap_difference_integral :
    (∫ p in Set.Icc (1/4 : ℝ) (3/4), 2*p*markedBootstrapLimit p) -
      (∫ p in Set.Icc (1/4 : ℝ) (3/4), 2*p*markedReplicaLimit p) = matchVB := by
  have hcont := marked_limit_functions_continuousOn
  have hb : Integrable (fun p : ℝ => 2*p*markedBootstrapLimit p)
      (volume.restrict (Set.Icc (1/4 : ℝ) (3/4))) :=
    ((continuousOn_const.mul continuousOn_id).mul hcont.2.1).integrableOn_Icc
  have hr : Integrable (fun p : ℝ => 2*p*markedReplicaLimit p)
      (volume.restrict (Set.Icc (1/4 : ℝ) (3/4))) :=
    ((continuousOn_const.mul continuousOn_id).mul hcont.2.2).integrableOn_Icc
  rw [← integral_sub hb hr]
  calc
    _ = ∫ p in Set.Icc (1/4 : ℝ) (3/4),
        2*p*(1+matchA*((1-p)/p)+matchB*((1-p)/p)^2) := by
      apply integral_congr_ae
      apply ae_of_all
      intro p
      unfold markedBootstrapLimit markedReplicaLimit matchA matchB
      ring
    _ = matchVB := by
      rw [matching_endpoint_score_polynomial]
      rfl

theorem matching_endpoint_product_moment_limits :
    Tendsto (fun n => mean (MatchProduct (n+1))
      (fun z => matchingEndpointMoment 0 z 0)) atTop (nhds matchV) ∧
    Tendsto (fun n => mean (MatchProduct (n+1))
      (fun z => matchingEndpointMoment 1 z 0) - mean (MatchProduct (n+1))
        (fun z => matchingEndpointMoment 2 z 0)) atTop (nhds matchVB) := by
  constructor
  · convert matching_endpoint_integrated_limit 0 using 1
    congr 1
    exact matching_endpoint_original_integral.symm
  · convert (matching_endpoint_integrated_limit 1).sub (matching_endpoint_integrated_limit 2) using 1
    congr 1
    exact matching_endpoint_bootstrap_difference_integral.symm

end AronowAudit.P001.TailA
